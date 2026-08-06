/-
  Estimators + Q divider — simulation, cross-check, and synthesis tests.

  What is pinned here, and why each number matters:

  * **Divider**: the `Signal`-level FSM's pure mirror (`runDivision`) equals the
    arithmetic reference (`divQref`) on a sweep including negatives, division by
    zero, and saturation — at both Q7.8 and Q15.16.

  * **On-chip Riccati reproduces the offline design**: `tvkStep` iterated from
    `P = 0` converges to gains within 49 / 12 LSB of the offline steady-state
    constants baked into `kalmanQ15_16`.  This cross-validates the offline
    design script and the fixed-point recursion against each other.

  * **KF vs H∞, measured** (deterministic LCG seeds, so exact reproducibility):
      - random noise  (profile A): KF error energy 1081071 < H∞ 1087559 —
        Kalman wins on its home turf, by 0.6 %.
      - adversarial square-wave gust at half-period 10 (profile B): KF 1282428
        vs H∞ 1175037 — H∞ wins by ~9 %.
    The honest engineering summary the tutorial draws from this: H∞ costs ~1 %
    on average and buys single-digit-% worst-case improvement PLUS the proven
    `γ = 2` energy bound (`proofs/…/EstimatorDesign.hinf_energy_bound`) — the
    certificate, not the 9 %, is the real product.

  * **Circuit = pure model, twice over**: (a) `Signal.val` co-sim (40 observer
    cycles + five full tvKalman FSM samples) — restored after the issue-#95
    fix in `Sparkle/Core/CircuitMonad.lean` made it feasible; and (b) the
    **emitted Verilog** simulated under iverilog: the RTL divider computes
    1.0/3.0 → 21845 and −7.5/2.5 → −196608 exactly, and five tvKalman samples
    match `tvkStep` bit-for-bit (x̂₁ = 0, 0, 1581, 8167, 22409).  The RTL
    simulation is also what caught the two `extractNat`/`extractWidth`
    elaborator bugs (silent 8-bit default on symbolic widths — a miscompile
    invisible to every Lean-side check).
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.Observer
import LSpec

set_option maxRecDepth 100000

namespace Sparkle.Tests.IP.Control.ObserverTest

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPointGen
open Sparkle.IP.Control.DividerQ
open Sparkle.IP.Control.Observer
open LSpec

/-! ### Divider cross-check (pure FSM vs arithmetic reference) -/

def divCases : List (Int × Int) :=
  [(256, 256), (256, 128), (100, 300), (-256, 256), (256, -256), (-256, -256),
   (1, 3), (-1, 3), (1, -3), (5000, 7), (-5000, 7), (30000, 1), (-30000, 1),
   (0, 5), (7, 0), (-7, 0), (32767, 2), (-32767, 2), (1, 32767), (12345, -67)]

def divMismatches (w f : Nat) (cases : List (Int × Int)) : Nat :=
  cases.foldl (init := 0) fun acc (a, b) =>
    let num := BitVec.ofInt w a
    let den := BitVec.ofInt w b
    if runDivision w f num den == divQref w f num den then acc else acc + 1

/-! ### Measured KF vs H∞ profiles -/

def qv (n d : Int) : BitVec 32 := q 32 16 n d

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def noise (s : UInt64) (ampNum ampDen : Int) : BitVec 32 :=
  let u : Int := ((s >>> 20).toNat % 20001 : Nat) - 10000
  q 32 16 (u * ampNum) (10000 * ampDen)

structure Plant where
  x1 : BitVec 32
  x2 : BitVec 32

def plantStep (p : Plant) (w : BitVec 32) : Plant :=
  let dt := dtQ 32 16
  ⟨clampSym 32 (xLim 32 16) (satAdd 32 p.x1 (mulQ 32 16 dt p.x2)),
   clampSym 32 (xLim 32 16) (satAdd 32 p.x2 w)⟩

/-- Run both fixed-gain filters against the same plant; return the two error
    energies (in 1e-6 units).  `adversarial` switches the gust from LCG-uniform
    to the square wave at half-period 10 that the sweep found worst for KF. -/
def runProfile (adversarial : Bool) (n : Nat) : Int × Int := Id.run do
  let mut p : Plant := ⟨0#32, 0#32⟩
  let mut kf : Est 32 := default
  let mut hi : Est 32 := default
  let mut s : UInt64 := 20250806
  let mut ekf : Int := 0
  let mut ehi : Int := 0
  for i in [0:n] do
    s := lcg s
    let wg :=
      if adversarial then
        if (i / 10) % 2 == 0 then qv 5 10 else qv (-5) 10
      else
        noise s 5 10
    s := lcg s
    let v := if adversarial then 0#32 else noise s 1 10
    p := plantStep p wg
    let y := satAdd 32 p.x1 v
    kf := obsStep 32 16 (kfK1 32 16) (kfK2 32 16) kf y (0#32)
    hi := obsStep 32 16 (hinfK1 32 16) (hinfK2 32 16) hi y (0#32)
    let dk := (satAdd 32 kf.x1 (-p.x1)).toInt
    let dh := (satAdd 32 hi.x1 (-p.x1)).toInt
    ekf := ekf + dk * dk / 65536
    ehi := ehi + dh * dh / 65536
  pure (ekf, ehi)

/-! ### tvKalman convergence (pure) -/

def tvConverged : TVK 32 := Id.run do
  let mut st : TVK 32 := default
  for _ in [0:200] do
    st := tvkStep 32 16 st (0#32) (0#32)
  pure st

def suite : TestSeq :=
  let (randKF, randHI) := runProfile false 800
  let (advKF, advHI) := runProfile true 600
  let tv := tvConverged
  group "Estimators + divider" <|
    -- Divider: FSM = reference, everywhere in the sweep.
    test "dividerQ FSM matches divQref at Q7.8 (20 cases)"
      (divMismatches 16 8 divCases == 0) $
    test "dividerQ FSM matches divQref at Q15.16 (20 cases)"
      (divMismatches 32 16 divCases == 0) $
    -- On-chip Riccati reproduces the offline design.
    test "tvKalman k1 converges to the offline steady-state gain (±100 LSB)"
      ((tv.k1.toInt - (kfK1 32 16).toInt).natAbs ≤ 100) $
    test "tvKalman k2 converges to the offline steady-state gain (±100 LSB)"
      ((tv.k2.toInt - (kfK2 32 16).toInt).natAbs ≤ 100) $
    test "converged covariance is inside its clamp and positive on the diagonal"
      (0 ≤ tv.p11.toInt && 0 ≤ tv.p22.toInt
        && tv.p11.toInt ≤ (pLim 32 16).toInt && tv.p22.toInt ≤ (pLim 32 16).toInt) $
    -- KF vs H∞, both directions, deterministic.
    test "random noise: Kalman beats H∞ (its design case)"
      (decide (randKF < randHI)) $
    test "adversarial gust: H∞ beats Kalman"
      (decide (advHI < advKF)) $
    test "adversarial margin is real (KF ≥ 1.05 × H∞)"
      (decide (100 * advKF ≥ 105 * advHI))

/-! ### Circuit-vs-pure co-sim through `Signal.val`

This co-sim originally had to be REMOVED because it hung: the historical
`circuit do` write path composed per-slot update lenses that rebuilt the full
bundled next-state per write, and the closure evaluator (no sharing) paid
~k^k per cycle in the register count k — even this 2-register observer died
near t ≈ 20, and the 16-register `tvKalman` at t = 5.  That was issue #95.

The fix (in `Sparkle/Core/CircuitMonad.lean`): the `Circuit` monad now
threads a flat pending-writes tuple (`Circuit.SigList`) — a write is pure
tuple surgery and the register file is bundled once — so `Signal.val`
evaluation is linear and this test now runs in milliseconds.  It is kept
precisely because it was the failing case: a regression here means the
evaluator lost sharing again. -/

def cosim : IO (Nat × Bool) := do
  -- (1) fixed-gain observer, 40 cycles against obsRun.
  let ys : List (BitVec 32) :=
    (List.range 40).map fun t => if t < 3 then 0#32 else qv 1 1
  let ySig : Signal defaultDomain (BitVec 32) :=
    ⟨fun t => if t < 3 then 0#32 else qv 1 1⟩
  let circ := kalmanQ15_16 ySig (Signal.pure 0#32)
  let pureStates := obsRun 32 16 (kfK1 32 16) (kfK2 32 16) default
    (ys.map fun y => (y, 0#32))
  let mut mismatches := 0
  for t in [0:39] do
    let c := circ.val (t + 1)
    let p := (pureStates[t]?).map (·.x1) |>.getD (0#32)
    if c != p then mismatches := mismatches + 1
  -- (2) tvKalman: five full FSM samples vs five tvkStep applications
  --     (constant y = 1.0 latched at each tick, 130 cycles apart).
  let yOne : Signal defaultDomain (BitVec 32) := ⟨fun _ => qv 1 1⟩
  let tickSig : Signal defaultDomain Bool := ⟨fun t => t % 130 == 2⟩
  let tvC := tvKalman 32 16 yOne (Signal.pure 0#32) tickSig
  let mut pureTvk : TVK 32 := default
  let mut tvOk := true
  for k in [1:6] do
    pureTvk := tvkStep 32 16 pureTvk (qv 1 1) 0#32
    let got := tvC.val (k * 130)
    if got != pureTvk.x1 then tvOk := false
  pure (mismatches, tvOk)

def main : IO UInt32 := do
  let (obsMismatches, tvOk) ← cosim
  if obsMismatches != 0 then
    IO.eprintln s!"fixed-gain observer co-sim: {obsMismatches} cycle mismatches"
    return 1
  if !tvOk then
    IO.eprintln "tvKalman co-sim: FSM samples do not match tvkStep"
    return 1
  IO.println "co-sim (Signal.val, post-#95-fix): observer 40 cyc + tvKalman 5 samples match pure models"
  lspecIO (Std.HashMap.ofList [("all", [suite])]) []

/-- `IO Unit` wrapper for `Tests/AllTests.lean` (see IIRBiquadTest). -/
def mainUnit : IO Unit := do
  let code ← main
  if code != 0 then IO.Process.exit 1

/-! ### Synthesis checks -/

section SynthesisChecks

set_option maxHeartbeats 400000000

def kalmanTop (y u : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  kalmanQ15_16 y u

def hinfTop (y u : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  hinfQ15_16 y u

def dividerTop (num den : Signal defaultDomain (BitVec 32)) (start : Signal defaultDomain Bool)
    : Signal defaultDomain (BitVec 32) :=
  Signal.fst (dividerQ15_16 num den start)

def tvKalmanTop (y u : Signal defaultDomain (BitVec 32)) (tick : Signal defaultDomain Bool)
    : Signal defaultDomain (BitVec 32) :=
  tvKalman 32 16 y u tick

#synthesizeVerilog kalmanTop
#synthesizeVerilog hinfTop
#synthesizeVerilog dividerTop
#synthesizeVerilog tvKalmanTop

end SynthesisChecks

end Sparkle.Tests.IP.Control.ObserverTest
