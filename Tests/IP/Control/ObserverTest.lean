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

  * **No `Signal.val` co-sim** — deliberately; see the note above `main` for
    why (issue #95: unshared loop evaluation is exponential in the number of
    state-register references).  The circuit↔model correspondence was instead
    verified at the STRONGEST level available: simulating the **emitted
    Verilog** under iverilog.  The RTL divider computes 1.0/3.0 → 21845 and
    −7.5/2.5 → −196608 exactly, and five full tvKalman samples (FSM + shared
    divider + covariance recursion, y = 1.0 held) match `tvkStep` bit-for-bit:
    x̂₁ = 0, 0, 1581, 8167, 22409 from both.  That RTL simulation is also what
    caught the two `extractNat`/`extractWidth` elaborator bugs that Lean-side
    testing structurally cannot see (silent 8-bit default on symbolic widths —
    a miscompile).
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

/-! ### Why there is no `Signal.val` co-sim here

The natural next test — driving `kalmanQ15_16` / `tvKalman` cycle-by-cycle via
`Signal.val` and comparing against `obsRun` / `tvkStep` — **hangs**: compiled
`Signal.loop` evaluation has no sharing, so a loop body that references its
state registers k times costs O(kᵗ) at cycle t.  Even the 2-register observer
becomes infeasible near t ≈ 20; the 16-register `tvKalman` FSM is hopeless.
This is issue #95 (the Keccak-sponge co-sim hang), reproduced here on a much
smaller circuit — the branching factor, not the register count, is what kills
it.

The repo's two working escapes are `Signal.loopMemo` simulation variants
(see `IP/YOLOv8/Primitives/Conv2DEngine.conv2DEngineSimulate`) and the CSim
JIT harness (see the PolicySignDemo tests).  Wiring the estimators into the
JIT harness is the right follow-up; until then the correspondence is carried
by (a) the pure-FSM-vs-reference cross-checks above, (b) the circuit bodies
mirroring the pure steps definition-for-definition, and (c) the
`#synthesizeVerilog` checks below. -/

def main : IO UInt32 := do
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
