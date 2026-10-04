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

  * **`Signal.val` co-sim** — present, as the `Signal.val co-sim (issue #95
    closed)` group below.  It could not exist for most of this file's life:
    unshared loop evaluation was exponential in the number of state-register
    references (issue #95; even the 2-register observer died near t ≈ 20).
    The flat pending-writes accumulator landed in PR #109 made evaluation
    linear, and the exact test that note declared impossible now runs in
    milliseconds.  The correspondence is additionally verified at the
    STRONGEST level available: simulating the **emitted Verilog** under
    iverilog.  The RTL divider computes 1.0/3.0 → 21845 and
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

/-! ### `Signal.val` co-sim — the test issue #95 used to rule out

For most of this file's life the natural test — driving `kalmanQ15_16` /
`tvKalman` cycle-by-cycle via `Signal.val` against `obsRun` / `tvkStep` —
**hung**: compiled `Signal.loop` evaluation had no sharing, so a loop body
referencing its state registers k times cost O(kᵗ) at cycle t, and even the
2-register observer died near t ≈ 20.  That was issue #95.

The flat pending-writes accumulator (`Circuit.SigList`, landed in PR #109
after its first attempt was reverted over the wide-record `.proj` miscompile)
made evaluation linear, so the impossible test is now just a test.  Measured
while closing #95: a 10-register chain samples t = 1000 in 0 ms, and the
40-cycle Kalman co-sim below runs in under a millisecond.

What #95 leaves in place: >64-bit datapaths (Keccak-f, SHA-512) are
*structurally* linear now but still pay per-op boxed-GMP costs under the
interpreter, so the CSim JIT (`lake exe control-jit-test`, three-backend
pattern) remains the recommended path for those.  This module is 32-bit
arithmetic, so `Signal.val` completes the backend triple here:
Signal.val / CSim JIT / iverilog, all against the same pure models. -/

/-- 40 cycles of the fixed-gain observer via `Signal.val`, y = 1.0 held. -/
def kalmanValTrace : List (BitVec 32) :=
  let one := q 32 16 1 1
  let hw : Signal defaultDomain (BitVec 32) :=
    kalmanQ15_16 (Signal.pure one) (Signal.pure 0#32)
  (List.range 40).map fun t => Signal.val hw t

/-- The same 40 cycles from the pure model (registered-output alignment:
    the value read at cycle t is the state after t steps, so t = 0 reads the
    reset value and t reads `obsRun`'s step t−1). -/
def kalmanValExpected : List (BitVec 32) :=
  let one := q 32 16 1 1
  let ys := List.replicate 40 one
  let pure := obsRun 32 16 (kfK1 32 16) (kfK2 32 16) default
    (ys.map fun y => (y, 0#32))
  (List.range 40).map fun t =>
    if t == 0 then (0#32 : BitVec 32) else ((pure[t-1]?).map (·.x1)).getD 0#32

/-- A tick that pulses at t = 0, 131, 262, … — one `tvKalman` sample per
    period, mirroring the JIT driver's pulse-then-hold-low protocol. -/
def tickEvery131 : Signal defaultDomain Bool :=
  let cnt : Signal defaultDomain (BitVec 8) := Signal.loop fun c =>
    Signal.register 0#8
      (Signal.mux (c === (130#8 : BitVec 8)) (Signal.pure 0#8) (c + 1#8))
  cnt === (0#8 : BitVec 8)

/-- Three full `tvKalman` FSM samples (16-register FSM + nested 50-cycle
    divider engine) via `Signal.val`, read at the end of each 131-cycle
    period. -/
def tvkValSamples : List (BitVec 32) :=
  let one := q 32 16 1 1
  let hw : Signal defaultDomain (BitVec 32) :=
    tvKalman 32 16 (Signal.pure one) (Signal.pure 0#32) tickEvery131
  [Signal.val hw 130, Signal.val hw 261, Signal.val hw 392]

def tvkValExpected : List (BitVec 32) := Id.run do
  let one := q 32 16 1 1
  let mut st : TVK 32 := default
  let mut out : List (BitVec 32) := []
  for _ in [0:3] do
    st := tvkStep 32 16 st one 0#32
    out := out ++ [st.x1]
  pure out

def valCoSimSuite : TestSeq :=
  group "Signal.val co-sim (issue #95 closed)" <|
    test "kalmanQ15_16: 40 cycles match obsRun bit-for-bit"
      (kalmanValTrace == kalmanValExpected) $
    test "tvKalman: 3 full FSM samples (divider engine incl.) match tvkStep"
      (tvkValSamples == tvkValExpected) $
    -- the third sample is the first NON-ZERO one (0, 0, 1581) — pin it so a
    -- co-sim that trivially reads zeros cannot pass
    test "third sample is the documented non-zero 1581"
      ((tvkValExpected[2]?.map (·.toInt)).getD 0 == 1581)

def main : IO UInt32 := do
  lspecIO (Std.HashMap.ofList [("all", [suite, valCoSimSuite])]) []

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
