/-
  FFTTests.FFTTest — the executable half of the FFT verification.

  Three layers of claim, weakest first:

  1. **`Zp` arithmetic is the modular arithmetic it claims to be.**
     The Barrett multiplier is checked against `(a·b) mod p` across
     every residue `a` paired with a spread of `b`, and add/sub across
     the wrap boundary.

  2. **The networks compute the DFT.**  `ct` and `ctFourStep` are
     compared to `dft` — over `Zp` this is *exact*, which is the whole
     reason the NTT instance is the right first target: no error
     budget, no tolerance, just `==`.

  3. **The circuit computes what the model computes.**  The same
     networks instantiated at `Signal dom (Zp ...)` are sampled and
     compared to the value-level run, and the pipelined variant is
     checked at its stated latency.

  The fixed-point instance can only be checked to a tolerance, so its
  tests assert an LSB bound rather than equality — and assert that the
  bound is *small*, which is the part that would break first if the
  rounding in `Cx.mul` regressed.
-/
import LSpec
import FFT

namespace FFTNTT.Tests

open FFTNTT
open Sparkle.Core.Domain
open Sparkle.Core.Signal

abbrev D : DomainConfig := defaultDomain

/-! ## Layer 1 — modular arithmetic -/

private def barrettMismatches : Nat := Id.run do
  let mut bad := 0
  for a in [0:12289] do
    for b in [0, 1, 2, 3, 97, 4096, 6144, 7777, 12287, 12288] do
      let x : Z12289 := Zp.ofNat 12289 14 a
      let y : Z12289 := Zp.ofNat 12289 14 b
      if (Zp.mul x y).toNat != (Zp.mulSpec x y).toNat then bad := bad + 1
  return bad

private def addSubMismatches : Nat := Id.run do
  let mut bad := 0
  for a in [0:12289] do
    for b in [0, 1, 6144, 12287, 12288] do
      let x : Z12289 := Zp.ofNat 12289 14 a
      let y : Z12289 := Zp.ofNat 12289 14 b
      if (Zp.add x y).toNat != (a + b) % 12289 then bad := bad + 1
      if (Zp.sub x y).toNat != (a + 12289 - b) % 12289 then bad := bad + 1
  return bad

def testModArith : IO LSpec.TestSeq := do
  -- ω_8 has order 8 and ω_8^4 = −1: the property every butterfly relies on.
  let w8  := (FFTRoot.twiddle (α := Z12289) 8 1)
  let w8_4 := (FFTRoot.twiddle (α := Z12289) 8 4)
  let w8_8 := (FFTRoot.twiddle (α := Z12289) 8 8)
  pure <| LSpec.group "Zp 12289 arithmetic" (
    LSpec.test "Barrett mul = (a*b) mod p"        (barrettMismatches == 0) ++
    LSpec.test "add/sub wrap correctly"           (addSubMismatches == 0) ++
    LSpec.test "w8^4 = -1"                        (w8_4.toNat == 12288) ++
    LSpec.test "w8^8 = 1"                         (w8_8.toNat == 1) ++
    LSpec.test "w8 is not itself 1"               (w8.toNat != 1)
  )

/-! ## Layer 2 — the networks compute the DFT (exactly, over Zp) -/

private def sampleZ (n : Nat) : HVec Z12289 n :=
  fun i => Zp.ofNat 12289 14 (i.val * i.val * 7 + 3)

private def natsZ {n : Nat} (x : HVec Z12289 n) : List Nat :=
  (HVec.toList x).map Zp.toNat

def testNTT : IO LSpec.TestSeq := do
  let x8  := sampleZ 8
  let x16 := sampleZ 16
  pure <| LSpec.group "NTT networks vs naive DFT" (
    LSpec.test "ct 3 = dft 8"
      (natsZ (ct (β := Z12289) 3 x8) == natsZ (dft (β := Z12289) 8 x8)) ++
    LSpec.test "ct 4 = dft 16"
      (natsZ (ct (β := Z12289) 4 x16) == natsZ (dft (β := Z12289) 16 x16)) ++
    LSpec.test "four-step 4x4 = ct 4"
      (natsZ (ctFourStep (β := Z12289) 2 2 x16) == natsZ (ct (β := Z12289) 4 x16)) ++
    LSpec.test "four-step 2x4 = ct 3"
      (natsZ (ctFourStep (β := Z12289) 1 2 x8) == natsZ (ct (β := Z12289) 3 x8)) ++
    LSpec.test "four-step 4x2 = ct 3"
      (natsZ (ctFourStep (β := Z12289) 2 1 x8) == natsZ (ct (β := Z12289) 3 x8)) ++
    LSpec.test "inverse round-trips"
      (natsZ (ict (β := Z12289) 4 (ct (β := Z12289) 4 x16)) == natsZ x16)
  )

/-- A non-power-of-two split, to pin down that the four-step index
    algebra is general and not accidentally radix-2 specific. -/
def testFourStepGeneral : IO LSpec.TestSeq := do
  let x12 : HVec Z12289 12 := sampleZ 12
  pure <| LSpec.group "four-step, N = 3 * 4" (
    LSpec.test "dftFourStep 3 4 = dft 12"
      (natsZ (dftFourStep (β := Z12289) 3 4 x12) == natsZ (dft (β := Z12289) 12 x12))
  )

/-! ## Layer 3 — circuit equals model -/

private def sampleSig (n : Nat) : HVec (Signal D Z12289) n :=
  fun i => Signal.pure (Zp.ofNat 12289 14 (i.val * i.val * 7 + 3))

private def sampleAt {n : Nat} (t : Nat) (x : HVec (Signal D Z12289) n) : List Nat :=
  (HVec.toList x).map (fun s => (s.val t).toNat)

def testCircuit : IO LSpec.TestSeq := do
  let model := natsZ (ct (β := Z12289) 3 (sampleZ 8))
  let comb  := sampleAt 0 (ct (β := Signal D Z12289) 3 (sampleSig 8))
  let piped := sampleAt (ctPipelinedLatency 3) (ctPipelined Z12289 3 (sampleSig 8))
  let pipedEarly := sampleAt 0 (ctPipelined Z12289 3 (sampleSig 8))
  let fsPiped := sampleAt (ctFourStepLatency 1 2) (ctFourStepPipelined Z12289 1 2 (sampleSig 8))
  pure <| LSpec.group "circuit = model" (
    LSpec.test "combinational ct matches the value model" (comb == model) ++
    LSpec.test "pipelined ct matches at stated latency"   (piped == model) ++
    LSpec.test "pipelined ct is not yet valid at t=0"     (pipedEarly != model) ++
    LSpec.test "pipelined four-step matches at latency"   (fsPiped == model)
  )

/-! ## Fixed point — tolerance, not equality -/

private def sampleCx : HVec C16_14 16 :=
  fun i => Cx.ofFloats 16 14 (0.0625 * Float.sin (2.0 * piF * 3.0 * i.val.toFloat / 16.0)) 0.0

/-- Largest componentwise difference, in LSB. -/
private def maxLsbDiff {n : Nat} (a b : HVec C16_14 n) : Nat := Id.run do
  let mut m := 0
  for (u, v) in (HVec.toList a).zip (HVec.toList b) do
    m := max m (max (u.re.toInt - v.re.toInt).natAbs (u.im.toInt - v.im.toInt).natAbs)
  return m

def testFixed : IO LSpec.TestSeq := do
  let x := sampleCx
  let viaCT := ct (β := C16_14) 4 x
  let viaFS := ctFourStep (β := C16_14) 2 2 x
  let viaDFT := dft (β := C16_14) 16 x
  -- A real sine at bin 3, amplitude 1/16, over 16 points: the spectrum
  -- is purely imaginary, ∓N·A/2 = ∓0.5 at bins 3 and 13.
  let peak3 := (viaCT ⟨3, by omega⟩).im.toInt
  let peak13 := (viaCT ⟨13, by omega⟩).im.toInt
  let expected : Int := 8192   -- 0.5 in Q1.14
  pure <| LSpec.group "fixed-point Q1.14 FFT" (
    LSpec.test "bin 3 is -0.5 within 2 LSB"    ((peak3 + expected).natAbs ≤ 2) ++
    LSpec.test "bin 13 is +0.5 within 2 LSB"   ((peak13 - expected).natAbs ≤ 2) ++
    LSpec.test "ct agrees with dft to 2 LSB"   (maxLsbDiff viaCT viaDFT ≤ 2) ++
    LSpec.test "four-step agrees with ct to 2 LSB" (maxLsbDiff viaCT viaFS ≤ 2) ++
    -- The rounding in Cx.mul is what keeps this tight; drop the
    -- round-to-nearest bias term and this jumps.
    LSpec.test "and the agreement is actually tight" (maxLsbDiff viaCT viaFS ≤ 1)
  )

def testCxAlgebra : IO LSpec.TestSeq := do
  let i : C16_14 := Cx.ofFloats 16 14 0.0 1.0
  let ii := Cx.mul i i
  let one : C16_14 := Cx.ofFloats 16 14 1.0 0.0
  let w8 := (FFTRoot.twiddle (α := C16_14) 8 2)
  pure <| LSpec.group "Cx 16 14 arithmetic" (
    LSpec.test "i * i = -1"        (ii.re.toInt == -16384 && ii.im.toInt == 0) ++
    LSpec.test "1 * 1 = 1"         (Cx.mul one one == one) ++
    LSpec.test "w8^2 = -i"         (w8.re.toInt == 0 && w8.im.toInt == -16384)
  )

/-! ## The synthesisable carrier

    `algOnRtl` re-expresses the modular arithmetic in the subset of
    operators Sparkle's Verilog elaborator recognises.  It is a
    *different program* from `Zp.add` / `Zp.mul` — mux-and-subtract
    instead of a lifted Lean `if` — so it needs checking against the
    model rather than inheriting its correctness. -/

private def rtlIn : Nat → Signal D (BitVec RtlW) :=
  fun i => Signal.pure (BitVec.ofNat RtlW ([3, 11, 4096, 12288, 7, 5000, 1, 9999].getD i 0))

private def rtlModel : HVec Z12289 8 :=
  fun i => Zp.ofNat 12289 14 ([3, 11, 4096, 12288, 7, 5000, 1, 9999].getD i.val 0)

private def tup8 (t : Nat)
    (o : Signal D (BitVec RtlW) × Signal D (BitVec RtlW) × Signal D (BitVec RtlW) ×
         Signal D (BitVec RtlW) × Signal D (BitVec RtlW) × Signal D (BitVec RtlW) ×
         Signal D (BitVec RtlW) × Signal D (BitVec RtlW)) : List Nat :=
  [o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1, o.2.2.2.2.2.1,
   o.2.2.2.2.2.2.1, o.2.2.2.2.2.2.2].map (fun s => (s.val t).toNat)

def testRtl : IO LSpec.TestSeq := do
  let model := natsZ (ct (β := Z12289) 3 rtlModel)
  let comb := tup8 0 (ntt8 (dom := D) (rtlIn 0) (rtlIn 1) (rtlIn 2) (rtlIn 3)
                            (rtlIn 4) (rtlIn 5) (rtlIn 6) (rtlIn 7))
  let fs := tup8 0 (ntt8fourStep (dom := D) (rtlIn 0) (rtlIn 1) (rtlIn 2) (rtlIn 3)
                                  (rtlIn 4) (rtlIn 5) (rtlIn 6) (rtlIn 7))
  let piped := tup8 3 (ntt8p (dom := D) (rtlIn 0) (rtlIn 1) (rtlIn 2) (rtlIn 3)
                              (rtlIn 4) (rtlIn 5) (rtlIn 6) (rtlIn 7))
  let pipedEarly := tup8 2 (ntt8p (dom := D) (rtlIn 0) (rtlIn 1) (rtlIn 2) (rtlIn 3)
                                   (rtlIn 4) (rtlIn 5) (rtlIn 6) (rtlIn 7))
  pure <| LSpec.group "RTL carrier = model" (
    LSpec.test "ntt8 (mux/Barrett RTL) matches the Zp model" (comb == model) ++
    LSpec.test "ntt8fourStep matches the Zp model"           (fs == model) ++
    LSpec.test "ntt8p valid at latency 3"                    (piped == model) ++
    LSpec.test "ntt8p not yet valid at cycle 2"              (pipedEarly != model)
  )

def suite : IO LSpec.TestSeq := do
  let a ← testModArith
  let b ← testNTT
  let c ← testFourStepGeneral
  let d ← testCircuit
  let e ← testCxAlgebra
  let f ← testFixed
  let g ← testRtl
  pure (a ++ b ++ c ++ d ++ e ++ f ++ g)

end FFTNTT.Tests
