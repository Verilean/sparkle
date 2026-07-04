/-
  IP.Crypto.G2ScalarMulHW — constant-time scalar multiplication
  k·P on BLS12-381 G2 via a Montgomery ladder over Jacobian
  coordinates, driving `G2PointOpHW.g2PointOpHW` (which in turn
  drives the Fp2 multiplier, which drives the Fp381 multiplier).

  This IS the BLS signing datapath: a BLS signature is
  σ = (sk mod r)·H(msg) ∈ G2 (see `BLS12_381.sign`).  Pass the
  scalar already reduced into [0, r) as `k`, and the hash point
  H(msg) as the base point P (Jacobian, Montgomery domain); the
  Jacobian result is σ.  Conversion to affine (one Fp2 inverse)
  and hash-to-curve are host concerns, exactly as the secp256k1
  signer takes the message hash `z` as an input.

  Structure: identical to `Secp256k1ScalarMulHW` — a Montgomery
  ladder (MSB-first, invariant R1 = R0 + P) that issues one ADD
  then one DOUBLE per scalar bit to a single shared point-op
  engine, with an `r0Inf` flag covering the leading-zero prefix
  where R0 is still ∞.  The scalar r is 255-bit, so we iterate
  bits 254 downto 0.

  Every point coordinate is an Fp2 element carried as two
  BitVec 384 signals (c0, c1).

  Composition: the point-op engine is driven over a flat
  start/done handshake (exposed `poStart`/`poOpDouble`/operand
  ports; `poResX0..poResZ1`/`poResDone` inputs), wired one level
  up — same synthesizable style as the whole stack.

  Cycle cost ≈ 255 · (add + double) ≈ 255 · (16 + 7) Fp2-muls ·
  48 cyc/Fp2-mul ≈ 255 · 1104 ≈ 281 k cycles per G2 scalar-mul
  (with the 14-cyc Fp381 Montgomery multiplier).

  SYNTH: this module drives `g2PointOpHW` over start/done PORTS
  (it does not inline it), so its own body is just the 12-register
  Fp2 ladder controller — `#synthesizeVerilog` completes in ~2 s.
  (The former super-linear translate wall on the wider G2 circuits
  is fixed by the O(1) wire-name collision check in
  Sparkle/IR/Builder.lean.)  Logic is additionally validated by the
  schedule-level sim cross-check against `BLS12_381.G2.mulScalar`.
-/
import Sparkle
import IP.Crypto.Proof.BLS12_381
import IP.Crypto.G2PointOpHW

namespace Sparkle.IP.Crypto.G2ScalarMulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output record.  Result is a G2 Jacobian point (Fp2 coords). -/
structure G2ScalarMulOut (dom : DomainConfig) where
  x0Out : Signal dom (BitVec 384)
  x1Out : Signal dom (BitVec 384)
  y0Out : Signal dom (BitVec 384)
  y1Out : Signal dom (BitVec 384)
  z0Out : Signal dom (BitVec 384)
  z1Out : Signal dom (BitVec 384)
  done : Signal dom Bool
  /-- Drive the external point-op engine. -/
  poStart : Signal dom Bool
  poOpDouble : Signal dom Bool
  poX1_0 : Signal dom (BitVec 384)
  poX1_1 : Signal dom (BitVec 384)
  poY1_0 : Signal dom (BitVec 384)
  poY1_1 : Signal dom (BitVec 384)
  poZ1_0 : Signal dom (BitVec 384)
  poZ1_1 : Signal dom (BitVec 384)
  poX2_0 : Signal dom (BitVec 384)
  poX2_1 : Signal dom (BitVec 384)
  poY2_0 : Signal dom (BitVec 384)
  poY2_1 : Signal dom (BitVec 384)
  poZ2_0 : Signal dom (BitVec 384)
  poZ2_1 : Signal dom (BitVec 384)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (G2ScalarMulOut dom) dom := ⟨⟩

/-- Bit `i` of a 256-bit scalar signal, as a Bool. -/
private def bitOf {dom : DomainConfig}
    (k : Signal dom (BitVec 256)) (iSig : Signal dom (BitVec 256)) :
    Signal dom Bool :=
  let sh := ((· >>> ·) <$> k <*> iSig : Signal dom (BitVec 256))
  let lo := (sh.map (fun v => v &&& 1#256) : Signal dom (BitVec 256))
  ((· == ·) <$> lo <*> (Signal.pure 1#256 : Signal dom (BitVec 256)))

/-- The G2 scalar-mul ladder FSM. -/
def g2ScalarMulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (k : Signal dom (BitVec 256))
    (px0 px1 py0 py1 pz0 pz1 : Signal dom (BitVec 384))
    (poResX0 poResX1 poResY0 poResY1 poResZ0 poResZ1 : Signal dom (BitVec 384))
    (poResDone : Signal dom Bool) :
    G2ScalarMulOut dom :=
  circuit do
    -- Phase: 0 idle, 1 issue-add, 2 wait-add, 3 issue-dbl, 4 wait-dbl, 5 complete.
    let phR ← Signal.reg (0#3)
    -- Bit index i (255..0), stored as BitVec 256 to feed the shifter.
    let biR ← Signal.reg (0#256)
    let kR ← Signal.reg (0#256)
    -- Ladder points R0, R1 (Jacobian, Fp2 coords).
    let r0x0R ← Signal.reg (0#384); let r0x1R ← Signal.reg (0#384)
    let r0y0R ← Signal.reg (0#384); let r0y1R ← Signal.reg (0#384)
    let r0z0R ← Signal.reg (0#384); let r0z1R ← Signal.reg (0#384)
    let r1x0R ← Signal.reg (0#384); let r1x1R ← Signal.reg (0#384)
    let r1y0R ← Signal.reg (0#384); let r1y1R ← Signal.reg (0#384)
    let r1z0R ← Signal.reg (0#384); let r1z1R ← Signal.reg (0#384)
    let r0InfR ← Signal.reg true
    let doneR ← Signal.reg false

    let phSig  := (phR : Signal dom (BitVec 3))
    let biSig  := (biR : Signal dom (BitVec 256))
    let kSig   := (kR : Signal dom (BitVec 256))
    let r0x0 := (r0x0R : Signal dom (BitVec 384)); let r0x1 := (r0x1R : Signal dom (BitVec 384))
    let r0y0 := (r0y0R : Signal dom (BitVec 384)); let r0y1 := (r0y1R : Signal dom (BitVec 384))
    let r0z0 := (r0z0R : Signal dom (BitVec 384)); let r0z1 := (r0z1R : Signal dom (BitVec 384))
    let r1x0 := (r1x0R : Signal dom (BitVec 384)); let r1x1 := (r1x1R : Signal dom (BitVec 384))
    let r1y0 := (r1y0R : Signal dom (BitVec 384)); let r1y1 := (r1y1R : Signal dom (BitVec 384))
    let r1z0 := (r1z0R : Signal dom (BitVec 384)); let r1z1 := (r1z1R : Signal dom (BitVec 384))
    let r0Inf := (r0InfR : Signal dom Bool)

    let ph1 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let ph2 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let ph3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let ph4 := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let ph5 := (Signal.pure 5#3 : Signal dom (BitVec 3))

    let isAddIssue := ((· == ·) <$> phSig <*> ph1 : Signal dom Bool)
    let isAddWait  := ((· == ·) <$> phSig <*> ph2 : Signal dom Bool)
    let isDblIssue := ((· == ·) <$> phSig <*> ph3 : Signal dom Bool)
    let isDblWait  := ((· == ·) <$> phSig <*> ph4 : Signal dom Bool)

    let bit := bitOf kSig biSig

    let opStart := ((· || ·) <$> isAddIssue <*> isDblIssue : Signal dom Bool)
    let opDouble := isDblIssue
    -- DOUBLE operand: bit ? R1 : R0.
    let dblX0 := (Signal.mux bit r1x0 r0x0 : Signal dom (BitVec 384))
    let dblX1 := (Signal.mux bit r1x1 r0x1 : Signal dom (BitVec 384))
    let dblY0 := (Signal.mux bit r1y0 r0y0 : Signal dom (BitVec 384))
    let dblY1 := (Signal.mux bit r1y1 r0y1 : Signal dom (BitVec 384))
    let dblZ0 := (Signal.mux bit r1z0 r0z0 : Signal dom (BitVec 384))
    let dblZ1 := (Signal.mux bit r1z1 r0z1 : Signal dom (BitVec 384))
    -- op1 = double ? dbl : R0 ; op2 = R1.
    let op1x0 := (Signal.mux opDouble dblX0 r0x0 : Signal dom (BitVec 384))
    let op1x1 := (Signal.mux opDouble dblX1 r0x1 : Signal dom (BitVec 384))
    let op1y0 := (Signal.mux opDouble dblY0 r0y0 : Signal dom (BitVec 384))
    let op1y1 := (Signal.mux opDouble dblY1 r0y1 : Signal dom (BitVec 384))
    let op1z0 := (Signal.mux opDouble dblZ0 r0z0 : Signal dom (BitVec 384))
    let op1z1 := (Signal.mux opDouble dblZ1 r0z1 : Signal dom (BitVec 384))

    let poDone := poResDone

    let addAck := ((· && ·) <$> isAddWait <*> poDone : Signal dom Bool)
    let dblAck := ((· && ·) <$> isDblWait <*> poDone : Signal dom Bool)

    let atBit0 := ((· == ·) <$> biSig <*> (Signal.pure 0#256 : Signal dom (BitVec 256))
                    : Signal dom Bool)

    -- ADD sum with ∞ correction: R0=∞ ⇒ R0+R1 = R1.
    let addSumX0 := (Signal.mux r0Inf r1x0 poResX0 : Signal dom (BitVec 384))
    let addSumX1 := (Signal.mux r0Inf r1x1 poResX1 : Signal dom (BitVec 384))
    let addSumY0 := (Signal.mux r0Inf r1y0 poResY0 : Signal dom (BitVec 384))
    let addSumY1 := (Signal.mux r0Inf r1y1 poResY1 : Signal dom (BitVec 384))
    let addSumZ0 := (Signal.mux r0Inf r1z0 poResZ0 : Signal dom (BitVec 384))
    let addSumZ1 := (Signal.mux r0Inf r1z1 poResZ1 : Signal dom (BitVec 384))

    let wrAddR0 := ((· && ·) <$> addAck <*> bit : Signal dom Bool)          -- bit=1
    let wrAddR1 := ((fun a b => a && !b) <$> addAck <*> bit : Signal dom Bool) -- bit=0
    let wrDblR0 := ((fun a b => a && !b) <$> dblAck <*> bit : Signal dom Bool) -- bit=0
    let wrDblR1 := ((· && ·) <$> dblAck <*> bit : Signal dom Bool)            -- bit=1

    let z0_384 := (Signal.pure 0#384 : Signal dom (BitVec 384))

    -- R0 registers: start ⇒ ∞ sentinel (0,0,0); addAck&bit ⇒ sum; dblAck&!bit ⇒ dbl.
    r0x0R <~ Signal.mux start z0_384 (Signal.mux wrAddR0 addSumX0 (Signal.mux wrDblR0 poResX0 r0x0))
    r0x1R <~ Signal.mux start z0_384 (Signal.mux wrAddR0 addSumX1 (Signal.mux wrDblR0 poResX1 r0x1))
    r0y0R <~ Signal.mux start z0_384 (Signal.mux wrAddR0 addSumY0 (Signal.mux wrDblR0 poResY0 r0y0))
    r0y1R <~ Signal.mux start z0_384 (Signal.mux wrAddR0 addSumY1 (Signal.mux wrDblR0 poResY1 r0y1))
    r0z0R <~ Signal.mux start z0_384 (Signal.mux wrAddR0 addSumZ0 (Signal.mux wrDblR0 poResZ0 r0z0))
    r0z1R <~ Signal.mux start z0_384 (Signal.mux wrAddR0 addSumZ1 (Signal.mux wrDblR0 poResZ1 r0z1))

    -- R1 registers: start ⇒ P; addAck&!bit ⇒ sum; dblAck&bit ⇒ dbl.
    r1x0R <~ Signal.mux start px0 (Signal.mux wrAddR1 addSumX0 (Signal.mux wrDblR1 poResX0 r1x0))
    r1x1R <~ Signal.mux start px1 (Signal.mux wrAddR1 addSumX1 (Signal.mux wrDblR1 poResX1 r1x1))
    r1y0R <~ Signal.mux start py0 (Signal.mux wrAddR1 addSumY0 (Signal.mux wrDblR1 poResY0 r1y0))
    r1y1R <~ Signal.mux start py1 (Signal.mux wrAddR1 addSumY1 (Signal.mux wrDblR1 poResY1 r1y1))
    r1z0R <~ Signal.mux start pz0 (Signal.mux wrAddR1 addSumZ0 (Signal.mux wrDblR1 poResZ0 r1z0))
    r1z1R <~ Signal.mux start pz1 (Signal.mux wrAddR1 addSumZ1 (Signal.mux wrDblR1 poResZ1 r1z1))

    let clearInf := ((· && ·) <$> wrAddR0 <*> r0Inf : Signal dom Bool)
    r0InfR <~ Signal.mux start (Signal.pure true : Signal dom Bool)
                (Signal.mux clearInf (Signal.pure false : Signal dom Bool) r0Inf)

    -- Phase / bit sequencing.
    let biDec := ((· - ·) <$> biSig <*> (Signal.pure 1#256 : Signal dom (BitVec 256))
                    : Signal dom (BitVec 256))
    let nextBit := ((fun d b0 => d && !b0) <$> dblAck <*> atBit0 : Signal dom Bool)
    let finish  := ((· && ·) <$> dblAck <*> atBit0 : Signal dom Bool)

    phR <~ Signal.mux start ph1
             (Signal.mux isAddIssue ph2
               (Signal.mux addAck ph3
                 (Signal.mux isDblIssue ph4
                   (Signal.mux nextBit ph1
                     (Signal.mux finish ph5 phSig)))))

    -- BLS scalar r is 255-bit ⇒ start the scan at bit 254.
    biR <~ Signal.mux start (Signal.pure 254#256 : Signal dom (BitVec 256))
             (Signal.mux nextBit biDec biSig)

    kR <~ Signal.mux start k kSig
    doneR <~ finish

    return ({ x0Out := r0x0, x1Out := r0x1
            , y0Out := r0y0, y1Out := r0y1
            , z0Out := r0z0, z1Out := r0z1
            , done := (doneR : Signal dom Bool)
            , poStart := opStart
            , poOpDouble := opDouble
            , poX1_0 := op1x0, poX1_1 := op1x1
            , poY1_0 := op1y0, poY1_1 := op1y1
            , poZ1_0 := op1z0, poZ1_1 := op1z1
            , poX2_0 := r1x0, poX2_1 := r1x1
            , poY2_0 := r1y0, poY2_1 := r1y1
            , poZ2_0 := r1z0, poZ2_1 := r1z1
            } : G2ScalarMulOut dom)

end Sparkle.IP.Crypto.G2ScalarMulHW
