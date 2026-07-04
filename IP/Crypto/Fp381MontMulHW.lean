/-
  IP.Crypto.Fp381MontMulHW — word-serial Montgomery modular
  multiplier for the BLS12-381 base field (Fp, 381-bit prime),
  Signal DSL.

  This is the HW analogue of blst's `mul_mont_384`: real-world
  BLS validator profiling shows the 384-bit Montgomery multiply
  is the single dominant cost (it is the innermost operation of
  Fp2/Fp6/Fp12 arithmetic, the Miller loop, and the final
  exponentiation).  Accelerating it in hardware speeds up every
  layer built on top.

  Algorithm: radix-2^32 CIOS (Coarsely Integrated Operand
  Scanning) Montgomery multiplication, one outer word per cycle.
  Operands are in the Montgomery domain (aM = a·R mod p); the
  module computes

      montmul(aM, bM) = aM · bM · R^-1 mod p            (R = 2^384)

  processing the 12 words of `b` LSB-first:

      t = 0
      for i = 0 .. 11:
          bi = word_i(b)                      -- 32-bit slice
          t  = t + a · bi                     -- 384×32 partial product
          m  = (low32(t) · n') mod 2^32       -- n' = -p^-1 mod 2^32
          t  = (t + m · p) >> 32              -- reduce one word
      if t ≥ p: t = t − p                     -- single conditional subtract

  Domain conversion (to/from Montgomery form) is the caller's
  job — do it once at the boundary of a scalar-mul / pairing,
  not per multiply.

  Interface:
    inputs  start (Bool pulse), aIn/bIn (BitVec 384, Montgomery)
    outputs result (BitVec 384, Montgomery), done (Bool pulse)

  Timing: start at cycle 0 ⇒ 12 word cycles (counts 1..12) ⇒
  done pulses at cycle 14, result valid.  Compare 258 cycles for
  the bit-serial engines: a ~18× per-multiply latency win.

  All intermediate arithmetic is carried in a 448-bit (14×32)
  space: the pre-shift value t + a·bi + m·p peaks at 414 bits,
  and the post-shift accumulator stays below 382 bits.
-/
import Sparkle
import IP.Crypto.Proof.BLS12_381

namespace Sparkle.IP.Crypto.Fp381MontMulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- The BLS12-381 base-field prime, embedded as a 448-bit
    constant (headroom for the CIOS intermediate). -/
def pBv : BitVec 448 := BitVec.ofNat 448 Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- p as a 384-bit constant (for the final conditional subtract
    on the reduced-width accumulator). -/
def pBv384 : BitVec 384 := BitVec.ofNat 384 Sparkle.IP.Crypto.BLS12_381.Fp.p

/-- Montgomery constant n' = -p^-1 mod 2^32, as a 448-bit value
    (only its low 32 bits matter; the multiply keeps low 32). -/
def nPrimeBv : BitVec 448 := BitVec.ofNat 448 0xfffcfffd

/-- Output record. -/
structure MulOut (dom : DomainConfig) where
  /-- The 384-bit Montgomery-domain field product (valid when
      `done` pulses). -/
  result : Signal dom (BitVec 384)
  /-- Pulses for one cycle when the multiply finishes. -/
  done   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MulOut dom) dom := ⟨⟩

/-- Word-serial CIOS Montgomery multiplier for BLS12-381 Fp. -/
def montMulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (aIn bIn : Signal dom (BitVec 384)) :
    MulOut dom :=
  circuit do
    -- 448-bit accumulator `t` (post-shift each cycle; < 2p).
    let accR ← Signal.reg (0#448)
    -- 384-bit operand a, latched on start.
    let aR ← Signal.reg (0#384)
    -- 384-bit operand b, shifted right 32 bits per cycle so the
    -- next word to process is always the low word.
    let bR ← Signal.reg (0#384)
    -- 5-bit counter 0..13.
    let cntR ← Signal.reg (0#5)
    -- done pulse.
    let doneR ← Signal.reg false

    let accSig := (accR : Signal dom (BitVec 448))
    let aSig   := (aR : Signal dom (BitVec 384))
    let bSig   := (bR : Signal dom (BitVec 384))
    let cntSig := (cntR : Signal dom (BitVec 5))

    let p0_5   := (Signal.pure 0#5  : Signal dom (BitVec 5))
    let p1_5   := (Signal.pure 1#5  : Signal dom (BitVec 5))
    -- Process 12 words on counts 1..12; finish (done) at count 13.
    let p13_5  := (Signal.pure 13#5 : Signal dom (BitVec 5))
    let pP     := (Signal.pure pBv  : Signal dom (BitVec 448))
    let nP     := (Signal.pure nPrimeBv : Signal dom (BitVec 448))

    let isIdle   := ((· == ·) <$> cntSig <*> p0_5 : Signal dom Bool)
    let isFinish := ((· == ·) <$> cntSig <*> p13_5 : Signal dom Bool)
    let busy     := ((fun i f => !(i || f)) <$> isIdle <*> isFinish : Signal dom Bool)

    -- Zero-prefix constants for widening.  We use the applicative
    -- `(· ++ ·) <$> zeroPrefix <*> value` form (which the synth
    -- elaborator lowers via the concat path) rather than
    -- `Signal.map (fun v => BitVec.append (0#N) v)`, because the
    -- map-with-append-lambda gets stuck in recursive inlining at
    -- these widths (see IP/Net/MemcachedServer.lean note).
    let z64  := (Signal.pure 0#64  : Signal dom (BitVec 64))
    let z416 := (Signal.pure 0#416 : Signal dom (BitVec 416))

    -- a widened to 448 bits (0#64 ++ a).
    let aWide := ((· ++ ·) <$> z64 <*> aSig : Signal dom (BitVec 448))

    -- Low 32-bit word of b, widened to 448 bits.
    let bLo32 := ((BitVec.extractLsb' 0 32 ·) <$> bSig : Signal dom (BitVec 32))
    let biWide := ((· ++ ·) <$> z416 <*> bLo32 : Signal dom (BitVec 448))

    -- t1 = t + a·bi (448-bit space).
    let abi := ((· * ·) <$> aWide <*> biWide : Signal dom (BitVec 448))
    let t1  := ((· + ·) <$> accSig <*> abi : Signal dom (BitVec 448))

    -- m = (low32(t1) · n') mod 2^32, held in the low 32 bits of a
    -- 448-bit value.
    let t1lo32 := ((BitVec.extractLsb' 0 32 ·) <$> t1 : Signal dom (BitVec 32))
    let t1lo := ((· ++ ·) <$> z416 <*> t1lo32 : Signal dom (BitVec 448))
    let mFull := ((· * ·) <$> t1lo <*> nP : Signal dom (BitVec 448))
    let mLo32 := ((BitVec.extractLsb' 0 32 ·) <$> mFull : Signal dom (BitVec 32))
    let m := ((· ++ ·) <$> z416 <*> mLo32 : Signal dom (BitVec 448))

    -- t2 = t1 + m·p, then shift down one word.
    let mp := ((· * ·) <$> m <*> pP : Signal dom (BitVec 448))
    let t2 := ((· + ·) <$> t1 <*> mp : Signal dom (BitVec 448))
    let p32_448 := (Signal.pure 32#448 : Signal dom (BitVec 448))
    let accNext := ((· >>> ·) <$> t2 <*> p32_448 : Signal dom (BitVec 448))

    -- b shifted right 32 bits each busy cycle.
    let p32_384 := (Signal.pure 32#384 : Signal dom (BitVec 384))
    let bShr := ((· >>> ·) <$> bSig <*> p32_384 : Signal dom (BitVec 384))
    -- cnt + 1.
    let cntInc := ((· + ·) <$> cntSig <*> p1_5 : Signal dom (BitVec 5))

    accR <~ Signal.mux start (Signal.pure 0#448 : Signal dom (BitVec 448))
              (Signal.mux busy accNext accSig)
    aR   <~ Signal.mux start aIn aSig
    bR   <~ Signal.mux start bIn
              (Signal.mux busy bShr bSig)
    cntR <~ Signal.mux start p1_5
              (Signal.mux isFinish p0_5
                (Signal.mux busy cntInc cntSig))
    doneR <~ isFinish

    -- Final conditional subtract of p on the 384-bit result:
    -- narrow the accumulator, compare against p, subtract if ≥.
    let accLo := ((BitVec.extractLsb' 0 384 ·) <$> accSig : Signal dom (BitVec 384))
    let pP384 := (Signal.pure pBv384 : Signal dom (BitVec 384))
    let ge    := ((BitVec.ule · ·) <$> pP384 <*> accLo : Signal dom Bool)
    let resOut := (Signal.mux ge ((· - ·) <$> accLo <*> pP384) accLo
                    : Signal dom (BitVec 384))

    return ({ result := resOut
            , done   := (doneR : Signal dom Bool)
            } : MulOut dom)

end Sparkle.IP.Crypto.Fp381MontMulHW
