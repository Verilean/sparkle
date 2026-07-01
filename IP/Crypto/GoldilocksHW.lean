/-
  IP.Crypto.GoldilocksHW — multi-cycle modular multiplier for
  the Goldilocks field (p = 2^64 - 2^32 + 1), Signal DSL.

  Algorithm: bit-serial "double-and-add" modular multiply
  (a.k.a. Russian-peasant mod p), processing the multiplier `b`
  MSB-first, one bit per cycle:

      acc = 0
      for i = 63 downto 0:
          acc = (2·acc)      mod p        -- shift
          if bit_i(b):  acc = (acc + a)   mod p        -- add

  Each `mod p` is at most a single conditional subtract of `p`
  because the intermediate stays below `2p`.  This computes
  exactly `(a·b) mod p`, matching `Goldilocks.mul`.

  Interface:
    inputs  start (Bool pulse), aIn/bIn (BitVec 64)
    outputs result (BitVec 64), done (Bool pulse)

  Timing: start at cycle 0 ⇒ 64 round cycles (counts 1..64) ⇒
  done pulses at cycle 66, result valid.

  This is Wave-2's cheapest field-mul HW warm-up (64-bit); the
  same shift-add skeleton scales to the 256-bit curve fields.
-/
import Sparkle
import IP.Crypto.Goldilocks

namespace Sparkle.IP.Crypto.GoldilocksHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Goldilocks prime as a 66-bit constant (headroom for the
    2·acc + a intermediate, which stays below 3p < 2^66). -/
def pBv : BitVec 66 := BitVec.ofNat 66 Sparkle.IP.Crypto.Goldilocks.p

/-- Output record. -/
structure MulOut (dom : DomainConfig) where
  /-- The 64-bit field product (valid when `done` pulses). -/
  result : Signal dom (BitVec 64)
  /-- Pulses for one cycle when the multiply finishes. -/
  done   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MulOut dom) dom := ⟨⟩

/-- Bit-serial Goldilocks modular multiplier. -/
def mulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (aIn bIn : Signal dom (BitVec 64)) :
    MulOut dom :=
  circuit do
    -- 66-bit accumulator (always reduced to < p at cycle end).
    let accR ← Signal.reg (0#66)
    -- 64-bit operand a, latched on start.
    let aR ← Signal.reg (0#64)
    -- 64-bit operand b, shifted left one bit per cycle (MSB first).
    let bR ← Signal.reg (0#64)
    -- 7-bit counter 0..64.
    let cntR ← Signal.reg (0#7)
    -- done pulse.
    let doneR ← Signal.reg false

    let accSig := (accR : Signal dom (BitVec 66))
    let aSig   := (aR : Signal dom (BitVec 64))
    let bSig   := (bR : Signal dom (BitVec 64))
    let cntSig := (cntR : Signal dom (BitVec 7))

    let p0_7   := (Signal.pure 0#7  : Signal dom (BitVec 7))
    let p1_7   := (Signal.pure 1#7  : Signal dom (BitVec 7))
    -- Process 64 bits on counts 1..64; finish (done pulse) at count 65.
    let p65_7  := (Signal.pure 65#7 : Signal dom (BitVec 7))
    let pP     := (Signal.pure pBv  : Signal dom (BitVec 66))

    let isIdle   := ((· == ·) <$> cntSig <*> p0_7 : Signal dom Bool)
    let isFinish := ((· == ·) <$> cntSig <*> p65_7 : Signal dom Bool)
    let busy     := ((fun i f => !(i || f)) <$> isIdle <*> isFinish : Signal dom Bool)

    -- Widen a to 66 bits for the add (zero-extend via prefix append).
    let aWide := (aSig.map (fun v => BitVec.append (0#2) v) : Signal dom (BitVec 66))

    -- MSB of b (bit 63): shift right 63.
    let p63_64 := (Signal.pure 63#64 : Signal dom (BitVec 64))
    let p0_64  := (Signal.pure 0#64  : Signal dom (BitVec 64))
    let bHi    := ((· >>> ·) <$> bSig <*> p63_64 : Signal dom (BitVec 64))
    let bHiZ   := ((· == ·) <$> bHi <*> p0_64 : Signal dom Bool)
    let bMsb   := ((fun z => !z) <$> bHiZ : Signal dom Bool)

    -- acc doubled (66-bit shift), then reduce once mod p.
    -- Reduction is a conditional subtract of p: subtract when p ≤ x.
    let p1_66     := (Signal.pure 1#66 : Signal dom (BitVec 66))
    let accDbl    := ((· <<< ·) <$> accSig <*> p1_66 : Signal dom (BitVec 66))
    let dblGe     := ((BitVec.ule · ·) <$> pP <*> accDbl : Signal dom Bool)
    let accDblRed := (Signal.mux dblGe ((· - ·) <$> accDbl <*> pP) accDbl
                        : Signal dom (BitVec 66))
    -- optionally add a, then reduce once mod p.
    let accPlusA  := ((· + ·) <$> accDblRed <*> aWide : Signal dom (BitVec 66))
    let addGe     := ((BitVec.ule · ·) <$> pP <*> accPlusA : Signal dom Bool)
    let accAddRed := (Signal.mux addGe ((· - ·) <$> accPlusA <*> pP) accPlusA
                        : Signal dom (BitVec 66))
    -- next acc: add-branch when bMsb, else the doubled-reduced value.
    let accNext   := (Signal.mux bMsb accAddRed accDblRed : Signal dom (BitVec 66))

    -- b shifted left one bit each busy cycle.
    let bShl := ((· <<< ·) <$> bSig <*> (Signal.pure 1#64 : Signal dom (BitVec 64))
                  : Signal dom (BitVec 64))
    -- cnt + 1.
    let cntInc := ((· + ·) <$> cntSig <*> p1_7 : Signal dom (BitVec 7))

    accR <~ Signal.mux start (Signal.pure 0#66 : Signal dom (BitVec 66))
              (Signal.mux busy accNext accSig)
    aR   <~ Signal.mux start aIn aSig
    bR   <~ Signal.mux start bIn
              (Signal.mux busy bShl bSig)
    cntR <~ Signal.mux start p1_7
              (Signal.mux isFinish p0_7
                (Signal.mux busy cntInc cntSig))
    doneR <~ isFinish

    -- Narrow the reduced accumulator to 64 bits for output.
    let resOut := ((BitVec.extractLsb' 0 64 ·) <$> accSig : Signal dom (BitVec 64))

    return ({ result := resOut
            , done   := (doneR : Signal dom Bool)
            } : MulOut dom)

end Sparkle.IP.Crypto.GoldilocksHW
