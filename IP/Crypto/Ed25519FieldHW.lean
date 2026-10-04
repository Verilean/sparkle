/-
  IP.Crypto.Ed25519FieldHW — multi-cycle modular multiplier for
  the Curve25519 base field (p = 2^255 - 19), Signal DSL.

  This is the HW engine promised in `IP/Crypto/Ed25519Field.lean`'s
  docstring ("The HW engine … follows in L.2.b").  Rather than a
  5-limb 51-bit radix pipeline, this ships the correctness-first
  bit-serial "double-and-add" modular multiply (Russian-peasant
  mod p), processing the multiplier `b` MSB-first one bit/cycle:

      acc = 0
      for i = 255 downto 0:
          acc = (2·acc)      mod p        -- shift
          if bit_i(b):  acc = (acc + a)   mod p        -- add

  Each `mod p` is at most a single conditional subtract of `p`
  because the intermediate stays below `2p`.  This computes
  exactly `(a·b) mod p`, matching `Ed25519Field.mul`.

  Interface:
    inputs  start (Bool pulse), aIn/bIn (BitVec 256)
    outputs result (BitVec 256), done (Bool pulse)

  Timing: start at cycle 0 ⇒ 256 round cycles (counts 1..256) ⇒
  done pulses at cycle 258, result valid.

  Same shift-add skeleton as the 64-bit Goldilocks warm-up,
  widened to 256-bit operands with a 258-bit accumulator.
-/
import Sparkle
import IP.Crypto.Proof.Ed25519Field

namespace Sparkle.IP.Crypto.Ed25519FieldHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Curve25519 prime as a 258-bit constant (headroom for the
    2·acc + a intermediate, which stays below 3p < 2^258). -/
def pBv : BitVec 258 := BitVec.ofNat 258 Sparkle.IP.Crypto.Ed25519Field.p

/-- Output record. -/
structure MulOut (dom : DomainConfig) where
  /-- The 256-bit field product (valid when `done` pulses). -/
  result : Signal dom (BitVec 256)
  /-- Pulses for one cycle when the multiply finishes. -/
  done   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MulOut dom) dom := ⟨⟩

/-- Bit-serial Curve25519 field modular multiplier. -/
def mulHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (aIn bIn : Signal dom (BitVec 256)) :
    MulOut dom :=
  circuit do
    -- 258-bit accumulator (always reduced to < p at cycle end).
    let accR ← Signal.reg (0#258)
    -- 256-bit operand a, latched on start.
    let aR ← Signal.reg (0#256)
    -- 256-bit operand b, shifted left one bit per cycle (MSB first).
    let bR ← Signal.reg (0#256)
    -- 9-bit counter 0..257.
    let cntR ← Signal.reg (0#9)
    -- done pulse.
    let doneR ← Signal.reg false

    let accSig := (accR : Signal dom (BitVec 258))
    let aSig   := (aR : Signal dom (BitVec 256))
    let bSig   := (bR : Signal dom (BitVec 256))
    let cntSig := (cntR : Signal dom (BitVec 9))

    let p0_9   := (Signal.pure 0#9   : Signal dom (BitVec 9))
    let p1_9   := (Signal.pure 1#9   : Signal dom (BitVec 9))
    -- Process 256 bits on counts 1..256; finish (done pulse) at count 257.
    let p257_9 := (Signal.pure 257#9 : Signal dom (BitVec 9))
    let pP     := (Signal.pure pBv   : Signal dom (BitVec 258))

    let isIdle   := (cntSig === p0_9 : Signal dom Bool)
    let isFinish := (cntSig === p257_9 : Signal dom Bool)
    let busy     := ((fun i f => !(i || f)) <$> isIdle <*> isFinish : Signal dom Bool)

    -- Widen a to 258 bits for the add (zero-extend via prefix append).
    let aWide := (aSig.map (fun v => BitVec.append (0#2) v) : Signal dom (BitVec 258))

    -- MSB of b (bit 255): shift right 255.
    let p255_256 := (Signal.pure 255#256 : Signal dom (BitVec 256))
    let p0_256   := (Signal.pure 0#256   : Signal dom (BitVec 256))
    let bHi    := (bSig >>> p255_256 : Signal dom (BitVec 256))
    let bHiZ   := (bHi === p0_256 : Signal dom Bool)
    let bMsb   := (~~~bHiZ : Signal dom Bool)

    -- acc doubled (258-bit shift), then reduce once mod p.
    let p1_258    := (Signal.pure 1#258 : Signal dom (BitVec 258))
    let accDbl    := (accSig <<< p1_258 : Signal dom (BitVec 258))
    let dblGe     := ((BitVec.ule · ·) <$> pP <*> accDbl : Signal dom Bool)
    let accDblRed := (Signal.mux dblGe (accDbl - pP) accDbl
                        : Signal dom (BitVec 258))
    -- optionally add a, then reduce once mod p.
    let accPlusA  := (accDblRed + aWide : Signal dom (BitVec 258))
    let addGe     := ((BitVec.ule · ·) <$> pP <*> accPlusA : Signal dom Bool)
    let accAddRed := (Signal.mux addGe (accPlusA - pP) accPlusA
                        : Signal dom (BitVec 258))
    -- next acc: add-branch when bMsb, else the doubled-reduced value.
    let accNext   := (Signal.mux bMsb accAddRed accDblRed : Signal dom (BitVec 258))

    -- b shifted left one bit each busy cycle.
    let bShl := (bSig <<< (Signal.pure 1#256 : Signal dom (BitVec 256))
                  : Signal dom (BitVec 256))
    -- cnt + 1.
    let cntInc := (cntSig + p1_9 : Signal dom (BitVec 9))

    accR <~ Signal.mux start (Signal.pure 0#258 : Signal dom (BitVec 258))
              (Signal.mux busy accNext accSig)
    aR   <~ Signal.mux start aIn aSig
    bR   <~ Signal.mux start bIn
              (Signal.mux busy bShl bSig)
    cntR <~ Signal.mux start p1_9
              (Signal.mux isFinish p0_9
                (Signal.mux busy cntInc cntSig))
    doneR <~ isFinish

    -- Narrow the reduced accumulator to 256 bits for output.
    let resOut := ((BitVec.extractLsb' 0 256 ·) <$> accSig : Signal dom (BitVec 256))

    return ({ result := resOut
            , done   := (doneR : Signal dom Bool)
            } : MulOut dom)

end Sparkle.IP.Crypto.Ed25519FieldHW
