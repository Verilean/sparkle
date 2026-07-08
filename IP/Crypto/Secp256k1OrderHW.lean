/-
  IP.Crypto.Secp256k1OrderHW — multi-cycle modular multiplier for
  the secp256k1 SCALAR field (mod the curve order n), Signal DSL.

  This is a byte-for-byte clone of `Secp256k1FieldHW.mulHW` with the
  reduction modulus swapped from the base-field prime `p` to the
  curve order `n = Secp256k1ECDSA.n`.  ECDSA computes `r` and `s`
  mod n (not mod p), so the sign FSM needs a mod-n multiplier
  alongside the mod-p one.

  Algorithm: bit-serial "double-and-add" modular multiply
  (Russian-peasant mod n), MSB-first, one bit/cycle:

      acc = 0
      for i = 255 downto 0:
          acc = (2·acc)      mod n        -- shift
          if bit_i(b):  acc = (acc + a)   mod n        -- add

  Each `mod n` is at most a single conditional subtract of `n`
  (the intermediate 2·acc + a stays below 3n < 2^258).  This
  computes exactly `(a·b) mod n`.

  Timing: start at cycle 0 ⇒ 256 round cycles ⇒ done pulses at
  cycle 258, result valid.  Same 258-cyc bit-serial structure as
  the mod-p engine.
-/
import Sparkle
import IP.Crypto.Proof.Secp256k1ECDSA

namespace Sparkle.IP.Crypto.Secp256k1OrderHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- secp256k1 curve order n as a 258-bit constant (headroom for the
    2·acc + a intermediate, which stays below 3n < 2^258). -/
def nBv : BitVec 258 := BitVec.ofNat 258 Sparkle.IP.Crypto.Secp256k1ECDSA.n

/-- Output record. -/
structure MulOut (dom : DomainConfig) where
  /-- The 256-bit product mod n (valid when `done` pulses). -/
  result : Signal dom (BitVec 256)
  /-- Pulses for one cycle when the multiply finishes. -/
  done   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MulOut dom) dom := ⟨⟩

/-- Bit-serial secp256k1 order (mod-n) modular multiplier. -/
def mulModNHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (aIn bIn : Signal dom (BitVec 256)) :
    MulOut dom :=
  circuit do
    let accR ← Signal.reg (0#258)
    let aR ← Signal.reg (0#256)
    let bR ← Signal.reg (0#256)
    let cntR ← Signal.reg (0#9)
    let doneR ← Signal.reg false

    let accSig := (accR : Signal dom (BitVec 258))
    let aSig   := (aR : Signal dom (BitVec 256))
    let bSig   := (bR : Signal dom (BitVec 256))
    let cntSig := (cntR : Signal dom (BitVec 9))

    let p0_9   := (Signal.pure 0#9   : Signal dom (BitVec 9))
    let p1_9   := (Signal.pure 1#9   : Signal dom (BitVec 9))
    let p257_9 := (Signal.pure 257#9 : Signal dom (BitVec 9))
    let pN     := (Signal.pure nBv   : Signal dom (BitVec 258))

    let isIdle   := (cntSig === p0_9 : Signal dom Bool)
    let isFinish := (cntSig === p257_9 : Signal dom Bool)
    let busy     := ((fun i f => !(i || f)) <$> isIdle <*> isFinish : Signal dom Bool)

    let aWide := (aSig.map (fun v => BitVec.append (0#2) v) : Signal dom (BitVec 258))

    let p255_256 := (Signal.pure 255#256 : Signal dom (BitVec 256))
    let p0_256   := (Signal.pure 0#256   : Signal dom (BitVec 256))
    let bHi    := (bSig >>> p255_256 : Signal dom (BitVec 256))
    let bHiZ   := (bHi === p0_256 : Signal dom Bool)
    let bMsb   := (~~~bHiZ : Signal dom Bool)

    let p1_258    := (Signal.pure 1#258 : Signal dom (BitVec 258))
    let accDbl    := (accSig <<< p1_258 : Signal dom (BitVec 258))
    let dblGe     := ((BitVec.ule · ·) <$> pN <*> accDbl : Signal dom Bool)
    let accDblRed := (Signal.mux dblGe (accDbl - pN) accDbl
                        : Signal dom (BitVec 258))
    let accPlusA  := (accDblRed + aWide : Signal dom (BitVec 258))
    let addGe     := ((BitVec.ule · ·) <$> pN <*> accPlusA : Signal dom Bool)
    let accAddRed := (Signal.mux addGe (accPlusA - pN) accPlusA
                        : Signal dom (BitVec 258))
    let accNext   := (Signal.mux bMsb accAddRed accDblRed : Signal dom (BitVec 258))

    let bShl := (bSig <<< (Signal.pure 1#256 : Signal dom (BitVec 256))
                  : Signal dom (BitVec 256))
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

    let resOut := ((BitVec.extractLsb' 0 256 ·) <$> accSig : Signal dom (BitVec 256))

    return ({ result := resOut
            , done   := (doneR : Signal dom Bool)
            } : MulOut dom)

end Sparkle.IP.Crypto.Secp256k1OrderHW
