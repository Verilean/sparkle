/-
  IP.Crypto.Ed25519OrderHW — bit-serial modular multiplier for the
  Ed25519 SCALAR field (mod the group order L), Signal DSL.

  A clone of `Secp256k1OrderHW.mulModNHW` with the modulus swapped
  to L = 2²⁵² + 27742317777372353535851937790883648493
  (= `Ed25519Sign.curveOrderL`).  EdDSA's `S = (r + k·a) mod L`
  needs a mod-L multiplier.

  Algorithm: bit-serial double-and-add mod L, MSB-first, one
  bit/cycle; each `mod L` is a single conditional subtract (2·acc+a
  stays below 3L < 2²⁵⁵ so a 258-bit accumulator has ample room).

  Timing: start at cycle 0 ⇒ done pulses at cycle 258.
-/
import Sparkle
import IP.Crypto.Proof.Ed25519Sign

namespace Sparkle.IP.Crypto.Ed25519OrderHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Ed25519 group order L as a 258-bit constant. -/
def lBv : BitVec 258 := BitVec.ofNat 258 Sparkle.IP.Crypto.Ed25519Sign.curveOrderL

/-- Output record. -/
structure MulOut (dom : DomainConfig) where
  /-- The 256-bit product mod L (valid when `done` pulses). -/
  result : Signal dom (BitVec 256)
  /-- Pulses for one cycle when the multiply finishes. -/
  done   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MulOut dom) dom := ⟨⟩

/-- Bit-serial Ed25519 order (mod-L) modular multiplier. -/
def mulModLHW {dom : DomainConfig}
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
    let pL     := (Signal.pure lBv   : Signal dom (BitVec 258))

    let isIdle   := ((· == ·) <$> cntSig <*> p0_9 : Signal dom Bool)
    let isFinish := ((· == ·) <$> cntSig <*> p257_9 : Signal dom Bool)
    let busy     := ((fun i f => !(i || f)) <$> isIdle <*> isFinish : Signal dom Bool)

    let aWide := (aSig.map (fun v => BitVec.append (0#2) v) : Signal dom (BitVec 258))

    let p255_256 := (Signal.pure 255#256 : Signal dom (BitVec 256))
    let p0_256   := (Signal.pure 0#256   : Signal dom (BitVec 256))
    let bHi    := ((· >>> ·) <$> bSig <*> p255_256 : Signal dom (BitVec 256))
    let bHiZ   := ((· == ·) <$> bHi <*> p0_256 : Signal dom Bool)
    let bMsb   := ((fun z => !z) <$> bHiZ : Signal dom Bool)

    let p1_258    := (Signal.pure 1#258 : Signal dom (BitVec 258))
    let accDbl    := ((· <<< ·) <$> accSig <*> p1_258 : Signal dom (BitVec 258))
    let dblGe     := ((BitVec.ule · ·) <$> pL <*> accDbl : Signal dom Bool)
    let accDblRed := (Signal.mux dblGe ((· - ·) <$> accDbl <*> pL) accDbl
                        : Signal dom (BitVec 258))
    let accPlusA  := ((· + ·) <$> accDblRed <*> aWide : Signal dom (BitVec 258))
    let addGe     := ((BitVec.ule · ·) <$> pL <*> accPlusA : Signal dom Bool)
    let accAddRed := (Signal.mux addGe ((· - ·) <$> accPlusA <*> pL) accPlusA
                        : Signal dom (BitVec 258))
    let accNext   := (Signal.mux bMsb accAddRed accDblRed : Signal dom (BitVec 258))

    let bShl := ((· <<< ·) <$> bSig <*> (Signal.pure 1#256 : Signal dom (BitVec 256))
                  : Signal dom (BitVec 256))
    let cntInc := ((· + ·) <$> cntSig <*> p1_9 : Signal dom (BitVec 9))

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

end Sparkle.IP.Crypto.Ed25519OrderHW
