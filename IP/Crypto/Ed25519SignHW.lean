/-
  IP.Crypto.Ed25519SignHW — the scalar half of an Ed25519 (RFC
  8032) signature: S = (r + k·a) mod L.

  An EdDSA signature is (R, S) where:
    * R = r·B   — a G-scalar-multiplication, produced by
                  `Ed25519ScalarMulHW` (base point B, scalar r);
    * S = (r + k·a) mod L.

  This module computes S.  It drives one `Ed25519OrderHW.mulModLHW`
  (mod-L multiplier) to form k·a, then adds r (mod L, one
  conditional subtract).  r, k, a are INPUTS — the SHA-512 hashing
  (and clamping) that produces them stays a host concern, exactly
  as the secp256k1 signer took the message hash z as an input.

  Composition (same as the rest of the stack): the multiplier is
  NOT instantiated here; `mlStart`/`mlA`/`mlB` are driver outputs
  and `mlResult`/`mlDone` are inputs, wired one level up.

  Interface:
    inputs  start (Bool pulse), r, k, a (BitVec 256, all < L),
            mlResult, mlDone (mod-L multiplier handshake in)
    outputs sOut (BitVec 256 = (r + k·a) mod L, valid at done),
            done (Bool pulse),
            mlStart, mlA, mlB (mod-L multiplier handshake out)

  Cost: one mod-L multiply (258 cyc) + a couple of handshake
  cycles.  (R = r·B — the expensive part — is the scalar-mul.)
-/
import Sparkle
import IP.Crypto.Proof.Ed25519Sign
import IP.Crypto.Ed25519OrderHW

namespace Sparkle.IP.Crypto.Ed25519SignHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Group order L as a 257-bit constant (headroom for r + k·a,
    both < L, sum < 2L < 2²⁵⁷). -/
def lBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.Ed25519Sign.curveOrderL

/-- Output record. -/
structure SignOut (dom : DomainConfig) where
  sOut : Signal dom (BitVec 256)
  done : Signal dom Bool
  mlStart : Signal dom Bool
  mlA : Signal dom (BitVec 256)
  mlB : Signal dom (BitVec 256)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (SignOut dom) dom := ⟨⟩

/-- Add mod L (combinational): widen to 257, add, single
    conditional subtract of L. -/
private def faddModL {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let s  := (aw + bw : Signal dom (BitVec 257))
  let pL := (Signal.pure lBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> pL <*> s : Signal dom Bool)
  let red := (Signal.mux ge (s - pL) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- S = (r + k·a) mod L FSM.  One mod-L multiply then add mod L. -/
def signHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (r k a : Signal dom (BitVec 256))
    (mlResult : Signal dom (BitVec 256))
    (mlDone : Signal dom Bool) :
    SignOut dom :=
  circuit do
    -- Phase: 0 idle, 1 trigger mul, 2 wait mul, 3 complete.
    let stR ← Signal.reg (0#2)
    let rR ← Signal.reg (0#256)
    let sR ← Signal.reg (0#256)
    let doneR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 2))
    let rS := (rR : Signal dom (BitVec 256))
    let sS := (sR : Signal dom (BitVec 256))

    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p3_2 := (Signal.pure 3#2 : Signal dom (BitVec 2))

    let isTrig := (stSig === p1_2 : Signal dom Bool)
    let isWait := (stSig === p2_2 : Signal dom Bool)
    let mulAck := (isWait &&& mlDone : Signal dom Bool)

    -- S = (r + k·a) mod L, computed at the mul-ack.
    let sVal := faddModL rS mlResult

    stR <~ Signal.mux start p1_2
              (Signal.mux isTrig p2_2
                (Signal.mux mulAck p3_2 stSig))

    rR <~ Signal.mux start r rS
    sR <~ Signal.mux mulAck sVal sS
    doneR <~ mulAck

    return ({ sOut := sS
            , done := (doneR : Signal dom Bool)
            , mlStart := isTrig
            , mlA := k
            , mlB := a
            } : SignOut dom)

end Sparkle.IP.Crypto.Ed25519SignHW
