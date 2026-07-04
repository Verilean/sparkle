/-
  IP.Crypto.BIP32CKDHW — BIP-32 CKDpriv child-key derivation FSM
  (Signal DSL), built on the HMAC-SHA-512 controller.

  CKDpriv(parent, i):
    I  = HMAC-SHA-512(parent.chainCode, data)
    IL = I[0:32]  (a 256-bit big-endian scalar)
    IR = I[32:64] (the child chain code)
    childKey       = (parent.privKey + IL) mod n   (secp256k1 order)
    childChainCode = IR

  where `data` is
    hardened      0x00 ‖ ser256(kpar) ‖ ser32(i)          (37 bytes)
    non-hardened  serP(parent.pubKey) ‖ ser32(i)          (37 bytes)
  — both exactly 37 bytes, which is the fixed message shape the
  `HMACSHA512HW` controller handles.  Selecting / building `data`
  (the SEC1 point serialisation for the non-hardened case) is the
  caller's concern; this module takes the message words (m0..m4)
  and the key words directly, mirroring how the ECDSA / Ed25519
  signers take their hash/scalar inputs.

  This module is a thin wrapper: it forwards `start` + key + msg to
  the HMAC controller, forwards the HMAC↔block handshake ports
  straight through, and post-processes the 64-byte HMAC digest:
    * IL = out0‖out1‖out2‖out3 (256-bit), reduced (+kpar) mod n
    * IR = out4..out7 (the child chain code)
  The near-order failure cases the pure-data `ckdPriv` rejects
  (IL ≥ n, child = 0) are measure-zero for a valid parent key and
  are not signalled here (same convention as the scalar-mul ladder).

  Interface:
    inputs  start, k0..k3 (chain code, 4×64), m0..m4 (msg, 37 B),
            blkOut0..7 / blkDone  (SHA-512 block engine handshake in)
    outputs childKey (BitVec 256), cc0..3 (child chain code, 4×64),
            done,  and the block-engine drive ports
            (blkStart / bhIn0..7 / bWin0..15) passed straight from
            the inner HMAC controller.
-/
import Sparkle
import IP.Crypto.HMACSHA512HW
import IP.Crypto.Proof.Secp256k1ECDSA

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.HMACSHA512HW (hmacSha512HW)

namespace Sparkle.IP.Crypto.BIP32CKDHW

/-- secp256k1 order n as a 257-bit constant (headroom for the
    (kpar + IL) sum before the single conditional subtract). -/
def nBv257 : BitVec 257 := BitVec.ofNat 257 Sparkle.IP.Crypto.Secp256k1ECDSA.n

/-- (a + b) mod n, single conditional subtract (a, b < n ⇒ sum < 2n). -/
private def addModN {dom : DomainConfig}
    (a b : Signal dom (BitVec 256)) : Signal dom (BitVec 256) :=
  let aw := (a.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let bw := (b.map (fun v => BitVec.append (0#1) v) : Signal dom (BitVec 257))
  let s  := ((· + ·) <$> aw <*> bw : Signal dom (BitVec 257))
  let nP := (Signal.pure nBv257 : Signal dom (BitVec 257))
  let ge := ((BitVec.ule · ·) <$> nP <*> s : Signal dom Bool)
  let red := (Signal.mux ge ((· - ·) <$> s <*> nP) s : Signal dom (BitVec 257))
  ((BitVec.extractLsb' 0 256 ·) <$> red : Signal dom (BitVec 256))

/-- Concatenate four big-endian 64-bit words (w0 = most significant)
    into a 256-bit value. -/
private def cat4 {dom : DomainConfig}
    (w0 w1 w2 w3 : Signal dom (BitVec 64)) : Signal dom (BitVec 256) :=
  let a := (BitVec.append <$> w0 <*> w1 : Signal dom (BitVec 128))
  let b := (BitVec.append <$> a <*> w2 : Signal dom (BitVec 192))
  (BitVec.append <$> b <*> w3 : Signal dom (BitVec 256))

/-- Output record: the child private key + child chain code, plus
    the block-engine drive ports forwarded from the inner HMAC. -/
structure CkdOut (dom : DomainConfig) where
  childKey : Signal dom (BitVec 256)
  cc0 : Signal dom (BitVec 64)
  cc1 : Signal dom (BitVec 64)
  cc2 : Signal dom (BitVec 64)
  cc3 : Signal dom (BitVec 64)
  done : Signal dom Bool
  blkStart : Signal dom Bool
  bhIn0 : Signal dom (BitVec 64)
  bhIn1 : Signal dom (BitVec 64)
  bhIn2 : Signal dom (BitVec 64)
  bhIn3 : Signal dom (BitVec 64)
  bhIn4 : Signal dom (BitVec 64)
  bhIn5 : Signal dom (BitVec 64)
  bhIn6 : Signal dom (BitVec 64)
  bhIn7 : Signal dom (BitVec 64)
  bWin0 : Signal dom (BitVec 64)
  bWin1 : Signal dom (BitVec 64)
  bWin2 : Signal dom (BitVec 64)
  bWin3 : Signal dom (BitVec 64)
  bWin4 : Signal dom (BitVec 64)
  bWin5 : Signal dom (BitVec 64)
  bWin6 : Signal dom (BitVec 64)
  bWin7 : Signal dom (BitVec 64)
  bWin8 : Signal dom (BitVec 64)
  bWin9 : Signal dom (BitVec 64)
  bWin10 : Signal dom (BitVec 64)
  bWin11 : Signal dom (BitVec 64)
  bWin12 : Signal dom (BitVec 64)
  bWin13 : Signal dom (BitVec 64)
  bWin14 : Signal dom (BitVec 64)
  bWin15 : Signal dom (BitVec 64)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (CkdOut dom) dom := ⟨⟩

/-- BIP-32 CKDpriv derivation.  `kpar` is the 256-bit parent private
    key; k0..k3 the parent chain code (HMAC key); m0..m4 the 37-byte
    HMAC message (hardened or non-hardened form, built by the
    caller). -/
def ckdPrivHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (kpar : Signal dom (BitVec 256))
    (k0 k1 k2 k3 : Signal dom (BitVec 64))
    (m0 m1 m2 m3 m4 : Signal dom (BitVec 64))
    (blkOut0 blkOut1 blkOut2 blkOut3
     blkOut4 blkOut5 blkOut6 blkOut7 : Signal dom (BitVec 64))
    (blkDone : Signal dom Bool) :
    CkdOut dom :=
  let h := hmacSha512HW start k0 k1 k2 k3 m0 m1 m2 m3 m4
             blkOut0 blkOut1 blkOut2 blkOut3
             blkOut4 blkOut5 blkOut6 blkOut7 blkDone
  -- IL = I[0:32] as a 256-bit big-endian scalar; child = (kpar+IL) mod n.
  let il := cat4 h.out0 h.out1 h.out2 h.out3
  let childKey := addModN kpar il
  { childKey := childKey
  , cc0 := h.out4, cc1 := h.out5, cc2 := h.out6, cc3 := h.out7
  , done := h.done
  , blkStart := h.blkStart
  , bhIn0 := h.bhIn0, bhIn1 := h.bhIn1, bhIn2 := h.bhIn2, bhIn3 := h.bhIn3
  , bhIn4 := h.bhIn4, bhIn5 := h.bhIn5, bhIn6 := h.bhIn6, bhIn7 := h.bhIn7
  , bWin0 := h.bWin0, bWin1 := h.bWin1, bWin2 := h.bWin2, bWin3 := h.bWin3
  , bWin4 := h.bWin4, bWin5 := h.bWin5, bWin6 := h.bWin6, bWin7 := h.bWin7
  , bWin8 := h.bWin8, bWin9 := h.bWin9, bWin10 := h.bWin10, bWin11 := h.bWin11
  , bWin12 := h.bWin12, bWin13 := h.bWin13, bWin14 := h.bWin14, bWin15 := h.bWin15
  }

end Sparkle.IP.Crypto.BIP32CKDHW
