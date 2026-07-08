/-
  IP.Crypto.HMACSHA512HW — HMAC-SHA-512 FSM specialised to the
  BIP-32 CKDpriv message shape (Signal DSL).

  HMAC-SHA-512(K, m) = SHA512( (K⊕opad) ‖ SHA512( (K⊕ipad) ‖ m ) )
  with the SHA-512 block size = 128 bytes (RFC 2104 / RFC 4231).

  BIP-32 CKDpriv always calls it with:
    * key = the 32-byte parent chain code (K ≤ blockSize, so
      `hmacKeyPad` just right-zero-pads it to 128 bytes; no
      pre-hash).
    * message = 37 bytes — either
        0x00 ‖ ser256(kpar) ‖ ser32(i)      (hardened) or
        serP(point)         ‖ ser32(i)      (non-hardened),
      both exactly 37 bytes.

  So the two SHA-512 invocations are each exactly TWO 1024-bit
  blocks:
    inner = SHA512( ipad[128] ‖ msg[37] )   — 165 bytes → 2 blocks
    outer = SHA512( opad[128] ‖ inner[64] ) — 192 bytes → 2 blocks

  This module is a 4-phase controller that drives ONE external
  `SHA512BlockHW.sha512BlockHW` compressor (over a start/done
  handshake — the block engine is instantiated one level up, the
  proven composition pattern) once per block:

    phase 0  inner block 1 : hIn=initH,   win = ipad words
    phase 1  inner block 2 : hIn=prevOut, win = msg ‖ pad ‖ len165
    phase 2  outer block 1 : hIn=initH,   win = opad words
    phase 3  outer block 2 : hIn=prevOut, win = inner ‖ pad ‖ len192

  The final `outer` 8×64 digest is the 64-byte HMAC output.

  Interface:
    inputs  start (Bool pulse)
            k0..k3      (BitVec 64)  — the 32-byte key, big-endian
                                       words (k0 = key bytes 0..7)
            m0..m3      (BitVec 64)  — msg bytes 0..31
            m4          (BitVec 64)  — msg bytes 32..36 in the top
                                       5 bytes, low 3 bytes = 0
            blkOut0..7  (BitVec 64)  — block engine result in
            blkDone     (Bool)       — block engine done in
    outputs out0..7     (BitVec 64)  — HMAC-SHA-512 digest (valid
                                       at `done`)
            done        (Bool pulse)
            blkStart    (Bool)       — pulse the block engine
            bhIn0..7    (BitVec 64)  — block engine hIn
            bWin0..15   (BitVec 64)  — block engine message words
-/
import Sparkle
import IP.Crypto.Proof.SHA512
import IP.Crypto.SHA512BlockHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
-- (initH values baked as literals below)

namespace Sparkle.IP.Crypto.HMACSHA512HW

/-- SHA-512 initial hash words as Signal constants.  Baked as
    explicit literals (not `initH.getD i` — an `Array` index the
    synth backend cannot reduce; it reports "Cannot infer hardware
    type from Nat"). -/
private def hi0 {dom : DomainConfig} : Signal dom (BitVec 64) := Signal.pure 0x6a09e667f3bcc908#64
private def hi1 {dom : DomainConfig} : Signal dom (BitVec 64) := Signal.pure 0xbb67ae8584caa73b#64
private def hi2 {dom : DomainConfig} : Signal dom (BitVec 64) := Signal.pure 0x3c6ef372fe94f82b#64
private def hi3 {dom : DomainConfig} : Signal dom (BitVec 64) := Signal.pure 0xa54ff53a5f1d36f1#64
private def hi4 {dom : DomainConfig} : Signal dom (BitVec 64) := Signal.pure 0x510e527fade682d1#64
private def hi5 {dom : DomainConfig} : Signal dom (BitVec 64) := Signal.pure 0x9b05688c2b3e6c1f#64
private def hi6 {dom : DomainConfig} : Signal dom (BitVec 64) := Signal.pure 0x1f83d9abfb41bd6b#64
private def hi7 {dom : DomainConfig} : Signal dom (BitVec 64) := Signal.pure 0x5be0cd19137e2179#64

/-- Output record.  Only the 8 digest words + `done` are the HMAC
    result; the `blk*` fields are the drive ports for the external
    SHA-512 block compressor. -/
structure HmacOut (dom : DomainConfig) where
  out0 : Signal dom (BitVec 64)
  out1 : Signal dom (BitVec 64)
  out2 : Signal dom (BitVec 64)
  out3 : Signal dom (BitVec 64)
  out4 : Signal dom (BitVec 64)
  out5 : Signal dom (BitVec 64)
  out6 : Signal dom (BitVec 64)
  out7 : Signal dom (BitVec 64)
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
    Sparkle.Core.HasDomain (HmacOut dom) dom := ⟨⟩

/-- XOR two 64-bit signals.  The caller passes the pad word as an
    inline-literal `Signal.pure` (NOT a `let`-bound BitVec fed to
    `Signal.pure` — that defeats the synth backend's constant
    tracing: "Cannot infer hardware type from Nat"). -/
private def xorPad {dom : DomainConfig}
    (x pad : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  (x ^^^ pad)

/-- 4-way message-word select across phases 1..4. -/
private def selW {dom : DomainConfig}
    (isP1 isP2 isP3 : Signal dom Bool)
    (w1 w2 w3 w4 : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  Signal.mux isP1 w1 (Signal.mux isP2 w2 (Signal.mux isP3 w3 w4))

/-- Latch a block-output word into a prev register: clear on start,
    take the new value on a block-ack, else hold. -/
private def latchW {dom : DomainConfig}
    (start blkAck : Signal dom Bool)
    (cur newv : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  Signal.mux start (Signal.pure 0#64 : Signal dom (BitVec 64))
    (Signal.mux blkAck newv cur)

/-- HMAC-SHA-512 controller for the BIP-32 (32-byte key, 37-byte
    message) shape.  Drives the external block compressor 4 times. -/
def hmacSha512HW {dom : DomainConfig}
    (start : Signal dom Bool)
    (k0 k1 k2 k3 : Signal dom (BitVec 64))
    (m0 m1 m2 m3 m4 : Signal dom (BitVec 64))
    (blkOut0 blkOut1 blkOut2 blkOut3
     blkOut4 blkOut5 blkOut6 blkOut7 : Signal dom (BitVec 64))
    (blkDone : Signal dom Bool) :
    HmacOut dom :=
  circuit do
    -- Phase register: 0 idle; 1 inner-blk1; 2 inner-blk2;
    -- 3 outer-blk1; 4 outer-blk2; 5 complete.
    let phR ← Signal.reg (0#3)
    -- Sub-phase: 0 = pulse blkStart this cycle, 1 = wait blkDone.
    let waitR ← Signal.reg false
    -- Latched previous block output (chaining digest / inner result).
    let p0R ← Signal.reg (0#64)
    let p1R ← Signal.reg (0#64)
    let p2R ← Signal.reg (0#64)
    let p3R ← Signal.reg (0#64)
    let p4R ← Signal.reg (0#64)
    let p5R ← Signal.reg (0#64)
    let p6R ← Signal.reg (0#64)
    let p7R ← Signal.reg (0#64)
    let doneR ← Signal.reg false

    let ph := (phR : Signal dom (BitVec 3))
    let waiting := (waitR : Signal dom Bool)
    let p0 := (p0R : Signal dom (BitVec 64))
    let p1 := (p1R : Signal dom (BitVec 64))
    let p2 := (p2R : Signal dom (BitVec 64))
    let p3 := (p3R : Signal dom (BitVec 64))
    let p4 := (p4R : Signal dom (BitVec 64))
    let p5 := (p5R : Signal dom (BitVec 64))
    let p6 := (p6R : Signal dom (BitVec 64))
    let p7 := (p7R : Signal dom (BitVec 64))

    let c0 := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let c1 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let c2 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let c3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let c4 := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let c5 := (Signal.pure 5#3 : Signal dom (BitVec 3))

    let isIdle := (ph === c0 : Signal dom Bool)
    let isP1 := (ph === c1 : Signal dom Bool)
    let isP2 := (ph === c2 : Signal dom Bool)
    let isP3 := (ph === c3 : Signal dom Bool)
    let isP4 := (ph === c4 : Signal dom Bool)
    let active := ((fun i c => !(i || c)) <$> isIdle
                    <*> (ph === c5) : Signal dom Bool)

    -- A block finishes when we're in a wait sub-phase and blkDone.
    let blkAck := (waiting &&& blkDone : Signal dom Bool)

    -- ── ipad / opad key words (K ⊕ pad, then zero-pad already 0) ──
    -- K is 32 bytes = k0..k3; bytes 32..127 of the padded key are 0,
    -- so ipad word i (i≥4) = 0⊕0x36..36 = 0x3636..36, opad = 0x5C..5C.
    let ipadS := (Signal.pure 0x3636363636363636#64 : Signal dom (BitVec 64))
    let opadS := (Signal.pure 0x5c5c5c5c5c5c5c5c#64 : Signal dom (BitVec 64))
    let ik0 := xorPad k0 ipadS
    let ik1 := xorPad k1 ipadS
    let ik2 := xorPad k2 ipadS
    let ik3 := xorPad k3 ipadS
    let ok0 := xorPad k0 opadS
    let ok1 := xorPad k1 opadS
    let ok2 := xorPad k2 opadS
    let ok3 := xorPad k3 opadS

    -- ── inner block 2 message words: msg(37) ‖ 0x80 ‖ 0… ‖ len ──
    -- m0..m3 = msg[0:32]; m4 = msg[32:37] in the top 5 bytes.
    -- m4 carries msg[32:37] in its TOP 5 bytes (low 3 = 0).  The SHA
    -- padding 0x80 lands at byte index 5 (0-based, from the MSB) of
    -- this word — i.e. bit position 16 — so OR in 0x0000000000800000.
    let m4pad := ((· ||| ·) <$> m4
                   <*> (Signal.pure 0x0000000000800000#64 : Signal dom (BitVec 64)))
    let z64 := (Signal.pure 0#64 : Signal dom (BitVec 64))
    let len165 := (Signal.pure 1320#64 : Signal dom (BitVec 64))  -- 165*8

    -- ── outer block 2 message words: inner(64) ‖ 0x80 ‖ 0… ‖ len ──
    -- p0..p7 = inner digest; word8 = 0x8000…0; word15 = 192*8.
    let pad80 := (Signal.pure 0x8000000000000000#64 : Signal dom (BitVec 64))
    let len192 := (Signal.pure 1536#64 : Signal dom (BitVec 64))  -- 192*8

    -- ── hIn selection: initH for block-1 phases, prev digest for block-2 ──
    let useInit := (isP1 ||| isP3 : Signal dom Bool)
    let bhIn0 := Signal.mux useInit hi0 p0
    let bhIn1 := Signal.mux useInit hi1 p1
    let bhIn2 := Signal.mux useInit hi2 p2
    let bhIn3 := Signal.mux useInit hi3 p3
    let bhIn4 := Signal.mux useInit hi4 p4
    let bhIn5 := Signal.mux useInit hi5 p5
    let bhIn6 := Signal.mux useInit hi6 p6
    let bhIn7 := Signal.mux useInit hi7 p7

    -- ── message-word selection per phase ──
    -- Phase 1 (inner blk1): ipad words. word0..3 = ik0..3, 4..15 = ipadRep.
    -- Phase 2 (inner blk2): m0..m3, m4pad, zeros, len165.
    -- Phase 3 (outer blk1): opad words. word0..3 = ok0..3, 4..15 = opadRep.
    -- Phase 4 (outer blk2): p0..p7, pad80, zeros, len192.
    let bWin0  := selW isP1 isP2 isP3 ik0 m0 ok0 p0
    let bWin1  := selW isP1 isP2 isP3 ik1 m1 ok1 p1
    let bWin2  := selW isP1 isP2 isP3 ik2 m2 ok2 p2
    let bWin3  := selW isP1 isP2 isP3 ik3 m3 ok3 p3
    let bWin4  := selW isP1 isP2 isP3 ipadS m4pad opadS p4
    let bWin5  := selW isP1 isP2 isP3 ipadS z64 opadS p5
    let bWin6  := selW isP1 isP2 isP3 ipadS z64 opadS p6
    let bWin7  := selW isP1 isP2 isP3 ipadS z64 opadS p7
    let bWin8  := selW isP1 isP2 isP3 ipadS z64 opadS pad80
    let bWin9  := selW isP1 isP2 isP3 ipadS z64 opadS z64
    let bWin10 := selW isP1 isP2 isP3 ipadS z64 opadS z64
    let bWin11 := selW isP1 isP2 isP3 ipadS z64 opadS z64
    let bWin12 := selW isP1 isP2 isP3 ipadS z64 opadS z64
    let bWin13 := selW isP1 isP2 isP3 ipadS z64 opadS z64
    let bWin14 := selW isP1 isP2 isP3 ipadS z64 opadS z64
    let bWin15 := selW isP1 isP2 isP3 ipadS len165 opadS len192

    -- blkStart pulses when active AND not yet waiting (start of a block).
    let blkStart := ((fun a w => a && !w) <$> active <*> waiting : Signal dom Bool)

    -- ── register updates ──
    -- On start: enter phase 1, not waiting, clear prev.
    -- On blkStart cycle (active & !waiting): flip to waiting.
    -- On blkAck: latch block result into prev, advance phase (or finish).
    let atLastPhase := isP4
    phR <~ Signal.mux start c1
            (Signal.mux blkAck
              (Signal.mux atLastPhase c5
                (Signal.mux isP1 c2 (Signal.mux isP2 c3 c4)))
              ph)
    waitR <~ Signal.mux start (Signal.pure false : Signal dom Bool)
              (Signal.mux blkStart (Signal.pure true : Signal dom Bool)
                (Signal.mux blkAck (Signal.pure false : Signal dom Bool)
                  waiting))
    -- Latch block outputs into prev on every blkAck.
    p0R <~ latchW start blkAck p0 blkOut0
    p1R <~ latchW start blkAck p1 blkOut1
    p2R <~ latchW start blkAck p2 blkOut2
    p3R <~ latchW start blkAck p3 blkOut3
    p4R <~ latchW start blkAck p4 blkOut4
    p5R <~ latchW start blkAck p5 blkOut5
    p6R <~ latchW start blkAck p6 blkOut6
    p7R <~ latchW start blkAck p7 blkOut7
    -- done pulses when the final block (phase 4) acks.
    doneR <~ (blkAck &&& atLastPhase : Signal dom Bool)

    return ({ out0 := p0, out1 := p1, out2 := p2, out3 := p3
            , out4 := p4, out5 := p5, out6 := p6, out7 := p7
            , done := (doneR : Signal dom Bool)
            , blkStart := blkStart
            , bhIn0 := bhIn0, bhIn1 := bhIn1, bhIn2 := bhIn2, bhIn3 := bhIn3
            , bhIn4 := bhIn4, bhIn5 := bhIn5, bhIn6 := bhIn6, bhIn7 := bhIn7
            , bWin0 := bWin0, bWin1 := bWin1, bWin2 := bWin2, bWin3 := bWin3
            , bWin4 := bWin4, bWin5 := bWin5, bWin6 := bWin6, bWin7 := bWin7
            , bWin8 := bWin8, bWin9 := bWin9, bWin10 := bWin10, bWin11 := bWin11
            , bWin12 := bWin12, bWin13 := bWin13, bWin14 := bWin14, bWin15 := bWin15
            } : HmacOut dom)

end Sparkle.IP.Crypto.HMACSHA512HW
