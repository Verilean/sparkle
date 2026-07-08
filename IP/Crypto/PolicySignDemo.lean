/-
  IP.Crypto.PolicySignDemo — policy-enforcing Ethereum signing
  device for Tang Nano 50K.

  Unlike the blind signer (EcdsaSignDemo, which signs a 32-byte
  hash the host hands it), THIS device receives the raw EIP-1559
  signing preimage `P = 0x02 || rlp([...])`, computes the
  Keccak-256 signing hash ON-CHIP, checks the transaction against
  an ON-CHIP POLICY (recipient allowlist + max value), and signs
  ONLY if the policy passes.  The recipient / value the policy
  checks are sliced from the SAME buffered bytes the sponge
  hashes, so a compromised host cannot desync the policy check
  from the signature: keys never leave the chip AND the chip
  refuses attacker-chosen transactions.

  Milestone 1 scope (host-serialized, single rate block):
    * The host sends a fixed 96-byte frame over UART:
        d (32) ‖ k (32) ‖ preimage-tail (32)
      — see below; `d`/`k` are the signing secrets (baked-in in a
      real device, host-supplied here for the demo), and the
      policy-relevant `to`/`value` are sliced from the buffered
      frame at fixed offsets.
    * The preimage is a single rate block (≤136 B); padding is a
      fixed combinational function applied at buffer-assembly time.
    * On policy PASS: stream 64 bytes `r‖s` back.  On policy FAIL:
      stream one reject byte (0xEE) and strobe a reject LED.

  This is intentionally a thin, synthesizable top that WIRES the
  three new/existing engines — the sponge (Keccak256Sponge),
  the policy engine (TxPolicy), and the ECDSA signer core
  (EcdsaSignDemo.signCore) — with the signer's `start` gated on
  `policyOk`.  The full on-chip RLP re-parse / variable-length
  preimage is Milestone 2.
-/
import Sparkle
import IP.Crypto.EcdsaSignDemo
import IP.Crypto.Keccak256Sponge
import IP.Crypto.TxPolicy
import IP.Net.UART

namespace Sparkle.IP.Crypto.PolicySignDemo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignDemo (signCore SignCoreOut wRx wTx bitDiv27M115200)
open Sparkle.IP.Crypto.Keccak256Sponge (keccak256SpongeHW SpongeOut rateLanes maxBlocks)
open Sparkle.IP.Crypto.TxPolicy (txPolicyOk txPolicyHW PolicyOut)
open Sparkle.IP.Net.UART (RxOut TxOut)

/-- Thin wrappers so the top can project engine outputs. -/
@[hardware_module] def wSponge {dom : DomainConfig}
    (start : Signal dom Bool) (nBlocks : Signal dom (BitVec 2))
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
     m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33
     : Signal dom (BitVec 64)) : SpongeOut dom :=
  keccak256SpongeHW start nBlocks
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
    m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33

@[hardware_module] def wSignCore {dom : DomainConfig}
    (start : Signal dom Bool) (d k z : Signal dom (BitVec 256)) : SignCoreOut dom :=
  signCore start d k z

/-- Output record for the Tang Nano top. -/
structure PolicyDemoOut (dom : DomainConfig) where
  /-- UART TX line. -/
  uartTx   : Signal dom Bool
  /-- One-cycle strobe when a signature completes (LED). -/
  signDone : Signal dom Bool
  /-- One-cycle strobe when a transaction is REJECTED by policy (LED). -/
  rejected : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (PolicyDemoOut dom) dom := ⟨⟩

/-! ### Frame layout (Milestone 1, host-serialized, single block)

    The host sends a fixed **128-byte** frame over UART, MSB byte
    first, as a 1024-bit big-endian shift register:

      d (32) ‖ k (32) ‖ to (32, address in low 20) ‖ value (32)

    * `d`, `k` — the ECDSA signing secrets (baked-in in a real
      device; host-supplied here for the demo).
    * The **message hashed on-chip** is the 64-byte tail
      `to(32) ‖ value(32)` — a single Keccak rate block.  This is
      the M1 stand-in for the EIP-1559 signing preimage; the
      policy-relevant fields are sliced from the SAME 64 bytes
      that feed the sponge, which is the whole security point.
    * `to`  = low 160 bits of the `to` word.
    * `value` = the `value` word.

    Keccak padding for a 64-byte message: append `0x01`, zero-fill
    to 135, then `0x80` → a single 136-byte block = 17 lanes.  The
    message occupies lanes 0..7 (64 B); lane 8 gets the `0x01`
    delimiter (byte 64 → LE lane 8 low byte); lane 16 gets `0x80`
    in its high byte (byte 135).  All fixed, so the lane vector is
    a pure combinational function of the buffered bytes. -/

/-- Shift a byte into the low end of a 1024-bit accumulator. -/
@[inline] private def shiftIn1024 {dom : DomainConfig}
    (acc : Signal dom (BitVec 1024)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 1024) :=
  (acc <<< (Signal.pure (8#1024) : Signal dom (BitVec 1024)))
    |||
    (b.map (fun v => BitVec.append (0#1016) v) : Signal dom (BitVec 1024))

/-- The Tang Nano 50K policy-enforcing signing top. -/
def policySignDemo {dom : DomainConfig}
    (uartRx : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) : PolicyDemoOut dom :=
  circuit do
    -- ===== RX byte assembler (128-byte frame → 1024-bit reg) =====
    let accR    ← Signal.reg (0#1024)
    let rxCntR  ← Signal.reg (0#8)      -- bytes received, 0..128
    let dR      ← Signal.reg (0#256)
    let kR      ← Signal.reg (0#256)
    let toR     ← Signal.reg (0#256)    -- `to` word (address in low 160)
    let valR    ← Signal.reg (0#256)    -- `value` word
    let hashStartR ← Signal.reg false   -- pulse to launch the sponge

    -- ===== hash→sign handoff =====
    let zR       ← Signal.reg (0#256)   -- latched signing hash
    let signStartR ← Signal.reg false   -- gated signer start
    let rejectR  ← Signal.reg false     -- policy-reject strobe

    -- ===== TX streamer =====
    let txAccR  ← Signal.reg (0#512)
    let txCntR  ← Signal.reg (0#8)
    let txBusyR ← Signal.reg false

    let accSig   := (accR : Signal dom (BitVec 1024))
    let rxCntSig := (rxCntR : Signal dom (BitVec 8))
    let dSig     := (dR : Signal dom (BitVec 256))
    let kSig     := (kR : Signal dom (BitVec 256))
    let toSig    := (toR : Signal dom (BitVec 256))
    let valSig   := (valR : Signal dom (BitVec 256))
    let zSig     := (zR : Signal dom (BitVec 256))
    let txAccSig := (txAccR : Signal dom (BitVec 512))
    let txCntSig := (txCntR : Signal dom (BitVec 8))
    let txBusySig := (txBusyR : Signal dom Bool)

    -- ===== UART RX =====
    let rx := wRx uartRx bitDiv
    let gotByte := rx.rxValid
    let accNext := shiftIn1024 accSig rx.rxByte
    let rxInc := (rxCntSig + (Signal.pure 1#8 : Signal dom (BitVec 8)))
    let atLast := (rxCntSig === (Signal.pure 127#8 : Signal dom (BitVec 8)))
    let lastByte := (gotByte &&& atLast : Signal dom Bool)

    accR <~ Signal.mux gotByte accNext accSig
    rxCntR <~ Signal.mux lastByte (Signal.pure 0#8 : Signal dom (BitVec 8))
                (Signal.mux gotByte rxInc rxCntSig)

    -- On the last byte, `accNext` holds all 128 bytes.  Split:
    --   d     = bits [1023:768]   (word 0, MSB-first)
    --   k     = bits [767:512]
    --   to    = bits [511:256]
    --   value = bits [255:0]
    let dSlice  := (accNext.map (fun v => BitVec.extractLsb' 768 256 v) : Signal dom (BitVec 256))
    let kSlice  := (accNext.map (fun v => BitVec.extractLsb' 512 256 v) : Signal dom (BitVec 256))
    let toSlice := (accNext.map (fun v => BitVec.extractLsb' 256 256 v) : Signal dom (BitVec 256))
    let vSlice  := (accNext.map (fun v => BitVec.extractLsb' 0   256 v) : Signal dom (BitVec 256))
    dR   <~ Signal.mux lastByte dSlice  dSig
    kR   <~ Signal.mux lastByte kSlice  kSig
    toR  <~ Signal.mux lastByte toSlice toSig
    valR <~ Signal.mux lastByte vSlice  valSig
    hashStartR <~ lastByte

    -- The 512-bit message `to ‖ value` (big-endian); byte 0 = MSB.
    let msg512 := (toSig ++ valSig : Signal dom (BitVec 512))
    -- message lanes 0..7: lane i = LE pack of message bytes 8i..8i+7.
    -- Message = to(32,BE) ‖ value(32,BE); msg512 byte 0 = MSB.  Keccak
    -- lanes are little-endian, so lane high byte = message byte 8i+7,
    -- lane low byte = message byte 8i.  Built fully inline with
    -- applicative `append <$> _ <*> _` over single-extract maps — the
    -- only `.map` shape the synth elaborator lowers (composed ops or
    -- `let`-bound helpers inside a map lambda do NOT lower).
    let ml0 := (((msg512.map (fun v => BitVec.extractLsb' 448 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 456 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 464 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 472 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 480 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 488 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 496 8 v) : Signal dom (BitVec 8)) ++ (msg512.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml1 := (((msg512.map (fun v => BitVec.extractLsb' 384 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 392 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 400 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 408 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 416 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 424 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 432 8 v) : Signal dom (BitVec 8)) ++ (msg512.map (fun v => BitVec.extractLsb' 440 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml2 := (((msg512.map (fun v => BitVec.extractLsb' 320 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 328 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 336 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 344 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 352 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 360 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 368 8 v) : Signal dom (BitVec 8)) ++ (msg512.map (fun v => BitVec.extractLsb' 376 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml3 := (((msg512.map (fun v => BitVec.extractLsb' 256 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 264 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 272 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 280 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 288 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 296 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 304 8 v) : Signal dom (BitVec 8)) ++ (msg512.map (fun v => BitVec.extractLsb' 312 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml4 := (((msg512.map (fun v => BitVec.extractLsb' 192 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 200 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 208 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 216 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 224 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 232 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 240 8 v) : Signal dom (BitVec 8)) ++ (msg512.map (fun v => BitVec.extractLsb' 248 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml5 := (((msg512.map (fun v => BitVec.extractLsb' 128 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 136 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 144 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 152 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 160 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 168 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 176 8 v) : Signal dom (BitVec 8)) ++ (msg512.map (fun v => BitVec.extractLsb' 184 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml6 := (((msg512.map (fun v => BitVec.extractLsb' 64 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 72 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 80 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 88 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 96 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 104 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 112 8 v) : Signal dom (BitVec 8)) ++ (msg512.map (fun v => BitVec.extractLsb' 120 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml7 := (((msg512.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((msg512.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (msg512.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let z64 := (Signal.pure 0#64 : Signal dom (BitVec 64))
    let mlPad01 := (Signal.pure 0x01#64 : Signal dom (BitVec 64))
    let mlPad80 := (Signal.pure 0x8000000000000000#64 : Signal dom (BitVec 64))
    let hashStartSig := (hashStartR : Signal dom Bool)
    let sponge := wSponge hashStartSig (Signal.pure 1#2 : Signal dom (BitVec 2))
      ml0 ml1 ml2 ml3 ml4 ml5 ml6 ml7
      mlPad01 z64 z64 z64 z64 z64 z64 z64 mlPad80
      z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64
    let zl0 := (((sponge.d0.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (sponge.d0.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let zl1 := (((sponge.d1.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (sponge.d1.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let zl2 := (((sponge.d2.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (sponge.d2.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let zl3 := (((sponge.d3.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (sponge.d3.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    -- z = BE scalar: digest lanes 0..3 byte-reversed, zl0 the high
    -- word.  Nested 2-way `append <$> _ <*> _` (a 4-arg applicative
    -- lambda does not lower — `Seq.seq: not a hardware module`).
    let z := (BitVec.append <$> zl0 <*>
               (BitVec.append <$> zl1 <*>
                 (zl2 ++ zl3
                  : Signal dom (BitVec 128))
                : Signal dom (BitVec 192))
             : Signal dom (BitVec 256))
    zR <~ Signal.mux sponge.done z zSig

    -- ===== policy: recipient = to[159:0], value = value word =====
    -- `txPolicyHW` is combinational (no registers), so it INLINES —
    -- calling it through a `@[hardware_module]` wrapper fails
    -- ("PolicyOut.policyOk: not a hardware module definition"): a
    -- stateless module has no clock to instantiate against.
    let recip := (toSig.map (fun v => BitVec.extractLsb' 0 160 v) : Signal dom (BitVec 160))
    let policyOk := txPolicyOk recip valSig
    -- On sponge.done, launch the signer ONLY if policy passes;
    -- else strobe reject.
    let doSign := (sponge.done &&& policyOk : Signal dom Bool)
    let doReject := ((· && ·) <$> sponge.done
                      <*> ((fun b => !b) <$> policyOk) : Signal dom Bool)
    signStartR <~ doSign
    rejectR <~ doReject

    -- ===== signer core (gated) =====
    let core := wSignCore (signStartR : Signal dom Bool) dSig kSig zSig

    -- ===== TX: on core.done stream r‖s (64 B); on reject send 0xEE =====
    let tx := wTx
                (txAccSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))
                (txBusySig &&& (Signal.pure true : Signal dom Bool))
                bitDiv
    let txAccept := (txBusySig &&& tx.txReady : Signal dom Bool)
    let rsConcat := (core.rOut ++ core.sOut : Signal dom (BitVec 512))
    -- reject frame: 0xEE in the top byte, rest zero.
    let rejFrame := (Signal.pure (BitVec.shiftLeft (0xEE#512) 504) : Signal dom (BitVec 512))
    let txShift := (txAccSig <<< (Signal.pure (8#512) : Signal dom (BitVec 512)))
    let loadEvt := (core.done ||| (rejectR : Signal dom Bool) : Signal dom Bool)
    let loadVal := Signal.mux core.done rsConcat rejFrame
    txAccR <~ Signal.mux loadEvt loadVal
                (Signal.mux txAccept txShift txAccSig)
    let txDec := (txCntSig - (Signal.pure 1#8 : Signal dom (BitVec 8)))
    -- byte count: 64 on sign-done, 1 on reject.
    let loadCnt := Signal.mux core.done (Signal.pure 64#8 : Signal dom (BitVec 8))
                     (Signal.pure 1#8 : Signal dom (BitVec 8))
    txCntR <~ Signal.mux loadEvt loadCnt
                (Signal.mux txAccept txDec txCntSig)
    let txMore := ((fun c => !(c == 0#8)) <$> txCntSig : Signal dom Bool)
    txBusyR <~ Signal.mux loadEvt (Signal.pure true : Signal dom Bool)
                (Signal.mux txAccept txMore txBusySig)

    return ({ uartTx := tx.txLine
            , signDone := core.done
            , rejected := (rejectR : Signal dom Bool)
            } : PolicyDemoOut dom)

end Sparkle.IP.Crypto.PolicySignDemo
