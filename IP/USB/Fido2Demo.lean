/-
  IP.USB.Fido2Demo — FIDO2 getAssertion signing top for Tang Nano 50K (M3).

  A synthesizable Tang Nano top (structural clone of
  `IP.Crypto.EcdsaSignDemo.ecdsaSignDemo`) that performs the core
  FIDO2 getAssertion cryptographic operation over the BL616
  CDC-ACM UART bridge:

    signature = ECDSA-P256(d, SHA-256(authenticatorData ‖ clientDataHash))

  the exact value a WebAuthn assertion carries.  It computes the
  SHA-256 signing hash ON-CHIP (via `sha256StreamHW`) and signs it
  with the M2 `p256SignCore`.

  ── Wire framing (M3 simplification) ──────────────────────────────
  A full HW CTAPHID + CBOR *parser* is out of M3 scope; a host shim
  (host/fido2/) translates the real CTAP2 getAssertion request into
  a FIXED 133-byte frame that this top consumes, MSB byte first:

    d(32) ‖ authenticatorData(37) ‖ clientDataHash(32) ‖ k(32)

  and streams back the 64-byte raw signature `r‖s`.  (The host shim
  DER-encodes r‖s and wraps the CTAP2 assertion response — the M1
  `DerSig` / `CTAP2Data` pure builders are the reference for that.)
  `d` and `k` arrive over the wire for the demo: a real device keeps
  `d` on-chip (M3's stateless-credential note) and derives `k` via
  RFC-6979 (M5).  The CTAPHID framer/deframer and CBOR emitter
  (`IP.USB.CTAPHID`, `IP.USB.CBOREmitHW`) are verified as standalone
  modules; wiring the full report layer into this top is M4/M5.

  The authenticatorData is built by the host (it embeds rpIdHash =
  SHA-256(rpId), flags, signCount) and hashed with clientDataHash
  on-chip — so the chip signs exactly what it hashed.
-/
import Sparkle
import IP.Crypto.P256SignDemo
import IP.Crypto.SHA256Stream
import IP.Net.UART

namespace Sparkle.IP.USB.Fido2Demo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.P256SignDemo (p256SignCore SignCoreOut)
open Sparkle.IP.Crypto.SHA256Stream (sha256StreamHW StreamOut)
open Sparkle.IP.Net.UART (uartRxHW uartTxHW RxOut TxOut)

/-! ### `@[hardware_module]` wrappers. -/

@[hardware_module] def wRx {dom : DomainConfig}
    (rxLine : Signal dom Bool) (bitDiv : Signal dom (BitVec 16)) : RxOut dom :=
  uartRxHW rxLine bitDiv

@[hardware_module] def wTx {dom : DomainConfig}
    (txByte : Signal dom (BitVec 8)) (txValid : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) : TxOut dom :=
  uartTxHW txByte txValid bitDiv

@[hardware_module] def wSignCore {dom : DomainConfig}
    (start : Signal dom Bool) (d k z : Signal dom (BitVec 256)) : SignCoreOut dom :=
  p256SignCore start d k z

@[hardware_module] def wSha256 {dom : DomainConfig}
    (start : Signal dom Bool) (nBlocks : Signal dom (BitVec 2))
    (blk0 blk1 : Signal dom (BitVec 512)) : StreamOut dom :=
  sha256StreamHW start nBlocks blk0 blk1

/-- Top-level output. -/
structure Fido2DemoOut (dom : DomainConfig) where
  uartTx        : Signal dom Bool
  /-- One-cycle strobe when an assertion signature completes (LED). -/
  assertionDone : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (Fido2DemoOut dom) dom := ⟨⟩

/-- Shift a byte into the low end of a 1064-bit accumulator. -/
@[inline] private def shiftIn1064 {dom : DomainConfig}
    (acc : Signal dom (BitVec 1064)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 1064) :=
  (acc <<< (Signal.pure (8#1064) : Signal dom (BitVec 1064)))
    |||
    (b.map (fun v => BitVec.append (0#1056) v) : Signal dom (BitVec 1064))

/-- The Tang Nano 50K FIDO2 getAssertion signing top. -/
def fido2Demo {dom : DomainConfig}
    (uartRx : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) : Fido2DemoOut dom :=
  circuit do
    -- ===== RX byte assembler: 133-byte frame → 1064-bit reg =====
    let accR   ← Signal.reg (0#1064)
    let rxCntR ← Signal.reg (0#8)
    let dR     ← Signal.reg (0#256)
    let adR    ← Signal.reg (0#296)   -- authenticatorData, 37 bytes
    let cdhR   ← Signal.reg (0#256)   -- clientDataHash, 32 bytes
    let kR     ← Signal.reg (0#256)
    let hashStartR ← Signal.reg false
    let zR     ← Signal.reg (0#256)
    let signStartR ← Signal.reg false

    -- ===== TX streamer =====
    let txAccR ← Signal.reg (0#512)
    let txCntR ← Signal.reg (0#8)
    let txBusyR ← Signal.reg false

    let accSig   := (accR : Signal dom (BitVec 1064))
    let rxCntSig := (rxCntR : Signal dom (BitVec 8))
    let dSig     := (dR : Signal dom (BitVec 256))
    let adSig    := (adR : Signal dom (BitVec 296))
    let cdhSig   := (cdhR : Signal dom (BitVec 256))
    let kSig     := (kR : Signal dom (BitVec 256))
    let zSig     := (zR : Signal dom (BitVec 256))
    let txAccSig := (txAccR : Signal dom (BitVec 512))
    let txCntSig := (txCntR : Signal dom (BitVec 8))
    let txBusySig := (txBusyR : Signal dom Bool)

    -- ===== UART RX =====
    let rx := wRx uartRx bitDiv
    let gotByte := rx.rxValid
    let accNext := shiftIn1064 accSig rx.rxByte
    let rxInc := (rxCntSig + (Signal.pure 1#8 : Signal dom (BitVec 8)))
    let atLast := (rxCntSig === (Signal.pure 132#8 : Signal dom (BitVec 8)))
    let lastByte := (gotByte &&& atLast : Signal dom Bool)

    accR <~ Signal.mux gotByte accNext accSig
    rxCntR <~ Signal.mux lastByte (Signal.pure 0#8 : Signal dom (BitVec 8))
                (Signal.mux gotByte rxInc rxCntSig)

    -- On the last byte, split the 1064-bit frame:
    --   d     = bits [1063:808]   (byte 0..31)
    --   ad    = bits [807:512]    (byte 32..68, 37 bytes = 296 bits)
    --   cdh   = bits [511:256]    (byte 69..100)
    --   k     = bits [255:0]      (byte 101..132)
    let dSlice   := (accNext.map (fun v => BitVec.extractLsb' 808 256 v) : Signal dom (BitVec 256))
    let adSlice  := (accNext.map (fun v => BitVec.extractLsb' 512 296 v) : Signal dom (BitVec 296))
    let cdhSlice := (accNext.map (fun v => BitVec.extractLsb' 256 256 v) : Signal dom (BitVec 256))
    let kSlice   := (accNext.map (fun v => BitVec.extractLsb' 0   256 v) : Signal dom (BitVec 256))
    dR   <~ Signal.mux lastByte dSlice dSig
    adR  <~ Signal.mux lastByte adSlice adSig
    cdhR <~ Signal.mux lastByte cdhSlice cdhSig
    kR   <~ Signal.mux lastByte kSlice kSig
    hashStartR <~ lastByte

    -- ===== build the two padded SHA-256 blocks for authData‖cdh =====
    -- Message = ad(37) ‖ cdh(32) = 69 bytes = 552 bits.  FIPS pad:
    --   block0 = message bytes 0..63              (ad[36:0] ‖ cdh[31:27]... )
    --   block1 = message bytes 64..68 ‖ 0x80 ‖ zeros ‖ len(64-bit BE = 552)
    -- Message bits, MSB-first: ad occupies bits [551:256] (296 bits),
    -- cdh bits [255:0] (256 bits) of a 552-bit value.
    -- Assemble msg552 = ad ‖ cdh, then slice blocks.
    let msg552 := (adSig ++ cdhSig : Signal dom (BitVec 552))
    -- block0 = top 512 bits of msg552.
    let blk0 := (msg552.map (fun v => BitVec.extractLsb' 40 512 v) : Signal dom (BitVec 512))
    -- remaining 40 message bits = msg552[39:0]; block1 = those 40 bits
    -- ‖ 0x80 ‖ (512-40-8-64 = 400 zero bits) ‖ len64(=552).
    let msgTail40 := (msg552.map (fun v => BitVec.extractLsb' 0 40 v) : Signal dom (BitVec 40))
    -- 0x80 padding byte + 400 zero bits + 64-bit length 552.
    let padConst := (Signal.pure (BitVec.append (0x80#8) (BitVec.append (0#400) (BitVec.ofNat 64 552)) : BitVec 472)
                      : Signal dom (BitVec 472))
    let blk1 := (msgTail40 ++ padConst : Signal dom (BitVec 512))

    let hashStartSig := (hashStartR : Signal dom Bool)
    let sha := wSha256 hashStartSig (Signal.pure 2#2 : Signal dom (BitVec 2)) blk0 blk1

    -- Latch z on hash done; pulse the signer the cycle after.
    zR <~ Signal.mux sha.done sha.hash zSig
    signStartR <~ sha.done

    -- ===== the signer core =====
    let core := wSignCore (signStartR : Signal dom Bool) dSig kSig zSig

    -- ===== TX: on done stream r‖s (64 bytes MSB-first) =====
    let tx := wTx
                (txAccSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))
                (txBusySig &&& (Signal.pure true : Signal dom Bool))
                bitDiv
    let txAccept := (txBusySig &&& tx.txReady : Signal dom Bool)
    let rsConcat := (core.rOut ++ core.sOut : Signal dom (BitVec 512))
    let txShift := (txAccSig <<< (Signal.pure (8#512) : Signal dom (BitVec 512)))
    txAccR <~ Signal.mux core.done rsConcat
                (Signal.mux txAccept txShift txAccSig)
    let txDec := (txCntSig - (Signal.pure 1#8 : Signal dom (BitVec 8)))
    txCntR <~ Signal.mux core.done (Signal.pure 64#8 : Signal dom (BitVec 8))
                (Signal.mux txAccept txDec txCntSig)
    let txMore := ((fun c => !(c == 0#8)) <$> txCntSig : Signal dom Bool)
    txBusyR <~ Signal.mux core.done (Signal.pure true : Signal dom Bool)
                (Signal.mux txAccept txMore txBusySig)

    return ({ uartTx := tx.txLine
            , assertionDone := core.done
            } : Fido2DemoOut dom)

/-- bitDiv for 115200 baud at a 27 MHz Tang Nano clock. -/
def bitDiv27M115200 : BitVec 16 := BitVec.ofNat 16 (27000000 / 115200 - 1)

end Sparkle.IP.USB.Fido2Demo
