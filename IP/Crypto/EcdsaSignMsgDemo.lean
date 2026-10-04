/-
  IP.Crypto.EcdsaSignMsgDemo — UART front-end for the fully on-chip secure
  signer (`EcdsaSignMsgSmall.signMsgSmallDemo`).

  Wire protocol (Tang Nano 20k, 115200 baud @ 27 MHz):

    * HOST → device: 136 bytes — the Keccak-256-padded message preimage
      (`0x01 … 0x80`, a single rate block).  The host applies the pad (it
      knows the length), so the device keeps a constant lane fill and no
      length byte — same convention as `PolicySignDemoM2` /
      `host/policy_signer` `keccak_pad136`.
    * device → HOST: 64 bytes — `r ‖ s` (MSB first).

  Everything secret stays on the die: `d` is baked (12345), `k` is derived
  on-chip (RFC-6979), and `z = keccak256(preimage)` is computed on-chip.
-/
import Sparkle
import IP.Crypto.EcdsaSignMsgSmall
import IP.Crypto.EcdsaSignSmallDemo
import IP.Net.UART

namespace Sparkle.IP.Crypto.EcdsaSignMsgDemo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignMsgSmall (signMsg1SmallDemo signZSmallDemo)
open Sparkle.IP.Crypto.EcdsaSignSmallDemo (wRx wTx SignSmallOut DemoOut)

/-- Shift a byte into the low end of a 1088-bit accumulator (136-byte block). -/
@[inline] private def shiftIn1088 {dom : DomainConfig}
    (acc : Signal dom (BitVec 1088)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 1088) :=
  (acc <<< (Signal.pure (8#1088) : Signal dom (BitVec 1088)))
    ||| (b.map (fun v => BitVec.append (0#1080) v) : Signal dom (BitVec 1088))

/-- UART signing demo: host sends the 136-byte padded preimage, device
    replies 64 bytes `r‖s`.  Baked key, on-chip nonce + hash. -/
def signMsgDemo {dom : DomainConfig}
    (uartRx : Signal dom Bool) (bitDiv : Signal dom (BitVec 16)) : DemoOut dom :=
  circuit do
    -- ===== RX: assemble 136 bytes (MSB-first) directly into `accR` =====
    -- No separate latched copy: after the last byte `accR` holds the padded
    -- preimage and no more bytes arrive during the ~1.3M-cycle sign, so the
    -- message lanes read straight off `accSig` (saves a 1088-bit register).
    let accR    ← Signal.reg (0#1088)
    let rxCntR  ← Signal.reg (0#8)     -- 0..135
    let startR  ← Signal.reg false
    let txDataR ← Signal.reg (0#512)   -- TX shift r‖s (MSB byte first)
    let remR    ← Signal.reg (0#7)     -- bytes left to send
    let sendingR ← Signal.reg false

    let accSig    := (accR : Signal dom (BitVec 1088))
    let rxCntSig  := (rxCntR : Signal dom (BitVec 8))
    let txDataSig := (txDataR : Signal dom (BitVec 512))
    let remSig    := (remR : Signal dom (BitVec 7))
    let sendingSig := (sendingR : Signal dom Bool)

    let rx := wRx uartRx bitDiv
    let gotByte := rx.rxValid
    let accNext := shiftIn1088 accSig rx.rxByte
    let rxInc := (rxCntSig + (Signal.pure 1#8 : Signal dom (BitVec 8)))
    let atLast := (rxCntSig === 135#8)
    let lastByte := (gotByte &&& atLast : Signal dom Bool)
    accR <~ Signal.mux gotByte accNext accSig
    rxCntR <~ Signal.mux lastByte (Signal.pure 0#8 : Signal dom (BitVec 8))
                (Signal.mux gotByte rxInc rxCntSig)
    startR <~ lastByte

    -- 17 message lanes from the registered padded preimage `preSig`
    -- (byte n at bit 1080-8n; lane i = LE pack of bytes 8i..8i+7).  Copied
    -- verbatim from PolicySignDemoM2 (proven against the reference).
    let ml0 := (((accSig.map (fun v => BitVec.extractLsb' 1024 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 1032 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 1040 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 1048 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 1056 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 1064 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 1072 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 1080 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml1 := (((accSig.map (fun v => BitVec.extractLsb' 960 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 968 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 976 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 984 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 992 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 1000 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 1008 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 1016 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml2 := (((accSig.map (fun v => BitVec.extractLsb' 896 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 904 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 912 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 920 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 928 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 936 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 944 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 952 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml3 := (((accSig.map (fun v => BitVec.extractLsb' 832 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 840 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 848 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 856 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 864 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 872 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 880 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 888 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml4 := (((accSig.map (fun v => BitVec.extractLsb' 768 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 776 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 784 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 792 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 800 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 808 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 816 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 824 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml5 := (((accSig.map (fun v => BitVec.extractLsb' 704 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 712 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 720 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 728 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 736 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 744 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 752 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 760 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml6 := (((accSig.map (fun v => BitVec.extractLsb' 640 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 648 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 656 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 664 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 672 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 680 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 688 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 696 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml7 := (((accSig.map (fun v => BitVec.extractLsb' 576 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 584 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 592 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 600 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 608 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 616 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 624 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 632 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml8 := (((accSig.map (fun v => BitVec.extractLsb' 512 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 520 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 528 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 536 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 544 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 552 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 560 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 568 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml9 := (((accSig.map (fun v => BitVec.extractLsb' 448 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 456 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 464 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 472 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 480 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 488 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 496 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml10 := (((accSig.map (fun v => BitVec.extractLsb' 384 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 392 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 400 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 408 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 416 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 424 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 432 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 440 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml11 := (((accSig.map (fun v => BitVec.extractLsb' 320 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 328 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 336 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 344 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 352 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 360 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 368 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 376 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml12 := (((accSig.map (fun v => BitVec.extractLsb' 256 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 264 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 272 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 280 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 288 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 296 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 304 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 312 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml13 := (((accSig.map (fun v => BitVec.extractLsb' 192 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 200 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 208 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 216 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 224 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 232 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 240 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 248 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml14 := (((accSig.map (fun v => BitVec.extractLsb' 128 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 136 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 144 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 152 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 160 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 168 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 176 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 184 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml15 := (((accSig.map (fun v => BitVec.extractLsb' 64 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 72 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 80 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 88 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 96 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 104 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 112 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 120 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml16 := (((accSig.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((accSig.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (accSig.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    -- ===== full on-chip signer: keccak(z) → rfc6979(k) → sign =====
    -- Single-block core (the padded preimage is one 136-byte rate block), which
    -- drops the multi-block sponge state to fit the Tang Nano 20k.
    let core := signMsg1SmallDemo (startR : Signal dom Bool)
      ml0 ml1 ml2 ml3 ml4 ml5 ml6 ml7 ml8 ml9 ml10 ml11 ml12 ml13 ml14 ml15 ml16

    -- ===== TX: on `core.done` load r‖s, pump 64 bytes (MSB first) =====
    let wantSend := sendingSig
    let tx := wTx
                (txDataSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))
                wantSend bitDiv
    let accepted := (wantSend &&& tx.txReady : Signal dom Bool)
    let rsConcat := (core.rOut ++ core.sOut : Signal dom (BitVec 512))
    let txShift := (txDataSig <<< (Signal.pure (8#512) : Signal dom (BitVec 512)))
    txDataR <~ Signal.mux core.done rsConcat (Signal.mux accepted txShift txDataSig)
    let remDec := (remSig - (Signal.pure 1#7 : Signal dom (BitVec 7)))
    remR <~ Signal.mux core.done (Signal.pure 64#7 : Signal dom (BitVec 7))
              (Signal.mux accepted remDec remSig)
    let txLast := (accepted &&& (remSig === 1#7) : Signal dom Bool)
    sendingR <~ Signal.mux core.done (Signal.pure true : Signal dom Bool)
                  (Signal.mux txLast (Signal.pure false : Signal dom Bool) sendingSig)

    return ({ uartTx := tx.txLine, signDone := core.done } : DemoOut dom)

/-- Shift a byte into the low end of a 256-bit accumulator. -/
@[inline] private def shiftIn256 {dom : DomainConfig}
    (acc : Signal dom (BitVec 256)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 256) :=
  (acc <<< (Signal.pure (8#256) : Signal dom (BitVec 256)))
    ||| (b.map (fun v => BitVec.append (0#248) v) : Signal dom (BitVec 256))

/-- UART front-end for the **k-on-chip** signer (no on-chip Keccak): the host
    sends the 32-byte hash `z` (big-endian, MSB first); the device derives the
    RFC-6979 nonce `k` on-chip and replies 64 bytes `r‖s`.  The private key `d`
    is baked and `k` never leaves the die — so a leaked wire can't recover `d`
    (the ECDSA key-security property).  This fits the Tang Nano 20k; the full
    on-chip-Keccak variant (`signMsgDemo`) needs a larger part. -/
def signZDemo {dom : DomainConfig}
    (uartRx : Signal dom Bool) (bitDiv : Signal dom (BitVec 16)) : DemoOut dom :=
  circuit do
    -- ===== RX: assemble 32 bytes (MSB-first) into `zR` =====
    let accR    ← Signal.reg (0#256)
    let rxCntR  ← Signal.reg (0#6)     -- 0..31
    let startR  ← Signal.reg false
    let txDataR ← Signal.reg (0#512)   -- TX shift r‖s (MSB byte first)
    let remR    ← Signal.reg (0#7)     -- bytes left to send
    let sendingR ← Signal.reg false

    let accSig    := (accR : Signal dom (BitVec 256))
    let rxCntSig  := (rxCntR : Signal dom (BitVec 6))
    let txDataSig := (txDataR : Signal dom (BitVec 512))
    let remSig    := (remR : Signal dom (BitVec 7))
    let sendingSig := (sendingR : Signal dom Bool)

    let rx := wRx uartRx bitDiv
    let gotByte := rx.rxValid
    let accNext := shiftIn256 accSig rx.rxByte
    let rxInc := (rxCntSig + (Signal.pure 1#6 : Signal dom (BitVec 6)))
    let atLast := (rxCntSig === 31#6)
    let lastByte := (gotByte &&& atLast : Signal dom Bool)
    accR <~ Signal.mux gotByte accNext accSig
    rxCntR <~ Signal.mux lastByte (Signal.pure 0#6 : Signal dom (BitVec 6))
                (Signal.mux gotByte rxInc rxCntSig)
    startR <~ lastByte

    -- ===== k-on-chip signer: rfc6979(k) → sign =====
    -- `accSig` holds the full 32-byte z after the last byte (no more bytes
    -- arrive during the ~1.3M-cycle sign), so feed it straight in.
    let core := signZSmallDemo (startR : Signal dom Bool) accSig

    -- ===== TX: on `core.done` load r‖s, pump 64 bytes (MSB first) =====
    let wantSend := sendingSig
    let tx := wTx
                (txDataSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))
                wantSend bitDiv
    let accepted := (wantSend &&& tx.txReady : Signal dom Bool)
    let rsConcat := (core.rOut ++ core.sOut : Signal dom (BitVec 512))
    let txShift := (txDataSig <<< (Signal.pure (8#512) : Signal dom (BitVec 512)))
    txDataR <~ Signal.mux core.done rsConcat (Signal.mux accepted txShift txDataSig)
    let remDec := (remSig - (Signal.pure 1#7 : Signal dom (BitVec 7)))
    remR <~ Signal.mux core.done (Signal.pure 64#7 : Signal dom (BitVec 7))
              (Signal.mux accepted remDec remSig)
    let txLast := (accepted &&& (remSig === 1#7) : Signal dom Bool)
    sendingR <~ Signal.mux core.done (Signal.pure true : Signal dom Bool)
                  (Signal.mux txLast (Signal.pure false : Signal dom Bool) sendingSig)

    return ({ uartTx := tx.txLine, signDone := core.done } : DemoOut dom)

end Sparkle.IP.Crypto.EcdsaSignMsgDemo
