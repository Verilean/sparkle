/-
  IP.Crypto.PolicySignDemoM2 — policy-enforcing Ethereum signer,
  Milestone 2: signs the REAL EIP-1559 transaction hash.

  Where M1 (`PolicySignDemo`) hashes a 64-byte `to‖value`
  stand-in, M2 hashes the genuine EIP-1559 signing preimage
  `P = 0x02 ‖ rlp([chainId, nonce, maxPriorityFee, maxFee,
  gasLimit, to, value, data, accessList])` on-chip, so the
  resulting `(r,s)` is a valid Ethereum signature that a node
  (e.g. a local anvil) accepts and executes.

  Wire frame (host-serialized, MSB byte first), 264 bytes:

      d(32) ‖ k(32) ‖ to(32) ‖ value(32) ‖ paddedPreimage(136)

  * The HOST applies Keccak padding (0x01 … 0x80) to the ≤135-byte
    preimage → a fixed 136-byte single rate block.  So the device
    keeps M1's CONSTANT lane fill: no length-dependent pad mux and
    no `len` byte on the wire.  (Matches `host/policy_signer/
    sign_tx.py` `keccak_pad136`.)
  * The sponge XORs the 17 message lanes of the padded block and
    runs Keccak-f once; `nBlocks = 1`.

  Policy note (honest M2 boundary).  RLP integer fields are
  big-endian with no leading zeros, so `to`/`value` sit at
  VARIABLE byte offsets inside the preimage — the device cannot
  fixed-offset-slice them from the hashed bytes.  So `to`/`value`
  are sent as DEDICATED fixed fields and the policy checks those.
  Binding those fields to the hashed preimage bytes (an on-chip
  RLP locate) is the M3 follow-up.  This is a documented reduction
  from M1's "sliced from the same bytes it hashes" guarantee, NOT
  a `sorry`.

  On policy PASS: stream 64 bytes `r‖s`.  On FAIL: one `0xEE`
  byte + a reject strobe.
-/
import Sparkle
import IP.Crypto.EcdsaSignDemo
import IP.Crypto.Keccak256Sponge
import IP.Crypto.TxPolicy
import IP.Net.UART

namespace Sparkle.IP.Crypto.PolicySignDemoM2

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignDemo (signCore SignCoreOut wRx wTx bitDiv27M115200)
open Sparkle.IP.Crypto.Keccak256Sponge (keccak256SpongeHW SpongeOut)
open Sparkle.IP.Crypto.TxPolicy (txPolicyOk)
open Sparkle.IP.Net.UART (RxOut TxOut)

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

structure PolicyDemoM2Out (dom : DomainConfig) where
  uartTx   : Signal dom Bool
  signDone : Signal dom Bool
  rejected : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (PolicyDemoM2Out dom) dom := ⟨⟩

/-- Shift a byte into the low end of a 2112-bit accumulator (264 B frame). -/
@[inline] private def shiftIn2112 {dom : DomainConfig}
    (acc : Signal dom (BitVec 2112)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 2112) :=
  (acc <<< (Signal.pure (8#2112) : Signal dom (BitVec 2112)))
    |||
    (b.map (fun v => BitVec.append (0#2104) v) : Signal dom (BitVec 2112))

/-- The Tang Nano 50K policy-enforcing signer (M2, real EIP-1559). -/
def policySignDemoM2 {dom : DomainConfig}
    (uartRx : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) : PolicyDemoM2Out dom :=
  circuit do
    -- ===== RX byte assembler (264-byte frame → 2112-bit reg) =====
    let accR    ← Signal.reg (0#2112)
    let rxCntR  ← Signal.reg (0#9)      -- bytes received, 0..264 (needs 9 bits)
    let dR      ← Signal.reg (0#256)
    let kR      ← Signal.reg (0#256)
    let toR     ← Signal.reg (0#256)
    let valR    ← Signal.reg (0#256)
    let preR    ← Signal.reg (0#1088)   -- padded preimage (136 B)
    let hashStartR ← Signal.reg false

    let zR         ← Signal.reg (0#256)
    let signStartR ← Signal.reg false
    let rejectR    ← Signal.reg false

    let txAccR  ← Signal.reg (0#512)
    let txCntR  ← Signal.reg (0#8)
    let txBusyR ← Signal.reg false

    let accSig   := (accR : Signal dom (BitVec 2112))
    let rxCntSig := (rxCntR : Signal dom (BitVec 9))
    let dSig     := (dR : Signal dom (BitVec 256))
    let kSig     := (kR : Signal dom (BitVec 256))
    let toSig    := (toR : Signal dom (BitVec 256))
    let valSig   := (valR : Signal dom (BitVec 256))
    let preSig   := (preR : Signal dom (BitVec 1088))
    let zSig     := (zR : Signal dom (BitVec 256))
    let txAccSig := (txAccR : Signal dom (BitVec 512))
    let txCntSig := (txCntR : Signal dom (BitVec 8))
    let txBusySig := (txBusyR : Signal dom Bool)

    let rx := wRx uartRx bitDiv
    let gotByte := rx.rxValid
    let accNext := shiftIn2112 accSig rx.rxByte
    let rxInc := (rxCntSig + (Signal.pure 1#9 : Signal dom (BitVec 9)))
    let atLast := (rxCntSig === (Signal.pure 263#9 : Signal dom (BitVec 9)))
    let lastByte := (gotByte &&& atLast : Signal dom Bool)

    accR <~ Signal.mux gotByte accNext accSig
    rxCntR <~ Signal.mux lastByte (Signal.pure 0#9 : Signal dom (BitVec 9))
                (Signal.mux gotByte rxInc rxCntSig)

    -- Field slices from the 2112-bit `accNext` (MSB-first):
    --   d     bytes 0..31   → extractLsb' 1856 256
    --   k     bytes 32..63  → extractLsb' 1600 256
    --   to    bytes 64..95  → extractLsb' 1344 256
    --   value bytes 96..127 → extractLsb' 1088 256
    --   pre   bytes 128..263→ extractLsb' 0 1088  (136 B padded block)
    let dSlice  := (accNext.map (fun v => BitVec.extractLsb' 1856 256 v) : Signal dom (BitVec 256))
    let kSlice  := (accNext.map (fun v => BitVec.extractLsb' 1600 256 v) : Signal dom (BitVec 256))
    let toSlice := (accNext.map (fun v => BitVec.extractLsb' 1344 256 v) : Signal dom (BitVec 256))
    let vSlice  := (accNext.map (fun v => BitVec.extractLsb' 1088 256 v) : Signal dom (BitVec 256))
    let preSlice := (accNext.map (fun v => BitVec.extractLsb' 0 1088 v) : Signal dom (BitVec 1088))
    dR   <~ Signal.mux lastByte dSlice  dSig
    kR   <~ Signal.mux lastByte kSlice  kSig
    toR  <~ Signal.mux lastByte toSlice toSig
    valR <~ Signal.mux lastByte vSlice  valSig
    preR <~ Signal.mux lastByte preSlice preSig
    hashStartR <~ lastByte

    -- 17 message lanes from the registered padded preimage `preSig`.
    -- Lane i = LE pack of preimage bytes 8i..8i+7 (byte-reversed).
    -- preimage byte n at preSig bit (1080 - 8n).  Fully-inline flat
    -- `append <$> single-extract <*> …` (the only shape that lowers).
    let ml0 := (((preSig.map (fun v => BitVec.extractLsb' 1024 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 1032 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 1040 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 1048 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 1056 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 1064 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 1072 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 1080 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml1 := (((preSig.map (fun v => BitVec.extractLsb' 960 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 968 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 976 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 984 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 992 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 1000 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 1008 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 1016 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml2 := (((preSig.map (fun v => BitVec.extractLsb' 896 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 904 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 912 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 920 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 928 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 936 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 944 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 952 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml3 := (((preSig.map (fun v => BitVec.extractLsb' 832 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 840 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 848 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 856 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 864 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 872 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 880 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 888 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml4 := (((preSig.map (fun v => BitVec.extractLsb' 768 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 776 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 784 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 792 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 800 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 808 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 816 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 824 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml5 := (((preSig.map (fun v => BitVec.extractLsb' 704 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 712 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 720 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 728 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 736 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 744 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 752 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 760 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml6 := (((preSig.map (fun v => BitVec.extractLsb' 640 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 648 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 656 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 664 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 672 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 680 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 688 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 696 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml7 := (((preSig.map (fun v => BitVec.extractLsb' 576 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 584 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 592 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 600 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 608 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 616 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 624 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 632 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml8 := (((preSig.map (fun v => BitVec.extractLsb' 512 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 520 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 528 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 536 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 544 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 552 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 560 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 568 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml9 := (((preSig.map (fun v => BitVec.extractLsb' 448 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 456 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 464 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 472 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 480 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 488 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 496 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml10 := (((preSig.map (fun v => BitVec.extractLsb' 384 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 392 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 400 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 408 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 416 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 424 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 432 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 440 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml11 := (((preSig.map (fun v => BitVec.extractLsb' 320 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 328 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 336 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 344 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 352 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 360 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 368 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 376 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml12 := (((preSig.map (fun v => BitVec.extractLsb' 256 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 264 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 272 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 280 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 288 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 296 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 304 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 312 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml13 := (((preSig.map (fun v => BitVec.extractLsb' 192 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 200 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 208 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 216 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 224 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 232 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 240 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 248 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml14 := (((preSig.map (fun v => BitVec.extractLsb' 128 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 136 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 144 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 152 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 160 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 168 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 176 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 184 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml15 := (((preSig.map (fun v => BitVec.extractLsb' 64 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 72 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 80 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 88 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 96 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 104 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 112 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 120 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let ml16 := (((preSig.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((preSig.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (preSig.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let z64 := (Signal.pure 0#64 : Signal dom (BitVec 64))
    let hashStartSig := (hashStartR : Signal dom Bool)
    let sponge := wSponge hashStartSig (Signal.pure 1#2 : Signal dom (BitVec 2))
      ml0 ml1 ml2 ml3 ml4 ml5 ml6 ml7 ml8 ml9 ml10 ml11 ml12 ml13 ml14 ml15 ml16
      z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64
    let zl0 := (((sponge.d0.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d0.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (sponge.d0.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let zl1 := (((sponge.d1.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d1.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (sponge.d1.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let zl2 := (((sponge.d2.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d2.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (sponge.d2.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let zl3 := (((sponge.d3.map (fun v => BitVec.extractLsb' 0 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 8 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 16 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 24 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 32 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 40 8 v) : Signal dom (BitVec 8)) ++ ((sponge.d3.map (fun v => BitVec.extractLsb' 48 8 v) : Signal dom (BitVec 8)) ++ (sponge.d3.map (fun v => BitVec.extractLsb' 56 8 v) : Signal dom (BitVec 8))))))))) : Signal dom (BitVec 64))
    let z := (BitVec.append <$> zl0 <*>
               (BitVec.append <$> zl1 <*>
                 (zl2 ++ zl3
                  : Signal dom (BitVec 128))
                : Signal dom (BitVec 192))
             : Signal dom (BitVec 256))
    zR <~ Signal.mux sponge.done z zSig

    -- Policy on the dedicated to/value fields (M2 boundary — see header).
    let recip := (toSig.map (fun v => BitVec.extractLsb' 0 160 v) : Signal dom (BitVec 160))
    let policyOk := txPolicyOk recip valSig
    let doSign := (sponge.done &&& policyOk : Signal dom Bool)
    let doReject := ((· && ·) <$> sponge.done
                      <*> (~~~policyOk) : Signal dom Bool)
    signStartR <~ doSign
    rejectR <~ doReject

    let core := wSignCore (signStartR : Signal dom Bool) dSig kSig zSig

    let tx := wTx
                (txAccSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))
                (txBusySig &&& (Signal.pure true : Signal dom Bool))
                bitDiv
    let txAccept := (txBusySig &&& tx.txReady : Signal dom Bool)
    let rsConcat := (core.rOut ++ core.sOut : Signal dom (BitVec 512))
    let rejFrame := (Signal.pure (BitVec.shiftLeft (0xEE#512) 504) : Signal dom (BitVec 512))
    let txShift := (txAccSig <<< (Signal.pure (8#512) : Signal dom (BitVec 512)))
    let loadEvt := (core.done ||| (rejectR : Signal dom Bool) : Signal dom Bool)
    let loadVal := Signal.mux core.done rsConcat rejFrame
    txAccR <~ Signal.mux loadEvt loadVal
                (Signal.mux txAccept txShift txAccSig)
    let txDec := (txCntSig - (Signal.pure 1#8 : Signal dom (BitVec 8)))
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
            } : PolicyDemoM2Out dom)

end Sparkle.IP.Crypto.PolicySignDemoM2
