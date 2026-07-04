/-
  IP.Crypto.EcdsaSignDemo — Tang Nano 50K secp256k1 ECDSA signing demo.

  A self-contained, synthesizable top-level that signs a message hash on
  an FPGA and streams the signature back over UART.

  ┌────────────────────────────────────────────────────────────────┐
  │ Tang Nano 50K bring-up                                          │
  │                                                                │
  │ Host → FPGA (UART RX, 96 bytes, big-endian):                   │
  │     d[32] ‖ k[32] ‖ z[32]                                       │
  │       d = private key, k = per-signature nonce, z = msg hash   │
  │   (RFC 6979 deterministic-k derivation + SHA-256 of the        │
  │    message are HOST concerns — the FPGA takes the three        │
  │    256-bit scalars directly, exactly as the pure-data          │
  │    `Secp256k1ECDSA.sign d k z` reference does.)                │
  │                                                                │
  │ FPGA → Host (UART TX, 64 bytes, big-endian):                   │
  │     r[32] ‖ s[32]     (the ECDSA signature)                    │
  │                                                                │
  │ Timing: one signature ≈ 1.8 M cycles (bit-serial field mul,    │
  │   256-bit double-and-add ladder, two Fermat inverses).  At a   │
  │   27 MHz Tang Nano clock that is ≈ 67 ms per signature — fine  │
  │   for a hardware-wallet "press-to-sign" UX.                     │
  │                                                                │
  │ Baud: 115200 8-N-1.  bitDiv = clk / baud − 1.                  │
  │   27 MHz → 27_000_000 / 115200 − 1 ≈ 233 (0xE9).               │
  │                                                                │
  │ Pins (.cst — placeholder, adjust to your board revision):      │
  │     clk    → 27 MHz oscillator pin                             │
  │     rst    → button (active-high; the Signal domain reset)     │
  │     uartRx → BL616/CH340 bridge TX  → FPGA input               │
  │     uartTx → FPGA output → bridge RX                           │
  │   (Reuse the same UART pins as the usb-webserver bring-up.)     │
  └────────────────────────────────────────────────────────────────┘

  Composition note.  The signer is a deep stack of start/done
  handshakes:

      signHW ─┬─▶ scalarMulHW ─▶ pointOpHW ─▶ mulHW      (k·G)
              ├─▶ modInvHW(p) / mulHW        (mod-p inv + muls)
              └─▶ modInvHW(n) / mulModNHW    (mod-n inv + muls)

  Each sub-engine exposes its "drive" side as OUTPUT ports and takes
  the result back as INPUT ports.  We close every loop with a 1-cycle
  feedback register inside a single `circuit do` (`reg` handle used
  before its `<~`), which is the standard clocked-feedback closure and
  synthesizes cleanly.  Every sub-engine is called through a thin
  `@[hardware_module]` wrapper so the synth elaborator emits it as a
  Verilog sub-module instance and lets us project its output-record
  fields.
-/
import Sparkle
import IP.Crypto.Proof.Secp256k1Field
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.Proof.Secp256k1PointJac
import IP.Crypto.Secp256k1FieldHW
import IP.Crypto.Secp256k1PointOpHW
import IP.Crypto.Secp256k1ScalarMulHW
import IP.Crypto.ModInvHW
import IP.Crypto.Secp256k1OrderHW
import IP.Crypto.Secp256k1ECDSAHW
import IP.Net.UART

namespace Sparkle.IP.Crypto.EcdsaSignDemo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Secp256k1FieldHW (mulHW MulOut)
open Sparkle.IP.Crypto.Secp256k1PointOpHW (pointOpHW PointOpOut)
open Sparkle.IP.Crypto.Secp256k1ScalarMulHW (scalarMulHW ScalarMulOut)
open Sparkle.IP.Crypto.ModInvHW (modInvHW ModInvOut)
open Sparkle.IP.Crypto.Secp256k1OrderHW (mulModNHW)
open Sparkle.IP.Crypto.Secp256k1ECDSAHW (signHW SignOut)
open Sparkle.IP.Net.UART (uartRxHW uartTxHW RxOut TxOut)

/-! ## `@[hardware_module]` wrappers.

    Tagging each engine makes the synth elaborator emit it as a
    Verilog sub-module *instance*, which is what lets a caller
    project the engine's output-record fields inside a `circuit do`
    (an inlined call cannot be field-projected). -/

@[hardware_module] def wMul {dom : DomainConfig}
    (start : Signal dom Bool) (aIn bIn : Signal dom (BitVec 256)) : MulOut dom :=
  mulHW start aIn bIn

@[hardware_module] def wMulN {dom : DomainConfig}
    (start : Signal dom Bool) (aIn bIn : Signal dom (BitVec 256)) :
    Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut dom :=
  mulModNHW start aIn bIn

@[hardware_module] def wPointOp {dom : DomainConfig}
    (start opDouble : Signal dom Bool)
    (x1 y1 z1 x2 y2 z2 : Signal dom (BitVec 256))
    (mulResult : Signal dom (BitVec 256)) (mulDone : Signal dom Bool) : PointOpOut dom :=
  pointOpHW start opDouble x1 y1 z1 x2 y2 z2 mulResult mulDone

@[hardware_module] def wScalarMul {dom : DomainConfig}
    (start : Signal dom Bool) (k : Signal dom (BitVec 256))
    (px py pz : Signal dom (BitVec 256))
    (poResX poResY poResZ : Signal dom (BitVec 256))
    (poResDone : Signal dom Bool) : ScalarMulOut dom :=
  scalarMulHW start k px py pz poResX poResY poResZ poResDone

@[hardware_module] def wInv {dom : DomainConfig}
    (start : Signal dom Bool) (aIn expBits : Signal dom (BitVec 256))
    (mulResult : Signal dom (BitVec 256)) (mulDone : Signal dom Bool) : ModInvOut dom :=
  modInvHW start aIn expBits mulResult mulDone

@[hardware_module] def wSign {dom : DomainConfig}
    (start : Signal dom Bool)
    (d k z : Signal dom (BitVec 256))
    (smX smY smZ : Signal dom (BitVec 256)) (smDone : Signal dom Bool)
    (pRes : Signal dom (BitVec 256)) (pDone : Signal dom Bool)
    (nRes : Signal dom (BitVec 256)) (nDone : Signal dom Bool) : SignOut dom :=
  signHW start d k z smX smY smZ smDone pRes pDone nRes nDone

/-! ## Signer core — all handshakes closed. -/

/-- Base-point / curve constants as 256-bit literals. -/
def gX : BitVec 256 := BitVec.ofNat 256 Sparkle.IP.Crypto.Secp256k1PointJac.baseX
def gY : BitVec 256 := BitVec.ofNat 256 Sparkle.IP.Crypto.Secp256k1PointJac.baseY
def one256 : BitVec 256 := 1#256

/-- Signature-core output. -/
structure SignCoreOut (dom : DomainConfig) where
  /-- Signature component r (valid at `done`). -/
  rOut : Signal dom (BitVec 256)
  /-- Signature component s (valid at `done`). -/
  sOut : Signal dom (BitVec 256)
  /-- Pulses when (r, s) is ready. -/
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (SignCoreOut dom) dom := ⟨⟩

/-- The ECDSA signer with every sub-engine wired and every start/done
    handshake closed by a 1-cycle feedback register.

    Engines instantiated:
      * `smMul`  — field mul for the scalar-mul point-op
      * `po`     — Jacobian point-op (double/add) for k·G
      * `sm`     — scalar-mul ladder (drives `po`)
      * `pMul`   — mod-p field mul (feeds the mod-p inverse AND the
                   signer's direct mod-p multiplies)
      * `pInv`   — mod-p Fermat inverse (drives `pMul`)
      * `nMul`   — mod-n mul (feeds the mod-n inverse AND the direct
                   mod-n multiplies)
      * `nInv`   — mod-n Fermat inverse (drives `nMul`)
      * `sign`   — the sign orchestrator (drives sm / mod-p / mod-n)

    The mod-p engine the signer drives can be EITHER an inverse
    (`pInvStart`) or a plain multiply (`pMulStart`); we route the
    inverse to `pInv` and the multiply to `pMul` and mux the result /
    done from whichever the signer triggered.  Same for mod-n. -/
def signCore {dom : DomainConfig}
    (start : Signal dom Bool)
    (d k z : Signal dom (BitVec 256)) : SignCoreOut dom :=
  circuit do
    -- ===== feedback registers (all 1-cycle delayed) =====
    -- scalar-mul point-op ↔ field-mul
    let smMulResR ← Signal.reg (0#256)
    let smMulDoneR ← Signal.reg false
    -- point-op → scalar-mul
    let poXR ← Signal.reg (0#256)
    let poYR ← Signal.reg (0#256)
    let poZR ← Signal.reg (0#256)
    let poDoneR ← Signal.reg false
    -- scalar-mul → sign
    let smXR ← Signal.reg (0#256)
    let smYR ← Signal.reg (0#256)
    let smZR ← Signal.reg (0#256)
    let smDoneR ← Signal.reg false
    -- mod-p mul feedback (into pInv and into sign)
    let pMulResR ← Signal.reg (0#256)
    let pMulDoneR ← Signal.reg false
    -- mod-p engine result → sign
    let pResR ← Signal.reg (0#256)
    let pDoneR ← Signal.reg false
    -- "the signer issued a DIRECT mod-p multiply and is awaiting it"
    -- (distinguishes the signer's multiply from the inverse's internal
    -- squarings, which share the same pMul engine).
    let pDirR ← Signal.reg false
    -- mod-n mul feedback (into nInv and into sign)
    let nMulResR ← Signal.reg (0#256)
    let nMulDoneR ← Signal.reg false
    -- mod-n engine result → sign
    let nResR ← Signal.reg (0#256)
    let nDoneR ← Signal.reg false
    let nDirR ← Signal.reg false

    let smMulResSig := (smMulResR : Signal dom (BitVec 256))
    let smMulDoneSig := (smMulDoneR : Signal dom Bool)
    let poXSig := (poXR : Signal dom (BitVec 256))
    let poYSig := (poYR : Signal dom (BitVec 256))
    let poZSig := (poZR : Signal dom (BitVec 256))
    let poDoneSig := (poDoneR : Signal dom Bool)
    let smXSig := (smXR : Signal dom (BitVec 256))
    let smYSig := (smYR : Signal dom (BitVec 256))
    let smZSig := (smZR : Signal dom (BitVec 256))
    let smDoneSig := (smDoneR : Signal dom Bool)
    let pMulResSig := (pMulResR : Signal dom (BitVec 256))
    let pMulDoneSig := (pMulDoneR : Signal dom Bool)
    let pResSig := (pResR : Signal dom (BitVec 256))
    let pDoneSig := (pDoneR : Signal dom Bool)
    let pDirSig := (pDirR : Signal dom Bool)
    let nMulResSig := (nMulResR : Signal dom (BitVec 256))
    let nMulDoneSig := (nMulDoneR : Signal dom Bool)
    let nResSig := (nResR : Signal dom (BitVec 256))
    let nDoneSig := (nDoneR : Signal dom Bool)
    let nDirSig := (nDirR : Signal dom Bool)

    -- ===== the sign orchestrator =====
    let gXSig := (Signal.pure gX : Signal dom (BitVec 256))
    let gYSig := (Signal.pure gY : Signal dom (BitVec 256))
    let gZSig := (Signal.pure one256 : Signal dom (BitVec 256))
    let sign := wSign start d k z smXSig smYSig smZSig smDoneSig
                  pResSig pDoneSig nResSig nDoneSig

    -- ===== scalar-mul + its point-op + field-mul =====
    let sm := wScalarMul sign.smStart sign.smK gXSig gYSig gZSig
                poXSig poYSig poZSig poDoneSig
    let po := wPointOp sm.poStart sm.poOpDouble
                sm.poX1 sm.poY1 sm.poZ1 sm.poX2 sm.poY2 sm.poZ2
                smMulResSig smMulDoneSig
    let smMul := wMul po.mulStart po.mulA po.mulB

    -- ===== mod-p inverse-or-multiply engine =====
    -- `pInv` drives its OWN internal field-mul port; but we give the
    -- inverse and the signer's direct multiply a SHARED `pMul` engine,
    -- muxing the start/operands by which one is active.
    let pInv := wInv sign.pInvStart sign.pA sign.pExp pMulResSig pMulDoneSig
    -- pMul serves either the inverse's internal multiply (pInv.mulStart)
    -- or the signer's direct mod-p multiply (sign.pMulStart).
    let pMulStart := ((· || ·) <$> pInv.mulStart <*> sign.pMulStart : Signal dom Bool)
    let pMulA := (Signal.mux sign.pMulStart sign.pA pInv.mulA : Signal dom (BitVec 256))
    let pMulB := (Signal.mux sign.pMulStart sign.pB pInv.mulB : Signal dom (BitVec 256))
    let pMul := wMul pMulStart pMulA pMulB

    -- ===== mod-n inverse-or-multiply engine =====
    let nInv := wInv sign.nInvStart sign.nA sign.nExp nMulResSig nMulDoneSig
    let nMulStart := ((· || ·) <$> nInv.mulStart <*> sign.nMulStart : Signal dom Bool)
    let nMulA := (Signal.mux sign.nMulStart sign.nA nInv.mulA : Signal dom (BitVec 256))
    let nMulB := (Signal.mux sign.nMulStart sign.nB nInv.mulB : Signal dom (BitVec 256))
    let nMul := wMulN nMulStart nMulA nMulB

    -- ===== close all feedback loops =====
    smMulResR <~ smMul.result
    smMulDoneR <~ smMul.done
    poXR <~ po.xOut
    poYR <~ po.yOut
    poZR <~ po.zOut
    poDoneR <~ po.done
    smXR <~ sm.xOut
    smYR <~ sm.yOut
    smZR <~ sm.zOut
    smDoneR <~ sm.done
    -- mod-p: the shared pMul result feeds both the inverse's internal
    -- multiply AND the signer's `pRes`; done likewise.  For the signer,
    -- `pRes/pDone` = inverse result when an inverse ran, else the mul.
    pMulResR <~ pMul.result
    pMulDoneR <~ pMul.done
    -- `pDir` tracks a pending signer DIRECT multiply: set when the
    -- signer issues one, cleared when pMul completes it.
    let pDirSet := sign.pMulStart
    let pMulFinish := ((· && ·) <$> pDirSig <*> pMul.done : Signal dom Bool)
    pDirR <~ Signal.mux pDirSet (Signal.pure true : Signal dom Bool)
              (Signal.mux pMul.done (Signal.pure false : Signal dom Bool) pDirSig)
    -- Signer's mod-p result: the direct multiply result when a direct
    -- multiply just finished, else the inverse result.
    pResR <~ Signal.mux pMulFinish pMul.result
              (Signal.mux pInv.done pInv.result pResSig)
    -- Signer's mod-p done pulses when EITHER the inverse finished OR the
    -- signer's own direct multiply finished (NOT the inverse's internal
    -- squarings — those are gated out by pDir).
    pDoneR <~ ((· || ·) <$> pInv.done <*> pMulFinish)
    -- mod-n (same structure):
    nMulResR <~ nMul.result
    nMulDoneR <~ nMul.done
    let nDirSet := sign.nMulStart
    let nMulFinish := ((· && ·) <$> nDirSig <*> nMul.done : Signal dom Bool)
    nDirR <~ Signal.mux nDirSet (Signal.pure true : Signal dom Bool)
              (Signal.mux nMul.done (Signal.pure false : Signal dom Bool) nDirSig)
    nResR <~ Signal.mux nMulFinish nMul.result
              (Signal.mux nInv.done nInv.result nResSig)
    nDoneR <~ ((· || ·) <$> nInv.done <*> nMulFinish)

    return ({ rOut := sign.rOut
            , sOut := sign.sOut
            , done := sign.done
            } : SignCoreOut dom)

/-! ## UART demo top-level.

    RX: shift 96 bytes (d‖k‖z, big-endian) into a 768-bit register;
    on the 96th byte, latch d/k/z and pulse `signStart`.
    TX: on `signCore.done`, latch r‖s (512 bits) into a shift
    register and stream the 64 bytes MSB-first, gated by `txReady`. -/

@[hardware_module] def wRx {dom : DomainConfig}
    (rxLine : Signal dom Bool) (bitDiv : Signal dom (BitVec 16)) : RxOut dom :=
  uartRxHW rxLine bitDiv

@[hardware_module] def wTx {dom : DomainConfig}
    (txByte : Signal dom (BitVec 8)) (txValid : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) : TxOut dom :=
  uartTxHW txByte txValid bitDiv

@[hardware_module] def wSignCore {dom : DomainConfig}
    (start : Signal dom Bool) (d k z : Signal dom (BitVec 256)) : SignCoreOut dom :=
  signCore start d k z

/-- Demo top-level output: the UART TX line (+ a `done` strobe you can
    wire to an LED). -/
structure DemoOut (dom : DomainConfig) where
  uartTx : Signal dom Bool
  /-- High-for-one-cycle when a signature completes (LED strobe). -/
  signDone : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (DemoOut dom) dom := ⟨⟩

/-- Shift a byte into the low end of a 768-bit accumulator (big-endian:
    first byte received ends up in the most-significant slot after 96). -/
@[inline] private def shiftIn768 {dom : DomainConfig}
    (acc : Signal dom (BitVec 768)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 768) :=
  ((· <<< ·) <$> acc <*> (Signal.pure (8#768) : Signal dom (BitVec 768)))
    |||
    (b.map (fun v => BitVec.append (0#760) v) : Signal dom (BitVec 768))

/-- Top-level Tang Nano 50K ECDSA signing demo. -/
def ecdsaSignDemo {dom : DomainConfig}
    (uartRx : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) : DemoOut dom :=
  circuit do
    -- ===== RX byte assembler =====
    let accR   ← Signal.reg (0#768)   -- shift register for d‖k‖z
    let rxCntR ← Signal.reg (0#7)     -- bytes received, 0..96
    let dR     ← Signal.reg (0#256)
    let kR     ← Signal.reg (0#256)
    let zR     ← Signal.reg (0#256)
    let startR ← Signal.reg false     -- signStart pulse

    -- ===== TX streamer =====
    let txAccR ← Signal.reg (0#512)   -- r‖s to shift out, MSB byte first
    let txCntR ← Signal.reg (0#7)     -- bytes left to send, 0..64
    let txBusyR ← Signal.reg false

    let accSig := (accR : Signal dom (BitVec 768))
    let rxCntSig := (rxCntR : Signal dom (BitVec 7))
    let dSig := (dR : Signal dom (BitVec 256))
    let kSig := (kR : Signal dom (BitVec 256))
    let zSig := (zR : Signal dom (BitVec 256))
    let txAccSig := (txAccR : Signal dom (BitVec 512))
    let txCntSig := (txCntR : Signal dom (BitVec 7))
    let txBusySig := (txBusyR : Signal dom Bool)

    -- ===== UART RX =====
    let rx := wRx uartRx bitDiv
    -- byte-received pulse
    let gotByte := rx.rxValid
    -- accumulator shifts in each received byte
    let accNext := shiftIn768 accSig rx.rxByte
    let rxInc := ((· + ·) <$> rxCntSig <*> (Signal.pure 1#7 : Signal dom (BitVec 7)))
    -- last (96th) byte just arrived when the count is at 95 and gotByte
    let atLast := ((· == ·) <$> rxCntSig <*> (Signal.pure 95#7 : Signal dom (BitVec 7)))
    let lastByte := ((· && ·) <$> gotByte <*> atLast : Signal dom Bool)

    accR <~ Signal.mux gotByte accNext accSig
    -- count wraps back to 0 after the last byte so a new frame can start
    rxCntR <~ Signal.mux lastByte (Signal.pure 0#7 : Signal dom (BitVec 7))
                (Signal.mux gotByte rxInc rxCntSig)
    -- On the last byte, `accNext` holds all 96 bytes: split into d,k,z.
    let dSlice := (accNext.map (fun v => BitVec.extractLsb' 512 256 v) : Signal dom (BitVec 256))
    let kSlice := (accNext.map (fun v => BitVec.extractLsb' 256 256 v) : Signal dom (BitVec 256))
    let zSlice := (accNext.map (fun v => BitVec.extractLsb' 0 256 v) : Signal dom (BitVec 256))
    dR <~ Signal.mux lastByte dSlice dSig
    kR <~ Signal.mux lastByte kSlice kSig
    zR <~ Signal.mux lastByte zSlice zSig
    -- signStart pulses the cycle AFTER the last byte (d/k/z are latched).
    startR <~ lastByte

    -- ===== the signer core =====
    let core := wSignCore (startR : Signal dom Bool) dSig kSig zSig

    -- ===== TX: on done, load r‖s and stream 64 bytes =====
    let tx := wTx
                -- top byte of the shift register
                (txAccSig.map (fun v => BitVec.extractLsb' 504 8 v) : Signal dom (BitVec 8))
                -- valid: we still have bytes to send and TX can accept
                ((· && ·) <$> txBusySig <*> (Signal.pure true : Signal dom Bool))
                bitDiv
    -- byte accepted this cycle = we are busy and TX was ready (not busy)
    let txAccept := ((· && ·) <$> txBusySig <*> tx.txReady : Signal dom Bool)
    -- r‖s concatenated: r in high 256, s in low 256.
    let rsConcat := ((· ++ ·) <$> core.rOut <*> core.sOut : Signal dom (BitVec 512))
    -- load on done; shift left one byte on each accepted byte.
    let txShift := ((· <<< ·) <$> txAccSig <*> (Signal.pure (8#512) : Signal dom (BitVec 512)))
    txAccR <~ Signal.mux core.done rsConcat
                (Signal.mux txAccept txShift txAccSig)
    let txDec := ((· - ·) <$> txCntSig <*> (Signal.pure 1#7 : Signal dom (BitVec 7)))
    txCntR <~ Signal.mux core.done (Signal.pure 64#7 : Signal dom (BitVec 7))
                (Signal.mux txAccept txDec txCntSig)
    -- busy while there are still bytes to send.
    let txMore := ((fun c => !(c == 0#7)) <$> txCntSig : Signal dom Bool)
    txBusyR <~ Signal.mux core.done (Signal.pure true : Signal dom Bool)
                (Signal.mux txAccept txMore txBusySig)

    return ({ uartTx := tx.txLine
            , signDone := core.done
            } : DemoOut dom)

/-- bitDiv for 115200 baud at a 27 MHz Tang Nano clock. -/
def bitDiv27M115200 : BitVec 16 := BitVec.ofNat 16 (27000000 / 115200 - 1)   -- ≈ 233

end Sparkle.IP.Crypto.EcdsaSignDemo
