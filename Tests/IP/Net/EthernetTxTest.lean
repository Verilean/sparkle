/-
  Cycle-by-cycle sim test for IP.Net.Ethernet.txFramer.

  Drive a single-frame TX with the same DMAC/SMAC/EthType/payload
  as the RX test's reference frame, capture the per-cycle `txByte`
  / `txValid` / `txSop` / `txEop` outputs, and compare them
  byte-for-byte against the hand-built reference frame:

    DMAC    : AA BB CC DD EE FF
    SMAC    : 11 22 33 44 55 66
    EthType : 08 00
    Payload : DE AD BE EF

  Total 18 bytes; the framer reads them across 19 cycles (cycle 0
  is the SOP edge with header byte 0; cycle 17 is the last payload
  byte; cycle 18 is back-to-idle with `txValid = 0`).
-/

import IP.Net.Ethernet
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.Ethernet

namespace Sparkle.Tests.IP.Net.EthernetTxTest

private def dmacVal : BitVec 48 := 0xAABBCCDDEEFF#48
private def smacVal : BitVec 48 := 0x112233445566#48
private def etVal   : BitVec 16 := 0x0800#16

private def payloadBytes : List (BitVec 8) :=
  [ 0xDE#8, 0xAD#8, 0xBE#8, 0xEF#8 ]

private def nPay : Nat := payloadBytes.length

/-- Inputs.  Header values are constant for the entire run (the
    framer latches them on `start`).  Payload byte stream is
    held high on cycles 14..17 inclusive (after the 14-byte
    header walks through). -/
private def dmacIn : Signal defaultDomain (BitVec 48) :=
  ⟨fun _ => dmacVal⟩
private def smacIn : Signal defaultDomain (BitVec 48) :=
  ⟨fun _ => smacVal⟩
private def etIn   : Signal defaultDomain (BitVec 16) :=
  ⟨fun _ => etVal⟩

private def payloadByteStream : Signal defaultDomain (BitVec 8) :=
  ⟨fun t =>
    if 14 ≤ t ∧ t < 14 + nPay then
      (payloadBytes[t - 14]?).getD 0#8
    else 0#8⟩
private def payloadValidStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (14 ≤ t ∧ t < 14 + nPay)⟩
private def payloadLastStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 14 + nPay - 1)⟩
private def startStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def txOut : TxOut defaultDomain :=
  txFramer dmacIn smacIn etIn payloadByteStream
           payloadValidStream payloadLastStream startStream

/-- Expected reference: each cycle's (byte, valid, sop, eop). -/
private def expected : List (BitVec 8 × Bool × Bool × Bool) :=
  [ (0xAA#8, true,  true,  false)   -- c0  DMAC[0], SOP
  , (0xBB#8, true,  false, false)   -- c1  DMAC[1]
  , (0xCC#8, true,  false, false)   -- c2  DMAC[2]
  , (0xDD#8, true,  false, false)   -- c3  DMAC[3]
  , (0xEE#8, true,  false, false)   -- c4  DMAC[4]
  , (0xFF#8, true,  false, false)   -- c5  DMAC[5]
  , (0x11#8, true,  false, false)   -- c6  SMAC[0]
  , (0x22#8, true,  false, false)   -- c7  SMAC[1]
  , (0x33#8, true,  false, false)   -- c8  SMAC[2]
  , (0x44#8, true,  false, false)   -- c9  SMAC[3]
  , (0x55#8, true,  false, false)   -- c10 SMAC[4]
  , (0x66#8, true,  false, false)   -- c11 SMAC[5]
  , (0x08#8, true,  false, false)   -- c12 EthType[0]
  , (0x00#8, true,  false, false)   -- c13 EthType[1]
  , (0xDE#8, true,  false, false)   -- c14 Payload[0]
  , (0xAD#8, true,  false, false)   -- c15 Payload[1]
  , (0xBE#8, true,  false, false)   -- c16 Payload[2]
  , (0xEF#8, true,  false, true)    -- c17 Payload[3], EOP
  , (0x00#8, false, false, false) ] -- c18 idle

def main : IO Unit := do
  IO.println "=== Ethernet TX framer sim ==="
  let mut ok := true
  for h : t in [:19] do
    let b   := txOut.txByte.val t
    let v   := txOut.txValid.val t
    let sop := txOut.txSop.val t
    let eop := txOut.txEop.val t
    let exp := expected[t]?.getD (0#8, false, false, false)
    let (eb, ev, esop, eeop) := exp
    -- Byte comparison only matters when the framer asserts valid;
    -- on idle cycles the byte path can hold whatever the last
    -- mux selected (don't-care).
    let bytePass := !v || b = eb
    let pass := bytePass ∧ v = ev ∧ sop = esop ∧ eop = eeop
    let mark := if pass then "✓" else "✗"
    let bHex := String.ofList (Nat.toDigits 16 b.toNat)
    let ebHex := String.ofList (Nat.toDigits 16 eb.toNat)
    IO.println s!"  cycle {t} {mark} got=(byte=0x{bHex}, valid={v}, sop={sop}, eop={eop})  exp=(byte=0x{ebHex}, valid={ev}, sop={esop}, eop={eeop})"
    if !pass then ok := false
  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.EthernetTxTest

section SynthesisChecks
-- Build-time check that `#synthesizeVerilog` accepts the TX
-- framer's 4-output record return.  Pairs with the RX
-- SynthesisChecks block in EthernetTest.lean.

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.Ethernet

private def synth_txByteOnly
    (dmacIn : Signal defaultDomain (BitVec 48))
    (smacIn : Signal defaultDomain (BitVec 48))
    (etIn   : Signal defaultDomain (BitVec 16))
    (payloadByte : Signal defaultDomain (BitVec 8))
    (payloadValid : Signal defaultDomain Bool)
    (payloadLast  : Signal defaultDomain Bool)
    (start        : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (txFramer dmacIn smacIn etIn payloadByte payloadValid payloadLast start).txByte

#synthesizeVerilog synth_txByteOnly

private def synth_txFramerAll
    (dmacIn : Signal defaultDomain (BitVec 48))
    (smacIn : Signal defaultDomain (BitVec 48))
    (etIn   : Signal defaultDomain (BitVec 16))
    (payloadByte : Signal defaultDomain (BitVec 8))
    (payloadValid : Signal defaultDomain Bool)
    (payloadLast  : Signal defaultDomain Bool)
    (start        : Signal defaultDomain Bool) :
    TxOut defaultDomain :=
  txFramer dmacIn smacIn etIn payloadByte payloadValid payloadLast start

#synthesizeVerilog synth_txFramerAll

end SynthesisChecks
