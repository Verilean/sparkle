/-
  Sim parity for IP.Net.Ethernet.rxFramer.

  Feed one synthetic Ethernet frame byte-by-byte and check that:
    * DMAC, SMAC, EthType are latched correctly by the time
      `hdrDone` strobes.
    * Payload bytes pass through with `payloadValid = 1` while in
      the sticky PAYLOAD state.

  Frame layout (no preamble/SFD — they're stripped by the PHY-side
  MAC before reaching this parser):
    DMAC    : 6 bytes  AA BB CC DD EE FF
    SMAC    : 6 bytes  11 22 33 44 55 66
    EthType : 2 bytes  08 00     (= 0x0800, IPv4)
    Payload : 4 bytes  DE AD BE EF

  Total 18 bytes; the engine reads them across 19 cycles (cycle 0
  is the SOP edge with byte index 0; cycle 18 is the last payload
  byte).
-/

import IP.Net.Ethernet
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.Ethernet

namespace Sparkle.Tests.IP.Net.EthernetTest

private def frameBytes : List (BitVec 8) :=
  [ 0xAA#8, 0xBB#8, 0xCC#8, 0xDD#8, 0xEE#8, 0xFF#8   -- DMAC
  , 0x11#8, 0x22#8, 0x33#8, 0x44#8, 0x55#8, 0x66#8   -- SMAC
  , 0x08#8, 0x00#8                                   -- EthType
  , 0xDE#8, 0xAD#8, 0xBE#8, 0xEF#8 ]                 -- Payload

private def n : Nat := frameBytes.length  -- 18

/-- The driver feeds one byte per cycle starting at cycle 0; SOP
    is high only on cycle 0; valid is high for all 18 bytes. -/
private def byteStream : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => (frameBytes[t]?).getD 0#8⟩

private def validStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < n)⟩

private def sopStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def eopStream : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = n - 1)⟩

private def rxIn : RxIn defaultDomain :=
  { byte := byteStream
  , valid := validStream
  , sop := sopStream
  , eop := eopStream }

private def rxOut : RxOut defaultDomain := rxFramerOfRxIn rxIn

/-- Walk `Signal dom α` for `cycles` cycles and pull out the `t`-th
    sample.  Tiny inline helper so the test doesn't depend on
    `Signal.sample` internals. -/
private def at_ {α : Type} (s : Signal defaultDomain α) (t : Nat) : α :=
  s.val t

def main : IO Unit := do
  -- Expected: at cycle 13 the engine reads EthType byte 1 ("0x00").
  -- The register update fires on the next cycle, so hdrDone latches
  -- to true at cycle 14 and the DMAC/SMAC/EthType registers carry
  -- the final values.  Cycle 14 is also when the engine is in
  -- PAYLOAD state for the first time and the first payload byte
  -- 0xDE is on the wire.
  let dmacAt14   := at_ rxOut.dmac 14
  let smacAt14   := at_ rxOut.smac 14
  let etAt14     := at_ rxOut.ethType 14
  let hdrAt14    := at_ rxOut.hdrDone 14
  let payAt14    := at_ rxOut.payloadByte 14
  let payValAt14 := at_ rxOut.payloadValid 14

  IO.println s!"DMAC at cycle 14    = 0x{(Nat.toDigits 16 dmacAt14.toNat |>.asString)} (expected 0xaabbccddeeff)"
  IO.println s!"SMAC at cycle 14    = 0x{(Nat.toDigits 16 smacAt14.toNat |>.asString)} (expected 0x112233445566)"
  IO.println s!"EthType at cycle 14 = 0x{(Nat.toDigits 16 etAt14.toNat |>.asString)} (expected 0x0800)"
  IO.println s!"hdrDone at cycle 14 = {hdrAt14} (expected true)"
  IO.println s!"payloadByte at 14   = 0x{(Nat.toDigits 16 payAt14.toNat |>.asString)} (expected 0xde)"
  IO.println s!"payloadValid at 14  = {payValAt14} (expected true)"

  let allOk := dmacAt14 = 0xAABBCCDDEEFF#48
            ∧ smacAt14 = 0x112233445566#48
            ∧ etAt14   = 0x0800#16
            ∧ hdrAt14  = true
            ∧ payAt14  = 0xDE#8
            ∧ payValAt14 = true
  if decide allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.EthernetTest

section SynthesisChecks
-- Build-time check that `#synthesizeVerilog` accepts the
-- multi-output (record return) shape.  This is the synth
-- counterpart to the sim test above and gates against
-- regressions in the splitReturnLeaves / lambda-port-dedup
-- path that landed in commit 119817c + follow-ups.

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.Ethernet

-- Single-Signal projection: exercises the `(rxFramer …).dmac`
-- projection-routed path through handleDefinitionUnfold's
-- structure-field detection.
private def synth_dmacOnly
    (byte : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool)
    (sop : Signal defaultDomain Bool)
    (eop : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 48) :=
  (rxFramer byte valid sop eop).dmac

#synthesizeVerilog synth_dmacOnly

-- Full 6-output record return: exercises splitReturnLeaves
-- through all 6 fields and the lambda-handler input-port
-- dedup so the emitted module has 4 inputs / 6 outputs, not
-- 24 inputs / 6 outputs.
private def synth_rxFramerAll
    (byte : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool)
    (sop : Signal defaultDomain Bool)
    (eop : Signal defaultDomain Bool) :
    RxOut defaultDomain :=
  rxFramer byte valid sop eop

#synthesizeVerilog synth_rxFramerAll

end SynthesisChecks
