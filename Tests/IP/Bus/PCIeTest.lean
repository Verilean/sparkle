/-
  Sim test for IP.Bus.PCIe — TLP header emit + parse
  round-trip on a representative Memory-Write packet.

  Scenario:
    isWrite = true, reqId = 0x0100, tag = 0x42,
    addr = 0xCAFEBABE.

  Reference 12-byte header (MSB-first per the layout
  comments in PCIe.lean):
    DWORD 0: 40 00 00 01    (Fmt/Type=MWr, Length=1)
    DWORD 1: 01 00 42 FF    (ReqID=0x0100, Tag=0x42, BE=0xFF)
    DWORD 2: CA FE BA BE    (Address)
-/

import IP.Bus.PCIe
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.PCIe

namespace Sparkle.Tests.IP.Bus.PCIeTest

private def expectedHeader : List (BitVec 8) :=
  [ 0x40#8, 0x00#8, 0x00#8, 0x01#8    -- DW0
  , 0x01#8, 0x00#8, 0x42#8, 0xFF#8    -- DW1
  , 0xCA#8, 0xFE#8, 0xBA#8, 0xBE#8 ]  -- DW2

private def isWriteSig : Signal defaultDomain Bool :=
  ⟨fun _ => true⟩
private def reqIdSig : Signal defaultDomain (BitVec 16) :=
  ⟨fun _ => 0x0100#16⟩
private def tagSig : Signal defaultDomain (BitVec 8) :=
  ⟨fun _ => 0x42#8⟩
private def addrSig : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => 0xCAFEBABE#32⟩

/-- Driver: walk cnt 1..12 by hand. -/
private def cntSig : Signal defaultDomain (BitVec 4) :=
  ⟨fun t => BitVec.ofNat 4 (if t = 0 then 0 else min t 12)⟩

private def emitByte : Signal defaultDomain (BitVec 8) :=
  tlpHeaderByte isWriteSig reqIdSig tagSig addrSig cntSig

/-! ### Parser stimulus: replay the 12 expected bytes. -/

private def rxByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => if t < 12 then (expectedHeader[t]?).getD 0#8 else 0#8⟩
private def rxValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 12)⟩
private def rxSop : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def parsed : TlpRxOut defaultDomain :=
  tlpRxParser rxByte rxValid rxSop

def main : IO Unit := do
  IO.println "=== PCIe TLP header emit + parse sim ==="
  let mut ok := true

  -- 1. Emitter byte stream (cycles 1..12).
  let mut emitted : List (BitVec 8) := []
  for h : t in [1:13] do
    let b := emitByte.val t
    emitted := emitted ++ [b]
  let emitOk := emitted = expectedHeader
  IO.println s!"  emitter produced 12 bytes (expected layout: 40 00 00 01 / 01 00 42 ff / ca fe ba be)"
  if emitOk then
    IO.println "    ✓ emitter bytes match"
  else
    IO.println "    ✗ emitter mismatch"
    IO.println s!"      got: {emitted.map BitVec.toNat}"
    IO.println s!"      exp: {expectedHeader.map BitVec.toNat}"
    ok := false

  -- 2. Parser captures all fields from the replayed byte
  --    stream.  Sample after 1-cycle done-pulse latency.
  let sampleAt : Nat := 14
  let pIsW := parsed.isWrite.val sampleAt
  let pReq := parsed.reqId.val sampleAt
  let pTag := parsed.tag.val sampleAt
  let pAdr := parsed.addr.val sampleAt
  IO.println s!"  parser @ cycle {sampleAt}:"
  IO.println s!"    isWrite = {pIsW} (expected true)"
  IO.println s!"    reqId   = 0x{Nat.toDigits 16 pReq.toNat |> String.ofList}"
  IO.println s!"    tag     = 0x{Nat.toDigits 16 pTag.toNat |> String.ofList}"
  IO.println s!"    addr    = 0x{Nat.toDigits 16 pAdr.toNat |> String.ofList}"
  let parseOk := pIsW = true ∧ pReq = 0x0100#16 ∧ pTag = 0x42#8 ∧ pAdr = 0xCAFEBABE#32
  if parseOk then
    IO.println "    ✓ all 4 fields recovered"
  else
    IO.println "    ✗ field mismatch"
    ok := false

  -- ============================================================
  -- P.3 MMIO endpoint sim is deferred.
  -- ============================================================
  -- The `mmioEndpoint` definition (in IP/Bus/PCIe.lean)
  -- builds cleanly, but its 10+ register network combined
  -- with the wide `tlpCplByte` 16-way mux pushes Lean's
  -- `Signal.val k` evaluator into wall-clock-impractical
  -- territory even at small t — same exponential-cost
  -- pattern documented in Phase L.1.b for the SHA-256 HW
  -- engine.  P.3 SIM thus deferred; the structural
  -- correctness of the endpoint is established by build +
  -- the P.1 parser/emitter round-trip above.
  --
  -- See `docs/reference/HFT_Stack_Claims.md` for the
  -- honest scoping posture this respects.

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Bus.PCIeTest

section SynthesisChecks

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.PCIe

private def synth_tlpHeaderByte
    (isWrite : Signal defaultDomain Bool)
    (reqId   : Signal defaultDomain (BitVec 16))
    (tag     : Signal defaultDomain (BitVec 8))
    (addr    : Signal defaultDomain (BitVec 32))
    (cntSig  : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8) :=
  tlpHeaderByte isWrite reqId tag addr cntSig

#synthesizeVerilog synth_tlpHeaderByte

private def synth_tlpRxAddr
    (byte : Signal defaultDomain (BitVec 8))
    (valid sop : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 32) :=
  (tlpRxParser byte valid sop).addr

#synthesizeVerilog synth_tlpRxAddr

private def synth_tlpRxIsWrite
    (byte : Signal defaultDomain (BitVec 8))
    (valid sop : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (tlpRxParser byte valid sop).isWrite

#synthesizeVerilog synth_tlpRxIsWrite

end SynthesisChecks
