/-
  Sim test for IP.Net.HTTP.{Emitter, Parser}.

  Scenarios:
    1. httpGetEmitter:  trigger at cycle 0; capture 18 bytes
       and assert they spell "GET / HTTP/1.0\r\n\r\n".
    2. httpRespEmitter: trigger at cycle 0; capture 34 bytes
       and assert "HTTP/1.0 200 OK\r\n\r\nHello, Sparkle!".
    3. httpRequestParser: feed the 18-byte GET request →
       gotRequest should pulse exactly once around cycle 4-5.
    4. httpStatusParser:  feed the 34-byte response → status
       output should latch to 200, done should pulse.
-/

import IP.Net.HTTP
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.HTTP

namespace Sparkle.Tests.IP.Net.HTTPTest

private def expectedRequest : List (BitVec 8) :=
  -- "GET / HTTP/1.0\r\n\r\n"
  [ 0x47#8, 0x45#8, 0x54#8, 0x20#8
  , 0x2F#8, 0x20#8
  , 0x48#8, 0x54#8, 0x54#8, 0x50#8, 0x2F#8
  , 0x31#8, 0x2E#8, 0x30#8
  , 0x0D#8, 0x0A#8, 0x0D#8, 0x0A#8 ]

private def expectedResponse : List (BitVec 8) :=
  -- "HTTP/1.0 200 OK\r\n\r\nHello, Sparkle!"
  [ 0x48#8, 0x54#8, 0x54#8, 0x50#8, 0x2F#8, 0x31#8, 0x2E#8, 0x30#8
  , 0x20#8, 0x32#8, 0x30#8, 0x30#8, 0x20#8, 0x4F#8, 0x4B#8
  , 0x0D#8, 0x0A#8, 0x0D#8, 0x0A#8
  , 0x48#8, 0x65#8, 0x6C#8, 0x6C#8, 0x6F#8
  , 0x2C#8, 0x20#8
  , 0x53#8, 0x70#8, 0x61#8, 0x72#8, 0x6B#8, 0x6C#8, 0x65#8
  , 0x21#8 ]

private def triggerOnce : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def reqEmit : HttpEmitOut defaultDomain :=
  httpGetEmitter triggerOnce

private def respEmit : HttpEmitOut defaultDomain :=
  httpRespEmitter triggerOnce

/-! ### Parser stimulus: replay the request / response bytes. -/

private def reqRxByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t =>
    if t < 18 then (expectedRequest[t]?).getD 0#8 else 0#8⟩
private def reqRxValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 18)⟩

private def reqParse : HttpRequestParserOut defaultDomain :=
  httpRequestParser reqRxByte reqRxValid

private def respRxByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t =>
    if t < 34 then (expectedResponse[t]?).getD 0#8 else 0#8⟩
private def respRxValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 34)⟩
private def respRxSop : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def statParse : HttpStatusParserOut defaultDomain :=
  httpStatusParser respRxByte respRxValid respRxSop

def main : IO Unit := do
  IO.println "=== HTTP emitter / parser sim ==="

  -- Emitter 1: GET request (18 bytes).
  let mut reqBytes : List (BitVec 8) := []
  for h : t in [:25] do
    let v := reqEmit.valid.val t
    let b := reqEmit.byte.val t
    if v then reqBytes := reqBytes ++ [b]
  let reqOk := reqBytes = expectedRequest
  IO.println s!"  GET emitter emitted {reqBytes.length} bytes (expected 18)"
  if reqOk then
    IO.println "    GET bytes ✓ match \"GET / HTTP/1.0\\r\\n\\r\\n\""
  else
    IO.println "    GET ✗ mismatch"
    IO.println s!"      got: {reqBytes.map BitVec.toNat}"

  -- Emitter 2: response (34 bytes).
  let mut respBytes : List (BitVec 8) := []
  for h : t in [:45] do
    let v := respEmit.valid.val t
    let b := respEmit.byte.val t
    if v then respBytes := respBytes ++ [b]
  let respOk := respBytes = expectedResponse
  IO.println s!"  RESP emitter emitted {respBytes.length} bytes (expected 34)"
  if respOk then
    IO.println "    RESP bytes ✓ match \"HTTP/1.0 200 OK\\r\\n\\r\\nHello, Sparkle!\""
  else
    IO.println "    RESP ✗ mismatch"
    IO.println s!"      got: {respBytes.map BitVec.toNat}"

  -- Parser 1: request detection.
  let mut reqDetected := false
  for t in [:25] do
    if reqParse.gotRequest.val t then reqDetected := true
  IO.println s!"  request parser gotRequest seen = {reqDetected} (expected true)"

  -- Parser 2: status code.
  -- After 34 input bytes + done-latency, sample at cycle 36.
  let statusAt36 := statParse.status.val 36
  let doneAt12 := (List.range 20).any (fun t => statParse.done.val t)
  IO.println s!"  status at cycle 36 = {statusAt36.toNat} (expected 200)"
  IO.println s!"  parser saw done pulse = {doneAt12}"

  let statusOk := statusAt36 = 200#16

  if reqOk ∧ respOk ∧ reqDetected ∧ statusOk ∧ doneAt12 then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.HTTPTest

section SynthesisChecks

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.HTTP

private def synth_httpGetByte
    (trigger : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (httpGetEmitter trigger).byte

#synthesizeVerilog synth_httpGetByte

private def synth_httpRespByte
    (trigger : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (httpRespEmitter trigger).byte

#synthesizeVerilog synth_httpRespByte

private def synth_httpRequestParser
    (byte : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (httpRequestParser byte valid).gotRequest

#synthesizeVerilog synth_httpRequestParser

private def synth_httpStatus
    (byte : Signal defaultDomain (BitVec 8))
    (valid sop : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 16) :=
  (httpStatusParser byte valid sop).status

#synthesizeVerilog synth_httpStatus

end SynthesisChecks
