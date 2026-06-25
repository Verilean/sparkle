/-
  Cycle-by-cycle sim test for IP.Net.ARP {Responder, Requester}.

  Scenario:
    * Client (`arpRequester`) at 10.0.0.10 / 01:02:03:04:05:06
      triggers an ARP query for 10.0.0.20.  Outputs 28 bytes of
      request packet.  After enough cycles, fed an ARP reply
      with SHA=AA:BB:CC:DD:EE:FF and SPA=10.0.0.20.  Cache
      should latch to AA:BB:CC:DD:EE:FF and cacheValid go high.

    * Server (`arpResponder`) at 10.0.0.20 /
      AA:BB:CC:DD:EE:FF.  Fed the request bytes the client
      emitted; should produce a 28-byte reply with the roles
      swapped: SHA=AA…FF, SPA=10.0.0.20, THA=01:02:03:04:05:06,
      TPA=10.0.0.10.

  Validation: build the expected request / reply byte traces
  by hand and diff against the simulated outputs cycle by
  cycle.  Both sides walk the same 28-byte ARP packet
  encoder, so any structural drift in `arpPacketByte` shows
  up in BOTH traces.
-/

import IP.Net.ARP
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.ARP

namespace Sparkle.Tests.IP.Net.ARPTest

/-! ### Hosts and addresses. -/
private def clientMac : BitVec 48 := 0x010203040506#48
private def clientIp  : BitVec 32 := 0x0A00000A#32      -- 10.0.0.10
private def serverMac : BitVec 48 := 0xAABBCCDDEEFF#48
private def serverIp  : BitVec 32 := 0x0A000014#32      -- 10.0.0.20

/-! ### Expected packet bytes (helpers). -/

private def macBytes (m : BitVec 48) : List (BitVec 8) :=
  List.range 6 |>.map (fun k =>
    BitVec.extractLsb' ((5 - k) * 8) 8 m)

private def ipBytes (ip : BitVec 32) : List (BitVec 8) :=
  List.range 4 |>.map (fun k =>
    BitVec.extractLsb' ((3 - k) * 8) 8 ip)

private def operBytes (op : BitVec 16) : List (BitVec 8) :=
  [ BitVec.extractLsb' 8 8 op
  , BitVec.extractLsb' 0 8 op ]

private def fixedHdr : List (BitVec 8) :=
  [ 0x00#8, 0x01#8,  -- HTYPE
    0x08#8, 0x00#8,  -- PTYPE
    0x06#8, 0x04#8 ] -- HLEN, PLEN

/-- Build the 28-byte ARP packet bytes for given OPER + SHA +
    SPA + THA + TPA.  MSB-first throughout. -/
def arpBytes (op : BitVec 16) (sha : BitVec 48) (spa : BitVec 32)
    (tha : BitVec 48) (tpa : BitVec 32) : List (BitVec 8) :=
  fixedHdr ++ operBytes op ++ macBytes sha ++ ipBytes spa
           ++ macBytes tha ++ ipBytes tpa

/-! ### Stimulus: client triggers a request to serverIp at
    cycle 0.  The request burst is 28 cycles (cycles 0..27);
    at cycle 100 we feed a synthetic reply byte stream
    (cycles 100..127). -/

private def requestBytes : List (BitVec 8) :=
  arpBytes 1#16 clientMac clientIp 0#48 serverIp

private def replyBytes : List (BitVec 8) :=
  arpBytes 2#16 serverMac serverIp clientMac clientIp

private def replyOffset : Nat := 100

/-- Trigger fires once at cycle 0; the client's burst counter
    handles the rest. -/
private def triggerSig : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def tpaSig : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => serverIp⟩

private def ownMacClient : Signal defaultDomain (BitVec 48) :=
  ⟨fun _ => clientMac⟩
private def ownIpClient  : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => clientIp⟩
private def ownMacServer : Signal defaultDomain (BitVec 48) :=
  ⟨fun _ => serverMac⟩
private def ownIpServer  : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => serverIp⟩

/-- Incoming-to-client stream: zeros until cycle 100, then 28
    reply bytes. -/
private def rxClientByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t =>
    if replyOffset ≤ t ∧ t < replyOffset + 28
      then (replyBytes[t - replyOffset]?).getD 0#8
      else 0#8⟩
private def rxClientValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (replyOffset ≤ t ∧ t < replyOffset + 28)⟩
private def rxClientSop : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = replyOffset)⟩

private def clientOut : ArpRequesterOut defaultDomain :=
  arpRequester triggerSig tpaSig ownMacClient ownIpClient
               rxClientByte rxClientValid rxClientSop

/-- Server scenario: feed the request bytes the client just
    emitted, starting at cycle 0.  (We replay the byte list
    rather than wiring the client's TX into the server's RX —
    simpler and isolates the two modules' correctness.) -/
private def rxServerByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t =>
    if t < 28 then (requestBytes[t]?).getD 0#8 else 0#8⟩
private def rxServerValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 28)⟩
private def rxServerSop : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def serverOut : ArpResponderOut defaultDomain :=
  arpResponder rxServerByte rxServerValid rxServerSop
               ownMacServer ownIpServer

def main : IO Unit := do
  IO.println "=== ARP responder + requester sim ==="
  -- Server should emit txStart one cycle after the parser
  -- finishes (cycle 28); then 28 reply bytes (cycles 28..55,
  -- but with the standard one-cycle counter lag, actual
  -- emission may start at 29 or 30 depending on the parser's
  -- `done` register latency).  Walk a generous window and
  -- look for the byte sequence.
  let mut serverEmitted : List (BitVec 8) := []
  for h : t in [:80] do
    let v := serverOut.payloadValid.val t
    let b := serverOut.payloadByte.val t
    if v then serverEmitted := serverEmitted ++ [b]
  let serverOk := serverEmitted = replyBytes
  IO.println s!"  server emitted {serverEmitted.length} bytes (expected 28)"
  if serverOk then
    IO.println "    server reply bytes ✓ match expected reply"
  else
    IO.println s!"    server reply bytes ✗ mismatch"
    IO.println s!"      got: {serverEmitted.map BitVec.toNat}"
    IO.println s!"      exp: {replyBytes.map BitVec.toNat}"

  -- Client: should emit 28 request bytes in cycles 0..27,
  -- then after the reply byte stream (cycles 100..127), the
  -- cache should latch and cacheValid should go high.
  let mut clientEmitted : List (BitVec 8) := []
  for h : t in [:80] do
    let v := clientOut.payloadValid.val t
    let b := clientOut.payloadByte.val t
    if v then clientEmitted := clientEmitted ++ [b]
  let clientOk := clientEmitted = requestBytes
  IO.println s!"  client emitted {clientEmitted.length} bytes (expected 28)"
  if clientOk then
    IO.println "    client request bytes ✓ match expected request"
  else
    IO.println s!"    client request bytes ✗ mismatch"
    IO.println s!"      got: {clientEmitted.map BitVec.toNat}"
    IO.println s!"      exp: {requestBytes.map BitVec.toNat}"

  -- Cache check: a few cycles after the reply byte stream
  -- finishes (cycle 100+28+2=130), cache should be serverMac.
  let cacheAt140 := clientOut.cache.val 140
  let cValidAt140 := clientOut.cacheValid.val 140
  let cacheOk := cacheAt140 = serverMac ∧ cValidAt140 = true
  IO.println s!"  cache at cycle 140 = 0x{Nat.toDigits 16 cacheAt140.toNat |> String.ofList} (expected 0xaabbccddeeff)"
  IO.println s!"  cacheValid at cycle 140 = {cValidAt140} (expected true)"

  if serverOk ∧ clientOk ∧ cacheOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.ARPTest

section SynthesisChecks
-- Build-time synth checks: single-Signal projections from the
-- ARP responder / requester records.  Full record-return
-- synth is exercised at the top level of the demo wrap-up;
-- here we just gate against regressions in the per-Signal
-- output paths.

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.ARP

private def synth_arpResponderByte
    (rxByte  : Signal defaultDomain (BitVec 8))
    (rxValid sopArp : Signal defaultDomain Bool)
    (ownMac : Signal defaultDomain (BitVec 48))
    (ownIp  : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 8) :=
  (arpResponder rxByte rxValid sopArp ownMac ownIp).payloadByte

#synthesizeVerilog synth_arpResponderByte

private def synth_arpRequesterByte
    (trigger : Signal defaultDomain Bool)
    (tpaIn   : Signal defaultDomain (BitVec 32))
    (ownMac  : Signal defaultDomain (BitVec 48))
    (ownIp   : Signal defaultDomain (BitVec 32))
    (rxByte  : Signal defaultDomain (BitVec 8))
    (rxValid sopArp : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (arpRequester trigger tpaIn ownMac ownIp rxByte rxValid sopArp).payloadByte

#synthesizeVerilog synth_arpRequesterByte

-- `synth_arpRequesterCache` (projecting `.cache` directly) hits
-- "Cannot synthesise arpPacketByte: not inlinable" because the
-- structure-projection unfold of arpRequester pulls in the
-- entire body (including the byteOut mux chain), and the
-- deeply-nested mux tree inside `arpPacketByte` runs into the
-- elaborator's inline depth limit at the projection-call site.
-- The `.payloadByte` projection (which DOES use byteOut)
-- synthesises fine, so the body itself is OK; this is a
-- splitReturnLeaves edge case to follow up on separately.
-- The end-to-end `arpRequester` flow is covered by the sim
-- test and by `synth_arpRequesterByte` above.

end SynthesisChecks
