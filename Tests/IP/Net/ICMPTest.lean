/-
  Sim test for IP.Net.ICMP.{icmpEchoResponder, icmpEchoRequester}.

  Scenario:
    * Server side (`icmpEchoResponder`): fed an 8-byte ICMP
      echo *request* with type=0x08, ident=0x1234, seq=0x5678.
      Must emit an 8-byte ICMP echo *reply* with type=0x00,
      ident=0x1234, seq=0x5678, and a recomputed checksum.

    * Client side (`icmpEchoRequester`): pulses trigger with
      ident=0x1234, seq=0x5678 at cycle 0; emits 8 request
      bytes.  At cycle 50 we replay an ICMP reply byte stream
      with matching ident/seq.  `replyOk` should latch true.
-/

import IP.Net.ICMP
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.ICMP
open Sparkle.IP.Net.IPv4

namespace Sparkle.Tests.IP.Net.ICMPTest

private def reqIdent : BitVec 16 := 0x1234#16
private def reqSeq   : BitVec 16 := 0x5678#16

/-- Reference 8-byte echo-request bytes (with checksum computed
    from the pure-data API). -/
private def requestChksum : BitVec 16 :=
  icmpEchoChecksum icmpTypeReq reqIdent reqSeq
private def replyChksum   : BitVec 16 :=
  icmpEchoChecksum icmpTypeRep reqIdent reqSeq

private def requestBytes : List (BitVec 8) :=
  [ icmpTypeReq, icmpCode
  , BitVec.extractLsb' 8 8 requestChksum, BitVec.extractLsb' 0 8 requestChksum
  , BitVec.extractLsb' 8 8 reqIdent,      BitVec.extractLsb' 0 8 reqIdent
  , BitVec.extractLsb' 8 8 reqSeq,        BitVec.extractLsb' 0 8 reqSeq ]

private def replyBytes : List (BitVec 8) :=
  [ icmpTypeRep, icmpCode
  , BitVec.extractLsb' 8 8 replyChksum, BitVec.extractLsb' 0 8 replyChksum
  , BitVec.extractLsb' 8 8 reqIdent,    BitVec.extractLsb' 0 8 reqIdent
  , BitVec.extractLsb' 8 8 reqSeq,      BitVec.extractLsb' 0 8 reqSeq ]

/-! ### Server-side stimulus: feed request bytes at cycles 0..7. -/
private def srvByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => if t < 8 then (requestBytes[t]?).getD 0#8 else 0#8⟩
private def srvValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (t < 8)⟩
private def srvSop : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def srvOut : IcmpResponderOut defaultDomain :=
  icmpEchoResponder srvByte srvValid srvSop

/-! ### Client-side stimulus: trigger at cycle 0; reply stream
    starts at cycle 50. -/

private def replyOffset : Nat := 50

private def cliTrigger : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩
private def cliIdent : Signal defaultDomain (BitVec 16) :=
  ⟨fun _ => reqIdent⟩
private def cliSeq : Signal defaultDomain (BitVec 16) :=
  ⟨fun _ => reqSeq⟩

private def cliRxByte : Signal defaultDomain (BitVec 8) :=
  ⟨fun t =>
    if replyOffset ≤ t ∧ t < replyOffset + 8
      then (replyBytes[t - replyOffset]?).getD 0#8
      else 0#8⟩
private def cliRxValid : Signal defaultDomain Bool :=
  ⟨fun t => decide (replyOffset ≤ t ∧ t < replyOffset + 8)⟩
private def cliRxSop : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = replyOffset)⟩

private def cliOut : IcmpRequesterOut defaultDomain :=
  icmpEchoRequester cliTrigger cliIdent cliSeq
                    cliRxByte cliRxValid cliRxSop

def main : IO Unit := do
  IO.println "=== ICMP echo responder + requester sim ==="

  -- Server: collect emitted bytes from txValid window.
  let mut srvBytes : List (BitVec 8) := []
  for h : t in [:40] do
    let v := srvOut.txValid.val t
    let b := srvOut.txByte.val t
    if v then srvBytes := srvBytes ++ [b]
  let srvOk := srvBytes = replyBytes
  IO.println s!"  server emitted {srvBytes.length} bytes (expected 8)"
  if srvOk then
    IO.println "    server reply bytes ✓ match expected reply (incl. checksum)"
  else
    IO.println s!"    server reply ✗ mismatch"
    IO.println s!"      got: {srvBytes.map BitVec.toNat}"
    IO.println s!"      exp: {replyBytes.map BitVec.toNat}"

  -- Client: collect emitted request bytes.
  let mut cliBytes : List (BitVec 8) := []
  for h : t in [:40] do
    let v := cliOut.txValid.val t
    let b := cliOut.txByte.val t
    if v then cliBytes := cliBytes ++ [b]
  let cliOk := cliBytes = requestBytes
  IO.println s!"  client emitted {cliBytes.length} bytes (expected 8)"
  if cliOk then
    IO.println "    client request bytes ✓ match expected request"
  else
    IO.println s!"    client request ✗ mismatch"
    IO.println s!"      got: {cliBytes.map BitVec.toNat}"
    IO.println s!"      exp: {requestBytes.map BitVec.toNat}"

  -- After the reply byte stream finishes (cycle 50+8+2 = 60),
  -- replyOk should latch true.
  let replyOkAt70 := cliOut.replyOk.val 70
  let okOk := replyOkAt70 = true
  IO.println s!"  client replyOk at cycle 70 = {replyOkAt70} (expected true)"

  if srvOk ∧ cliOk ∧ okOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.ICMPTest

section SynthesisChecks
-- Build-time synth checks for ICMP responder + requester.
-- Both rely on `icmpEchoChecksumSig` which in turn calls
-- `IPv4.onesAdd16Sig`; with the latter now Signal-native
-- the whole tree synthesises cleanly.

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.ICMP

private def synth_icmpResponderByte
    (byte  : Signal defaultDomain (BitVec 8))
    (valid sopIcmp : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (icmpEchoResponder byte valid sopIcmp).txByte

#synthesizeVerilog synth_icmpResponderByte

private def synth_icmpRequesterByte
    (trigger : Signal defaultDomain Bool)
    (ident seq : Signal defaultDomain (BitVec 16))
    (byte  : Signal defaultDomain (BitVec 8))
    (valid sopIcmp : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  (icmpEchoRequester trigger ident seq byte valid sopIcmp).txByte

#synthesizeVerilog synth_icmpRequesterByte

private def synth_icmpRequesterReplyOk
    (trigger : Signal defaultDomain Bool)
    (ident seq : Signal defaultDomain (BitVec 16))
    (byte  : Signal defaultDomain (BitVec 8))
    (valid sopIcmp : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (icmpEchoRequester trigger ident seq byte valid sopIcmp).replyOk

#synthesizeVerilog synth_icmpRequesterReplyOk

end SynthesisChecks
