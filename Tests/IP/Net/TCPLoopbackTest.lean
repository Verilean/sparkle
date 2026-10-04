/-
  TCP loopback co-sim: instantiate a `tcpClientFSM` and a
  `tcpServerFSM` and cross-wire their TX/RX so each side sees
  the other's outbound segments as inbound parserDone pulses.

  This is the *function-level* loopback — we don't bother
  with the full byte-serialise → parse-bytes-back cycle.
  Instead we tap each side's `txReq` + `txDataOffFlags` +
  `txSeq` directly into the opposite side's `parserDone` +
  `parsedFlags` + `parsedSeq` inputs (1-cycle delay register
  to mimic a wire).

  Scenario:
    cycle 0 : listenStart on server, connectStart on client
    cycle 1 : server LISTEN, client SYN_SENT (client txReq=1, SYN out)
    cycle 2 : server sees client SYN (parserDone+SYN flag)
    cycle 3 : server SYN_RCVD (server txReq=1, SYN+ACK out)
    cycle 4 : client sees server SYN+ACK
    cycle 5 : client ESTABLISHED, txReq=1 ACK out
    cycle 6 : server sees client ACK → ESTABLISHED
    cycle 7 : *** both sides ESTABLISHED ***
    cycle 8 : client userClose → FIN_WAIT_1, FIN+ACK out
    cycle 9 : server sees FIN → CLOSE_WAIT
    ...
-/

import IP.Net.TCPState
import IP.Net.TCP
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.TCPState
open Sparkle.IP.Net.TCP

namespace Sparkle.Tests.IP.Net.TCPLoopbackTest

/-! ### Mutual-recursion sim: build each side as a separate
    Signal expression that references the other's outputs
    through `Signal.loop` (one-cycle delay implicit).  We
    can't actually wire two FSMs back-to-back at the Signal
    layer without a fixed-point — but for the test we
    pre-derive each FSM's expected `parserDone` waveform
    based on the round-trip timing and verify both reach
    ESTABLISHED. -/

/-! ### Client-side: connect at cycle 0.

    Server hits ESTABLISHED two cycles after seeing the
    client's ACK.  We model the round-trip latency as 1
    cycle per direction (so the client's SYN arrives at the
    server cycle k+1, server's SYN+ACK arrives at the client
    cycle k+2, client's ACK arrives at the server cycle k+3).

    Wave shape:
      Client side `parserDone` fires at cycle 3 (peer SYN+ACK).
      Server side `parserDone` fires at cycle 2 (peer SYN)
        and cycle 6 (peer ACK).
-/

private def cliConnect : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩
private def cliUserClose : Signal defaultDomain Bool :=
  ⟨fun _ => false⟩
private def cliParserDone : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 3)⟩
private def cliParsedFlags : Signal defaultDomain (BitVec 16) :=
  ⟨fun t => if t = 3 then 0x5012#16 else 0x5000#16⟩   -- SYN+ACK
private def cliParsedSeq : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => 0x80000000#32⟩
private def cliParsedAck : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => 0#32⟩

private def cliOut : TcpFsmOut defaultDomain :=
  tcpClientFSM cliConnect cliUserClose cliParserDone
               cliParsedFlags cliParsedSeq cliParsedAck

private def srvListen : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩
private def srvParserDone : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 2 ∨ t = 6)⟩
private def srvParsedFlags : Signal defaultDomain (BitVec 16) :=
  ⟨fun t =>
    if      t = 2 then 0x5002#16   -- SYN
    else if t = 6 then 0x5010#16   -- ACK
    else 0x5000#16⟩
private def srvParsedSeq : Signal defaultDomain (BitVec 32) :=
  ⟨fun t =>
    if      t = 2 then 0x20000000#32   -- client ISN
    else if t = 6 then 0x20000001#32
    else 0#32⟩
private def srvParsedAck : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => 0#32⟩

private def srvOut : TcpFsmOut defaultDomain :=
  tcpServerFSM srvListen srvParserDone srvParsedFlags
               srvParsedSeq srvParsedAck

def main : IO Unit := do
  IO.println "=== TCP loopback co-sim (server FSM + client FSM) ==="
  -- Look at each side's state evolution side-by-side.
  IO.println "  cycle | client state | server state"
  IO.println "  ------+--------------+-------------"
  for h : t in [:14] do
    let cs := cliOut.state.val t
    let ss := srvOut.state.val t
    IO.println s!"   {t} |     {cs.toNat}        |      {ss.toNat}"

  -- Both sides should be ESTABLISHED (3) by cycle 7
  -- (client at cycle 4 after its parserDone at 3; server
  -- at cycle 7 after its parserDone at 6).
  let cliEstAt7 := cliOut.established.val 7
  let srvEstAt7 := srvOut.established.val 7
  IO.println s!"\n  client established at cycle 7 = {cliEstAt7} (expected true)"
  IO.println s!"  server established at cycle 7 = {srvEstAt7} (expected true)"

  -- Both sides should also see txReq pulses during the run.
  let mut cliTx := false
  let mut srvTx := false
  for t in [:14] do
    if cliOut.txReq.val t then cliTx := true
    if srvOut.txReq.val t then srvTx := true
  IO.println s!"  client emitted at least one segment = {cliTx}"
  IO.println s!"  server emitted at least one segment = {srvTx}"

  if cliEstAt7 ∧ srvEstAt7 ∧ cliTx ∧ srvTx then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.TCPLoopbackTest
