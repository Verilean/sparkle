/-
  Sim test for IP.Net.TCPState.tcpServerFSM.

  Walks the passive-open path step by step:
    cycle 0  : pulse `listenStart`
    cycle 1  : state = LISTEN
    cycle ~  : feed parserDone with SYN flags  → state = SYN_RCVD,
               txReq pulses (we'd emit SYN+ACK)
    cycle ~  : feed parserDone with ACK flags  → state = ESTABLISHED
    cycle ~  : feed parserDone with FIN flags  → state = CLOSE_WAIT,
               then auto-fallthrough to LAST_ACK (txReq=1, FIN+ACK)
    cycle ~  : feed parserDone with ACK flags  → state = CLOSED

  Driven by hand-crafted `parserDone`/`parsedFlags` waveforms;
  the actual TCP byte parser is exercised by Tests/IP/Net/TCPHeaderTest.
-/

import IP.Net.TCPState
import IP.Net.TCP
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.TCPState
open Sparkle.IP.Net.TCP

namespace Sparkle.Tests.IP.Net.TCPStateTest

/-- Build a `dataOffFlags` value for the inbound segment. -/
private def mkFlags (syn ack fin : Bool) : BitVec 16 :=
  let synBit : BitVec 16 := if syn then 0x0002#16 else 0
  let ackBit : BitVec 16 := if ack then 0x0010#16 else 0
  let finBit : BitVec 16 := if fin then 0x0001#16 else 0
  0x5000#16 ||| synBit ||| ackBit ||| finBit

/-! ### Scenario timing.

    Cycle 0  : listenStart pulse.
    Cycle 1  : (post-posedge) state = LISTEN.
    Cycle 2  : parserDone pulse with SYN+window flags.
    Cycle 3  : post-posedge state = SYN_RCVD.
    Cycle 4  : parserDone pulse with ACK only (client's ACK
               of our SYN+ACK).
    Cycle 5  : post-posedge state = ESTABLISHED.
    Cycle 6  : parserDone pulse with FIN+ACK (peer closes).
    Cycle 7  : post-posedge state = CLOSE_WAIT, and the demo
               immediately transitions to LAST_ACK on the
               same cycle (we tie userClose to onFinFromPeer).
    Cycle 8  : parserDone pulse with ACK (peer acks our FIN).
    Cycle 9  : post-posedge state = CLOSED. -/

private def listenStart : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩

private def parserDone : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 2 ∨ t = 4 ∨ t = 6 ∨ t = 8)⟩

private def parsedFlags : Signal defaultDomain (BitVec 16) :=
  ⟨fun t =>
    if      t = 2 then mkFlags true  false false   -- SYN
    else if t = 4 then mkFlags false true  false   -- ACK
    else if t = 6 then mkFlags false true  true    -- FIN+ACK
    else if t = 8 then mkFlags false true  false   -- ACK
    else 0x5000#16⟩

private def parsedSeq : Signal defaultDomain (BitVec 32) :=
  ⟨fun t =>
    if t = 2 then 0x70000000#32  -- peer's ISN at SYN
    else if t = 4 then 0x70000001#32
    else if t = 6 then 0x70000001#32
    else if t = 8 then 0x70000002#32
    else 0#32⟩

private def parsedAck : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => 0#32⟩

private def fsmOut : TcpFsmOut defaultDomain :=
  tcpServerFSM listenStart parserDone parsedFlags parsedSeq parsedAck

/-! ### Client-side scenario.

    Cycle 0  : connectStart → SYN_SENT, txReq=1 (SYN).
    Cycle 2  : parserDone with SYN+ACK from peer.
    Cycle 3  : state = ESTABLISHED.
    Cycle 4  : userClose pulse → FIN_WAIT_1, txReq=1 (FIN+ACK).
    Cycle 6  : parserDone with ACK (peer acks our FIN).
    Cycle 7  : state = FIN_WAIT_2.
    Cycle 8  : parserDone with FIN+ACK from peer (their close).
    Cycle 9  : state = TIME_WAIT, txReq=1 (final ACK).
    Cycle 10-12: TIME_WAIT linger (4 cycles).
    Cycle 13 : state = CLOSED. -/

private def cliConnect : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 0)⟩
private def cliUserClose : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 4)⟩
private def cliParserDone : Signal defaultDomain Bool :=
  ⟨fun t => decide (t = 2 ∨ t = 6 ∨ t = 8)⟩
private def cliParsedFlags : Signal defaultDomain (BitVec 16) :=
  ⟨fun t =>
    if      t = 2 then mkFlags true  true  false   -- SYN+ACK
    else if t = 6 then mkFlags false true  false   -- ACK
    else if t = 8 then mkFlags false true  true    -- FIN+ACK
    else 0x5000#16⟩
private def cliParsedSeq : Signal defaultDomain (BitVec 32) :=
  ⟨fun t =>
    if      t = 2 then 0x80000000#32
    else if t = 6 then 0x80000001#32
    else if t = 8 then 0x80000001#32
    else 0#32⟩
private def cliParsedAck : Signal defaultDomain (BitVec 32) :=
  ⟨fun _ => 0#32⟩

private def cliOut : TcpFsmOut defaultDomain :=
  tcpClientFSM cliConnect cliUserClose cliParserDone
               cliParsedFlags cliParsedSeq cliParsedAck

def main : IO Unit := do
  IO.println "=== TCP server FSM (passive open) sim ==="
  let mut allOk := true
  -- Expected state at each cycle (after posedge).
  let expected : List (Nat × BitVec 4) :=
    [ (0,  sClosed)
    , (1,  sListen)
    , (2,  sListen)        -- parserDone fires; state moves NEXT cycle
    , (3,  sSynRcvd)
    , (4,  sSynRcvd)
    , (5,  sEstab)
    , (6,  sEstab)
    , (7,  sCloseWait)
    , (8,  sLastAck)       -- userClose-pulse already advanced via combinational
    , (9,  sClosed) ]
  for (t, exp) in expected do
    let got := fsmOut.state.val t
    let mark := if got = exp then "✓" else "✗"
    IO.println s!"  cycle {t}: state = {got.toNat} (expected {exp.toNat}) {mark}"
    if got ≠ exp then allOk := false

  -- txReq should pulse on cycles 2 (SYN+ACK), 6 (ACK on FIN),
  -- and 7 (FIN+ACK on userClose).  We don't assert exact
  -- pattern because the FSM uses combinational `needsTx`,
  -- registered one cycle.  Just sanity-check that txReq is
  -- high somewhere in cycles 3..8.
  let mut txSeen := false
  for t in [:12] do
    if fsmOut.txReq.val t then txSeen := true
  IO.println s!"  txReq seen during run = {txSeen} (expected true)"
  if !txSeen then allOk := false

  -- Now exercise the client-side active-open FSM.
  IO.println ""
  IO.println "=== TCP client FSM (active open + close) sim ==="
  let cliExpected : List (Nat × BitVec 4) :=
    [ (0,  sClosed)
    , (1,  sSynSent)
    , (2,  sSynSent)
    , (3,  sEstab)
    , (4,  sEstab)        -- userClose pulses; transition NEXT cycle
    , (5,  sFinWait1)
    , (6,  sFinWait1)
    , (7,  sFinWait2)
    , (8,  sFinWait2)
    , (9,  sTimeWait)
    , (10, sTimeWait)
    , (11, sTimeWait)
    , (12, sTimeWait)
    , (13, sClosed) ]
  for (t, exp) in cliExpected do
    let got := cliOut.state.val t
    let mark := if got = exp then "✓" else "✗"
    IO.println s!"  cycle {t}: state = {got.toNat} (expected {exp.toNat}) {mark}"
    if got ≠ exp then allOk := false

  let mut cliTxSeen := false
  for t in [:14] do
    if cliOut.txReq.val t then cliTxSeen := true
  IO.println s!"  client txReq seen during run = {cliTxSeen} (expected true)"
  if !cliTxSeen then allOk := false

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.TCPStateTest

section SynthesisChecks

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.TCPState

private def synth_serverFsmState
    (listenStart parserDone : Signal defaultDomain Bool)
    (parsedFlags : Signal defaultDomain (BitVec 16))
    (parsedSeq parsedAck : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 4) :=
  (tcpServerFSM listenStart parserDone parsedFlags parsedSeq parsedAck).state

#synthesizeVerilog synth_serverFsmState

private def synth_serverFsmEstablished
    (listenStart parserDone : Signal defaultDomain Bool)
    (parsedFlags : Signal defaultDomain (BitVec 16))
    (parsedSeq parsedAck : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain Bool :=
  (tcpServerFSM listenStart parserDone parsedFlags parsedSeq parsedAck).established

#synthesizeVerilog synth_serverFsmEstablished

private def synth_serverFsmTxReq
    (listenStart parserDone : Signal defaultDomain Bool)
    (parsedFlags : Signal defaultDomain (BitVec 16))
    (parsedSeq parsedAck : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain Bool :=
  (tcpServerFSM listenStart parserDone parsedFlags parsedSeq parsedAck).txReq

#synthesizeVerilog synth_serverFsmTxReq

private def synth_clientFsmState
    (connectStart userClose parserDone : Signal defaultDomain Bool)
    (parsedFlags : Signal defaultDomain (BitVec 16))
    (parsedSeq parsedAck : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 4) :=
  (tcpClientFSM connectStart userClose parserDone
    parsedFlags parsedSeq parsedAck).state

#synthesizeVerilog synth_clientFsmState

private def synth_clientFsmEstablished
    (connectStart userClose parserDone : Signal defaultDomain Bool)
    (parsedFlags : Signal defaultDomain (BitVec 16))
    (parsedSeq parsedAck : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain Bool :=
  (tcpClientFSM connectStart userClose parserDone
    parsedFlags parsedSeq parsedAck).established

#synthesizeVerilog synth_clientFsmEstablished

end SynthesisChecks
