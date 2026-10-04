/-
  Sim test for IP.Bus.CANopenHW.{cobIdDemuxHW, nmtStateFsmHW}.

  Behavioural:
    * cobIdDemuxHW: sample several COB-IDs (NMT, SYNC, TPDO1,
      Heartbeat, SDO Tx/Rx) and compare each cycle's (fc, nid)
      output against `IP.Bus.CANopen.decodeCobId`.
    * nmtStateFsmHW: feed a small NMT command sequence and
      check the state register.

  Synth via #synthesizeVerilog.
-/

import IP.Bus.CANopen
import IP.Bus.CANopenHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.CANopenHW
open Sparkle.IP.Bus.CANopen (decodeCobId cobIdOf fcNmt fcSync fcHeartbeat fcSdoTx fcSdoRx fcTpdo1)

namespace Sparkle.Tests.IP.Bus.CANopenHWTest

abbrev D := defaultDomain

def main : IO Unit := do
  IO.println "=== CANopen HW (COB-ID demux + NMT FSM) vs pure-data ==="

  let mut ok := true

  -- COB-ID demux: cycle t → cobId at index t.
  IO.println "-- COB-ID demux --"
  let cobIds : Array Nat := #[
    cobIdOf fcNmt 0,            -- NMT broadcast
    cobIdOf fcSync 0,           -- SYNC
    cobIdOf fcHeartbeat 5,      -- Heartbeat node 5
    cobIdOf fcSdoTx 7,          -- SDO Tx node 7
    cobIdOf fcSdoRx 7,          -- SDO Rx node 7
    cobIdOf fcTpdo1 3           -- TPDO1 node 3
  ]
  let cobIdSig : Signal D (BitVec 11) := ⟨fun t =>
    if h : t < cobIds.size then BitVec.ofNat 11 cobIds[t]! else 0#11⟩

  let demux := cobIdDemuxHW cobIdSig
  for t in [:cobIds.size] do
    let (expFc, expNid) := decodeCobId cobIds[t]!
    let hwFc := (demux.fc.val t).toNat
    let hwNid := (demux.nid.val t).toNat
    if hwFc ≠ expFc ∨ hwNid ≠ expNid then
      IO.println s!"  MISMATCH cobId=0x{Nat.toDigits 16 cobIds[t]! |> String.ofList}: expected fc={expFc} nid={expNid}, hw fc={hwFc} nid={hwNid}"
      ok := false
  if ok then
    IO.println s!"  ok all {cobIds.size} COB-IDs decoded correctly"

  -- Check one-hot flags.
  IO.println "-- COB-ID demux one-hot flags --"
  let nmtAt0 := demux.isNmt.val 0
  let syncAt1 := demux.isSync.val 1
  let hbAt2 := demux.isHeartbeat.val 2
  let sdoTxAt3 := demux.isSdoTx.val 3
  let sdoRxAt4 := demux.isSdoRx.val 4
  if !(nmtAt0 && syncAt1 && hbAt2 && sdoTxAt3 && sdoRxAt4) then
    IO.println s!"  UNEXPECTED flags: nmt={nmtAt0} sync={syncAt1} hb={hbAt2} sdoTx={sdoTxAt3} sdoRx={sdoRxAt4}"
    ok := false
  else
    IO.println "  ok all one-hot flags fire correctly"

  -- NMT FSM.  Sequence:
  --   cycle 0: reset (state = boot-up)
  --   cycle 1: valid + startRemote (0x01) → operational
  --   cycle 2: valid + stopRemote  (0x02) → stopped
  --   cycle 3: valid + resetNode   (0x81) → boot-up
  --   cycle 4: valid + preOp       (0x80) → pre-op
  IO.println "-- NMT FSM --"
  let rstSig : Signal D Bool := ⟨fun t => decide (t = 0)⟩
  let cmdSig : Signal D (BitVec 8) := ⟨fun t =>
    match t with
    | 0 => 0#8
    | 1 => 0x01#8
    | 2 => 0x02#8
    | 3 => 0x81#8
    | 4 => 0x80#8
    | _ => 0#8⟩
  let vSig : Signal D Bool := ⟨fun t => decide (t ≥ 1 ∧ t ≤ 4)⟩

  let fsm := nmtStateFsmHW rstSig cmdSig vSig

  -- state should be observed AFTER the transitioning edge, so
  -- state at cycle 2 = 1 (operational, from cycle 1's cmd).
  let states := (List.range 6).map (fun t => (t, (fsm.state.val t).toNat))
  for (t, s) in states do
    IO.println s!"  cycle {t}: state = {s}"

  -- Check state at cycle 2 = 1 (operational).
  let s2 := (fsm.state.val 2).toNat
  let s3 := (fsm.state.val 3).toNat
  let s4 := (fsm.state.val 4).toNat
  let s5 := (fsm.state.val 5).toNat
  if s2 ≠ 1 then IO.println s!"  FSM: expected state at cycle 2 = 1 (oper), got {s2}"; ok := false
  if s3 ≠ 2 then IO.println s!"  FSM: expected state at cycle 3 = 2 (stopped), got {s3}"; ok := false
  if s4 ≠ 3 then IO.println s!"  FSM: expected state at cycle 4 = 3 (boot-up), got {s4}"; ok := false
  if s5 ≠ 0 then IO.println s!"  FSM: expected state at cycle 5 = 0 (pre-op), got {s5}"; ok := false
  if ok then
    IO.println "  ok NMT FSM state transitions match"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Bus.CANopenHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Bus.CANopenHW

private def synth_canopenFc
    (cobId : Signal defaultDomain (BitVec 11)) :
    Signal defaultDomain (BitVec 4) :=
  (cobIdDemuxHW cobId).fc

#synthesizeVerilog synth_canopenFc

private def synth_canopenIsNmt
    (cobId : Signal defaultDomain (BitVec 11)) :
    Signal defaultDomain Bool :=
  (cobIdDemuxHW cobId).isNmt

#synthesizeVerilog synth_canopenIsNmt

private def synth_canopenNmtState
    (reset : Signal defaultDomain Bool)
    (cmdIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 2) :=
  (nmtStateFsmHW reset cmdIn valid).state

#synthesizeVerilog synth_canopenNmtState

end SynthesisChecks
