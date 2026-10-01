/-
  Transaction-level testbench layer (`Sparkle/Verification/Tlm.lean`) on
  JIT-simulated ready/valid designs.

    1. The library FIFO: transactions arrive in order under every mix of
       input gaps and output back-pressure.
    2. A register stage computing 3x + 1: results match the untimed model.
    3. A stage that DROPS data under back-pressure: the scoreboard reports it.
    4. A stage that CHANGES its payload while waiting for `ready`: the
       monitor reports the protocol violation.
    5. One test sequence, written against `Endpoint`, gives the same
       results on the RTL and on the untimed model.
    6. A hung handshake is a timeout error, not an endless loop.
    7. `Pace` is deterministic.
    8. With Verilator installed: the same bench on the Verilator backend
       sees every handshake in the same cycle as on the JIT.
  The designs synthesize (`#synthesizeVerilog`).
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.CircuitDo
import Sparkle.Library.Queue.SyncFIFO
import Sparkle.Verification.Tlm

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.Tlm

namespace Sparkle.Tests.TlmTest

/-! ### Designs under test -/

/-- The library FIFO (depth 4).  Output: `(enqReady, deqValid, deqData)`,
    32 bits each, `enqReady` in the top word. -/
def fifoTop (enqValid : Signal defaultDomain Bool) (enqData : Signal defaultDomain (BitVec 32))
    (deqReady : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 32 × BitVec 32 × BitVec 32) :=
  Sparkle.Library.Queue.SyncFIFO.syncFIFO enqValid enqData deqReady

/-- One-entry register stage computing `3·x + 1`.
    `inReady = ¬full ∨ outReady`: it accepts when empty or being emptied.
    Output: `inReady ++ outValid ++ outData` (34 bits). -/
def stage (inValid : Signal defaultDomain Bool) (inData : Signal defaultDomain (BitVec 32))
    (outReady : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 34) :=
  circuit do
    let full ← Signal.reg false
    let data ← Signal.reg 0#32
    let fullS := (full : Signal defaultDomain Bool)
    let dataS := (data : Signal defaultDomain (BitVec 32))
    let inReady := Signal.mux fullS outReady (Signal.pure true)
    let accept := inValid &&& inReady
    full <~ Signal.mux accept (Signal.pure true) (Signal.mux outReady (Signal.pure false) fullS)
    data <~ Signal.mux accept (inData * 3#32 + 1#32) dataS
    return (Signal.mux inReady (Signal.pure 1#1) (Signal.pure 0#1)) ++
           ((Signal.mux fullS (Signal.pure 1#1) (Signal.pure 0#1)) ++ dataS)

/-- BROKEN on purpose: always ready, so a new input overwrites a result
    that is still waiting — data is DROPPED under back-pressure. -/
def stageDrops (inValid : Signal defaultDomain Bool) (inData : Signal defaultDomain (BitVec 32))
    (outReady : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 34) :=
  circuit do
    let full ← Signal.reg false
    let data ← Signal.reg 0#32
    let fullS := (full : Signal defaultDomain Bool)
    let dataS := (data : Signal defaultDomain (BitVec 32))
    full <~ Signal.mux inValid (Signal.pure true) (Signal.mux outReady (Signal.pure false) fullS)
    data <~ Signal.mux inValid (inData * 3#32 + 1#32) dataS
    return (Signal.pure 1#1 : Signal defaultDomain (BitVec 1)) ++
           ((Signal.mux fullS (Signal.pure 1#1) (Signal.pure 0#1)) ++ dataS)

/-- BROKEN on purpose: a result that waits for `ready` keeps counting up —
    the payload CHANGES while `valid` is high. -/
def stageUnstable (inValid : Signal defaultDomain Bool) (inData : Signal defaultDomain (BitVec 32))
    (outReady : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 34) :=
  circuit do
    let full ← Signal.reg false
    let data ← Signal.reg 0#32
    let fullS := (full : Signal defaultDomain Bool)
    let dataS := (data : Signal defaultDomain (BitVec 32))
    let inReady := Signal.mux fullS outReady (Signal.pure true)
    let accept := inValid &&& inReady
    full <~ Signal.mux accept (Signal.pure true) (Signal.mux outReady (Signal.pure false) fullS)
    data <~ Signal.mux accept (inData * 3#32 + 1#32) (Signal.mux outReady dataS (dataS + 1#32))
    return (Signal.mux inReady (Signal.pure 1#1) (Signal.pure 0#1)) ++
           ((Signal.mux fullS (Signal.pure 1#1) (Signal.pure 0#1)) ++ dataS)

#sim fifoTop
#sim stage
#sim stageDrops
#sim stageUnstable

section SynthesisChecks
#synthesizeVerilog fifoTop
#synthesizeVerilog stage
end SynthesisChecks

/-! ### Port maps — the only DUT-specific testbench code -/

def fifoEnq : SourcePort fifoTop.Sim.SimInput fifoTop.Sim.SimOutput (BitVec 32) where
  name := "enq"
  drive i x := { i with _gen_enqValid := if x.isSome then 1 else 0, _gen_enqData := x.getD 0 }
  ready o := o.out.extractLsb' 64 32 != 0

def fifoDeq : SinkPort fifoTop.Sim.SimInput fifoTop.Sim.SimOutput (BitVec 32) where
  name := "deq"
  setReady i r := { i with _gen_deqReady := if r then 1 else 0 }
  valid o := if o.out.extractLsb' 32 32 != 0 then some (o.out.extractLsb' 0 32) else none

def stageIn : SourcePort stage.Sim.SimInput stage.Sim.SimOutput (BitVec 32) where
  name := "in"
  drive i x := { i with _gen_inValid := if x.isSome then 1 else 0, _gen_inData := x.getD 0 }
  ready o := o.out.getLsbD 33
def stageOut : SinkPort stage.Sim.SimInput stage.Sim.SimOutput (BitVec 32) where
  name := "out"
  setReady i r := { i with _gen_outReady := if r then 1 else 0 }
  valid o := if o.out.getLsbD 32 then some (o.out.extractLsb' 0 32) else none

def dropsIn : SourcePort stageDrops.Sim.SimInput stageDrops.Sim.SimOutput (BitVec 32) where
  name := "in"
  drive i x := { i with _gen_inValid := if x.isSome then 1 else 0, _gen_inData := x.getD 0 }
  ready o := o.out.getLsbD 33
def dropsOut : SinkPort stageDrops.Sim.SimInput stageDrops.Sim.SimOutput (BitVec 32) where
  name := "out"
  setReady i r := { i with _gen_outReady := if r then 1 else 0 }
  valid o := if o.out.getLsbD 32 then some (o.out.extractLsb' 0 32) else none

def unstableIn : SourcePort stageUnstable.Sim.SimInput stageUnstable.Sim.SimOutput (BitVec 32) where
  name := "in"
  drive i x := { i with _gen_inValid := if x.isSome then 1 else 0, _gen_inData := x.getD 0 }
  ready o := o.out.getLsbD 33
def unstableOut : SinkPort stageUnstable.Sim.SimInput stageUnstable.Sim.SimOutput (BitVec 32) where
  name := "out"
  setReady i r := { i with _gen_outReady := if r then 1 else 0 }
  valid o := if o.out.getLsbD 32 then some (o.out.extractLsb' 0 32) else none

/-! ### Untimed models -/

def items : List (BitVec 32) := (List.range 24).map fun k => BitVec.ofNat 32 (k * 1000003 + 7)

/-- The stage as a function on transactions. -/
def stageModel (xs : List (BitVec 32)) : List (BitVec 32) := xs.map (· * 3#32 + 1#32)

/-- One test sequence, in terms of blocking transport only. -/
def sequence (ep : Endpoint (BitVec 32) (BitVec 32)) : IO (List (Option (BitVec 32))) := do
  let _ ← ep.put 5#32
  let _ ← ep.put 6#32
  let a ← ep.get
  let _ ← ep.put 7#32
  let b ← ep.get
  let c ← ep.get
  return [a, b, c]

/-! ### Driver -/

def check (label : String) (ok : Bool) (detail : String := "") : IO Bool := do
  if ok then IO.println s!"  PASS {label}" else IO.println s!"  FAIL {label} {detail}"
  return ok

def paces : List (String × Pace × Pace) :=
  [ ("no gaps, no back-pressure", .always, .always)
  , ("input gaps", .random 1 40, .always)
  , ("back-pressure", .always, .every 3)
  , ("both, random", .random 2 60, .random 3 50)
  , ("slow consumer", .always, .pattern [false, false, false, true]) ]

def main : IO Unit := do
  IO.println "--- Transaction-level testbench ---"
  let mut ok := true

  -- 1. FIFO keeps order under every pacing
  for (label, inP, outP) in paces do
    let sim ← fifoTop.Sim.load
    let (r, lat) ← runStream sim default fifoEnq fifoDeq items items inP outP
    Sparkle.Core.Sim.Sim.destroy sim
    ok := (← check s!"FIFO in order: {label} ({r.cycles} cycles, latency {lat.foldl min 1000}..{lat.foldl max 0})"
      r.ok s!"{r.errors}") && ok

  -- 2. the 3x+1 stage against its untimed model
  for (label, inP, outP) in paces do
    let sim ← stage.Sim.load
    let (r, _) ← runStream sim default stageIn stageOut items (stageModel items) inP outP
    Sparkle.Core.Sim.Sim.destroy sim
    ok := (← check s!"stage == model: {label}" r.ok s!"{r.errors}") && ok

  -- 3. a stage that drops data: fine without back-pressure, caught with it
  do
    let sim ← stageDrops.Sim.load
    let (r, _) ← runStream sim default dropsIn dropsOut items (stageModel items) .always .always
    Sparkle.Core.Sim.Sim.destroy sim
    ok := (← check "dropping stage passes when never stalled" r.ok s!"{r.errors}") && ok
    let sim ← stageDrops.Sim.load
    let (r, _) ← runStream sim default dropsIn dropsOut items (stageModel items) .always (.every 3)
      (maxCycles := 400)
    Sparkle.Core.Sim.Sim.destroy sim
    ok := (← check s!"dropping stage is caught under back-pressure ({r.errors.length} errors)"
      (!r.ok) "no error reported") && ok

  -- 4. payload changes while valid waits for ready
  do
    let sim ← stageUnstable.Sim.load
    let (r, _) ← runStream sim default unstableIn unstableOut items (stageModel items) .always (.every 3)
      (maxCycles := 400)
    Sparkle.Core.Sim.Sim.destroy sim
    let flagged := r.errors.any fun e => (e.splitOn "payload changed").length > 1
    ok := (← check "unstable payload is a protocol error" flagged s!"{r.errors.take 3}") && ok

  -- 5. one sequence on the RTL and on the model
  do
    let sim ← stage.Sim.load
    let b ← Bench.new sim (default : stage.Sim.SimInput)
    let d ← b.addDriver stageIn
    let m ← b.addMonitor stageOut
    let rtl ← sequence (Endpoint.ofRtl b d m)
    let rep ← b.report
    Sparkle.Core.Sim.Sim.destroy sim
    let model ← Endpoint.ofModel (fun (_ : Unit) (x : BitVec 32) => ((), [x * 3#32 + 1#32])) ()
    let ref ← sequence model
    ok := (← check "Endpoint: RTL == model for one sequence"
      (rtl == ref && rtl == [some 16#32, some 19#32, some 22#32] && rep.ok)
      s!"rtl {repr rtl} model {repr ref} {rep.errors}") && ok

  -- 6. a consumer that is never ready: the FIFO fills, the 5th put times out
  do
    let sim ← fifoTop.Sim.load
    let b ← Bench.new sim (default : fifoTop.Sim.SimInput) (maxCycles := 60)
    let d ← b.addDriver fifoEnq
    let m ← b.addMonitor fifoDeq (.pattern [false])
    let ep := Endpoint.ofRtl b d m
    let mut accepted := 0
    for k in [0:5] do
      if ← ep.put (BitVec.ofNat 32 k) then accepted := accepted + 1
    let rep ← b.report
    Sparkle.Core.Sim.Sim.destroy sim
    let timedOut := rep.errors.any fun e => (e.splitOn "timeout").length > 1
    ok := (← check s!"full FIFO: 4 puts accepted, the 5th times out at cycle {rep.cycles}"
      (accepted == 4 && timedOut && rep.cycles == 60) s!"accepted {accepted} {rep.errors}") && ok

  -- 8. the same bench on Verilator: the handshakes happen in the same cycles
  if (← IO.Process.output { cmd := "which", args := #["verilator"] }).exitCode == 0 then
    let fifoRun (sim : fifoTop.Sim.Simulator) := do
      let b ← Bench.new sim (default : fifoTop.Sim.SimInput)
      let d ← b.addDriver fifoEnq (.random 2 60)
      let m ← b.addMonitor fifoDeq (.random 3 50)
      d.sendAll items
      let _ ← b.runUntil (m.count items.length) "all transactions"
      return (← d.log, ← m.log, (← b.report).errors)
    let stageRun (sim : stage.Sim.Simulator) := do
      let b ← Bench.new sim (default : stage.Sim.SimInput)
      let d ← b.addDriver stageIn (.random 5 70)
      let m ← b.addMonitor stageOut (.every 2)
      d.sendAll items
      let _ ← b.runUntil (m.count items.length) "all transactions"
      return (← d.log, ← m.log, (← b.report).errors)
    let j ← fifoTop.Sim.load
    let fj ← fifoRun j
    Sparkle.Core.Sim.Sim.destroy j
    let v ← fifoTop.Sim.loadVerilator
    let fv ← fifoRun { handle := v.handle }
    Sparkle.Core.Sim.Sim.destroy v
    ok := (← check s!"FIFO: Verilator == JIT, handshake for handshake ({fj.2.1.length} transactions)"
      (fj == fv && fj.2.2.isEmpty && fj.2.1.map (·.2) == items)
      s!"jit {fj.2.1.take 4} verilator {fv.2.1.take 4} {fv.2.2.take 2}") && ok
    let j ← stage.Sim.load
    let sj ← stageRun j
    Sparkle.Core.Sim.Sim.destroy j
    let v ← stage.Sim.loadVerilator
    let sv ← stageRun { handle := v.handle }
    Sparkle.Core.Sim.Sim.destroy v
    ok := (← check "stage: Verilator == JIT, handshake for handshake"
      (sj == sv && sj.2.2.isEmpty && sj.2.1.map (·.2) == stageModel items)
      s!"jit {sj.2.1.take 4} verilator {sv.2.1.take 4} {sv.2.2.take 2}") && ok
  else
    IO.println "  SKIP Verilator comparison (verilator not found)"

  -- 7. pacing is deterministic
  let every3 := (List.range 9).map (Pace.every 3).active
  ok := (← check "Pace.every 3" (every3 == [true, false, false, true, false, false, true, false, false])) && ok
  let rnd := (List.range 1000).filter (Pace.random 7 30).active
  ok := (← check s!"Pace.random 30% is about 30% ({rnd.length}/1000) and repeatable"
    (rnd.length > 230 && rnd.length < 370 &&
     rnd == (List.range 1000).filter (Pace.random 7 30).active)) && ok
  ok := (← check "mismatches reports the first difference and the length"
    (mismatches "x" [1, 2, 4] [1, 2, 3, 5] ==
      ["x: transaction 2 is some 4, expected some 3", "x: 3 transactions, expected 4"])) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.TlmTest
