/-
  Transaction-level testbenches for ready/valid interfaces.

  A cycle-level test pokes `valid`, `data` and `ready` by hand and decodes
  the outputs bit by bit.  This layer lets a test speak in TRANSACTIONS:

    let bench ← Bench.new sim idleInput
    let drv ← bench.addDriver enqPort            -- testbench → DUT stream
    let mon ← bench.addMonitor deqPort           -- DUT → testbench stream
    drv.sendAll [1, 2, 3]
    let _ ← bench.runUntil (mon.count 3) "three results"
    bench.check "fifo" (← mon.items) [1, 2, 3]

  It sits on the `Sparkle.Core.Sim.Sim` interface, so the same bench drives
  the JIT simulator or Verilator.

  Pieces
  * `SourcePort` / `SinkPort` — how one ready/valid stream maps onto the
    simulator's input and output records (the only DUT-specific code).
  * `Driver` — offers queued transactions; once it has raised `valid` it
    keeps the same payload until the DUT accepts it.
  * `Monitor` — applies back-pressure, collects accepted transactions with
    their cycle numbers, and checks the protocol: after `valid`, the DUT
    must hold `valid` and the payload until the handshake.
  * `Pace` — when an agent is willing to act (always, every n-th cycle, a
    pattern, pseudo-random): the knob that exercises back-pressure and idle
    gaps.
  * `Endpoint` — blocking `put` / `get`.  The same test sequence runs
    against the RTL (`Endpoint.ofRtl`) or an untimed model
    (`Endpoint.ofModel`), which is what makes a model a drop-in reference.
  * `Bench.check` — in-order scoreboard.

  Timing (the `Sim` contract, as the JIT implements it): in cycle t the
  bench sets the inputs, the simulator evaluates and clocks, and `read`
  returns the outputs of that evaluation.  A handshake happens in cycle t
  when `valid` and `ready` are both high in it.  An agent decides its
  cycle-t inputs from what it saw up to cycle t-1 — it never reacts
  combinationally to the DUT.
-/
import Sparkle.Core.Sim

namespace Sparkle.Verification.Tlm

open Sparkle.Core.Sim

/-! ### Pacing -/

/-- When an agent is willing to act in a cycle. -/
inductive Pace where
  /-- every cycle -/
  | always
  /-- one cycle in `period` (cycles 0, period, 2·period, …) -/
  | every (period : Nat)
  /-- a repeating pattern, one entry per cycle -/
  | pattern (bits : List Bool)
  /-- about `percent` % of cycles, pseudo-random but reproducible -/
  | random (seed percent : Nat)
  deriving Repr

def Pace.active (p : Pace) (cycle : Nat) : Bool :=
  match p with
  | .always => true
  | .every period => period ≤ 1 || cycle % period == 0
  | .pattern bits => bits.isEmpty || bits.getD (cycle % bits.length) true
  | .random seed percent =>
    -- a fixed integer hash of (seed, cycle); no global state
    let x := (cycle + 1) * 2654435761 + seed * 40503
    let y := (x ^^^ (x >>> 15)) * 2246822519 % 4294967296
    ((y ^^^ (y >>> 13)) % 100) < percent

/-! ### Ports -/

/-- A stream the TESTBENCH produces: a ready/valid input of the DUT. -/
structure SourcePort (I O α : Type) where
  name : String
  /-- set `valid` and the payload fields (`none` = not valid) -/
  drive : I → Option α → I
  /-- the DUT's `ready` in this cycle's outputs -/
  ready : O → Bool

/-- A stream the DUT produces: a ready/valid output of the DUT. -/
structure SinkPort (I O β : Type) where
  name : String
  /-- set the testbench's `ready` -/
  setReady : I → Bool → I
  /-- the payload when the DUT's `valid` is high in this cycle's outputs -/
  valid : O → Option β

/-! ### Bench -/

/-- One participant of the bench. -/
structure Agent (I O : Type) where
  name : String
  /-- contribute to this cycle's inputs -/
  drive : Nat → I → IO I
  /-- see this cycle's outputs; returns protocol errors -/
  observe : Nat → O → IO (List String)
  /-- still has work queued (keeps `drain` running) -/
  busy : IO Bool

structure Bench (S I O : Type) where
  sim : S
  /-- inputs when no agent drives a field -/
  idle : I
  maxCycles : Nat
  agents : IO.Ref (Array (Agent I O))
  cycleRef : IO.Ref Nat
  errorsRef : IO.Ref (Array String)

namespace Bench

variable {S I O : Type} [Sim S I O]

/-- Reset the simulator and start an empty bench. -/
def new (sim : S) (idle : I) (maxCycles : Nat := 10000) : IO (Bench S I O) := do
  Sim.reset sim
  return { sim, idle, maxCycles
           agents := ← IO.mkRef #[], cycleRef := ← IO.mkRef 0, errorsRef := ← IO.mkRef #[] }

def cycle (b : Bench S I O) : IO Nat := b.cycleRef.get

def error (b : Bench S I O) (msg : String) : IO Unit :=
  b.errorsRef.modify (·.push msg)

def errors (b : Bench S I O) : IO (List String) := return (← b.errorsRef.get).toList

/-- One clock cycle: every agent drives, the simulator steps, every agent
    observes. -/
def tick (b : Bench S I O) : IO Unit := do
  let c ← b.cycleRef.get
  let agents ← b.agents.get
  let mut i := b.idle
  for a in agents do
    i ← a.drive c i
  Sim.step b.sim i
  let o ← Sim.read b.sim
  for a in agents do
    for e in ← a.observe c o do
      b.error s!"cycle {c}: {a.name}: {e}"
  b.cycleRef.set (c + 1)

/-- Clock until `cond` holds.  `false` (and an error) if `maxCycles` is
    reached first — a hung handshake ends the test instead of spinning. -/
def runUntil (b : Bench S I O) (cond : IO Bool) (what : String) : IO Bool := do
  let mut going := true
  let mut ok := true
  while going do
    if ← cond then going := false
    else if (← b.cycleRef.get) ≥ b.maxCycles then
      b.error s!"timeout after {b.maxCycles} cycles waiting for {what}"
      ok := false
      going := false
    else b.tick
  return ok

/-- Clock `n` cycles. -/
def run (b : Bench S I O) (n : Nat) : IO Unit := do
  for _ in [0:n] do b.tick

/-- Clock until no agent has work queued. -/
def drain (b : Bench S I O) : IO Bool :=
  b.runUntil (do
    let agents ← b.agents.get
    let mut busy := false
    for a in agents do
      if ← a.busy then busy := true
    return !busy) "the drivers to finish"

end Bench

/-! ### Driver -/

/-- Sends transactions on a `SourcePort`, in order. -/
structure Driver (α : Type) where
  queue : IO.Ref (Array α)
  /-- index of the next transaction to offer -/
  next : IO.Ref Nat
  /-- (cycle of the handshake, transaction) -/
  sent : IO.Ref (Array (Nat × α))

namespace Driver

def send {α : Type} (d : Driver α) (x : α) : IO Unit := d.queue.modify (·.push x)

def sendAll {α : Type} (d : Driver α) (xs : List α) : IO Unit :=
  d.queue.modify (· ++ xs.toArray)

/-- every queued transaction has been accepted -/
def idle {α : Type} (d : Driver α) : IO Bool :=
  return (← d.next.get) ≥ (← d.queue.get).size

def log {α : Type} (d : Driver α) : IO (List (Nat × α)) := return (← d.sent.get).toList

end Driver

/-- Add a driver for `port`.  It raises `valid` when `pace` allows and a
    transaction is queued, and — as the protocol requires of a source —
    keeps offering the same transaction until `ready`. -/
def Bench.addDriver {S I O α : Type} (b : Bench S I O) (port : SourcePort I O α)
    (pace : Pace := .always) : IO (Driver α) := do
  let d : Driver α := { queue := ← IO.mkRef #[], next := ← IO.mkRef 0, sent := ← IO.mkRef #[] }
  -- the transaction on the wires in the current cycle, if any
  let offered : IO.Ref (Option α) ← IO.mkRef none
  -- `valid` was raised and not yet accepted: must not be withdrawn
  let committed : IO.Ref Bool ← IO.mkRef false
  let agent : Agent I O := {
    name := port.name
    drive := fun c i => do
      let q ← d.queue.get
      let n ← d.next.get
      let x? := if n < q.size && ((← committed.get) || pace.active c) then q[n]? else none
      offered.set x?
      if x?.isSome then committed.set true
      return port.drive i x?
    observe := fun c o => do
      if let some x := ← offered.get then
        if port.ready o then
          d.sent.modify (·.push (c, x))
          d.next.modify (· + 1)
          committed.set false
      return []
    busy := return !(← d.idle) }
  b.agents.modify (·.push agent)
  return d

/-! ### Monitor -/

/-- Receives transactions on a `SinkPort`. -/
structure Monitor (β : Type) where
  /-- (cycle of the handshake, transaction) -/
  received : IO.Ref (Array (Nat × β))
  /-- how many `get` has handed out -/
  taken : IO.Ref Nat

namespace Monitor

def log {β : Type} (m : Monitor β) : IO (List (Nat × β)) := return (← m.received.get).toList

def items {β : Type} (m : Monitor β) : IO (List β) := return (← m.received.get).toList.map (·.2)

/-- at least `n` transactions have arrived -/
def count {β : Type} (m : Monitor β) (n : Nat) : IO Bool := return (← m.received.get).size ≥ n

end Monitor

/-- Add a monitor for `port`.  `ready` follows `pace` (back-pressure).  The
    monitor reports a protocol error when the DUT, having raised `valid`
    without a handshake, drops `valid` or changes the payload. -/
def Bench.addMonitor {S I O β : Type} [BEq β] (b : Bench S I O) (port : SinkPort I O β)
    (pace : Pace := .always) : IO (Monitor β) := do
  let m : Monitor β := { received := ← IO.mkRef #[], taken := ← IO.mkRef 0 }
  let readyNow : IO.Ref Bool ← IO.mkRef false
  -- a transaction that was valid last cycle and not accepted
  let pending : IO.Ref (Option β) ← IO.mkRef none
  let agent : Agent I O := {
    name := port.name
    drive := fun c i => do
      let r := pace.active c
      readyNow.set r
      return port.setReady i r
    observe := fun c o => do
      let before ← pending.get
      match port.valid o with
      | some y =>
        let changed := match before with
          | some y' => y' != y
          | none => false
        if ← readyNow.get then
          m.received.modify (·.push (c, y))
          pending.set none
        else pending.set (some y)
        return if changed then ["the payload changed while valid was waiting for ready"] else []
      | none =>
        pending.set none
        return if before.isSome then ["valid was withdrawn before the handshake"] else []
    busy := return false }
  b.agents.modify (·.push agent)
  return m

/-! ### Blocking transport -/

/-- A transaction-level view of a component: blocking `put` of a request
    and `get` of a response.  A test written against `Endpoint` runs on the
    RTL and on a model unchanged. -/
structure Endpoint (α β : Type) where
  /-- returns once the transaction has been accepted (false: timeout) -/
  put : α → IO Bool
  /-- the next response, in order (`none`: none arrived in time) -/
  get : IO (Option β)

/-- The RTL behind a driver/monitor pair.  `put` clocks the bench until the
    driver's transaction is accepted; `get` clocks until a response the test
    has not seen yet is available.  The monitor keeps collecting while `put`
    runs, so a put cannot deadlock on an unread response. -/
def Endpoint.ofRtl {S I O α β : Type} [Sim S I O] (b : Bench S I O)
    (d : Driver α) (m : Monitor β) : Endpoint α β where
  put x := do
    d.send x
    b.runUntil d.idle "a put to be accepted"
  get := do
    let n ← m.taken.get
    if ← b.runUntil (m.count (n + 1)) "a response" then
      m.taken.set (n + 1)
      return (← m.received.get)[n]?.map (·.2)
    else return none

/-- An untimed model: `step state request = (state', responses)`. -/
def Endpoint.ofModel {σ α β : Type} (step : σ → α → σ × List β) (init : σ) :
    IO (Endpoint α β) := do
  let state ← IO.mkRef init
  let out : IO.Ref (Array β) ← IO.mkRef #[]
  let taken ← IO.mkRef 0
  return {
    put := fun x => do
      let (s', ys) := step (← state.get) x
      state.set s'
      out.modify (· ++ ys.toArray)
      return true
    get := do
      let n ← taken.get
      match (← out.get)[n]? with
      | some y => taken.set (n + 1); return some y
      | none => return none }

/-! ### Scoreboard -/

/-- In-order comparison.  Reports the first difference and a length
    mismatch; `[]` when equal. -/
def mismatches {β : Type} [BEq β] [Repr β] (what : String) (got expected : List β) : List String :=
  let firstDiff := (List.range (min got.length expected.length)).find? fun k =>
    got[k]? != expected[k]?
  let diff := match firstDiff with
    | some k =>
      [s!"{what}: transaction {k} is {repr (got[k]?)}, expected {repr (expected[k]?)}"]
    | none => []
  let len := if got.length != expected.length then
      [s!"{what}: {got.length} transactions, expected {expected.length}"]
    else []
  diff ++ len

/-- Record the differences between `got` and `expected` as bench errors. -/
def Bench.check {S I O β : Type} [BEq β] [Repr β] (b : Bench S I O) (what : String)
    (got expected : List β) : IO Unit := do
  for e in mismatches what got expected do b.error e

/-! ### Report -/

structure Report where
  cycles : Nat
  errors : List String
  deriving Repr

def Report.ok (r : Report) : Bool := r.errors.isEmpty

def Bench.report {S I O : Type} (b : Bench S I O) : IO Report :=
  return { cycles := ← b.cycleRef.get, errors := (← b.errorsRef.get).toList }

/-- Latency of each transaction through a stream DUT: handshake cycle at
    the monitor minus handshake cycle at the driver, pairing them in order. -/
def latencies {α β : Type} (sent : List (Nat × α)) (received : List (Nat × β)) : List Nat :=
  (sent.zip received).map fun ((cs, _), (cr, _)) => cr - cs

/-- The common case in one call: a DUT with one input stream and one output
    stream.  Sends `items`, waits for `expected.length` results (or the
    timeout), compares them in order, and returns the report together with
    the per-transaction latencies. -/
def runStream {S I O α β : Type} [Sim S I O] [BEq β] [Repr β]
    (sim : S) (idle : I) (src : SourcePort I O α) (snk : SinkPort I O β)
    (items : List α) (expected : List β)
    (inPace outPace : Pace := .always) (maxCycles : Nat := 10000) :
    IO (Report × List Nat) := do
  let b ← Bench.new sim idle maxCycles
  let d ← b.addDriver src inPace
  let m ← b.addMonitor snk outPace
  d.sendAll items
  let _ ← b.runUntil (m.count expected.length) s!"{expected.length} transactions on {snk.name}"
  -- a few more cycles: anything further the DUT emits is an error
  b.run 4
  b.check snk.name (← m.items) expected
  return (← b.report, latencies (← d.log) (← m.log))

end Sparkle.Verification.Tlm
