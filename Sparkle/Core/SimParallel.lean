/-
  SimParallel — High-level simulation runner with automatic backend selection.

  `runSim` is the single entry point users should need. It dispatches to:
  - `runSingleSim` (single-threaded evalTick loop) for 1 endpoint, 0 connections
  - `runMultiDomainSim` (JIT.runCDC) for 2 endpoints, 1 connection
  - an error for unsupported combinations.

  Users who want to force a specific backend (benchmarking, debugging) can
  call `runSingleSim` / `runMultiDomainSim` directly.

  Typical usage:

    -- 1 domain:
    let sim ← my_counter.Sim.load
    sim.reset
    let stats ← runSim [sim.toEndpoint] (cycles := 1_000_000)

    -- 2 domains with CDC:
    let p ← producer.Sim.load
    let c ← consumer.Sim.load
    let stats ← runSim [p.toEndpoint, c.toEndpoint]
      (connections := [("data_out", "data_in")])
      (cycles := 1_000_000)
-/

import Sparkle.Core.JIT

namespace Sparkle.Core.SimParallel

open Sparkle.Core.JIT

/-- Everything runSim needs about one loaded JIT domain. Usually built via
    `someModule.Sim.Simulator.toEndpoint`. -/
structure SimEndpoint where
  handle       : JITHandle
  moduleName   : String
  lookupOutput : String → Option UInt32
  lookupInput  : String → Option UInt32
  outputNames  : List String
  inputNames   : List String

/-- `(producerOutputPortName, consumerInputPortName)` — a single wire connection
    between two domains routed through the CDC SPSC queue. -/
abbrev Connection := String × String

/-- Aggregated statistics returned by `runSim`. For single-domain runs,
    `messagesSent`/`messagesReceived`/`rollbacks` are all 0. -/
structure SimStats where
  cyclesRun        : UInt64
  messagesSent     : UInt64
  messagesReceived : UInt64
  rollbacks        : UInt64
  deriving Repr

/-- Single-threaded `evalTick` loop. Forces the non-parallel backend.
    Use this directly if you want to bypass `runSim`'s auto-selection. -/
def runSingleSim (ep : SimEndpoint) (cycles : UInt64) : IO SimStats := do
  for _ in [0 : cycles.toNat] do
    JIT.evalTick ep.handle
  pure { cyclesRun := cycles
       , messagesSent := 0
       , messagesReceived := 0
       , rollbacks := 0 }

/-- Multi-domain CDC runner backed by `JIT.runCDC`. Forces the parallel
    backend. Use this directly if you want to skip `runSim` dispatch.

    Raises `IO.userError` if the connection names are not valid ports of
    the producer/consumer endpoints. -/
def runMultiDomainSim
    (producer consumer : SimEndpoint)
    (connection : Connection)
    (producerCycles consumerCycles : UInt64)
    : IO SimStats := do
  let (outName, inName) := connection
  let outIdx ← match producer.lookupOutput outName with
    | some i => pure i
    | none =>
      throw (IO.userError
        s!"runMultiDomainSim: producer '{producer.moduleName}' has no output port '{outName}'. Available outputs: {producer.outputNames}")
  let inIdx ← match consumer.lookupInput inName with
    | some i => pure i
    | none =>
      throw (IO.userError
        s!"runMultiDomainSim: consumer '{consumer.moduleName}' has no input port '{inName}'. Available inputs: {consumer.inputNames}")
  let (sent, recv, rolls) ← JIT.runCDC
    producer.handle consumer.handle
    producerCycles consumerCycles
    outIdx inIdx
  pure { cyclesRun := producerCycles
       , messagesSent := sent
       , messagesReceived := recv
       , rollbacks := rolls }

/-- High-level dispatcher: automatically picks the fastest runner.

    Rules:
    - `[ep]` with no connections → `runSingleSim` (fastest for 1 domain)
    - `[prod, cons]` with one connection → `runMultiDomainSim` (CDC queue)
    - anything else → `IO.userError` describing the limitation.

    Limitations:
    - 3+ endpoints are not yet supported (needs multi-queue runCDC).
    - Multi-connection between the same pair of endpoints is not yet
      supported (needs runCDC extension). See KnownIssues Issue 3.
-/
def runSim
    (endpoints : List SimEndpoint)
    (connections : List Connection := [])
    (cycles : UInt64)
    : IO SimStats := do
  match endpoints, connections with
  | [ep], [] => runSingleSim ep cycles
  | [ep], _  :: _ =>
    throw (IO.userError
      s!"runSim: single endpoint '{ep.moduleName}' cannot have connections; use runSim [ep] (cycles := ...) instead.")
  | [prod, cons], [c] =>
    runMultiDomainSim prod cons c cycles cycles
  | [prod, cons], [] =>
    throw (IO.userError
      s!"runSim: two endpoints ('{prod.moduleName}', '{cons.moduleName}') require exactly one connection. \
         If you meant two independent runs, call runSingleSim on each endpoint.")
  | [_, _], _ :: _ :: _ =>
    throw (IO.userError
      s!"runSim: multi-connection CDC is not yet supported (got {connections.length} connections). \
         See KnownIssues Issue 3.1.")
  | _, _ =>
    throw (IO.userError
      s!"runSim: only 1 or 2 endpoints are supported (got {endpoints.length}). \
         See KnownIssues Issue 3.2.")

end Sparkle.Core.SimParallel
