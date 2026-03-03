/-
  JITLoop — JIT-accelerated Signal.loopMemo replacement

  Provides `Signal.loopMemoJIT` with the same `IO (Signal dom α)` API as
  `loopMemo`, but uses JIT-compiled C++ under the hood for ~200x speedup.

  Also provides `JIT.run` for streaming mode (O(1) memory) for long runs.

  **Design principle**: Read values via explicitly named output wires
  (`JIT.getWire` with stable names that feed the top-level output),
  not via `getOutput` (192-bit packed output is skipped by CppSim backend).

  Usage:
    let soc ← Signal.loopMemoJIT
      (jitCppPath := "verilator/generated_soc_jit.cpp")
      (wireNames := #["_gen_pcReg", "_gen_uartValidBV", ...])
      (loadMem := fun h => ...)
      (reconstruct := fun _h vals => pure (mkMyResult vals))
-/

import Sparkle.Core.Signal
import Sparkle.Core.JIT

namespace Sparkle.Core.JITLoop

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT

/-- JIT-accelerated loopMemo replacement using named output wires.
    Returns IO (Signal dom α) that reads from JIT simulation.

    Parameters:
    - `jitCppPath`: Path to the pre-generated `*_jit.cpp` file
    - `wireNames`: Array of `_gen_*` wire names to read each cycle.
      Use wires that feed the top-level output — they are stable
      (not affected by DCE or name collisions on internal state).
    - `loadMem`: Optional callback to load firmware/data into JIT memories
    - `reconstruct`: Converts wire values (UInt64 array, indexed by wireNames)
      into the result type `α` -/
private unsafe def loopMemoJITImpl {dom : DomainConfig} {α : Type} [Inhabited α]
    (jitCppPath : String)
    (wireNames : Array String)
    (loadMem : JITHandle → IO Unit := fun _ => pure ())
    (reconstruct : JITHandle → Array UInt64 → IO α)
    : IO (Signal dom α) := do
  -- 1. Compile and load JIT shared library
  let handle ← JIT.compileAndLoad jitCppPath
  -- 2. Resolve wire indices by exact name
  let wireIndices ← wireNames.mapM fun name => do
    match ← JIT.findWire handle name with
    | some idx => pure idx
    | none => throw (IO.userError s!"loopMemoJIT: wire '{name}' not found in JIT module")
  -- 3. Load firmware/data
  loadMem handle
  -- 4. Build cached Signal that reads from JIT
  let cacheRef ← IO.mkRef (#[] : Array α)
  let cacheSizeRef ← IO.mkRef (0 : Nat)
  let evalAt (t : Nat) : IO α := do
    let sz ← cacheSizeRef.get
    if t < sz then
      let arr ← cacheRef.get
      return if h : t < arr.size then arr[t] else default
    -- Advance JIT forward to timestep t
    for _ in [sz:t + 1] do
      JIT.eval handle
      -- Read named wire values
      let vals ← wireIndices.mapM fun idx =>
        JIT.getWire handle idx
      let state ← reconstruct handle vals
      let arr ← cacheRef.swap #[]
      cacheRef.set (arr.push state)
      JIT.tick handle
    cacheSizeRef.set (t + 1)
    let arr ← cacheRef.get
    return if h : t < arr.size then arr[t] else default
  return ⟨fun t =>
    match unsafeIO (evalAt t) with
    | .ok v => v
    | .error _ => default⟩

@[implemented_by loopMemoJITImpl]
opaque Signal.loopMemoJIT {dom : DomainConfig} {α : Type} [Inhabited α]
    (jitCppPath : String)
    (wireNames : Array String)
    (loadMem : JITHandle → IO Unit := fun _ => pure ())
    (reconstruct : JITHandle → Array UInt64 → IO α)
    : IO (Signal dom α)

/-- Run JIT simulation for up to `cycles` cycles with a per-cycle callback.
    No state caching — O(1) memory. The callback receives the cycle number
    and an array of wire values (indexed by wireNames order).
    Return `false` from the callback to stop early.

    Parameters:
    - `handle`: Pre-loaded JIT handle
    - `cycles`: Maximum number of cycles to run
    - `wireIndices`: Pre-resolved wire indices (from JIT.findWire)
    - `callback`: Called each cycle with (cycle, wireValues); return false to stop -/
def JIT.run (handle : JITHandle) (cycles : Nat)
    (wireIndices : Array UInt32)
    (callback : Nat → Array UInt64 → IO Bool)
    : IO Unit := do
  for cycle in [:cycles] do
    JIT.eval handle
    let vals ← wireIndices.mapM fun idx =>
      JIT.getWire handle idx
    let continue_ ← callback cycle vals
    if !continue_ then return
    JIT.tick handle

/-- Resolve an array of wire names to their JIT indices.
    Throws if any wire name is not found. -/
def JIT.resolveWires (handle : JITHandle) (wireNames : Array String) : IO (Array UInt32) := do
  wireNames.mapM fun name => do
    match ← JIT.findWire handle name with
    | some idx => pure idx
    | none => throw (IO.userError s!"JIT.resolveWires: wire '{name}' not found")

/-- Resolve an array of register names to their JIT indices.
    Throws if any register name is not found. -/
def JIT.resolveRegs (handle : JITHandle) (regNames : Array String) : IO (Array UInt32) := do
  regNames.mapM fun name => do
    match ← JIT.findReg handle name with
    | some idx => pure idx
    | none => throw (IO.userError s!"JIT.resolveRegs: register '{name}' not found")

/-- Run JIT simulation with an oracle callback for cycle-skipping.
    Same as `JIT.run` but with an additional `oracle` that can inject register
    state to skip cycles. When the oracle returns `some (skipCount, updates)`,
    the updates are applied via `JIT.setReg` and the cycle counter advances
    by `max skipCount 1` (skipping that many cycles at once).

    Parameters:
    - `handle`: Pre-loaded JIT handle
    - `cycles`: Maximum number of cycles to run
    - `wireIndices`: Pre-resolved wire indices (from JIT.resolveWires)
    - `oracle`: Called each cycle with (cycle, wireValues); return
      `some (skipCount, updates)` to skip forward, or `none` for normal tick.
      `skipCount` is how many cycles to advance; `updates` is an array of
      (regIdx, value) pairs to apply.
    - `callback`: Called each cycle with (cycle, wireValues); return false to stop

    Returns: the number of cycles actually executed -/
def JIT.runOptimized (handle : JITHandle) (cycles : Nat)
    (wireIndices : Array UInt32)
    (oracle : Nat → Array UInt64 → IO (Option (Nat × Array (UInt32 × UInt64))))
    (callback : Nat → Array UInt64 → IO Bool)
    : IO Nat := do
  let mut cycle := 0
  while cycle < cycles do
    JIT.eval handle
    let vals ← wireIndices.mapM fun idx => JIT.getWire handle idx
    let continue_ ← callback cycle vals
    if !continue_ then return cycle
    match ← oracle cycle vals with
    | none =>
      -- Normal cycle: tick
      JIT.tick handle
      cycle := cycle + 1
    | some (skipCount, updates) =>
      -- Cycle-skip: apply register state directly, skip tick
      for (regIdx, val) in updates do
        JIT.setReg handle regIdx val
      cycle := cycle + (max skipCount 1)
  return cycle

end Sparkle.Core.JITLoop
