import Sparkle.Core.Domain
import Std.Data.HashMap

/-!
# Signal Module

This module defines the stream-based signal semantics for Sparkle HDL.

## Overview

Signals represent time-varying hardware values using infinite streams.
A `Signal d α` is essentially a function `Nat → α` where `Nat` represents
discrete time steps (clock cycles).

## Key Concepts

- **Stream**: An infinite sequence `Nat → α` representing values over time
- **Signal**: A stream tagged with a clock domain for type safety
- **Domain**: Type-level clock domain tracking prevents mixing signals from different clocks

## Core Primitives

### Registers

Use `Signal.register init input` to create state elements (delays by 1 cycle):

```lean
-- Simple register chain (feed-forward)
def registerChain (input : Signal Domain (BitVec 8)) : Signal Domain (BitVec 8) :=
  let d1 := Signal.register 0#8 input
  let d2 := Signal.register 0#8 d1
  d2

-- Counter with feedback (requires let rec)
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  let rec count := Signal.register 0#8 (count.map (· + 1))
  count
```

### Multiplexers

Use `Signal.mux` for conditional logic (NOT if-then-else):

```lean
def conditionalInc (enable : Signal Domain Bool) (input : Signal Domain (BitVec 8))
    : Signal Domain (BitVec 8) :=
  let next := input.map (· + 1)
  Signal.mux enable next input  -- Select between increment or hold
```

## Simulation

Signals can be simulated directly to verify behavior before synthesis:

```lean
#eval Signal.simulate myCircuit inputs |>.take 10
```

See also: `Sparkle.Core.Domain` for clock domain configuration.
-/

namespace Sparkle.Core.Signal

open Sparkle.Core.Domain

-- Cache reader: reads arr[t] from an IORef, with the entire read in C.
-- Prevents Lean 4.28's LICM from hoisting `unsafeIO cacheRef.get` out of
-- lambdas by making the read genuinely depend on `t` (opaque + @[extern]).
@[extern "sparkle_cache_get"]
private opaque cacheGet {α : Type} [Nonempty α] (ref : @& IO.Ref (Array α)) (t : @& Nat) (fallback : α) : α

-- Signal evaluator: calls signal_val(t) inside IO for proper sequencing.
-- Prevents the Lean compiler from reordering pure signal evaluation after
-- IO operations like cacheRef.swap that empty the cache.
@[extern "sparkle_eval_at"]
private opaque evalSignalAt {α : Type} (f : @& (Nat → α)) (t : @& Nat) : IO α
/--
  Stream is an infinite sequence of values indexed by natural numbers.
  Time 0 is the initial state, time 1 is after first clock cycle, etc.
-/
def Stream (α : Type u) : Type u := Nat → α

/--
  Signal represents a time-varying value in a specific clock domain.
  It wraps a Stream and carries domain information at the type level.

  The domain parameter ensures signals from different clock domains
  cannot be accidentally mixed.
-/
structure Signal (dom : DomainConfig) (α : Type u) where
  val : Stream α

-- Inhabited instance needed for opaque definitions
instance [Inhabited α] : Inhabited (Signal dom α) where
  default := ⟨fun _ => default⟩

namespace Signal

variable {dom : DomainConfig} {α β γ : Type u}

/-- Access the value of a signal at a specific time -/
@[inline]
def atTime (s : Signal dom α) (t : Nat) : α := s.val t

/-- Create a constant signal (same value at all times) -/
def pure (x : α) : Signal dom α :=
  ⟨fun _ => x⟩

/-- Map a function over a signal (combinational logic) -/
def map (f : α → β) (s : Signal dom α) : Signal dom β :=
  ⟨fun t => f (s.val t)⟩

/-- Apply a signal of functions to a signal of values -/
def ap (sf : Signal dom (α → β)) (s : Signal dom α) : Signal dom β :=
  ⟨fun t => sf.val t (s.val t)⟩

/-- Sequence two signals -/
def seq (sf : Signal dom (α → β)) (s : Unit → Signal dom α) : Signal dom β :=
  ap sf (s ())

/-- Monadic bind for signals -/
def bind (s : Signal dom α) (f : α → Signal dom β) : Signal dom β :=
  ⟨fun t => (f (s.val t)).val t⟩

/--
  Register (D Flip-Flop) primitive.

  At time 0: outputs the initial value
  At time t > 0: outputs the input value from time (t-1)

  This implements a single-cycle delay, the fundamental building block
  of sequential logic.
-/
def register (init : α) (input : Signal dom α) : Signal dom α :=
  ⟨fun t => match t with
    | 0 => init
    | n + 1 => input.val n⟩

/--
  Register with enable signal.

  When enable is true: register updates normally
  When enable is false: register holds its current value
-/
def registerWithEnable (init : α) (en : Signal dom Bool) (input : Signal dom α) : Signal dom α :=
  let rec go (t : Nat) (prev : α) : α :=
    match t with
    | 0 => init
    | n + 1 =>
      if en.val n then input.val n else prev
  ⟨fun t => match t with
    | 0 => init
    | n + 1 => if en.val n then input.val n else go n init⟩

/-- Helper to create a signal from a stream -/
def fromStream (s : Stream α) : Signal dom α := ⟨s⟩

/-- Helper to extract stream from signal -/
def toStream (s : Signal dom α) : Stream α := s.val

/-- Sample a signal for the first n cycles -/
def sample (s : Signal dom α) (n : Nat) : List α :=
  List.range n |>.map s.val

end Signal

-- Functor instance for Signal
instance : Functor (Signal dom) where
  map := Signal.map

-- Applicative instance for Signal
instance : Applicative (Signal dom) where
  pure := Signal.pure
  seq := Signal.seq

-- Monad instance for Signal
instance : Monad (Signal dom) where
  pure := Signal.pure
  bind := Signal.bind

-- Additional combinators

namespace Signal

variable {dom : DomainConfig} {α β : Type u}

/-- Lift a binary operation to signals (combinational logic) -/
def lift2 (f : α → β → γ) (sa : Signal dom α) (sb : Signal dom β) : Signal dom γ :=
  f <$> sa <*> sb

/-- Delay a signal by n cycles, filling with initial value -/
def delay (n : Nat) (init : α) (s : Signal dom α) : Signal dom α :=
  ⟨fun t => if t < n then init else s.val (t - n)⟩

/-- Create a signal that counts up from 0 -/
partial def counter : Signal dom Nat :=
  let rec cnt := register 0 (cnt.map (· + 1))
  cnt

/-- Mux (multiplexer): select between two signals based on condition -/
def mux (cond : Signal dom Bool) (thenSig : Signal dom α) (elseSig : Signal dom α) : Signal dom α :=
  ⟨fun t => if cond.val t then thenSig.val t else elseSig.val t⟩

/--
  Synchronous memory primitive (RAM/BRAM).

  Creates a memory with registered read (1-cycle latency).
  Writes occur on the clock edge when writeEnable is true.

  Parameters:
  - addrWidth: Address width (memory size = 2^addrWidth)
  - dataWidth: Data width (width of each memory word)
  - writeAddr: Write address signal
  - writeData: Write data signal
  - writeEnable: Write enable signal (write occurs when true)
  - readAddr: Read address signal

  Returns: Read data signal (registered, 1-cycle latency)

  Behavior:
  - At time t, if writeEnable.atTime t is true:
      memory[writeAddr.atTime t] := writeData.atTime t
  - readData.atTime (t+1) = memory[readAddr.atTime t]

  Example:
    ```lean
    -- 256-byte memory (8-bit address, 8-bit data)
    let readData := Signal.memory 8 8 writeAddr writeData writeEnable readAddr
    ```
-/
-- Memoized memory implementation: uses a flat Array (size 2^addrWidth) to cache
-- memory state incrementally. Writes are applied sequentially; reads are O(1).
-- Falls back to the recursive O(t) implementation for addrWidth > 20.
-- HashMap-backed sparse memory for large address spaces (addrWidth > 20).
-- Uses a HashMap instead of a dense Array to avoid O(2^addrWidth) initialization.
-- Only stores entries that have been written, so memory usage is proportional
-- to the number of unique addresses written, not the address space size.
private unsafe def memorySparseImpl {addrWidth dataWidth : Nat}
    (writeAddr : Signal dom (BitVec addrWidth))
    (writeData : Signal dom (BitVec dataWidth))
    (writeEnable : Signal dom Bool)
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec dataWidth) :=
  match unsafeIO (do
    let mapRef ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Nat (BitVec dataWidth))
    let stepRef ← IO.mkRef (0 : Nat)
    let processAndRead (t : Nat) : IO (BitVec dataWidth) := do
      if t == 0 then return 0#dataWidth
      let mut step ← stepRef.get
      while step + 1 < t do
        let we := writeEnable.val step
        let waddr := (writeAddr.val step).toNat
        let wdata := writeData.val step
        if we then
          let m ← mapRef.get
          mapRef.set (m.insert waddr wdata)
        step := step + 1
      stepRef.set step
      let raddr := (readAddr.val (t - 1)).toNat
      let m ← mapRef.get
      return m.getD raddr (0#dataWidth)
    return (⟨fun t =>
      match unsafeIO (processAndRead t) with
      | .ok v => v
      | .error _ => 0#dataWidth
    ⟩ : Signal dom (BitVec dataWidth))
  ) with
  | .ok sig => sig
  | .error _ => ⟨fun _ => 0#dataWidth⟩

private unsafe def memoryImpl {addrWidth dataWidth : Nat}
    (writeAddr : Signal dom (BitVec addrWidth))
    (writeData : Signal dom (BitVec dataWidth))
    (writeEnable : Signal dom Bool)
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec dataWidth) :=
  if addrWidth > 20 then
    memorySparseImpl writeAddr writeData writeEnable readAddr
  else
    let size := 2 ^ addrWidth
    match unsafeIO (do
      let arrRef ← IO.mkRef (Array.replicate size (0#dataWidth))
      let stepRef ← IO.mkRef (0 : Nat)
      -- Process writes and read in a single IO action so the result is used
      -- and the compiler cannot DCE the write operations.
      -- IMPORTANT: Never hold a `take`d array while evaluating signals (.val).
      -- Signal evaluation can re-enter this function at a different timestep,
      -- causing a double-take on arrRef → segfault (Lean's take leaves a dummy).
      -- Fix: evaluate signals first, then briefly take/mutate/set.
      let processAndRead (t : Nat) : IO (BitVec dataWidth) := do
        if t == 0 then return 0#dataWidth
        let mut step ← stepRef.get
        while step + 1 < t do
          -- Evaluate signals BEFORE touching the array ref
          let we := writeEnable.val step
          let waddr := (writeAddr.val step).toNat
          let wdata := writeData.val step
          if we && waddr < size then
            -- Briefly take, mutate in-place (rc=1), set back
            let arr ← arrRef.take
            arrRef.set (arr.set! waddr wdata)
          step := step + 1
        stepRef.set step
        -- Evaluate read address first
        let raddr := (readAddr.val (t - 1)).toNat
        -- Briefly take to read
        let arr ← arrRef.take
        let result := if raddr < arr.size then arr[raddr]! else 0#dataWidth
        arrRef.set arr
        return result
      return (⟨fun t =>
        match unsafeIO (processAndRead t) with
        | .ok v => v
        | .error _ => 0#dataWidth
      ⟩ : Signal dom (BitVec dataWidth))
    ) with
    | .ok sig => sig
    | .error _ => ⟨fun _ => 0#dataWidth⟩

@[implemented_by memoryImpl]
opaque memory {addrWidth dataWidth : Nat}
    (writeAddr : Signal dom (BitVec addrWidth))
    (writeData : Signal dom (BitVec dataWidth))
    (writeEnable : Signal dom Bool)
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec dataWidth)

/--
  Memory with combinational (same-cycle) reads.

  Unlike `memory` which has 1-cycle read latency (reads `readAddr` from the
  previous cycle), `memoryComboRead` reads `readAddr` from the current cycle.
  Writes from previous cycles (0..t-1) are visible; the write at cycle t is not.

  Use this for register files where reads must be combinational.
  NOT synthesizable — use `memory` for synthesis targets.
-/
-- HashMap-backed sparse memory with combinational (same-cycle) reads.
-- For large address spaces (addrWidth > 20) where a flat Array would be too large.
-- Writes from cycles 0..t-1 are applied, then readAddr at cycle t is looked up.
private unsafe def memoryComboReadSparseImpl {addrWidth dataWidth : Nat}
    (writeAddr : Signal dom (BitVec addrWidth))
    (writeData : Signal dom (BitVec dataWidth))
    (writeEnable : Signal dom Bool)
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec dataWidth) :=
  match unsafeIO (do
    let mapRef ← IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap Nat (BitVec dataWidth))
    let stepRef ← IO.mkRef (0 : Nat)
    let processAndRead (t : Nat) : IO (BitVec dataWidth) := do
      let mut step ← stepRef.get
      while step < t do
        let we := writeEnable.val step
        let waddr := (writeAddr.val step).toNat
        let wdata := writeData.val step
        if we then
          let m ← mapRef.get
          mapRef.set (m.insert waddr wdata)
        step := step + 1
      stepRef.set step
      let raddr := (readAddr.val t).toNat
      let m ← mapRef.get
      return m.getD raddr (0#dataWidth)
    return (⟨fun t =>
      match unsafeIO (processAndRead t) with
      | .ok v => v
      | .error _ => 0#dataWidth
    ⟩ : Signal dom (BitVec dataWidth))
  ) with
  | .ok sig => sig
  | .error _ => ⟨fun _ => 0#dataWidth⟩

private unsafe def memoryComboReadImpl {addrWidth dataWidth : Nat}
    (writeAddr : Signal dom (BitVec addrWidth))
    (writeData : Signal dom (BitVec dataWidth))
    (writeEnable : Signal dom Bool)
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec dataWidth) :=
  if addrWidth > 20 then
    memoryComboReadSparseImpl writeAddr writeData writeEnable readAddr
  else
    let size := 2 ^ addrWidth
    match unsafeIO (do
      let arrRef ← IO.mkRef (Array.replicate size (0#dataWidth))
      let stepRef ← IO.mkRef (0 : Nat)
      -- IMPORTANT: Never hold a `take`d array while evaluating signals (.val).
      -- Signal evaluation can re-enter this function at a different timestep,
      -- causing a double-take on arrRef → segfault (Lean's take leaves a dummy).
      -- Fix: evaluate signals first, then briefly take/mutate/set.
      let processAndRead (t : Nat) : IO (BitVec dataWidth) := do
        let mut step ← stepRef.get
        -- Process writes from step 0..t-1
        while step < t do
          -- Evaluate signals BEFORE touching the array ref
          let we := writeEnable.val step
          let waddr := (writeAddr.val step).toNat
          let wdata := writeData.val step
          if we && waddr < size then
            -- Briefly take, mutate in-place (rc=1), set back
            let arr ← arrRef.take
            arrRef.set (arr.set! waddr wdata)
          step := step + 1
        stepRef.set step
        -- Evaluate read address BEFORE taking array
        let raddr := (readAddr.val t).toNat
        -- Briefly take to read
        let arr ← arrRef.take
        let result := if raddr < arr.size then arr[raddr]! else 0#dataWidth
        arrRef.set arr
        return result
      return (⟨fun t =>
        match unsafeIO (processAndRead t) with
        | .ok v => v
        | .error _ => 0#dataWidth
      ⟩ : Signal dom (BitVec dataWidth))
    ) with
    | .ok sig => sig
    | .error _ => ⟨fun _ => 0#dataWidth⟩

@[implemented_by memoryComboReadImpl]
opaque memoryComboRead {addrWidth dataWidth : Nat}
    (writeAddr : Signal dom (BitVec addrWidth))
    (writeData : Signal dom (BitVec dataWidth))
    (writeEnable : Signal dom Bool)
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec dataWidth)

/--
  Synchronous memory with initial contents (RAM/BRAM).

  Like `memory`, but starts with pre-loaded data instead of all zeros.
  Synthesizable: generates Verilog `initial $readmemh(...)` or inline
  `initial begin mem[0]=...; end` blocks.

  Parameters:
  - initData: Initial memory contents as a function from address to data
  - writeAddr: Write address signal
  - writeData: Write data signal
  - writeEnable: Write enable signal
  - readAddr: Read address signal

  Returns: Read data signal (registered, 1-cycle latency)
-/
private unsafe def memoryWithInitImpl {addrWidth dataWidth : Nat}
    (initData : BitVec addrWidth → BitVec dataWidth)
    (writeAddr : Signal dom (BitVec addrWidth))
    (writeData : Signal dom (BitVec dataWidth))
    (writeEnable : Signal dom Bool)
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec dataWidth) :=
  if addrWidth > 20 then
    -- Fallback: recursive implementation for huge address spaces
    let rec memState (t : Nat) : BitVec addrWidth → BitVec dataWidth :=
      match t with
      | 0 => initData
      | n + 1 =>
        let prevMem := memState n
        fun addr =>
          if writeEnable.val n && addr == writeAddr.val n then
            writeData.val n
          else
            prevMem addr
    ⟨fun t =>
      match t with
      | 0 => initData (readAddr.val 0)
      | n + 1 => memState n (readAddr.val n)⟩
  else
    let size := 2 ^ addrWidth
    -- Initialize array from initData
    let initArr := Array.ofFn (n := size) fun (i : Fin size) =>
      initData (BitVec.ofNat addrWidth i.val)
    match unsafeIO (do
      let arrRef ← IO.mkRef initArr
      let stepRef ← IO.mkRef (0 : Nat)
      -- IMPORTANT: Never hold a `take`d array while evaluating signals (.val).
      -- Signal evaluation can re-enter this function at a different timestep,
      -- causing a double-take on arrRef → segfault (Lean's take leaves a dummy).
      -- Fix: evaluate signals first, then briefly take/mutate/set.
      let processAndRead (t : Nat) : IO (BitVec dataWidth) := do
        if t == 0 then return initData (readAddr.val 0)
        let mut step ← stepRef.get
        while step + 1 < t do
          -- Evaluate signals BEFORE touching the array ref
          let we := writeEnable.val step
          let waddr := (writeAddr.val step).toNat
          let wdata := writeData.val step
          if we && waddr < size then
            -- Briefly take, mutate in-place (rc=1), set back
            let arr ← arrRef.take
            arrRef.set (arr.set! waddr wdata)
          step := step + 1
        stepRef.set step
        -- Evaluate read address first
        let raddr := (readAddr.val (t - 1)).toNat
        -- Briefly take to read
        let arr ← arrRef.take
        let result := if raddr < arr.size then arr[raddr]! else initData (readAddr.val (t - 1))
        arrRef.set arr
        return result
      return (⟨fun t =>
        match unsafeIO (processAndRead t) with
        | .ok v => v
        | .error _ => initData (readAddr.val 0)
      ⟩ : Signal dom (BitVec dataWidth))
    ) with
    | .ok sig => sig
    | .error _ => ⟨fun _ => initData (readAddr.val 0)⟩

@[implemented_by memoryWithInitImpl]
opaque memoryWithInit {addrWidth dataWidth : Nat}
    (initData : BitVec addrWidth → BitVec dataWidth)
    (writeAddr : Signal dom (BitVec addrWidth))
    (writeData : Signal dom (BitVec dataWidth))
    (writeEnable : Signal dom Bool)
    (readAddr : Signal dom (BitVec addrWidth))
    : Signal dom (BitVec dataWidth)

/--
  Fixed-point combinator for feedback loops.

  Allows defining circuits where the output feeds back into the input,
  such as counters or state machines.

  Usage:
    Signal.loop fun feedback =>
      let next := ... use feedback ...
      register 0 next

  Note: The simulation semantics are defined as a fixed point.
  For synthesis, this is recognized by the compiler.
-/
private unsafe def loopImpl [Inhabited α] (f : Signal dom α → Signal dom α) : Signal dom α :=
  let rec result := f result
  result

@[implemented_by loopImpl]
opaque loop [Inhabited α] (f : Signal dom α → Signal dom α) : Signal dom α

/--
  Memoized fixed-point combinator for feedback loops.

  Like `loop`, but caches the loop output per timestep in an array.
  When evaluating sequentially (t=0,1,2,...), prior timesteps are O(1) lookups
  instead of rebuilding the entire temporal chain.

  This eliminates stack overflow for large loop bodies (e.g., 56-register SoC)
  by turning O(t) stack depth per evaluation into O(1) with cached results.

  Returns IO because it allocates a mutable cache internally.
-/
private unsafe def loopMemoImpl {dom : DomainConfig} {α : Type} [Inhabited α]
    (f : Signal dom α → Signal dom α) : IO (Signal dom α) := do
  let cacheRef ← IO.mkRef (#[] : Array α)
  let cacheSizeRef ← IO.mkRef (0 : Nat)
  -- cacheGet is an @[extern] C function: reads cacheRef[t] entirely in C.
  -- The Lean compiler cannot hoist this because cacheGet is opaque and
  -- genuinely depends on t. Without this, LICM hoists unsafeIO cacheRef.get
  -- out of the lambda, caching a stale empty array forever.
  let result : Signal dom α := ⟨fun t => cacheGet cacheRef t default⟩
  let inner := f result
  -- evalAt: populate cache sequentially up to t, return value at t.
  -- Each inner.val i reads result.val (i-1) which is a cache hit (already pushed).
  let evalAt (t : Nat) : IO α := do
    let sz ← cacheSizeRef.get
    if t < sz then
      let arr ← cacheRef.get
      return if h : t < arr.size then arr[t] else default
    else
      for i in [sz:t + 1] do
        -- evalSignalAt forces evaluation BEFORE the swap.
        -- Without it, the compiler reorders `inner.val i` (pure) after
        -- `cacheRef.swap #[]` (IO), emptying the cache during evaluation.
        let v ← evalSignalAt inner.val i
        -- swap out (rc=1), push in-place, set back
        let arr ← cacheRef.swap #[]
        cacheRef.set (arr.push v)
      cacheSizeRef.set (t + 1)
      let arr ← cacheRef.get
      return if h : t < arr.size then arr[t] else default
  return ⟨fun t =>
    match unsafeIO (evalAt t) with
    | .ok v => v
    | .error _ => default⟩

@[implemented_by loopMemoImpl]
opaque loopMemo {dom : DomainConfig} {α : Type} [Inhabited α] (f : Signal dom α → Signal dom α) : IO (Signal dom α)

end Signal

-- ============================================================================
-- BitVec Utilities for Signal DSL
-- ============================================================================

/-- Arithmetic shift right with BitVec shift amount.
    Wraps `BitVec.sshiftRight` (which takes Nat) so it can be used
    in the applicative Signal DSL pattern: `(ashr · ·) <$> a <*> b` -/
def ashr (a b : BitVec n) : BitVec n :=
  a.sshiftRight b.toNat

-- Notation and syntax sugar

/-- Bundle multiple signals for convenience -/
private unsafe def bundle2Impl {dom : DomainConfig} {α β : Type u}
    (a : Signal dom α) (b : Signal dom β) : Signal dom (α × β) :=
  ⟨fun t => (a.val t, b.val t)⟩

@[implemented_by bundle2Impl]
def bundle2 {dom : DomainConfig} {α β : Type u}
    (a : Signal dom α) (b : Signal dom β) : Signal dom (α × β) :=
  (·, ·) <$> a <*> b

private unsafe def bundle3Impl {dom : DomainConfig} {α β γ : Type u}
    (a : Signal dom α) (b : Signal dom β) (c : Signal dom γ) : Signal dom (α × β × γ) :=
  ⟨fun t => (a.val t, b.val t, c.val t)⟩

@[implemented_by bundle3Impl]
def bundle3 {dom : DomainConfig} {α β γ : Type u}
    (a : Signal dom α) (b : Signal dom β) (c : Signal dom γ) : Signal dom (α × β × γ) :=
  (·, ·, ·) <$> a <*> b <*> c

/-- Unbundle a signal of pairs
⚠️  WARNING: This function returns a Lean-level tuple and CANNOT be used with
pattern matching in synthesis context. Use Signal.fst/snd instead:

WRONG:  let (a, b) := unbundle2 signal  -- ❌ Causes "Unbound variable" errors
RIGHT:  let a := signal.fst            -- ✓ Works in synthesis
        let b := signal.snd
-/
def unbundle2 {dom : DomainConfig} {α β : Type u}
    (s : Signal dom (α × β)) : Signal dom α × Signal dom β :=
  (s.map Prod.fst, s.map Prod.snd)

-- ============================================================================
-- Tuple Projection Methods (Readable alternatives to map Prod.fst/snd)
-- ============================================================================

/-- Project first element from a 2-tuple signal -/
private unsafe def fstImpl {dom : DomainConfig} {α β : Type u}
    (s : Signal dom (α × β)) : Signal dom α :=
  ⟨fun t => (s.val t).1⟩

@[implemented_by fstImpl]
def Signal.fst {dom : DomainConfig} {α β : Type u} (s : Signal dom (α × β)) : Signal dom α :=
  s.map Prod.fst

/-- Project second element from a 2-tuple signal -/
private unsafe def sndImpl {dom : DomainConfig} {α β : Type u}
    (s : Signal dom (α × β)) : Signal dom β :=
  ⟨fun t => (s.val t).2⟩

@[implemented_by sndImpl]
def Signal.snd {dom : DomainConfig} {α β : Type u} (s : Signal dom (α × β)) : Signal dom β :=
  s.map Prod.snd

/-- Unbundle a 3-tuple signal
⚠️  WARNING: Returns a Lean-level tuple. Cannot use with pattern matching in synthesis.
Use Signal.proj3_1/2/3 instead.
-/
def unbundle3 {dom : DomainConfig} {α β γ : Type u}
    (s : Signal dom (α × β × γ)) : Signal dom α × Signal dom β × Signal dom γ :=
  (s.map (·.1), s.map (·.2.1), s.map (·.2.2))

/-- Project first element from a 3-tuple signal -/
def Signal.proj3_1 {dom : DomainConfig} {α β γ : Type u}
    (s : Signal dom (α × β × γ)) : Signal dom α :=
  s.map (·.1)

/-- Project second element from a 3-tuple signal -/
def Signal.proj3_2 {dom : DomainConfig} {α β γ : Type u}
    (s : Signal dom (α × β × γ)) : Signal dom β :=
  s.map (·.2.1)

/-- Project third element from a 3-tuple signal -/
def Signal.proj3_3 {dom : DomainConfig} {α β γ : Type u}
    (s : Signal dom (α × β × γ)) : Signal dom γ :=
  s.map (·.2.2)

/-- Unbundle a 4-tuple signal -/
def unbundle4 {dom : DomainConfig} {α β γ δ : Type u}
    (s : Signal dom (α × β × γ × δ)) : Signal dom α × Signal dom β × Signal dom γ × Signal dom δ :=
  (s.map (·.1), s.map (·.2.1), s.map (·.2.2.1), s.map (·.2.2.2))

/-- Project first element from a 4-tuple signal -/
def Signal.proj4_1 {dom : DomainConfig} {α β γ δ : Type u}
    (s : Signal dom (α × β × γ × δ)) : Signal dom α :=
  s.map (·.1)

/-- Project second element from a 4-tuple signal -/
def Signal.proj4_2 {dom : DomainConfig} {α β γ δ : Type u}
    (s : Signal dom (α × β × γ × δ)) : Signal dom β :=
  s.map (·.2.1)

/-- Project third element from a 4-tuple signal -/
def Signal.proj4_3 {dom : DomainConfig} {α β γ δ : Type u}
    (s : Signal dom (α × β × γ × δ)) : Signal dom γ :=
  s.map (·.2.2.1)

/-- Project fourth element from a 4-tuple signal -/
def Signal.proj4_4 {dom : DomainConfig} {α β γ δ : Type u}
    (s : Signal dom (α × β × γ × δ)) : Signal dom δ :=
  s.map (·.2.2.2)

/-- Unbundle a 5-tuple signal -/
def unbundle5 {dom : DomainConfig} {α β γ δ ε : Type u}
    (s : Signal dom (α × β × γ × δ × ε)) : Signal dom α × Signal dom β × Signal dom γ × Signal dom δ × Signal dom ε :=
  (s.map (·.1), s.map (·.2.1), s.map (·.2.2.1), s.map (·.2.2.2.1), s.map (·.2.2.2.2))

/-- Unbundle a 6-tuple signal -/
def unbundle6 {dom : DomainConfig} {α β γ δ ε ζ : Type u}
    (s : Signal dom (α × β × γ × δ × ε × ζ)) : Signal dom α × Signal dom β × Signal dom γ × Signal dom δ × Signal dom ε × Signal dom ζ :=
  (s.map (·.1), s.map (·.2.1), s.map (·.2.2.1), s.map (·.2.2.2.1), s.map (·.2.2.2.2.1), s.map (·.2.2.2.2.2))

/-- Unbundle a 7-tuple signal -/
def unbundle7 {dom : DomainConfig} {α β γ δ ε ζ η : Type u}
    (s : Signal dom (α × β × γ × δ × ε × ζ × η)) : Signal dom α × Signal dom β × Signal dom γ × Signal dom δ × Signal dom ε × Signal dom ζ × Signal dom η :=
  (s.map (·.1), s.map (·.2.1), s.map (·.2.2.1), s.map (·.2.2.2.1), s.map (·.2.2.2.2.1), s.map (·.2.2.2.2.2.1), s.map (·.2.2.2.2.2.2))

/-- Unbundle an 8-tuple signal -/
def unbundle8 {dom : DomainConfig} {α β γ δ ε ζ η θ : Type u}
    (s : Signal dom (α × β × γ × δ × ε × ζ × η × θ)) : Signal dom α × Signal dom β × Signal dom γ × Signal dom δ × Signal dom ε × Signal dom ζ × Signal dom η × Signal dom θ :=
  (s.map (·.1), s.map (·.2.1), s.map (·.2.2.1), s.map (·.2.2.2.1), s.map (·.2.2.2.2.1), s.map (·.2.2.2.2.2.1), s.map (·.2.2.2.2.2.2.1), s.map (·.2.2.2.2.2.2.2))

-- ============================================================================
-- Tuple Macros for Signal.loop Pipeline Pattern
-- ============================================================================

/-- Project the i-th element (0-indexed) from a right-nested pair signal.
    `projN! state n i` extracts element `i` from `n`-element nested pair.

    Example (4-element tuple `(A × (B × (C × D)))`):
      `projN! s 4 0` → `Signal.fst s`              -- A
      `projN! s 4 1` → `Signal.fst (Signal.snd s)`  -- B
      `projN! s 4 2` → `Signal.fst (Signal.snd (Signal.snd s))`  -- C
      `projN! s 4 3` → `Signal.snd (Signal.snd (Signal.snd s))`  -- D (last uses snd) -/
syntax "projN!" term:max num num : term

macro_rules
  | `(projN! $s $n 0) => do
    if n.getNat == 1 then `($s)
    else `(Signal.fst $s)
  | `(projN! $s $n $i) => do
    let n' := n.getNat
    let i' := i.getNat
    if i' == n' - 1 then
      -- Last element: chain of Signal.snd
      let mut result ← `($s)
      for _ in [:i'] do
        result ← `(Signal.snd $result)
      return result
    else
      -- Middle element: Signal.fst after i chains of Signal.snd
      let mut result ← `($s)
      for _ in [:i'] do
        result ← `(Signal.snd $result)
      `(Signal.fst $result)

/-- Bundle a list of signals into a right-nested pair using `bundle2`.
    `bundleAll! [a, b, c, d]` → `bundle2 a (bundle2 b (bundle2 c d))`

    For a single element, returns that element directly. -/
syntax "bundleAll!" "[" term,+ "]" : term

macro_rules
  | `(bundleAll! [$a]) => `($a)
  | `(bundleAll! [$a, $b]) => `(bundle2 $a $b)
  | `(bundleAll! [$a, $bs,*]) => `(bundle2 $a (bundleAll! [$bs,*]))

end Sparkle.Core.Signal
