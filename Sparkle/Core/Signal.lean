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

-- Hardware operator overloading for Signal (BitVec n)
-- Enables writing `a + b` instead of `(· + ·) <$> a <*> b`

instance : HAdd (Signal dom (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := (· + ·) <$> a <*> b

instance : HSub (Signal dom (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hSub a b := (· - ·) <$> a <*> b

instance : HMul (Signal dom (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hMul a b := (· * ·) <$> a <*> b

instance : HAnd (Signal dom (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hAnd a b := (· &&& ·) <$> a <*> b

instance : HOr (Signal dom (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hOr a b := (· ||| ·) <$> a <*> b

instance : HXor (Signal dom (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hXor a b := (· ^^^ ·) <$> a <*> b

-- Bit concatenation for Signal (BitVec)
-- Enables: a ++ b instead of (· ++ ·) <$> a <*> b

instance : HAppend (Signal dom (BitVec m)) (Signal dom (BitVec n)) (Signal dom (BitVec (m + n))) where
  hAppend a b := (· ++ ·) <$> a <*> b

instance : HAppend (Signal dom (BitVec m)) (BitVec n) (Signal dom (BitVec (m + n))) where
  hAppend a b := (· ++ ·) <$> a <*> Signal.pure b

instance : HAppend (BitVec m) (Signal dom (BitVec n)) (Signal dom (BitVec (m + n))) where
  hAppend a b := (· ++ ·) <$> Signal.pure a <*> b

-- Mixed Signal/constant operator overloading
-- Enables: `count + 1#8`, `val &&& 0xFF#8` without explicit Signal.pure

-- Implementation uses (· op ·) <$> a <*> Signal.pure b form so that the
-- synthesis compiler's Seq.seq + Functor.map pattern recognizes the operation
-- even inside inlined private function bodies.

instance : HAdd (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hAdd a b := (· + ·) <$> a <*> Signal.pure b
instance : HAdd (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := (· + ·) <$> Signal.pure a <*> b

instance : HSub (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hSub a b := (· - ·) <$> a <*> Signal.pure b
instance : HSub (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hSub a b := (· - ·) <$> Signal.pure a <*> b

instance : HMul (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hMul a b := (· * ·) <$> a <*> Signal.pure b
instance : HMul (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hMul a b := (· * ·) <$> Signal.pure a <*> b

instance : HAnd (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hAnd a b := (· &&& ·) <$> a <*> Signal.pure b
instance : HAnd (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hAnd a b := (· &&& ·) <$> Signal.pure a <*> b

instance : HOr (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hOr a b := (· ||| ·) <$> a <*> Signal.pure b
instance : HOr (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hOr a b := (· ||| ·) <$> Signal.pure a <*> b

instance : HXor (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hXor a b := (· ^^^ ·) <$> a <*> Signal.pure b
instance : HXor (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hXor a b := (· ^^^ ·) <$> Signal.pure a <*> b

instance : HShiftLeft (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hShiftLeft a b := (· <<< ·) <$> a <*> Signal.pure b
instance : HShiftLeft (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hShiftLeft a b := (· <<< ·) <$> Signal.pure a <*> b
instance : HShiftRight (Signal dom (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hShiftRight a b := (· >>> ·) <$> a <*> Signal.pure b
instance : HShiftRight (BitVec n) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hShiftRight a b := (· >>> ·) <$> Signal.pure a <*> b

-- Boolean operator overloading for Signal Bool
-- Enables: a &&& b, a ||| b, a ^^^ b, ~~~a

instance : HAnd (Signal dom Bool) (Signal dom Bool) (Signal dom Bool) where
  hAnd a b := (· && ·) <$> a <*> b

instance : HOr (Signal dom Bool) (Signal dom Bool) (Signal dom Bool) where
  hOr a b := (· || ·) <$> a <*> b

instance : HXor (Signal dom Bool) (Signal dom Bool) (Signal dom Bool) where
  hXor a b := (xor · ·) <$> a <*> b

instance : Complement (Signal dom Bool) where
  complement a := (fun x => !x) <$> a

instance : Complement (Signal dom (BitVec n)) where
  complement a := (fun x => ~~~x) <$> a

-- Shift operators for Signal (BitVec n)
-- Enables: a <<< b, a >>> b

instance : HShiftLeft (Signal dom (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hShiftLeft a b := (· <<< ·) <$> a <*> b

instance : HShiftRight (Signal dom (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hShiftRight a b := (· >>> ·) <$> a <*> b

-- Comparison operators for Signal (BitVec n)
-- Return Signal dom Bool

/-- Unsigned less-than: `a <ₛ b` on signals. -/
def Signal.lt [LT α] [DecidableRel (α := α) (· < ·)] (a b : Signal dom α) : Signal dom Bool :=
  (fun x y => decide (x < y)) <$> a <*> b

/-- Unsigned less-or-equal: `a ≤ₛ b` on signals. -/
def Signal.le [LE α] [DecidableRel (α := α) (· ≤ ·)] (a b : Signal dom α) : Signal dom Bool :=
  (fun x y => decide (x ≤ y)) <$> a <*> b

-- Signed/unsigned comparison for Signal (BitVec n)

/-- Signed less-than on BitVec signals. -/
def Signal.slt (a b : Signal dom (BitVec n)) : Signal dom Bool :=
  (BitVec.slt · ·) <$> a <*> b

/-- Unsigned less-than on BitVec signals. -/
def Signal.ult (a b : Signal dom (BitVec n)) : Signal dom Bool :=
  (BitVec.ult · ·) <$> a <*> b

/-- Signed less-or-equal on BitVec signals. -/
def Signal.sle (a b : Signal dom (BitVec n)) : Signal dom Bool :=
  (BitVec.sle · ·) <$> a <*> b

/-- Unsigned less-or-equal on BitVec signals. -/
def Signal.ule (a b : Signal dom (BitVec n)) : Signal dom Bool :=
  (BitVec.ule · ·) <$> a <*> b

/-- Arithmetic shift right on BitVec signals. -/
def Signal.ashr (a b : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  (fun x y => BitVec.sshiftRight x y.toNat) <$> a <*> b

-- Mixed constant variants for slt/ult/ashr
def Signal.sltC (a : Signal dom (BitVec n)) (b : BitVec n) : Signal dom Bool :=
  (fun x => BitVec.slt x b) <$> a
def Signal.ultC (a : Signal dom (BitVec n)) (b : BitVec n) : Signal dom Bool :=
  (fun x => BitVec.ult x b) <$> a
def Signal.ashrC (a : Signal dom (BitVec n)) (b : BitVec n) : Signal dom (BitVec n) :=
  (fun x => BitVec.sshiftRight x b.toNat) <$> a

-- Negation for Signal (BitVec n)

instance : Neg (Signal dom (BitVec n)) where
  neg a := (fun x => -x) <$> a

-- Hardware equality operator
-- Expands to (· == ·) <$> a <*> b, which the synthesis compiler recognizes

/-- Hardware equality: `a === b` compares two signals element-wise each cycle. -/
def Signal.beq [BEq α] (a b : Signal dom α) : Signal dom Bool :=
  (· == ·) <$> a <*> b

scoped infix:50 " === " => Signal.beq

/-- Constant signal with explicit domain binding.
    Use instead of `Signal.pure` when the domain can't be inferred:
    `let rnd := Signal.lit dom 32#16` instead of `let rnd := Signal.pure 32#16` -/
abbrev Signal.lit (dom : DomainConfig) (x : α) : Signal dom α := Signal.pure x

-- Implicit constant lifting (scoped to avoid global instance pollution)

scoped instance {n : Nat} : Coe (BitVec n) (Signal dom (BitVec n)) where
  coe x := Signal.pure x

scoped instance : Coe Bool (Signal dom Bool) where
  coe x := Signal.pure x

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

-- Fixed-point combinator for feedback loops.
-- Uses memoized evaluation via C FFI barriers (cacheGet/evalSignalAt)
-- to prevent stack overflow during simulation. The pure `Signal dom α`
-- signature is preserved via `unsafeIO` in the returned signal.
private unsafe def loopImpl {dom : DomainConfig} {α : Type} [Inhabited α]
    (f : Signal dom α → Signal dom α) : Signal dom α :=
  match unsafeIO (loopMemoCore f) with
  | .ok sig => sig
  | .error _ => default
where
  loopMemoCore (f : Signal dom α → Signal dom α) : IO (Signal dom α) := do
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

@[implemented_by loopImpl]
opaque loop {dom : DomainConfig} {α : Type} [Inhabited α] (f : Signal dom α → Signal dom α) : Signal dom α

/--
  Memoized fixed-point combinator for feedback loops (IO variant).

  Identical semantics to `loop`, but returns `IO` explicitly.
  Kept for backward compatibility with existing simulation code.
  New code should prefer `Signal.loop` directly (or `Signal.circuit`).
-/
private unsafe def loopMemoImpl {dom : DomainConfig} {α : Type} [Inhabited α]
    (f : Signal dom α → Signal dom α) : IO (Signal dom α) :=
  return loopImpl f

@[implemented_by loopMemoImpl]
opaque loopMemo {dom : DomainConfig} {α : Type} [Inhabited α] (f : Signal dom α → Signal dom α) : IO (Signal dom α)

/-- Chained conditional mux: priority-encoded multiplexer.
    `Signal.cond [(c1, v1), (c2, v2), ...] default` selects the first
    matching condition's value, falling back to `default`. -/
def cond (cases : List (Signal dom Bool × Signal dom α)) (default : Signal dom α) : Signal dom α :=
  cases.foldr (fun (c, v) acc => Signal.mux c v acc) default

end Signal

-- Hardware conditional macro (synthesis-compatible)
-- Defined after Signal.mux so ``Signal.mux`` resolves correctly.
-- Uses mkIdent to bypass macro hygiene (prevents _hyg suffixes that would
-- break the synthesis compiler's `name.endsWith ".mux"` check).

/-- Hardware switch: replaces deeply nested `Signal.mux` chains.
    Default value comes first, then condition/value pairs (first match wins):
    ```
    hw_cond fsmReg
      | startAndIdle  => (1#4 : Signal dom _)
      | stemDone      => (2#4 : Signal dom _)
    ```
    expands to `Signal.mux startAndIdle (1#4) (Signal.mux stemDone (2#4) fsmReg)` -/
scoped syntax "hw_cond" term ("|" term " => " term)* : term

macro_rules
  | `(hw_cond $default) => `($default)
  | `(hw_cond $default | $cond => $val $[| $conds => $vals]*) => do
    let rest ← `(hw_cond $default $[| $conds => $vals]*)
    let muxId := Lean.mkIdent ``Signal.mux
    `($muxId $cond $val $rest)

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

/-- Unbundle a signal of pairs.

⚠️  Returns a Lean-level tuple. Pattern-matching on the result
(`let (a, b) := unbundle2 signal`) silently breaks in synthesis because the
tuple is destructured at elaboration time. Use `Signal.fst` / `Signal.snd`
directly instead. This binding is kept only so legacy test files still
compile. -/
@[deprecated "Use `Signal.fst` and `Signal.snd` directly. Pattern-matching on `unbundle2` breaks in synthesis." (since := "2026-04-08")]
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

/-- Unbundle a 3-tuple signal.

⚠️  Same caveat as `unbundle2`: the returned Lean tuple cannot be pattern-matched
in synthesis code. Use `Signal.proj3_1 / proj3_2 / proj3_3` instead. -/
@[deprecated "Use `Signal.proj3_1`, `Signal.proj3_2`, `Signal.proj3_3` directly." (since := "2026-04-08")]
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

/-- Unbundle a 4-tuple signal.

⚠️  Same caveat as `unbundle2`. Use `Signal.proj4_1..proj4_4` instead. -/
@[deprecated "Use `Signal.proj4_1..proj4_4` directly." (since := "2026-04-08")]
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

-- ============================================================================
-- hw_let: Tuple Destructuring for Signal Pipeline Pattern
-- ============================================================================

/-- Destructure a 2-element right-nested pair signal into named bindings.
    `hw_let (a, b) := sig; body` expands to:
    `let a := Signal.fst sig; let b := Signal.snd sig; body` -/
macro "hw_let" "(" a:ident "," b:ident ")" " := " e:term ";" body:term : term =>
  `(let _hw_tmp := $e; let $a := Signal.fst _hw_tmp; let $b := Signal.snd _hw_tmp; $body)

/-- Destructure a 3-element right-nested pair signal `(A × (B × C))`. -/
macro "hw_let" "(" a:ident "," b:ident "," c:ident ")" " := " e:term ";" body:term : term =>
  `(let _hw_tmp := $e;
    let $a := Signal.fst _hw_tmp;
    let $b := Signal.fst (Signal.snd _hw_tmp);
    let $c := Signal.snd (Signal.snd _hw_tmp);
    $body)

/-- Destructure a 4-element right-nested pair signal `(A × (B × (C × D)))`. -/
macro "hw_let" "(" a:ident "," b:ident "," c:ident "," d:ident ")" " := " e:term ";" body:term : term =>
  `(let _hw_tmp := $e;
    let $a := Signal.fst _hw_tmp;
    let $b := Signal.fst (Signal.snd _hw_tmp);
    let $c := Signal.fst (Signal.snd (Signal.snd _hw_tmp));
    let $d := Signal.snd (Signal.snd (Signal.snd _hw_tmp));
    $body)

-- ============================================================================
-- Signal.circuit: Imperative Register Assignment DSL
-- ============================================================================

/--
  Imperative-style hardware description with `<~` register assignment.

  `Signal.circuit` desugars to `Signal.loop` + `Signal.register` + `bundleAll!`.
  Registers are declared with `Signal.reg`, assigned with `<~`, and the
  block returns a Signal expression.

  **Simple counter:**
  ```lean
  def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
    Signal.circuit (dom := dom) do
      let count ← Signal.reg 0#8
      count <~ count + 1#8
      return count
  ```

  **State machine with multiple registers:**
  ```lean
  def upDown {dom : DomainConfig} (up : Signal dom Bool) : Signal dom (BitVec 8) :=
    Signal.circuit (dom := dom) do
      let count ← Signal.reg 0#8
      count <~ Signal.mux up (count + 1#8) (count - 1#8)
      return count
  ```

  **Desugaring:** The macro collects all `let x ← Signal.reg init` declarations
  and `x <~ expr` assignments, then rewrites into:
  ```lean
  Signal.loop fun _state =>
    let x := projN! _state N 0    -- unpack register outputs
    let y := projN! _state N 1
    ...
    let xNext := <rhs of x <~>   -- compute next values
    let yNext := <rhs of y <~>
    ...
    -- remaining let bindings and body
    let _ := <return expr>        -- body is for type, output taken from loop
    bundleAll! [Signal.register init0 xNext, Signal.register init1 yNext, ...]
  ```
-/

-- Syntax for the circuit block
declare_syntax_cat circuitStmt
syntax "let " ident " ← " "Signal.reg " term ";" : circuitStmt    -- register declaration
syntax ident " <~ " term ";" : circuitStmt                          -- register assignment
syntax "let " ident " := " term ";" : circuitStmt                   -- local let binding
syntax "return " term : circuitStmt                                  -- return expression (last, no semicolon)

syntax "Signal.circuit" "do" ppLine circuitStmt* : term

open Lean in
open Lean.Macro in
macro_rules
  | `(Signal.circuit do $stmts*) => do
    -- Phase 1: Collect register declarations (name, init)
    let mut regs : Array (TSyntax `ident × TSyntax `term) := #[]
    -- Phase 2: Collect assignments (name, rhs)
    let mut assigns : Array (TSyntax `ident × TSyntax `term) := #[]
    -- Phase 3: Collect let bindings (name, rhs)
    let mut lets : Array (TSyntax `ident × TSyntax `term) := #[]
    -- Phase 4: Return expression
    let mut retExpr : Option (TSyntax `term) := none

    for stmt in stmts do
      match stmt with
      | `(circuitStmt| let $name ← Signal.reg $init ;) =>
        regs := regs.push (name, init)
      | `(circuitStmt| $name:ident <~ $rhs ;) =>
        assigns := assigns.push (name, rhs)
      | `(circuitStmt| let $name := $rhs ;) =>
        lets := lets.push (name, rhs)
      | `(circuitStmt| return $e) =>
        retExpr := some e
      | _ => Macro.throwUnsupported

    if regs.isEmpty then
      Macro.throwError "Signal.circuit: no registers declared (use `let x ← Signal.reg init`)"

    let ret ← match retExpr with
      | some e => pure e
      | none => Macro.throwError "Signal.circuit: missing `return` expression"

    let n := regs.size

    -- Build the loop body tail: bundleAll! [Signal.register init0 next0, ...]
    let mut regTerms : Array (TSyntax `term) := #[]
    for (regName, init) in regs do
      let mut found := false
      for (aName, aRhs) in assigns do
        if aName.getId == regName.getId then
          regTerms := regTerms.push (← `(Signal.register $init $aRhs))
          found := true
          break
      if !found then
        -- No assignment: register holds its value (feedback to self)
        regTerms := regTerms.push (← `(Signal.register $init $regName))
    let bundled ←
      if regTerms.size == 1 then
        pure regTerms[0]!
      else if regTerms.size == 2 then
        `(bundle2 $(regTerms[0]!) $(regTerms[1]!))
      else
        `(bundleAll! [$regTerms,*])
    let mut body := bundled

    -- Prepend let bindings (in reverse order to nest)
    for i in [:lets.size] do
      let (name, rhs) := lets[lets.size - 1 - i]!
      body ← `(let $name := $rhs; $body)

    -- Prepend register projections from state tuple
    for i in [:n] do
      let (regName, _) := regs[n - 1 - i]!
      let idx := Syntax.mkNumLit (toString (n - 1 - i))
      let total := Syntax.mkNumLit (toString n)
      body ← `(let $regName := projN! _circuit_state $total $idx; $body)

    -- Wrap in Signal.loop
    let loopExpr ← `(Signal.loop fun _circuit_state => $body)

    -- After the loop, project registers and evaluate the return expression
    let mut result ← pure ret

    -- Prepend let bindings for the return context
    for i in [:lets.size] do
      let (name, rhs) := lets[lets.size - 1 - i]!
      result ← `(let $name := $rhs; $result)

    -- Project registers from loop output
    for i in [:n] do
      let (regName, _) := regs[n - 1 - i]!
      let idx := Syntax.mkNumLit (toString (n - 1 - i))
      let total := Syntax.mkNumLit (toString n)
      result ← `(let $regName := projN! _circuit_result $total $idx; $result)

    `(let _circuit_result := $loopExpr; $result)

end Sparkle.Core.Signal
