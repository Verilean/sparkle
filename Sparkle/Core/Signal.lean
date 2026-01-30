import Sparkle.Core.Domain

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

Use `Signal.register` to create state elements (delays by 1 cycle):

```lean
def counter : Signal Domain (BitVec 8) := do
  let count ← Signal.register 0
  count <~ count + 1
  return count
```

### Multiplexers

Use `Signal.mux` or if-then-else for conditional logic:

```lean
def conditionalInc (enable : Bool) (x : BitVec 8) : Signal Domain (BitVec 8) := do
  let val ← Signal.register 0
  val <~ if enable then val + x else val
  return val
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
opaque loop [Inhabited α] (f : Signal dom α → Signal dom α) : Signal dom α

end Signal

-- Notation and syntax sugar

/-- Bundle multiple signals for convenience -/
def bundle2 {dom : DomainConfig} {α β : Type u}
    (a : Signal dom α) (b : Signal dom β) : Signal dom (α × β) :=
  (·, ·) <$> a <*> b

def bundle3 {dom : DomainConfig} {α β γ : Type u}
    (a : Signal dom α) (b : Signal dom β) (c : Signal dom γ) : Signal dom (α × β × γ) :=
  (·, ·, ·) <$> a <*> b <*> c

/-- Unbundle a signal of pairs -/
def unbundle2 {dom : DomainConfig} {α β : Type u}
    (s : Signal dom (α × β)) : Signal dom α × Signal dom β :=
  (s.map Prod.fst, s.map Prod.snd)

-- ============================================================================
-- Tuple Projection Methods (Readable alternatives to map Prod.fst/snd)
-- ============================================================================

/-- Project first element from a 2-tuple signal -/
def Signal.fst {dom : DomainConfig} {α β : Type u} (s : Signal dom (α × β)) : Signal dom α :=
  s.map Prod.fst

/-- Project second element from a 2-tuple signal -/
def Signal.snd {dom : DomainConfig} {α β : Type u} (s : Signal dom (α × β)) : Signal dom β :=
  s.map Prod.snd

/-- Unbundle a 3-tuple signal -/
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

end Sparkle.Core.Signal
