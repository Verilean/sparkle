/-
  Sparkle.Core.CircuitMonad — v2.

  State-passing monad whose register state is a heterogeneous
  Prod chain (`Sparkle.Core.HList`) rather than a homogeneous
  Vector.  This is the reincarnation of the retired v1 PoC
  (archived on branch `poc/circuit-monad`).

  Why Prod chains, not Vector.  The IR elaborator
  (`Sparkle/Compiler/Elab.lean`) already recognises Prod /
  `Signal.map Prod.fst` / `Signal.map Prod.snd` as wire
  slicing — so any state shape that is *definitionally* a Prod
  chain reaches synthesis through the existing rules, no new
  elaborator code needed.  Vector required new rules; HList
  inherits them for free.

  Heterogeneous registers.  The v1 PoC was constrained to one
  element type `τ` per `runCircuit` because Vector requires it.
  HList lifts that: a single circuit can mix `BitVec 2` state
  with `BitVec 8` counters with `Bool` flags.

  Status.  Simulation: should match the macro DSL on the same
  circuits.  Synthesis: the goal of this PoC is to verify that
  the Prod-chain reduction does in fact reach `#synthesizeVerilog`
  successfully where the Vector version did not.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Wireable

namespace Sparkle.Core

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### Single-slot abstraction over a Prod-chain state.

    Each register slot is identified by a *getter/setter* lens
    into the HList.  We don't expose `Fin n` indexing — the lens
    pair is what the macro-style allocator would produce, and
    the elaborator can reduce a lens that's a chain of `.1`/`.2`
    accesses into a plain bit slice. -/

namespace Circuit

/-- Slot accessor over a state of static shape `S`.

    Concretely a pair `(read, update)` of lens functions over
    the Prod-chain state.  Defined as a plain Prod alias rather
    than a `structure` so the elaborator's existing Prod /
    Prod.fst / Prod.snd recognition lowers field access without
    needing a separate struct-projection rule. -/
@[reducible] def Slot (dom : DomainConfig) (S : Type) (τ : Type) : Type :=
  (Signal dom S → Signal dom τ) × (Signal dom τ → Signal dom S → Signal dom S)

@[reducible] def Slot.read {dom : DomainConfig} {S : Type} {τ : Type}
    (s : Slot dom S τ) : Signal dom S → Signal dom τ := s.1

@[reducible] def Slot.update {dom : DomainConfig} {S : Type} {τ : Type}
    (s : Slot dom S τ) : Signal dom τ → Signal dom S → Signal dom S := s.2

@[reducible] def Slot.mk {dom : DomainConfig} {S : Type} {τ : Type}
    (read : Signal dom S → Signal dom τ)
    (update : Signal dom τ → Signal dom S → Signal dom S) : Slot dom S τ :=
  (read, update)

end Circuit

/-- Register handle = `(liveRead, slot)` Prod.

    Same rationale as `Slot` — a Prod alias rather than a
    `structure`, so accesses through `.1` / `.2` ride on the
    existing elaborator rules. -/
@[reducible] def Reg (dom : DomainConfig) (S : Type) (τ : Type) : Type :=
  Signal dom τ × Circuit.Slot dom S τ

@[reducible] def Reg.liveRead {dom : DomainConfig} {S : Type} {τ : Type}
    (r : Reg dom S τ) : Signal dom τ := r.1

@[reducible] def Reg.slot {dom : DomainConfig} {S : Type} {τ : Type}
    (r : Reg dom S τ) : Circuit.Slot dom S τ := r.2

@[reducible] def Reg.mk {dom : DomainConfig} {S : Type} {τ : Type}
    (liveRead : Signal dom τ) (slot : Circuit.Slot dom S τ) : Reg dom S τ :=
  (liveRead, slot)

/-- A `Reg dom S τ` coerces to its live `Signal dom τ` read.
    Lets user code use `cnt` directly anywhere a `Signal dom τ`
    is expected (e.g. as the rhs of `Circuit.next` or
    `Signal.mux`), without needing an explicit `Circuit.read`
    or `.1`. -/
instance {dom : DomainConfig} {S τ : Type} : CoeHead (Reg dom S τ) (Signal dom τ) where
  coe r := r.1

/-- `CoeOut`: lets Lean coerce a `Reg` to a `Signal` even when
    the expected type isn't fully known (e.g. when both
    arguments to `Signal.mux` need coercion and neither side
    pins down the `α` first).  `CoeOut` is checked when going
    *from* a concrete known type, not *to* one, so it triggers
    on a `Reg` lhs regardless of whether the target Signal's
    `τ` is yet determined. -/
instance {dom : DomainConfig} {S τ : Type} : CoeOut (Reg dom S τ) (Signal dom τ) where
  coe r := r.1


/-! ### Operator instances lifting `Reg` to `Signal`.

    `cnt + 1#8` doesn't trigger the `CoeHead` above because Lean
    resolves `HAdd cnt 1#8` by looking up `HAdd` with the lhs
    type `Reg …`, not by coercing first.  We provide the mixed
    `HAdd (Reg …) (BitVec n) (Signal …)` instances explicitly,
    mirroring the existing `Signal × BitVec` instances. -/

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HAdd (Reg dom S (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hAdd a b := a.1 + b

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HSub (Reg dom S (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hSub a b := a.1 - b

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HMul (Reg dom S (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hMul a b := a.1 * b

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HAdd (Reg dom S (BitVec n)) (Reg dom S (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := a.1 + b.1

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HSub (Reg dom S (BitVec n)) (Reg dom S (BitVec n)) (Signal dom (BitVec n)) where
  hSub a b := a.1 - b.1

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HMul (Reg dom S (BitVec n)) (Reg dom S (BitVec n)) (Signal dom (BitVec n)) where
  hMul a b := a.1 * b.1

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HAdd (Reg dom S (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := a.1 + b

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HAdd (Signal dom (BitVec n)) (Reg dom S (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := a + b.1

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HXor (Reg dom S (BitVec n)) (Reg dom S (BitVec n)) (Signal dom (BitVec n)) where
  hXor a b := a.1 ^^^ b.1

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HAnd (Reg dom S (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hAnd a b := a.1 &&& b

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HAnd (Reg dom S (BitVec n)) (Reg dom S (BitVec n)) (Signal dom (BitVec n)) where
  hAnd a b := a.1 &&& b.1

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HOr (Reg dom S (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hOr a b := a.1 ||| b

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HOr (Reg dom S (BitVec n)) (Reg dom S (BitVec n)) (Signal dom (BitVec n)) where
  hOr a b := a.1 ||| b.1

instance {dom : DomainConfig} {S : Type} {n : Nat} :
    HXor (Reg dom S (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hXor a b := a.1 ^^^ b

namespace Circuit

variable {dom : DomainConfig} {S τ α β : Type}

/-- Pending next-cycle writes accumulated by the body.

    `nextOf live` returns the closed next-state Signal — we
    build it by chaining slot updates over the user's `<~`
    calls in source order, starting from `live` as the
    "everything holds" baseline. -/
def NextBuilder (dom : DomainConfig) (S : Type) : Type :=
  Signal dom S → Signal dom S

end Circuit

/-- The Circuit monad — state-passing over the pending writes
    accumulator `Circuit.NextBuilder dom S`.

    `S` is the static HList shape of the register state.  The
    macro / allocator chooses `S` at `runCircuit` time and the
    type stays fixed across the body. -/
def Circuit (dom : DomainConfig) (S : Type) (α : Type) : Type :=
  Circuit.NextBuilder dom S → α × Circuit.NextBuilder dom S

namespace Circuit

variable {dom : DomainConfig} {S α β : Type}

@[reducible, inline] def pure' (a : α) : Circuit dom S α := fun b => (a, b)

@[reducible, inline] def bind (m : Circuit dom S α) (k : α → Circuit dom S β) :
    Circuit dom S β :=
  fun b =>
    let p := m b
    k p.fst p.snd

@[reducible] instance : Monad (Circuit dom S) where
  pure := Circuit.pure'
  bind := Circuit.bind

/-- Record a next-cycle Signal for one register slot.  Repeat
    writes overwrite earlier ones via Slot.update's "stamp into
    the slot" semantics (last write wins, matching the macro). -/
@[reducible, inline] def next (r : Reg dom S τ) (sig : Signal dom τ) : Circuit dom S Unit :=
  fun b =>
    let b' : NextBuilder dom S := fun live => r.slot.update sig (b live)
    ((), b')

/-- Type class capturing "things that can be the rhs of a
    register write" — a `Signal dom τ` directly, or a bare
    element value (e.g. `BitVec n`, `Bool`) that we wrap in
    `Signal.pure`.

    Lets `circuit do` lower `state <~ 0#2` (BitVec rhs) and
    `cnt <~ cnt + 1#8` (Signal rhs) through the same
    `Circuit.next` shape without per-case syntax tracking. -/
class AsSignal (dom : DomainConfig) (τ : Type) (α : Type) where
  toSignal : α → Signal dom τ

@[reducible] instance {dom : DomainConfig} {τ : Type} :
    AsSignal dom τ (Signal dom τ) where
  toSignal s := s

@[reducible] instance {dom : DomainConfig} {n : Nat} :
    AsSignal dom (BitVec n) (BitVec n) where
  toSignal v := Signal.pure v

@[reducible] instance {dom : DomainConfig} :
    AsSignal dom Bool Bool where
  toSignal v := Signal.pure v

/-- Polymorphic register-write: accepts either a `Signal dom τ`
    or a bare `τ` value (lifted via `AsSignal`).  Replaces
    `next` at the user-visible API; `next` remains as the raw
    `Signal`-only form used internally. -/
@[reducible, inline] def nextAny {α : Type} [AsSignal dom τ α]
    (r : Reg dom S τ) (val : α) : Circuit dom S Unit :=
  next r (AsSignal.toSignal val)

/-- Read the live current-cycle Signal of a register handle.
    Just a projection — there for symmetry with `next`. -/
@[reducible, inline] def read (r : Reg dom S τ) : Signal dom τ := r.liveRead

end Circuit

/-! ### Arbitrary-arity `runCircuitH` via HList state.

    The generalisation of `runCircuit{1,2,3,4}` to any list of
    register types.  Constraint `[HListWireable αs]` ensures
    every slot type is synth-friendly; without it a user could
    drop e.g. `Option Nat` into the list and hit a synth
    failure deep inside the elaborator.

    Three pieces:

      1. `RegList dom S αs` — heterogeneous list of register
         handles, one per slot, sharing one outer state shape S.
      2. `mkRegList` — builds the `RegList` from a live state
         Signal by composing `Prod.fst` / `Prod.snd` accessors
         (the slot lenses are constructed once, recursively).
      3. `runCircuitH` — closes the body with `Signal.loop` and
         a chain of `Signal.register`s, one per slot.

    Each piece is `@[reducible, inline]` so the IR elaborator
    can unfold through them at synth time. -/

/-- `RegList dom S αs` — a tuple of register handles for slots
    `αs`, all carrying the same outer state shape `S`.  Defined
    structurally on `αs` so a `RegList dom S (α :: αs')`
    decomposes into `Reg dom S α × RegList dom S αs'`.  `S` is
    *fixed* across the whole list — it doesn't shrink as we
    recurse, which is the key to keeping the slot lenses typed
    against the original outer state. -/
@[reducible] def RegList (dom : DomainConfig) (S : Type) : List Type → Type
  | []      => Unit
  | α :: αs => Reg dom S α × RegList dom S αs

/-- Build a `RegList dom S αs` by walking down `αs`.

    Constructed slot lenses are pure `Signal`-level chains of
    `Signal.map Prod.fst / Prod.snd` and `bundle2` — the same
    primitives Sparkle's IR elaborator already lowers.  No
    value-level `Signal.map` closures over arbitrary functions.

    The slot read/update lenses are passed in as Signal-level
    operations (rather than pure-value functions) so the
    chained `Prod.fst`/`Prod.snd` calls stay visible to the
    elaborator at every recursion depth. -/
@[reducible] def mkRegList {dom : DomainConfig} {S : Type}
    (liveOuter : Signal dom S) :
    (αs : List Type) →
    (readSig : Signal dom S → Signal dom (HList αs)) →
    (writeSig : Signal dom (HList αs) → Signal dom S → Signal dom S) →
    RegList dom S αs
  | [],       _,    _      => ()
  | α :: αs', readSig, writeSig =>
    let headReadSig : Signal dom S → Signal dom α :=
      fun s => Signal.map Prod.fst (readSig s)
    let tailReadSig : Signal dom S → Signal dom (HList αs') :=
      fun s => Signal.map Prod.snd (readSig s)
    let headWriteSig : Signal dom α → Signal dom S → Signal dom S :=
      fun n s => writeSig (bundle2 n (tailReadSig s)) s
    let tailWriteSig : Signal dom (HList αs') → Signal dom S → Signal dom S :=
      fun n s => writeSig (bundle2 (headReadSig s) n) s
    let slot : Circuit.Slot dom S α :=
      Circuit.Slot.mk headReadSig headWriteSig
    let head : Reg dom S α :=
      Reg.mk (headReadSig liveOuter) slot
    let tail := mkRegList liveOuter αs' tailReadSig tailWriteSig
    (head, tail)

/-- For each slot of `αs`, take the corresponding `init` and a
    slice of `nextState`, and emit a `Signal.register`.  Pack
    the results back into a `Signal dom (HList αs)`.

    Reducible so the synth elaborator unfolds through it to the
    underlying `Signal.register` / `bundle2` chain. -/
@[reducible, inline] def packRegister {dom : DomainConfig} :
    (αs : List Type) → HList αs → Signal dom (HList αs) → Signal dom (HList αs)
  | [],       _,    _    => Signal.pure ()
  | _ :: αs', init, next =>
    bundle2 (Signal.register init.1 (Signal.map Prod.fst next))
            (packRegister αs' init.2 (Signal.map Prod.snd next))

/-- Generic `runCircuit` taking any HList of initial values.
    The body receives a matching `RegList` of register handles.

    `[HListWireable αs]` requires every slot type to be
    `Wireable`, gating non-synthesisable types at the call
    site instead of the synth elaborator. -/
@[reducible, inline] def runCircuitH {dom : DomainConfig} {αs : List Type} {ρ : Type}
    [HListWireable αs] [Inhabited (HList αs)]
    (inits : HList αs)
    (body : RegList dom (HList αs) αs →
            Circuit dom (HList αs) (Signal dom ρ)) : Signal dom ρ :=
  let idRead  : Signal dom (HList αs) → Signal dom (HList αs) := fun s => s
  let idWrite : Signal dom (HList αs) → Signal dom (HList αs) → Signal dom (HList αs) :=
    fun n _ => n
  let stateLoop : Signal dom (HList αs) :=
    Signal.loop (α := HList αs) (fun live =>
      let regs := mkRegList live αs idRead idWrite
      let bResult := body regs id
      let b' : Circuit.NextBuilder dom (HList αs) := bResult.snd
      let nextState : Signal dom (HList αs) := b' live
      packRegister αs inits nextState)
  let regs := mkRegList stateLoop αs idRead idWrite
  (body regs id).fst

end Sparkle.Core
