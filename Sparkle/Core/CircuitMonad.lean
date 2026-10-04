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

/-- Slot accessor over a state of static shape `S`, writing into a
    pending-writes accumulator of type `W`.

    Concretely a pair `(read, update)`: `read` is a lens over the live
    Prod-chain state (unchanged from the original design); `update` stamps a
    new Signal into the slot's entry of the pending-writes accumulator `W`.

    ## Why `update` targets `W` (a tuple of per-slot Signals), not `Signal S`

    The original `update : Signal τ → Signal S → Signal S` rebuilt the FULL
    bundled next-state on every write — reading every other slot back out of
    the previous accumulator via lens chains.  Composing k writes therefore
    built a k-deep chain in which each layer referenced the previous layer
    once per slot, and the closure evaluator (which has no sharing — the
    heap DAG is walked as a tree) paid ~k^k per cycle.  That is the real
    mechanism behind issue #95: a 10-register pass-through chain hung near
    t≈20 through `Signal.val`, while hand-written `bundleAll!` FSMs (flat,
    single next-tuple) of 6+ registers were instant.

    With `W = SigList` (one pending Signal per slot), a write is pure tuple
    surgery — no Signal nodes are created, nothing re-reads other slots —
    and `runCircuitH` bundles the accumulator ONCE into the register file.
    Evaluation cost per cycle is linear in the circuit size.

    Defined as a plain Prod alias rather than a `structure` so the
    elaborator's existing Prod / Prod.fst / Prod.snd recognition lowers
    field access without needing a separate struct-projection rule. -/
@[reducible] def Slot (dom : DomainConfig) (S : Type) (W : Type) (τ : Type) : Type :=
  (Signal dom S → Signal dom τ) × (Signal dom τ → W → W)

@[reducible] def Slot.read {dom : DomainConfig} {S W : Type} {τ : Type}
    (s : Slot dom S W τ) : Signal dom S → Signal dom τ := s.1

@[reducible] def Slot.update {dom : DomainConfig} {S W : Type} {τ : Type}
    (s : Slot dom S W τ) : Signal dom τ → W → W := s.2

@[reducible] def Slot.mk {dom : DomainConfig} {S W : Type} {τ : Type}
    (read : Signal dom S → Signal dom τ)
    (update : Signal dom τ → W → W) : Slot dom S W τ :=
  (read, update)

end Circuit

/-- Register handle = `(liveRead, slot)` Prod.

    Same rationale as `Slot` — a Prod alias rather than a
    `structure`, so accesses through `.1` / `.2` ride on the
    existing elaborator rules. -/
@[reducible] def Reg (dom : DomainConfig) (S : Type) (W : Type) (τ : Type) : Type :=
  Signal dom τ × Circuit.Slot dom S W τ

@[reducible] def Reg.liveRead {dom : DomainConfig} {S W : Type} {τ : Type}
    (r : Reg dom S W τ) : Signal dom τ := r.1

@[reducible] def Reg.slot {dom : DomainConfig} {S W : Type} {τ : Type}
    (r : Reg dom S W τ) : Circuit.Slot dom S W τ := r.2

@[reducible] def Reg.mk {dom : DomainConfig} {S W : Type} {τ : Type}
    (liveRead : Signal dom τ) (slot : Circuit.Slot dom S W τ) : Reg dom S W τ :=
  (liveRead, slot)

/-- A `Reg dom S τ` coerces to its live `Signal dom τ` read.
    Lets user code use `cnt` directly anywhere a `Signal dom τ`
    is expected (e.g. as the rhs of `Circuit.next` or
    `Signal.mux`), without needing an explicit `Circuit.read`
    or `.1`. -/
instance {dom : DomainConfig} {S W τ : Type} : CoeHead (Reg dom S W τ) (Signal dom τ) where
  coe r := r.1

/-- `CoeOut`: lets Lean coerce a `Reg` to a `Signal` even when
    the expected type isn't fully known (e.g. when both
    arguments to `Signal.mux` need coercion and neither side
    pins down the `α` first).  `CoeOut` is checked when going
    *from* a concrete known type, not *to* one, so it triggers
    on a `Reg` lhs regardless of whether the target Signal's
    `τ` is yet determined. -/
instance {dom : DomainConfig} {S W τ : Type} : CoeOut (Reg dom S W τ) (Signal dom τ) where
  coe r := r.1

/-! ### Reg-typed arithmetic / bitwise overloads.

    `return a + b` (where `a b : Reg dom S W (BitVec n)`) goes
    through the `CoeHead Reg → Signal` instance, which then
    drives Lean's `HAdd` resolution via the Signal overload's
    `(· + ·) <$> a <*> b` Applicative lift.  Under the
    ρ-generic `runCircuitH`, the Applicative path leaks the
    Stream's `t : Nat` binder into wire translation (the same
    failure mode this whole edge case keeps hitting).

    The fix is to short-circuit the coerce: provide a Reg-Reg
    overload that lowers straight to the Signal-Signal HAdd
    instance, skipping the typeclass projection.  Lean prefers
    the more specific Reg overload, so `a + b` resolves here
    instead of going through `CoeHead`. -/
instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HAdd (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := (a.1 + b.1 : Signal dom (BitVec n))

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HSub (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hSub a b := (a.1 - b.1 : Signal dom (BitVec n))

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HMul (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hMul a b := (a.1 * b.1 : Signal dom (BitVec n))

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HAnd (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hAnd a b := (a.1 &&& b.1 : Signal dom (BitVec n))

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HOr  (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hOr  a b := (a.1 ||| b.1 : Signal dom (BitVec n))

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HXor (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hXor a b := (a.1 ^^^ b.1 : Signal dom (BitVec n))


/-! ### Operator instances lifting `Reg` to `Signal`.

    `cnt + 1#8` doesn't trigger the `CoeHead` above because Lean
    resolves `HAdd cnt 1#8` by looking up `HAdd` with the lhs
    type `Reg …`, not by coercing first.  We provide the mixed
    `HAdd (Reg …) (BitVec n) (Signal …)` instances explicitly,
    mirroring the existing `Signal × BitVec` instances. -/

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HAdd (Reg dom S W (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hAdd a b := a.1 + b

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HSub (Reg dom S W (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hSub a b := a.1 - b

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HMul (Reg dom S W (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hMul a b := a.1 * b

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HAdd (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := a.1 + b.1

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HSub (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hSub a b := a.1 - b.1

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HMul (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hMul a b := a.1 * b.1

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HAdd (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := a.1 + b

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HAdd (Signal dom (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hAdd a b := a + b.1

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HXor (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hXor a b := a.1 ^^^ b.1

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HAnd (Reg dom S W (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hAnd a b := a.1 &&& b

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HAnd (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hAnd a b := a.1 &&& b.1

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HOr (Reg dom S W (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
  hOr a b := a.1 ||| b

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HOr (Reg dom S W (BitVec n)) (Reg dom S W (BitVec n)) (Signal dom (BitVec n)) where
  hOr a b := a.1 ||| b.1

instance {dom : DomainConfig} {S W : Type} {n : Nat} :
    HXor (Reg dom S W (BitVec n)) (BitVec n) (Signal dom (BitVec n)) where
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

/-- Pending-writes accumulator: one Signal per register slot.

    This replaces the function-composition `NextBuilder` as the thing the
    `Circuit` monad threads.  A write is a pure tuple update; `runCircuitH`
    bundles the final tuple into the register file once (flat, depth-1).
    See the `Slot` docstring for why the composed form was catastrophic for
    simulation (issue #95). -/
@[reducible] def SigList (dom : DomainConfig) : List Type → Type
  | []      => Unit
  | α :: αs => Signal dom α × SigList dom αs

end Circuit

/-- The Circuit monad — state-passing over the pending-writes
    accumulator `W` (a `Circuit.SigList` at `runCircuitH`: one pending
    Signal per register slot; see `Slot` for why this replaced the
    function-composition `NextBuilder`, issue #95). -/
def Circuit (dom : DomainConfig) (W : Type) (α : Type) : Type :=
  W → α × W

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
    the slot" semantics (last write wins, matching the macro).

    Note the accumulator parameter of `Circuit` here is the pending-writes
    tuple (a `Circuit.SigList` at `runCircuitH`), NOT the live-state shape:
    the write is pure tuple surgery and never touches the Signal graph. -/
@[reducible, inline] def next {W : Type} (r : Reg dom S W τ) (sig : Signal dom τ) :
    Circuit dom W Unit :=
  fun w => ((), r.slot.update sig w)

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
@[reducible, inline] def nextAny {W : Type} {α : Type} [AsSignal dom τ α]
    (r : Reg dom S W τ) (val : α) : Circuit dom W Unit :=
  next r (AsSignal.toSignal val)

/-- Read the live current-cycle Signal of a register handle.
    Just a projection — there for symmetry with `next`. -/
@[reducible, inline] def read {W : Type} (r : Reg dom S W τ) : Signal dom τ := r.liveRead

end Circuit

/-! ### `HasDomain ρ dom` — outParam-style typeclass that walks
    a return type ρ and reports the unique `DomainConfig` of
    every `Signal` leaf it contains.

    `runCircuitH`'s ρ-generalisation (single Signal / tuple of
    Signals / user record packing several Signals) lets the body
    return any Lean value, but the surrounding `Signal.loop`
    needs `dom` to be a specific `DomainConfig` value, not a
    metavariable.  Without this class, type inference can pull
    `dom` out of `ρ` only when `ρ` is *literally* `Signal dom τ`
    — a Prod or record wrapping Signal leaves it inaccessible to
    the elaborator.

    `dom` is `outParam` so it's inferred from `ρ`; one instance
    per shape walks the type structurally.  User-defined records
    can pick up a `HasDomain` instance via a one-line manual
    `instance : HasDomain MyOut dom := ⟨⟩` (any single-`dom`
    record qualifies; the instance is empty because the class
    carries no methods — it's purely an inference hint). -/
class HasDomain (ρ : Type) (dom : outParam DomainConfig)

/-- Base case: a single `Signal dom τ` carries `dom`. -/
instance {dom : DomainConfig} {τ : Type} :
    HasDomain (Signal dom τ) dom where

/-- Recursive case: a `Prod` of two values whose `HasDomain`
    instances agree on `dom` carries the same `dom`.  If the two
    sides disagree, instance search fails with a clear error
    rather than silently picking one. -/
instance {α β : Type} {dom : DomainConfig}
    [HasDomain α dom] [HasDomain β dom] :
    HasDomain (Prod α β) dom where

/-! ### `SignalLeaves` — flatten ρ into a list of its Signal
    leaves so the wire-translation compiler can emit one output
    port per leaf.

    Companion of `HasDomain`.  `toLeaves r` walks the value
    structurally and produces a `(name, Σ τ, Signal dom τ)`
    triple for every Signal slot in `r`.  The compiler's
    `synthesizeCombinational` reads the list and registers each
    leaf as its own Verilog wire, so
    `circuit do { … return ⟨a, b, c⟩ }` (or its record-literal
    equivalent) yields three real `output` ports rather than
    one bundled `bundle2` blob.

    The class is `outParam ρ` — driven by the user value;
    `dom` is `outParam` so instance search can resolve from
    `ρ`.  Base instances handle `Signal dom τ`, `Prod α β`,
    `Unit`, and `PUnit`.  User records pick up a derived
    instance via `deriving SignalLeaves`. -/
class SignalLeaves (ρ : Type) (dom : outParam DomainConfig) where
  /-- Walk `r` and emit one (label, τ, signal) record per
      `Signal dom τ` leaf.  The label is intended for output-
      port naming on the Verilog side; for unlabelled leaves
      (`Signal dom τ` at the top level, `Prod`'s sides) we
      pass `none` and the compiler invents a positional name. -/
  toLeaves : ρ → List (Option String × (Σ τ, Signal dom τ))

/-- Base case: a single `Signal dom τ` is one anonymous leaf. -/
@[reducible] instance {dom : DomainConfig} {τ : Type} :
    SignalLeaves (Signal dom τ) dom where
  toLeaves s := [(none, ⟨τ, s⟩)]

/-- Prod: concatenate the two sides' leaves, left first. -/
@[reducible] instance {dom : DomainConfig} {α β : Type}
    [SignalLeaves α dom] [SignalLeaves β dom] :
    SignalLeaves (Prod α β) dom where
  toLeaves p := SignalLeaves.toLeaves p.fst ++ SignalLeaves.toLeaves p.snd

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
@[reducible] def RegList (dom : DomainConfig) (S W : Type) : List Type → Type
  | []      => Unit
  | α :: αs => Reg dom S W α × RegList dom S W αs

/-- Build a `RegList dom S W αs` by walking down `αs`.

    Read lenses are pure `Signal`-level chains of `Signal.map Prod.fst /
    Prod.snd` — the same primitives Sparkle's IR elaborator already lowers.

    Write "lenses" are pure tuple updates into the pending-writes
    accumulator: `lift` lifts an update on the local `SigList` suffix into
    an update on the full accumulator `W`.  No Signal node is built on the
    write path — this flatness is the issue-#95 fix (see `Slot`). -/
@[reducible] def mkRegList {dom : DomainConfig} {S W : Type}
    (liveOuter : Signal dom S) :
    (αs : List Type) →
    (readSig : Signal dom S → Signal dom (HList αs)) →
    (lift : (Circuit.SigList dom αs → Circuit.SigList dom αs) → W → W) →
    RegList dom S W αs
  | [],       _,    _      => ()
  | α :: αs', readSig, lift =>
    let headReadSig : Signal dom S → Signal dom α :=
      fun s => Signal.map Prod.fst (readSig s)
    let tailReadSig : Signal dom S → Signal dom (HList αs') :=
      fun s => Signal.map Prod.snd (readSig s)
    let headWrite : Signal dom α → W → W :=
      fun n => lift (fun sl => (n, sl.2))
    let tailLift : (Circuit.SigList dom αs' → Circuit.SigList dom αs') → W → W :=
      fun f => lift (fun sl => (sl.1, f sl.2))
    let slot : Circuit.Slot dom S W α :=
      Circuit.Slot.mk headReadSig headWrite
    let head : Reg dom S W α :=
      Reg.mk (headReadSig liveOuter) slot
    let tail := mkRegList liveOuter αs' tailReadSig tailLift
    (head, tail)

/-- The "everything holds" seed for the pending-writes accumulator: each
    slot's entry is its own live read.  A slot that is never written keeps
    its value; a written slot's entry is replaced by `Circuit.next`. -/
@[reducible] def mkHolds {dom : DomainConfig} :
    (αs : List Type) → (live : Signal dom (HList αs)) → Circuit.SigList dom αs
  | [],       _    => ()
  | _ :: αs', live =>
    (Signal.map Prod.fst live, mkHolds αs' (Signal.map Prod.snd live))

/-- One `Signal.register` per slot, fed DIRECTLY by that slot's pending
    Signal — no projection of a bundled next-state, no reconstruction.
    Pack the register outputs back into a `Signal dom (HList αs)`.

    Reducible so the synth elaborator unfolds through it to the underlying
    `Signal.register` / `bundle2` chain. -/
@[reducible, inline] def packRegister {dom : DomainConfig} :
    (αs : List Type) → HList αs → Circuit.SigList dom αs → Signal dom (HList αs)
  | [],       _,    _      => Signal.pure ()
  | _ :: αs', init, writes =>
    bundle2 (Signal.register init.1 writes.1)
            (packRegister αs' init.2 writes.2)

/-- Generic `runCircuit` taking any HList of initial values.
    The body receives a matching `RegList` of register handles
    and returns an arbitrary `ρ`.

    `ρ` is *unconstrained*: it can be a single `Signal dom τ`,
    a tuple `(Signal dom τ₁, Signal dom τ₂)`, a user-defined
    record packing several Signals (e.g. an Ethernet `RxOut`),
    or any combination.  The synthesis elaborator
    (`Sparkle/Compiler/Elab.lean`) walks `ρ` structurally and
    emits one Verilog wire per Signal leaf, so multi-output
    blocks come out of `circuit do { … return ⟨a, b, c⟩ }`
    naturally without a `bundle2`-shaped contortion.

    The `Circuit` accumulator is `Circuit.SigList dom αs` — the flat
    pending-writes tuple seeded by `mkHolds` — rather than the historical
    `NextBuilder` function composition.  See `Slot` for why (issue #95).

    `[HListWireable αs]` requires every slot type to be
    `Wireable`, gating non-synthesisable types at the call
    site instead of the synth elaborator. -/
@[reducible] def runCircuitH {dom : DomainConfig} {αs : List Type} {ρ : Type}
    [HasDomain ρ dom]
    [HListWireable αs] [Inhabited (HList αs)]
    (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
            Circuit dom (Circuit.SigList dom αs) ρ) : ρ :=
  let idRead : Signal dom (HList αs) → Signal dom (HList αs) := fun s => s
  let idLift : (Circuit.SigList dom αs → Circuit.SigList dom αs) →
      Circuit.SigList dom αs → Circuit.SigList dom αs := fun f => f
  let stateLoop : Signal dom (HList αs) :=
    Signal.loop (α := HList αs) (fun live =>
      let regs := mkRegList live αs idRead idLift
      let bResult := body regs (mkHolds αs live)
      packRegister αs inits bResult.snd)
  let regs := mkRegList stateLoop αs idRead idLift
  (body regs (mkHolds αs stateLoop)).fst

end Sparkle.Core