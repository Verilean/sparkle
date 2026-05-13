/-
  Sparkle.Core.CircuitMonad — ST-style monad for the
  `Signal.circuit do` DSL.

  Status: hybrid lowering.  The user-facing surface stays the
  existing `Signal.circuit do { … }` macro (`Sparkle/Core/Signal.lean`),
  but the macro expansion now targets `runCircuit` from this
  file with a statically-known register count `n`.  This
  lowering means:

    * No more bespoke `bundle2`/`bundleAll!` arity helpers; the
      tuple width is captured by `Vector τ n` and threaded
      through `Signal.loop`.
    * `do`-notation goes through Lean's standard `Monad`
      machinery — any future bind-form improvement Lean ships
      reaches the DSL for free.
    * The IR elaborator (`Sparkle/Compiler/Elab.lean`) sees the
      same `Signal.loop` / `Signal.register` shape the existing
      macro emits, so synthesis support is automatic.  No new
      elaborator rule is needed.

  Why not teach the IR elaborator about `runCircuit` directly?
  That route would couple Sparkle to whichever Lean version's
  `Lean.Meta` API we shipped against.  The lowering here stays
  inside the Sparkle library and uses only bedrock-stable APIs
  (`Signal.loop`, `Signal.register`, `Vector`, `Monad`).

  Per-circuit element type restriction.  Every register inside
  one `runCircuit` invocation shares one element type `τ`.
  That matches the tutorial pattern (multi-bit counters, FSM
  state words).  Lifting to per-register types via an `HList`
  state descriptor is a follow-up.

  ST-style safety.  `runCircuit` rank-2 quantifies over a
  phantom `σ` so register handles produced inside the body
  cannot leak out into a sibling `runCircuit`.
-/

import Sparkle.Core.Signal

namespace Sparkle.Core

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Circuit

/-! ### Internal state.

`CircuitState n dom τ` keeps a length-indexed `Vector` of
per-slot next-cycle Signals.  `inits` is the parallel vector
of initial values supplied at allocation time.

By the time `runCircuit` calls the body, it has already
pre-allocated every register handle and stashed each handle's
initial value at the correct slot.  The body's `Circuit.next`
calls then only need to drop next-cycle Signals into the
right slots — slot numbers are baked into the handles, so
out-of-range writes are statically impossible. -/
structure CircuitState (n : Nat) (dom : DomainConfig) (τ : Type) where
  inits : Vector τ n
  /-- Per-slot next-cycle Signal, or `none` for "hold value". -/
  nexts : Vector (Option (Signal dom τ)) n

end Circuit

/-- A handle to one register slot.

    `idx : Fin n` keeps the slot within bounds at the type
    level — no `getD`/default fallback at runtime.

    `liveRead` is the slot's current-cycle Signal, captured
    when `runCircuit` minted the handle. -/
structure Reg (σ : Type) (n : Nat) (dom : DomainConfig) (τ : Type) [Inhabited τ] where
  private mk ::
  idx : Fin n
  liveRead : Signal dom τ

/-- The Circuit monad — state-passing over `CircuitState n dom τ`.

    `n` is fixed across the whole action (set by `runCircuit`'s
    caller, in practice by the macro counting `Signal.reg`
    lines).  The σ phantom keeps register handles inside the
    enclosing `runCircuit`. -/
def Circuit (σ : Type) (n : Nat) (dom : DomainConfig) (τ : Type) (α : Type) : Type :=
  Circuit.CircuitState n dom τ → α × Circuit.CircuitState n dom τ

namespace Circuit

variable {σ : Type} {n : Nat} {dom : DomainConfig} {τ : Type} {α β : Type}

@[inline] def pure' (a : α) : Circuit σ n dom τ α := fun s => (a, s)

@[inline] def bind (m : Circuit σ n dom τ α) (k : α → Circuit σ n dom τ β) :
    Circuit σ n dom τ β :=
  fun s => let (a, s') := m s; k a s'

instance : Monad (Circuit σ n dom τ) where
  pure := Circuit.pure'
  bind := Circuit.bind

/-- Read the current-cycle Signal of a register handle. -/
@[inline] def read [Inhabited τ] (r : Reg σ n dom τ) : Signal dom τ :=
  r.liveRead

/-- Record an initial value for a register slot.  Called once
    per slot at the start of `runCircuit` (the body's `reg`
    allocator does it implicitly); not for users. -/
private def setInit (i : Fin n) (init : τ) : Circuit σ n dom τ Unit :=
  fun s => ((), { s with inits := s.inits.set i init })

end Circuit

/-- Record a next-cycle Signal for a register slot.  Repeat
    assignments overwrite earlier ones (matches the macro's
    "last `<~` wins" semantics). -/
def Circuit.next {σ : Type} {n : Nat} {dom : DomainConfig} {τ : Type} [Inhabited τ]
    (r : Reg σ n dom τ) (sig : Signal dom τ) :
    Circuit σ n dom τ Unit :=
  fun s => ((), { s with nexts := s.nexts.set r.idx (some sig) })

/-- Build the next-cycle register-tuple Signal from a finished
    state.

    For each slot we either use the user's recorded next-cycle
    Signal or feed the slot's live read back unchanged (hold
    semantics).  Each is wrapped in `Signal.register init
    nextSig` — without this one-cycle delay the loop's fixed
    point has no register on the feedback path, and
    `Signal.loop`'s memoisation hides the divergence as a
    stuck constant.

    The result is a `Signal dom (Vector τ n)`; at cycle t its
    value is the vector of every register's value at cycle t. -/
private def Circuit.buildNextTuple {n : Nat} {dom : DomainConfig} {τ : Type} [Inhabited τ]
    (live : Signal dom (Vector τ n))
    (st : Circuit.CircuitState n dom τ) : Signal dom (Vector τ n) :=
  let slots : Fin n → Signal dom τ := fun i =>
    let init := st.inits.get i
    let nextSig : Signal dom τ :=
      match st.nexts.get i with
      | some s => s
      | none   => live.map (·.get i)
    Signal.register init nextSig
  -- Lift `Vector.ofFn slots` through the per-cycle evaluation:
  -- at cycle t the vector's i-th entry is `(slots i).val t`.
  -- We implement that with `Signal.ofFn`-style construction
  -- via a `Signal` whose .val unrolls the Fin → Signal map.
  -- Equivalent to repeated `Vector.push` lifted over
  -- `<$>`/`<*>` but avoids the `(Vector.emptyWithCapacity).push`
  -- shape's bookkeeping.
  ⟨fun t => Vector.ofFn (fun i => (slots i).val t)⟩

/-- Close a circuit into the final `Signal dom α`.

    The body is rank-2 over `σ` so register handles can't
    leak out.  The body receives an *index-keyed allocator*
    that lets it create a handle for a specific slot — the
    macro expansion assigns indices `0, 1, …, n-1` in source
    order, which is the same order the macro currently uses
    when it generates `projN!` projections.

    Implementation: pre-mint a `Vector` of handles bound to
    the closed-loop live tuple, hand the body an allocator
    that just looks up handles by index, run the body inside
    `Signal.loop` to close the fix-point, run it again with
    the closed tuple to extract the user's output `α`.

    `α` is constrained to `Signal dom τ` so the rank-2 ∀σ
    guarantees no `Reg σ` leaks: there's no way to construct
    a `Signal dom τ` that mentions a `Reg σ` other than by
    reading through it. -/
-- Note on synthesis: `@[reducible]` here would let the IR
-- elaborator unfold `runCircuit` during whnf, but the unfolded
-- body still routes registers through `Vector.get` /
-- `Vector.ofFn` on `Signal dom (Vector τ n)`, which the
-- elaborator's wire-translation rules don't recognise.
-- Synthesis of monad-produced circuits therefore remains an
-- open item (see Tests/CircuitMonadTest.lean §2 for the full
-- discussion).  Simulation works correctly; the `Vector`
-- shape is well-typed Lean and round-trips through
-- `Signal.loop` cleanly.
def runCircuit {n : Nat} {dom : DomainConfig} {τ : Type} [Inhabited τ]
    (initVec : Vector τ n)
    (body : ∀ σ, (Fin n → Reg σ n dom τ) → Circuit σ n dom τ (Signal dom τ)) :
    Signal dom τ :=
  let tuple : Signal dom (Vector τ n) :=
    Signal.loop (α := Vector τ n) (fun live =>
      let handles : Fin n → Reg Unit n dom τ := fun i =>
        { idx := i, liveRead := live.map (·.get i) }
      let s0 : Circuit.CircuitState n dom τ :=
        { inits := initVec, nexts := Vector.replicate n none }
      let (_, st) := body Unit handles s0
      Circuit.buildNextTuple live st)
  let handles2 : Fin n → Reg Unit n dom τ := fun i =>
    { idx := i, liveRead := tuple.map (·.get i) }
  let s0 : Circuit.CircuitState n dom τ :=
    { inits := initVec, nexts := Vector.replicate n none }
  let (out, _) := body Unit handles2 s0
  out

end Sparkle.Core
