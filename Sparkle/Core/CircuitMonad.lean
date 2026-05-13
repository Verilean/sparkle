/-
  Sparkle.Core.CircuitMonad — proof-of-concept ST-style monad
  replacement for `Signal.circuit do`.

  Why this exists.  The current surface DSL —

      Signal.circuit (dom := dom) do
        let count ← Signal.reg 0#8
        count <~ count + 1#8
        return count

  — is a custom-syntax macro that pattern-matches four hard-coded
  statement shapes and reassembles them into a `Signal.loop`.
  Anything outside those shapes (`if` / `match` / `for` / local
  helper bindings) must be smuggled in via plain `let`, and
  type errors surface as generic "match failure on circuitStmt"
  rather than typed diagnostics.

  This file builds a real monad — `Circuit σ dom τ α` — so the
  user writes the same logic as plain Lean:

      def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
        runCircuit fun _ => do
          let count ← Circuit.reg 0#8
          Circuit.next count (count.read + 1#8)
          pure count.read

  and `if`/`match`/helper `let`s come along for free.

  Design.  Each `Circuit σ dom τ α` action is a **function from
  the run-state register tuple to (α, list of registers)**.  The
  σ-rank phantom keeps register handles from leaking across
  nested `runCircuit` invocations.  `Circuit.reg init` appends
  a slot and returns a handle whose `read` projects the
  live-tuple Signal at the handle's index.  `Circuit.next` records
  a next-cycle Signal for a slot.  `runCircuit` calls
  `Signal.loop` once, threading the live tuple through the body
  and assembling the next-cycle tuple from the recorded entries.

  Status: prototype.  Restricted to a single element type per
  circuit (every register holds a `τ` for the same `τ`); the
  follow-up will lift this to `HVect`-style per-register types
  via a state descriptor.  The macro-based `Signal.circuit do`
  remains the supported surface DSL until this PoC reaches
  parity.
-/

import Sparkle.Core.Signal
import Sparkle.Compiler.InlineAttr

namespace Sparkle.Core

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Circuit

/-! ### Internal state -/

/-- Accumulator for one `runCircuit` body pass.  We record:

* `inits` — initial values, in declaration order.  Used both for
  fresh-index allocation in `Circuit.reg` and as the `init`
  argument to `Signal.register` when `runCircuit` closes the loop.
* `nexts` — for each declared slot, the user's next-cycle Signal
  if they called `Circuit.next` for it, or `none` meaning
  "hold value" (the register feeds itself).

Both arrays grow in lock-step; `nexts[i]` is the assignment for
the register declared at position `i` in `inits`. -/
structure CircuitState (dom : DomainConfig) (τ : Type) : Type where
  inits : Array τ
  nexts : Array (Option (Signal dom τ))

namespace CircuitState

@[inline] def empty {dom : DomainConfig} {τ : Type} : CircuitState dom τ :=
  { inits := #[], nexts := #[] }

end CircuitState

end Circuit

/-- A handle to one register slot inside a `Circuit σ dom τ α`
    action.  The σ phantom keeps the handle from escaping its
    enclosing `runCircuit` (rank-2 quantifier on the body),
    exactly like `ST`'s `STRef σ`.

    `liveRead` is the projection-into-the-live-tuple Signal,
    captured at `Circuit.reg`-time.  It refers to the *current
    cycle*'s value of this register, so `r.read + 1` reads the
    current value and feeds the sum back via `Circuit.next`. -/
structure Reg (σ : Type) (dom : DomainConfig) (τ : Type) [Inhabited τ] : Type where
  private mk ::
  idx : Nat
  liveRead : Signal dom τ

/-- The Circuit monad — state-passing over `CircuitState dom τ`.

    Restricted (in this PoC) to a single per-circuit element
    type `τ`: every register declared inside the same
    `runCircuit` invocation has the same payload type.  That
    matches the most common tutorial case (8-bit counter,
    3-bit FSM, BitVec-N pipeline) without dragging in
    heterogeneous-list infrastructure.

    The σ-rank phantom keeps `Reg σ` handles inside their
    enclosing `runCircuit`. -/
def Circuit (σ : Type) (dom : DomainConfig) (τ : Type) (α : Type) : Type :=
  Circuit.CircuitState dom τ → α × Circuit.CircuitState dom τ

namespace Circuit

variable {σ : Type} {dom : DomainConfig} {τ : Type} {α β : Type}

@[inline] def pure' (a : α) : Circuit σ dom τ α := fun s => (a, s)

@[inline] def bind (m : Circuit σ dom τ α) (k : α → Circuit σ dom τ β) :
    Circuit σ dom τ β :=
  fun s => let (a, s') := m s; k a s'

instance : Monad (Circuit σ dom τ) where
  pure := Circuit.pure'
  bind := Circuit.bind

/-- Read the current-cycle Signal of a register handle. -/
@[inline] def read [Inhabited τ] (r : Reg σ dom τ) : Signal dom τ :=
  r.liveRead

end Circuit

/-- Allocate a fresh register in the current circuit.

    Internal — takes the **live tuple Signal** as an explicit
    argument so it can build the `liveRead` projection at
    declaration time.  `runCircuit` partially-applies this
    against its own loop-bound live tuple before handing the
    resulting `Circuit σ dom τ` over to the user.

    Users see the partially-applied alias `Circuit.reg`,
    declared via `runCircuit`'s closure, which takes only the
    init value. -/
private def Circuit.regAux {σ : Type} {dom : DomainConfig} {τ : Type} [Inhabited τ]
    (liveTuple : Signal dom (Array τ)) (init : τ) :
    Circuit σ dom τ (Reg σ dom τ) :=
  fun s =>
    let i := s.inits.size
    let live : Signal dom τ := liveTuple.map (fun arr => arr.getD i init)
    let r : Reg σ dom τ := { idx := i, liveRead := live }
    let s' : CircuitState dom τ := {
      inits := s.inits.push init,
      nexts := s.nexts.push none
    }
    (r, s')

/-- Record a next-cycle Signal for a register.  Last assignment
    wins (matches the macro's left-to-right shadow semantics). -/
def Circuit.next {σ : Type} {dom : DomainConfig} {τ : Type} [Inhabited τ]
    (r : Reg σ dom τ) (sig : Signal dom τ) : Circuit σ dom τ Unit :=
  fun s => ((), { s with nexts := s.nexts.set! r.idx (some sig) })

/-- Build the next-cycle register-array Signal from a finished
    `CircuitState`.

    For each slot index `i`:
    * if the user called `Circuit.next r sig`, use `sig`
    * otherwise feed the live read of slot `i` back unchanged
      (the "hold" semantics)

    We then fold the per-slot Signals into a single
    `Signal dom (Array τ)` using `Functor`/`Applicative` ops on
    `Signal` (no bespoke `map₂` — the Functor + Applicative
    instances Signal already provides give us
    `(· ::-into-array)` lifting for free). -/
private def Circuit.buildNextTuple {dom : DomainConfig} {τ : Type} [Inhabited τ]
    (live : Signal dom (Array τ))
    (st : Circuit.CircuitState dom τ) : Signal dom (Array τ) :=
  let n := st.inits.size
  let initArr : Signal dom (Array τ) := Signal.pure (Array.mkEmpty n)
  -- Fold slots in order, appending each register's *current*
  -- value to the accumulator.
  --
  -- Crucially, every slot is wrapped in `Signal.register init
  -- nextSig` here — without that wrap the loop would have no
  -- cycle delay and `Signal.loop`'s fix-point would diverge
  -- (or, with memoisation, return the very first computed
  -- value forever, which is the bug an earlier version of this
  -- file hit on the counter sample: `[1, 1, 1, …]` instead of
  -- `[0, 1, 2, …]`).
  --
  -- `nextSig` for a slot is the user's `Circuit.next` argument
  -- if they assigned one; otherwise we feed the live value back
  -- unchanged ("hold" semantics, matching the macro).
  (List.range n).foldl (init := initArr) fun acc i =>
    let init := st.inits.getD i default
    let nextSig : Signal dom τ :=
      match st.nexts[i]? with
      | some (some s) => s
      | _ =>
        -- Hold: feed the live read back unchanged.
        live.map (fun arr => arr.getD i init)
    let slot : Signal dom τ := Signal.register init nextSig
    (fun a v => a.push v) <$> acc <*> slot

/-- Close a circuit into the final Signal.

    The user body is universally quantified over `σ`, so any
    register handle the body creates is statically incompatible
    with handles from any other `runCircuit` call — that's the
    ST-style escape protection.  Concretely the body has type

        ∀ σ, (τ → Circuit σ dom τ (Reg σ dom τ)) → Circuit σ dom τ (Signal dom τ)

    i.e. it receives the partially-applied `Circuit.reg` (live
    tuple already plumbed in) and a fresh `CircuitState`, and
    produces the value the user wants out of the circuit
    (typically the projection of one register, but it can be
    any `Signal dom τ` built from handle reads + Signal
    combinators).

    The Signal returned to the caller is the body's `α`
    (already a `Signal dom τ` whose `live` projections refer to
    the closed-loop tuple). -/
-- Note on synthesis: `runCircuit` does NOT carry
-- `@[inline_hardware]` — that tag only helps the elaborator
-- if it can also unfold the body lambda, which it can't here
-- because the body is rank-2 quantified over σ.  The PoC's
-- IR-recognition gap is documented in
-- `Tests/CircuitMonadTest.lean` §2.  Adding the tag here would
-- be misleading.
def runCircuit {dom : DomainConfig} {τ : Type} [Inhabited τ]
    (body : ∀ σ, (τ → Circuit σ dom τ (Reg σ dom τ)) →
                  Circuit σ dom τ (Signal dom τ)) :
    Signal dom τ :=
  -- The fixed-point Signal of register arrays — its value at
  -- cycle `t` is the array of all register values at cycle `t`.
  let tuple : Signal dom (Array τ) :=
    Signal.loop (α := Array τ) (fun live =>
      let regAux := Circuit.regAux (σ := Unit) (τ := τ) live
      let (_, st) := body Unit regAux Circuit.CircuitState.empty
      Circuit.buildNextTuple live st)
  -- Re-run the body one more time with the closed tuple to get
  -- the user's output Signal.  The body is pure (it only
  -- threads `CircuitState` and reads from `live`), so running
  -- it twice with the same live tuple is sound; the second run
  -- discards its `CircuitState` changes because we already
  -- baked them into `tuple`.
  let regAux := Circuit.regAux (σ := Unit) (τ := τ) tuple
  let (out, _) := body Unit regAux Circuit.CircuitState.empty
  out

/-! ### Worked example

`counter` written in the new monad form, mirroring the
macro version's behaviour. -/

namespace Example

/-- An 8-bit counter that increments every cycle starting at 0.
    Equivalent to the macro version

        def counter : Signal dom (BitVec 8) :=
          Signal.circuit do
            let c ← Signal.reg 0#8
            c <~ c + 1#8
            return c

    written through the monad PoC. -/
def counter {dom : DomainConfig} : Signal dom (BitVec 8) :=
  runCircuit fun _σ reg => do
    let c ← reg 0#8
    Circuit.next c (Circuit.read c + 1#8)
    Pure.pure (Circuit.read c)

/-- Sample the first 5 cycles.  Not pin-checked at compile
    time: `Signal.val` reaches through an `@[implemented_by]`
    FFI shim that the kernel-side native_decide / decide
    interpreters can't reach, exactly like the rest of
    `Sparkle.Core.Signal`.  Run `#eval Example.counterSample`
    in a JIT-enabled `#eval` (e.g. inside the tutorial Docker
    image's xlean kernel) to see `[0, 1, 2, 3, 4]`.

    The fact that the *definition* type-checks already proves
    the surface API works: the `Circuit` monad's `do`-notation
    expands cleanly, the σ-rank quantifier prevents handle
    escape, and the worked example's `Signal dom (BitVec 8)`
    return type matches the macro version. -/
def counterSample : List (BitVec 8) :=
  let s : Signal Sparkle.Core.Domain.defaultDomain (BitVec 8) := counter
  (List.range 5).map (fun i => s.val i)

end Example

end Sparkle.Core
