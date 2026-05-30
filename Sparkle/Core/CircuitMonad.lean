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

/-- Read the live current-cycle Signal of a register handle.
    Just a projection — there for symmetry with `next`. -/
@[reducible, inline] def read (r : Reg dom S τ) : Signal dom τ := r.liveRead

end Circuit

/-! ### Concrete arity helpers (do-notation surface).

    `body` is a `Circuit dom S (Signal dom ρ)` — Lean's standard
    `do`-notation desugars through the Monad instance above.

    The IR elaborator recognises `Bind.bind` / `Pure.pure` when
    specialised to `Sparkle.Core.Circuit` (see
    `Sparkle/Compiler/Elab.lean`) and force-reduces them with
    `withTransparency .all`, so the typeclass projection is no
    longer opaque at synthesis time. -/

/-- Single-register circuit. -/
@[reducible, inline] def runCircuit1 {dom : DomainConfig} {τ₀ ρ : Type} [Inhabited τ₀]
    (init₀ : τ₀)
    (body : Reg dom τ₀ τ₀ → Circuit dom τ₀ (Signal dom ρ)) : Signal dom ρ :=
  let slot : Circuit.Slot dom τ₀ τ₀ :=
    Circuit.Slot.mk id (fun next _ => next)
  let stateLoop : Signal dom τ₀ :=
    Signal.loop (α := τ₀) (fun live =>
      let r : Reg dom τ₀ τ₀ := Reg.mk live slot
      let bResult := body r id
      let b' : Circuit.NextBuilder dom τ₀ := bResult.snd
      let nextState : Signal dom τ₀ := b' live
      Signal.register init₀ nextState)
  let r : Reg dom τ₀ τ₀ := Reg.mk stateLoop slot
  let outResult := body r id
  outResult.fst

/-- Two-register circuit — state shape `τ₀ × τ₁`. -/
@[reducible, inline] def runCircuit2 {dom : DomainConfig} {τ₀ τ₁ ρ : Type} [Inhabited τ₀] [Inhabited τ₁]
    (init₀ : τ₀) (init₁ : τ₁)
    (body : Reg dom (τ₀ × τ₁) τ₀ → Reg dom (τ₀ × τ₁) τ₁ →
            Circuit dom (τ₀ × τ₁) (Signal dom ρ)) : Signal dom ρ :=
  let S := τ₀ × τ₁
  let slot0 : Circuit.Slot dom S τ₀ :=
    Circuit.Slot.mk (Signal.map Prod.fst)
                    (fun n s => bundle2 n (Signal.map Prod.snd s))
  let slot1 : Circuit.Slot dom S τ₁ :=
    Circuit.Slot.mk (Signal.map Prod.snd)
                    (fun n s => bundle2 (Signal.map Prod.fst s) n)
  let stateLoop : Signal dom S :=
    Signal.loop (α := S) (fun live =>
      let r0 : Reg dom S τ₀ := Reg.mk (Signal.map Prod.fst live) slot0
      let r1 : Reg dom S τ₁ := Reg.mk (Signal.map Prod.snd live) slot1
      let bResult := body r0 r1 id
      let b' : Circuit.NextBuilder dom S := bResult.snd
      let nextState : Signal dom S := b' live
      let nextS : Signal dom S :=
        bundle2 (Signal.register init₀ (Signal.map Prod.fst nextState))
                (Signal.register init₁ (Signal.map Prod.snd nextState))
      nextS)
  let r0 : Reg dom S τ₀ := Reg.mk (Signal.map Prod.fst stateLoop) slot0
  let r1 : Reg dom S τ₁ := Reg.mk (Signal.map Prod.snd stateLoop) slot1
  (body r0 r1 id).fst

end Sparkle.Core
