/-
  RV32 IDEX flush/squash — sequential invariant (LTL-style)

  This is invariant B from `docs/RV32_Architecture_Status.md` §2.2:

      "When mret commits at cycle N, the IDEX inst at cycle N+1 is
       squashed-NOP and writes no state."

  We prove the underlying *generic* fact: for any IDEX latch driven
  by the canonical pattern

      register init (mux freezeIDEX old (mux squash (pure init) new))

  if `freezeIDEX = false` and `squash = true` at cycle t, the
  register's value at cycle t+1 equals `init`.

  In `SoC.lean`, every IDEX control bit (regWrite, memWrite, isMret,
  isCsr, isEcall, branch, jump, ...) follows this pattern with
  `init = false` (or `0#k`), so this lemma covers them all.

  The connection to invariant B specifically: `flushOrDelay`
  (line 1062) includes `idex_isMret` as a disjunct, and `squash`
  (line 1296) includes `flushOrDelay`. So at the cycle where
  `idex_isMret = true ∧ ¬freezeIDEX`, the next cycle's IDEX has
  every control bit cleared.

  Reachability of `idex_isMret = true ∧ freezeIDEX` is a separate
  question (handled by reasoning about the AMO/PTW state machines:
  if mret is in IDEX, AMO writeback or PTW finished a cycle earlier
  or freezeIDEX would have prevented mret from advancing). We do NOT
  prove that here; we prove the *if* direction unconditionally.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Verification.Temporal

namespace Sparkle.IP.RV32.Pipeline

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.Temporal

/-! ## The IDEX-bit latch model

  The exact expression in SoC.lean is repeated dozens of times. We
  parameterise over the type `α`, the init value, and the three input
  signals (freeze, squash, "old", "new"). -/

/-- Next-state for an IDEX control-bit latch. -/
def idexNextSignal {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze squash : Signal dom Bool)
    (old new : Signal dom α) (init : α) : Signal dom α :=
  Signal.mux freeze old (Signal.mux squash (Signal.pure init) new)

/-- The IDEX control-bit latch as a register. -/
def idexLatchSignal {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze squash : Signal dom Bool)
    (old new : Signal dom α) (init : α) : Signal dom α :=
  Signal.register init (idexNextSignal freeze squash old new init)

/-! ## Sequential invariant — the squash guarantee -/

/--
  **Generic IDEX squash guarantee.**

  If `freeze = false` and `squash = true` at cycle `t`, the IDEX
  latch's value at cycle `t+1` is `init` — the squashed value. -/
theorem idex_squash_clears_next_cycle {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze squash : Signal dom Bool)
    (old new : Signal dom α) (init : α) (t : Nat) :
    freeze.atTime t = false →
    squash.atTime t = true →
    (idexLatchSignal freeze squash old new init).atTime (t + 1) = init := by
  intro h_freeze h_squash
  unfold idexLatchSignal idexNextSignal
  unfold Signal.atTime
  -- (register init nextSig).val (t+1) = nextSig.val t
  show (Signal.register init _).val (t + 1) = init
  -- Goal: (mux freeze old (mux squash (pure init) new)).val t = init
  show (Signal.mux freeze old (Signal.mux squash (Signal.pure init) new)).val t = init
  unfold Signal.mux
  show (if freeze.val t then _ else _) = init
  rw [show freeze.val t = false from h_freeze]
  show (if squash.val t then _ else _) = init
  rw [show squash.val t = true from h_squash]
  rfl

/--
  **LTL phrasing**: ∀ t, ¬freeze t ∧ squash t → next-cycle latch = init. -/
theorem idex_squash_clears_LTL {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze squash : Signal dom Bool)
    (old new : Signal dom α) (init : α) :
    ∀ t, freeze.atTime t = false → squash.atTime t = true →
         (idexLatchSignal freeze squash old new init).atTime (t + 1) = init :=
  fun t => idex_squash_clears_next_cycle freeze squash old new init t

/-! ## Specialisation: invariant B — mret squashes IDEX next cycle

  In SoC.lean, `flushOrDelay` is a Bool signal that includes
  `idex_isMret` as a disjunct, and `squash` includes `flushOrDelay`
  as a disjunct. So `idex_isMret.val t = true → squash.val t = true`.
  Combined with `freeze.val t = false`, the generic lemma above
  yields invariant B for every IDEX control bit. -/

/--
  **Invariant B (mret idempotency on stale IDEX).**

  If mret is in IDEX at cycle `t`, and IDEX is not frozen, then any
  IDEX control bit at cycle `t+1` is `init` — the squashed value.

  Hypothesis `h_squash_includes_mret` captures the structural fact
  that `squash` includes `idex_isMret`'s disjunct (encoded as: when
  `idex_isMret.val t = true`, `squash.val t = true`). This is true
  for the SoC.lean wiring at the time of writing. -/
theorem mret_squashes_idex_next_cycle {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze squash idex_isMret : Signal dom Bool)
    (old new : Signal dom α) (init : α) (t : Nat)
    (h_squash_includes_mret :
      idex_isMret.atTime t = true → squash.atTime t = true) :
    idex_isMret.atTime t = true →
    freeze.atTime t = false →
    (idexLatchSignal freeze squash old new init).atTime (t + 1) = init := by
  intro h_mret h_freeze
  exact idex_squash_clears_next_cycle freeze squash old new init t
    h_freeze (h_squash_includes_mret h_mret)

/-- Symmetric for sret. -/
theorem sret_squashes_idex_next_cycle {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze squash idex_isSret : Signal dom Bool)
    (old new : Signal dom α) (init : α) (t : Nat)
    (h_squash_includes_sret :
      idex_isSret.atTime t = true → squash.atTime t = true) :
    idex_isSret.atTime t = true →
    freeze.atTime t = false →
    (idexLatchSignal freeze squash old new init).atTime (t + 1) = init := by
  intro h_sret h_freeze
  exact idex_squash_clears_next_cycle freeze squash old new init t
    h_freeze (h_squash_includes_sret h_sret)

/-! ## Pure-side spec for the squash inclusion

  The structural fact `idex_isMret.val t = true → squash.val t = true`
  is itself a Bool theorem about how `squash` is constructed:

      squash = (stall ∧ ¬freezeIDEX) ∨ flushOrDelay ∨ stallDelay
      flushOrDelay = flush ∨ flushDelay
      flush = branchTaken ∨ idex_jump ∨ trap_taken ∨ idex_isMret ∨ ...

  Since `flush ⊇ idex_isMret`, we have `squash ⊇ idex_isMret`.
  Encoded as a `decide`-closed proposition over Bool^n: -/

/-- `squash` includes `idex_isMret` if it's built as the standard
    `(stallTerm) ∨ flushOrDelay ∨ stallDelay` disjunction with
    `flushOrDelay ⊇ idex_isMret`. -/
@[inline] def squashPure
    (stallAndNotFreeze flushOrDelay stallDelay : Bool) : Bool :=
  stallAndNotFreeze || flushOrDelay || stallDelay

@[inline] def flushOrDelayContainsMretPure
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay : Bool) : Bool :=
  let flush := branchTaken || idex_jump || trap_taken || idex_isMret
                || idex_isSret || idex_isSFenceVMA || dMMURedirect
  flush || flushDelay

/-- The pure structural inclusion: `idex_isMret → flushOrDelay`. -/
theorem flushOrDelay_contains_mret
    (branchTaken idex_jump trap_taken idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay : Bool) :
    flushOrDelayContainsMretPure
      branchTaken idex_jump trap_taken true idex_isSret
      idex_isSFenceVMA dMMURedirect flushDelay = true := by
  revert branchTaken idex_jump trap_taken idex_isSret
    idex_isSFenceVMA dMMURedirect flushDelay
  decide

/-- `idex_isMret → squash` (combinational, pure). -/
theorem squash_contains_mret
    (stallAndNotFreeze flushOrDelay stallDelay : Bool) :
    flushOrDelay = true →
    squashPure stallAndNotFreeze flushOrDelay stallDelay = true := by
  intro h
  unfold squashPure
  rw [h]
  cases stallAndNotFreeze <;> cases stallDelay <;> rfl

end Sparkle.IP.RV32.Pipeline
