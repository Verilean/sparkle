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

/-- Symmetric for trap_taken (cornerstone of invariants A and E). -/
theorem trap_squashes_idex_next_cycle {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze squash trap_taken : Signal dom Bool)
    (old new : Signal dom α) (init : α) (t : Nat)
    (h_squash_includes_trap :
      trap_taken.atTime t = true → squash.atTime t = true) :
    trap_taken.atTime t = true →
    freeze.atTime t = false →
    (idexLatchSignal freeze squash old new init).atTime (t + 1) = init := by
  intro h_trap h_freeze
  exact idex_squash_clears_next_cycle freeze squash old new init t
    h_freeze (h_squash_includes_trap h_trap)

/-- Symmetric for dMMURedirect (cornerstone of invariant C). -/
theorem dMMURedirect_squashes_idex_next_cycle {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze squash dMMURedirect : Signal dom Bool)
    (old new : Signal dom α) (init : α) (t : Nat)
    (h_squash_includes_dMMU :
      dMMURedirect.atTime t = true → squash.atTime t = true) :
    dMMURedirect.atTime t = true →
    freeze.atTime t = false →
    (idexLatchSignal freeze squash old new init).atTime (t + 1) = init := by
  intro h_dmmu h_freeze
  exact idex_squash_clears_next_cycle freeze squash old new init t
    h_freeze (h_squash_includes_dMMU h_dmmu)


/-! ## Pure-side spec for the squash inclusion

  The structural fact `idex_isMret.val t = true → squash.val t = true`
  is itself a Bool theorem about how `squash` is constructed:

      squash = (stall ∧ ¬freezeIDEX) ∨ flushOrDelay ∨ stallDelay
      flushOrDelay = flush ∨ flushDelay
      flush = branchTaken ∨ idex_jump ∨ trap_taken ∨ idex_isMret ∨ ...

  Since `flush ⊇ idex_isMret`, we have `squash ⊇ idex_isMret`.
  Encoded as a `decide`-closed proposition over Bool^n: -/

/-- 7-way `flush` disjunction (~SoC.lean line 1093):

      flush = branchTaken ∨ idex_jump ∨ trap_taken ∨ idex_isMret
            ∨ idex_isSret ∨ idex_isSFenceVMA ∨ dMMURedirect -/
@[inline] def flushPure
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Bool) : Bool :=
  branchTaken || idex_jump || trap_taken || idex_isMret
    || idex_isSret || idex_isSFenceVMA || dMMURedirect

/-- `flushOrDelay = flush ∨ flushDelay`. -/
@[inline] def flushOrDelayPure
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay : Bool) : Bool :=
  flushPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
    idex_isSFenceVMA dMMURedirect || flushDelay

/-- `freezeIDEX = holdEX ∨ (divStall ∧ ¬flushOrDelay)`.

    Note the "∧ ¬flushOrDelay" on `divStall`: a flush *unfreezes*
    IDEX (the divider's pending instruction is being squashed
    anyway, so we don't need to hold it). holdEX (= pendingWriteEn ∨
    mmuBusy) freezes regardless. -/
@[inline] def freezeIDEXPure
    (holdEX divStall flushOrDelay : Bool) : Bool :=
  holdEX || (divStall && !flushOrDelay)

/-- `squash = (stall ∧ ¬freezeIDEX) ∨ flushOrDelay ∨ stallDelay`. -/
@[inline] def squashPure
    (stallAndNotFreeze flushOrDelay stallDelay : Bool) : Bool :=
  stallAndNotFreeze || flushOrDelay || stallDelay

/-! ### Per-source flush-inclusion lemmas — closed by `decide` -/

/-- `branchTaken → flush`. -/
theorem flush_contains_branchTaken
    (idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Bool) :
    flushPure true idex_jump trap_taken idex_isMret idex_isSret
      idex_isSFenceVMA dMMURedirect = true := by
  revert idex_jump trap_taken idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect
  decide

/-- `idex_jump → flush`. -/
theorem flush_contains_idex_jump
    (branchTaken trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Bool) :
    flushPure branchTaken true trap_taken idex_isMret idex_isSret
      idex_isSFenceVMA dMMURedirect = true := by
  revert branchTaken trap_taken idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect
  decide

/-- `trap_taken → flush`. -/
theorem flush_contains_trap_taken
    (branchTaken idex_jump idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Bool) :
    flushPure branchTaken idex_jump true idex_isMret idex_isSret
      idex_isSFenceVMA dMMURedirect = true := by
  revert branchTaken idex_jump idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect
  decide

/-- `idex_isMret → flush`. -/
theorem flush_contains_idex_isMret
    (branchTaken idex_jump trap_taken idex_isSret
     idex_isSFenceVMA dMMURedirect : Bool) :
    flushPure branchTaken idex_jump trap_taken true idex_isSret
      idex_isSFenceVMA dMMURedirect = true := by
  revert branchTaken idex_jump trap_taken idex_isSret idex_isSFenceVMA dMMURedirect
  decide

/-- `idex_isSret → flush`. -/
theorem flush_contains_idex_isSret
    (branchTaken idex_jump trap_taken idex_isMret
     idex_isSFenceVMA dMMURedirect : Bool) :
    flushPure branchTaken idex_jump trap_taken idex_isMret true
      idex_isSFenceVMA dMMURedirect = true := by
  revert branchTaken idex_jump trap_taken idex_isMret idex_isSFenceVMA dMMURedirect
  decide

/-- `idex_isSFenceVMA → flush`. -/
theorem flush_contains_idex_isSFenceVMA
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     dMMURedirect : Bool) :
    flushPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
      true dMMURedirect = true := by
  revert branchTaken idex_jump trap_taken idex_isMret idex_isSret dMMURedirect
  decide

/-- `dMMURedirect → flush`. -/
theorem flush_contains_dMMURedirect
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA : Bool) :
    flushPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
      idex_isSFenceVMA true = true := by
  revert branchTaken idex_jump trap_taken idex_isMret idex_isSret idex_isSFenceVMA
  decide

/-- `flush → flushOrDelay`. -/
theorem flushOrDelay_contains_flush
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay : Bool) :
    flushPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
      idex_isSFenceVMA dMMURedirect = true →
    flushOrDelayPure branchTaken idex_jump trap_taken idex_isMret
      idex_isSret idex_isSFenceVMA dMMURedirect flushDelay = true := by
  intro h
  unfold flushOrDelayPure
  rw [h]
  cases flushDelay <;> rfl

/-- `flushOrDelay → squash`. -/
theorem squash_contains_flushOrDelay
    (stallAndNotFreeze flushOrDelay stallDelay : Bool) :
    flushOrDelay = true →
    squashPure stallAndNotFreeze flushOrDelay stallDelay = true := by
  intro h
  unfold squashPure
  rw [h]
  cases stallAndNotFreeze <;> cases stallDelay <;> rfl

/-- Backward-compat alias for the lemma named in commit 8610936.
    Takes the post-flushOrDelay value as input. -/
theorem squash_contains_mret
    (stallAndNotFreeze flushOrDelay stallDelay : Bool) :
    flushOrDelay = true →
    squashPure stallAndNotFreeze flushOrDelay stallDelay = true :=
  squash_contains_flushOrDelay stallAndNotFreeze flushOrDelay stallDelay

/-- **Direct bridge: `idex_isMret → squash`.** Composes the chain
    flush ← idex_isMret → flushOrDelay → squash. Symmetric to
    `squash_contains_dMMURedirect` etc. -/
theorem squash_contains_idex_isMret
    (branchTaken idex_jump trap_taken idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay
     stallAndNotFreeze stallDelay : Bool) :
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken idex_jump trap_taken true
        idex_isSret idex_isSFenceVMA dMMURedirect flushDelay)
      stallDelay = true := by
  apply squash_contains_flushOrDelay
  apply flushOrDelay_contains_flush
  exact flush_contains_idex_isMret branchTaken idex_jump trap_taken
    idex_isSret idex_isSFenceVMA dMMURedirect

/-- **Direct bridge: `dMMURedirect → squash`.**

    Composes the three step-lemmas above (flush ← dMMURedirect,
    flushOrDelay ← flush, squash ← flushOrDelay) into a single
    one-shot statement. This is what the cycle-N+1 invariant C
    composite uses when claiming "dMMURedirect at N → IDEX
    squashed at N+1". -/
theorem squash_contains_dMMURedirect
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA flushDelay stallAndNotFreeze stallDelay : Bool) :
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken idex_jump trap_taken idex_isMret
        idex_isSret idex_isSFenceVMA true flushDelay)
      stallDelay = true := by
  apply squash_contains_flushOrDelay
  apply flushOrDelay_contains_flush
  exact flush_contains_dMMURedirect branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA

/-- **Direct bridge: `trap_taken → squash`.** Used by invariant B
    (mret idempotency) and invariants A/E (regfile + store
    suppression on trap entry). -/
theorem squash_contains_trap_taken
    (branchTaken idex_jump idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay
     stallAndNotFreeze stallDelay : Bool) :
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken idex_jump true idex_isMret
        idex_isSret idex_isSFenceVMA dMMURedirect flushDelay)
      stallDelay = true := by
  apply squash_contains_flushOrDelay
  apply flushOrDelay_contains_flush
  exact flush_contains_trap_taken branchTaken idex_jump idex_isMret
    idex_isSret idex_isSFenceVMA dMMURedirect

/-- **Direct bridge: `branchTaken → squash`.** -/
theorem squash_contains_branchTaken
    (idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay
     stallAndNotFreeze stallDelay : Bool) :
    squashPure stallAndNotFreeze
      (flushOrDelayPure true idex_jump trap_taken idex_isMret
        idex_isSret idex_isSFenceVMA dMMURedirect flushDelay)
      stallDelay = true := by
  apply squash_contains_flushOrDelay
  apply flushOrDelay_contains_flush
  exact flush_contains_branchTaken idex_jump trap_taken idex_isMret
    idex_isSret idex_isSFenceVMA dMMURedirect

/-- **Direct bridge: `idex_jump → squash`.** -/
theorem squash_contains_idex_jump
    (branchTaken trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay
     stallAndNotFreeze stallDelay : Bool) :
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken true trap_taken idex_isMret
        idex_isSret idex_isSFenceVMA dMMURedirect flushDelay)
      stallDelay = true := by
  apply squash_contains_flushOrDelay
  apply flushOrDelay_contains_flush
  exact flush_contains_idex_jump branchTaken trap_taken idex_isMret
    idex_isSret idex_isSFenceVMA dMMURedirect

/-- **Direct bridge: `idex_isSret → squash`.** -/
theorem squash_contains_idex_isSret
    (branchTaken idex_jump trap_taken idex_isMret
     idex_isSFenceVMA dMMURedirect flushDelay
     stallAndNotFreeze stallDelay : Bool) :
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken idex_jump trap_taken idex_isMret
        true idex_isSFenceVMA dMMURedirect flushDelay)
      stallDelay = true := by
  apply squash_contains_flushOrDelay
  apply flushOrDelay_contains_flush
  exact flush_contains_idex_isSret branchTaken idex_jump trap_taken
    idex_isMret idex_isSFenceVMA dMMURedirect

/-- **Direct bridge: `idex_isSFenceVMA → squash`.** -/
theorem squash_contains_idex_isSFenceVMA
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     dMMURedirect flushDelay
     stallAndNotFreeze stallDelay : Bool) :
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken idex_jump trap_taken idex_isMret
        idex_isSret true dMMURedirect flushDelay)
      stallDelay = true := by
  apply squash_contains_flushOrDelay
  apply flushOrDelay_contains_flush
  exact flush_contains_idex_isSFenceVMA branchTaken idex_jump trap_taken
    idex_isMret idex_isSret dMMURedirect

/-! ## Composite specs -/

theorem flushPure_spec :
    ∀ (b1 b2 b3 b4 b5 b6 b7 : Bool),
      flushPure b1 b2 b3 b4 b5 b6 b7 = (b1 || b2 || b3 || b4 || b5 || b6 || b7) := by
  decide

theorem flushOrDelayPure_spec :
    ∀ (b1 b2 b3 b4 b5 b6 b7 b8 : Bool),
      flushOrDelayPure b1 b2 b3 b4 b5 b6 b7 b8 =
        (b1 || b2 || b3 || b4 || b5 || b6 || b7 || b8) := by
  decide

theorem freezeIDEXPure_spec :
    ∀ (holdEX divStall flushOrDelay : Bool),
      freezeIDEXPure holdEX divStall flushOrDelay =
        (holdEX || (divStall && !flushOrDelay)) := by
  decide

/-! ## Signal-level wrappers -/

def flushSignal {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) : Signal dom Bool :=
  branchTaken ||| idex_jump ||| trap_taken ||| idex_isMret
    ||| idex_isSret ||| idex_isSFenceVMA ||| dMMURedirect

def flushOrDelaySignal {dom : DomainConfig}
    (flush flushDelay : Signal dom Bool) : Signal dom Bool :=
  flush ||| flushDelay

def freezeIDEXSignal {dom : DomainConfig}
    (holdEX divStall flushOrDelay : Signal dom Bool) : Signal dom Bool :=
  holdEX ||| (divStall &&& (~~~flushOrDelay))

def squashSignal {dom : DomainConfig}
    (stallAndNotFreeze flushOrDelay stallDelay : Signal dom Bool) : Signal dom Bool :=
  stallAndNotFreeze ||| flushOrDelay ||| stallDelay

/-! ## stallAndNotFreeze helper

  The `stallAndNotFreeze` argument to `squashSignal` is itself a
  composite predicate: stall fires AND freezeIDEX does not. We
  expose it as a small named primitive so call sites don't need
  the inline `(stall &&& (~~~freezeIDEX))` shape. -/

@[inline] def stallAndNotFreezePure
    (stall freezeIDEX : Bool) : Bool :=
  stall && !freezeIDEX

@[simp] theorem stallAndNotFreeze_no_stall (freezeIDEX : Bool) :
    stallAndNotFreezePure false freezeIDEX = false := rfl

@[simp] theorem stallAndNotFreeze_with_freeze (stall : Bool) :
    stallAndNotFreezePure stall true = false := by
  unfold stallAndNotFreezePure; cases stall <;> rfl

@[simp] theorem stallAndNotFreeze_active :
    stallAndNotFreezePure true false = true := rfl

theorem stallAndNotFreezePure_spec
    (stall freezeIDEX : Bool) :
    stallAndNotFreezePure stall freezeIDEX = (stall && !freezeIDEX) := rfl

def stallAndNotFreezeSignal {dom : DomainConfig}
    (stall freezeIDEX : Signal dom Bool) : Signal dom Bool :=
  stall &&& (~~~freezeIDEX)

/-! ## Cycle-wise lifts of squash_contains_* bridges

  Lift the per-source `squash_contains_X` Bool-level lemmas to
  Signal-level cycle-t statements: when X.val t is true, the
  cycle-t value of the canonical `squashPure ∘ flushOrDelayPure`
  composition is also true. -/

theorem squashSig_contains_dMMURedirect_atTime {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay stallAndNotFreeze
     stallDelay : Signal dom Bool) (t : Nat)
    (h_dmmu : dMMURedirect.val t = true) :
    squashPure (stallAndNotFreeze.val t)
      (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
        (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
        (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
      (stallDelay.val t) = true := by
  rw [h_dmmu]
  exact squash_contains_dMMURedirect (branchTaken.val t) (idex_jump.val t)
    (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
    (idex_isSFenceVMA.val t) (flushDelay.val t)
    (stallAndNotFreeze.val t) (stallDelay.val t)

theorem squashSig_contains_trap_taken_atTime {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay stallAndNotFreeze
     stallDelay : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.val t = true) :
    squashPure (stallAndNotFreeze.val t)
      (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
        (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
        (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
      (stallDelay.val t) = true := by
  rw [h_trap]
  exact squash_contains_trap_taken (branchTaken.val t) (idex_jump.val t)
    (idex_isMret.val t) (idex_isSret.val t) (idex_isSFenceVMA.val t)
    (dMMURedirect.val t) (flushDelay.val t)
    (stallAndNotFreeze.val t) (stallDelay.val t)

theorem squashSig_contains_idex_isMret_atTime {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay stallAndNotFreeze
     stallDelay : Signal dom Bool) (t : Nat)
    (h_mret : idex_isMret.val t = true) :
    squashPure (stallAndNotFreeze.val t)
      (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
        (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
        (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
      (stallDelay.val t) = true := by
  rw [h_mret]
  exact squash_contains_idex_isMret (branchTaken.val t) (idex_jump.val t)
    (trap_taken.val t) (idex_isSret.val t) (idex_isSFenceVMA.val t)
    (dMMURedirect.val t) (flushDelay.val t)
    (stallAndNotFreeze.val t) (stallDelay.val t)

theorem squashSig_contains_idex_isSret_atTime {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect flushDelay stallAndNotFreeze
     stallDelay : Signal dom Bool) (t : Nat)
    (h_sret : idex_isSret.val t = true) :
    squashPure (stallAndNotFreeze.val t)
      (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
        (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
        (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
      (stallDelay.val t) = true := by
  rw [h_sret]
  exact squash_contains_idex_isSret (branchTaken.val t) (idex_jump.val t)
    (trap_taken.val t) (idex_isMret.val t) (idex_isSFenceVMA.val t)
    (dMMURedirect.val t) (flushDelay.val t)
    (stallAndNotFreeze.val t) (stallDelay.val t)

/-! ## Canonical "squashSig" wrapper

  When the pipeline's `squash` Signal is constructed in the
  canonical way (= `Signal.mux ... ||| ...` mirroring
  `flushOrDelayPure ∘ flushPure`), we can recognize it as
  "the canonical squashPure-of-flushOrDelayPure construction"
  and apply the cycle-wise lifts. This wrapper is for documentation
  / alias purposes; the actual signal in SoC.lean is computed by
  the loop body and equals this expression cycle-wise.
-/

/-- Cycle-wise definition of the canonical squashSig. -/
@[inline] def canonicalSquashAtTime {dom : DomainConfig}
    (stallAndNotFreeze branchTaken idex_jump trap_taken
     idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect
     flushDelay stallDelay : Signal dom Bool) (t : Nat) : Bool :=
  squashPure (stallAndNotFreeze.val t)
    (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
      (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
      (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
    (stallDelay.val t)

/-! ## Sequential flushDelay register after each flush source

  flushDelay = `Signal.register false flush`. When any flush
  source fires at cycle t, flush.val t = true, so
  flushDelay.val (t+1) = true. -/

/-- **flushSig.val t = true → flushDelay at t+1 = true.** Helper for
    the per-source variants below. -/
private theorem flushDelayReg_set_helper {dom : DomainConfig}
    (flush : Signal dom Bool) (t : Nat)
    (h : flush.val t = true) :
    (Signal.register false flush).val (t + 1) = true := by
  show (Signal.register false flush).val (t + 1) = true
  show flush.val t = true
  exact h

/-- **trap_taken at t → flushDelay (computed via flushSignal) at t+1 = true.** -/
theorem flushDelayReg_set_after_trap {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) (t : Nat)
    (h_trap : trap_taken.val t = true) :
    (Signal.register false
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)).val (t + 1) = true := by
  apply flushDelayReg_set_helper
  unfold flushSignal
  show (((((((branchTaken.val t || idex_jump.val t) || trap_taken.val t)
    || idex_isMret.val t) || idex_isSret.val t) || idex_isSFenceVMA.val t)
    || dMMURedirect.val t)) = true
  rw [h_trap]
  cases branchTaken.val t <;> cases idex_jump.val t <;>
    cases idex_isMret.val t <;> cases idex_isSret.val t <;>
    cases idex_isSFenceVMA.val t <;> cases dMMURedirect.val t <;> rfl

/-- **branchTaken at t → flushDelay at t+1 = true.** -/
theorem flushDelayReg_set_after_branchTaken {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) (t : Nat)
    (h_branch : branchTaken.val t = true) :
    (Signal.register false
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)).val (t + 1) = true := by
  apply flushDelayReg_set_helper
  unfold flushSignal
  show (((((((branchTaken.val t || idex_jump.val t) || trap_taken.val t)
    || idex_isMret.val t) || idex_isSret.val t) || idex_isSFenceVMA.val t)
    || dMMURedirect.val t)) = true
  rw [h_branch]
  rfl

/-- **idex_isMret at t → flushDelay at t+1 = true.** -/
theorem flushDelayReg_set_after_mret {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) (t : Nat)
    (h_mret : idex_isMret.val t = true) :
    (Signal.register false
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)).val (t + 1) = true := by
  apply flushDelayReg_set_helper
  unfold flushSignal
  show (((((((branchTaken.val t || idex_jump.val t) || trap_taken.val t)
    || idex_isMret.val t) || idex_isSret.val t) || idex_isSFenceVMA.val t)
    || dMMURedirect.val t)) = true
  rw [h_mret]
  cases branchTaken.val t <;> cases idex_jump.val t <;>
    cases trap_taken.val t <;> cases idex_isSret.val t <;>
    cases idex_isSFenceVMA.val t <;> cases dMMURedirect.val t <;> rfl

/-- **idex_jump at t → flushDelay at t+1 = true.** -/
theorem flushDelayReg_set_after_jump {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) (t : Nat)
    (h_jump : idex_jump.val t = true) :
    (Signal.register false
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)).val (t + 1) = true := by
  apply flushDelayReg_set_helper
  unfold flushSignal
  show (((((((branchTaken.val t || idex_jump.val t) || trap_taken.val t)
    || idex_isMret.val t) || idex_isSret.val t) || idex_isSFenceVMA.val t)
    || dMMURedirect.val t)) = true
  rw [h_jump]
  cases branchTaken.val t <;> cases trap_taken.val t <;>
    cases idex_isMret.val t <;> cases idex_isSret.val t <;>
    cases idex_isSFenceVMA.val t <;> cases dMMURedirect.val t <;> rfl

/-- **idex_isSret at t → flushDelay at t+1 = true.** -/
theorem flushDelayReg_set_after_sret {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) (t : Nat)
    (h_sret : idex_isSret.val t = true) :
    (Signal.register false
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)).val (t + 1) = true := by
  apply flushDelayReg_set_helper
  unfold flushSignal
  show (((((((branchTaken.val t || idex_jump.val t) || trap_taken.val t)
    || idex_isMret.val t) || idex_isSret.val t) || idex_isSFenceVMA.val t)
    || dMMURedirect.val t)) = true
  rw [h_sret]
  cases branchTaken.val t <;> cases idex_jump.val t <;>
    cases trap_taken.val t <;> cases idex_isMret.val t <;>
    cases idex_isSFenceVMA.val t <;> cases dMMURedirect.val t <;> rfl

/-- **idex_isSFenceVMA at t → flushDelay at t+1 = true.** -/
theorem flushDelayReg_set_after_sfence {dom : DomainConfig}
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool) (t : Nat)
    (h_sfence : idex_isSFenceVMA.val t = true) :
    (Signal.register false
      (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect)).val (t + 1) = true := by
  apply flushDelayReg_set_helper
  unfold flushSignal
  show (((((((branchTaken.val t || idex_jump.val t) || trap_taken.val t)
    || idex_isMret.val t) || idex_isSret.val t) || idex_isSFenceVMA.val t)
    || dMMURedirect.val t)) = true
  rw [h_sfence]
  cases branchTaken.val t <;> cases idex_jump.val t <;>
    cases trap_taken.val t <;> cases idex_isMret.val t <;>
    cases idex_isSret.val t <;> cases dMMURedirect.val t <;> rfl

/-! ## flushOrDelay ⊇ flushDelay

  Direct Bool-level inclusion: when flushDelay is true,
  flushOrDelay is true regardless of the 7 flush sources. -/

theorem flushOrDelay_contains_flushDelay
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Bool) :
    flushOrDelayPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
      idex_isSFenceVMA dMMURedirect true = true := by
  unfold flushOrDelayPure
  cases flushPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
    idex_isSFenceVMA dMMURedirect <;> rfl

/-- **squash ⊇ flushDelay** via the chain
    flushDelay → flushOrDelay → squash. -/
theorem squash_contains_flushDelay
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect stallAndNotFreeze stallDelay : Bool) :
    squashPure stallAndNotFreeze
      (flushOrDelayPure branchTaken idex_jump trap_taken idex_isMret idex_isSret
        idex_isSFenceVMA dMMURedirect true)
      stallDelay = true := by
  apply squash_contains_flushOrDelay
  exact flushOrDelay_contains_flushDelay branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect

/-! ## Cycle-N+2 IDEX squash stability

  When a flush source fires at cycle N, the chain
    flush(N) → flushDelay(N+1) → squash(N+1) → IDEX-NOP(N+2)
  ensures the IDEX latch at cycle N+2 is the squashed-init
  value. This is the cycle-wise lift establishing that an
  IDEX squash persists through the cycle after a flush event,
  not just ending at N+1.

  Wraps the hypothesis "flushDelay observed at cycle N+1 = true"
  rather than re-deriving it; downstream callers can chain in
  `flushDelayReg_set_after_*` to convert "flush source X at N"
  into the flushDelay hypothesis. -/

/-- **flushDelay at cycle N+1 + freeze=false at N+1 → IDEX at N+2 = init.**

    Reuses `idex_squash_clears_next_cycle` (passing N+1 as the
    cycle), with the squash hypothesis discharged via
    `squash_contains_flushDelay`. -/
theorem idex_squash_persists_via_flushDelay {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze : Signal dom Bool)
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (flushDelay stallAndNotFreeze stallDelay : Signal dom Bool)
    (old new : Signal dom α) (init : α) (n : Nat)
    (h_flushDelay : flushDelay.atTime (n + 1) = true)
    (h_no_freeze : freeze.atTime (n + 1) = false) :
    -- At cycle (n+1)+1 = n+2, IDEX latch = init.
    let squashSig :=
      ⟨fun t => squashPure (stallAndNotFreeze.val t)
        (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
          (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
          (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
        (stallDelay.val t)⟩
    (idexLatchSignal freeze squashSig old new init).atTime (n + 2) = init := by
  apply idex_squash_clears_next_cycle freeze _ old new init (n + 1)
  · exact h_no_freeze
  · -- Show squashSig at n+1 = true, using flushDelay = true.
    unfold Signal.atTime
    show squashPure _ _ _ = true
    rw [show flushDelay.val (n + 1) = true from h_flushDelay]
    exact squash_contains_flushDelay (branchTaken.val (n + 1)) (idex_jump.val (n + 1))
      (trap_taken.val (n + 1)) (idex_isMret.val (n + 1)) (idex_isSret.val (n + 1))
      (idex_isSFenceVMA.val (n + 1)) (dMMURedirect.val (n + 1))
      (stallAndNotFreeze.val (n + 1)) (stallDelay.val (n + 1))

/-! ## Multi-cycle composite: trap at N → IDEX at N+2 = init

  Chains `flushDelayReg_set_after_trap` (cycle N → N+1) with
  `idex_squash_persists_via_flushDelay` (cycle N+1 → N+2).

  Statement: a trap at cycle N forces the IDEX latch at cycle
  N+2 to be the squashed-init value, provided the freeze
  signal is clear at cycle N+1.

  This complements the single-cycle `mret_squashes_idex_next_cycle`
  variants (commit 4e155d3 et al.) which handle the immediate
  N+1 squash; this lemma extends the squash to N+2 — required
  for proving that a trap doesn't merely abort the in-flight
  EXWB instruction but also keeps IDEX cleared across the cycle
  after the trap, while the kernel handler is starting to
  fetch.
-/

theorem idex_squash_at_N_plus_2_after_trap {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze : Signal dom Bool)
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (flushDelay stallAndNotFreeze stallDelay : Signal dom Bool)
    (old new : Signal dom α) (init : α) (n : Nat)
    (h_trap_n : trap_taken.val n = true)
    (h_no_freeze_n1 : freeze.atTime (n + 1) = false)
    -- Wire flushDelay := register false (flushSignal ...).
    (h_flushDelay_def :
      ∀ t, flushDelay.val t = (Signal.register false
        (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
          idex_isSFenceVMA dMMURedirect)).val t) :
    let squashSig :=
      ⟨fun t => squashPure (stallAndNotFreeze.val t)
        (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
          (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
          (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
        (stallDelay.val t)⟩
    (idexLatchSignal freeze squashSig old new init).atTime (n + 2) = init := by
  -- Step 1: trap at n → flushDelay at n+1 = true (via wire-def + flushDelayReg_set_after_trap).
  have h_flushDelay_n1 : flushDelay.atTime (n + 1) = true := by
    unfold Signal.atTime
    rw [h_flushDelay_def (n + 1)]
    exact flushDelayReg_set_after_trap branchTaken idex_jump trap_taken idex_isMret
      idex_isSret idex_isSFenceVMA dMMURedirect n h_trap_n
  -- Step 2: apply idex_squash_persists_via_flushDelay.
  exact idex_squash_persists_via_flushDelay freeze branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect flushDelay
    stallAndNotFreeze stallDelay old new init n h_flushDelay_n1 h_no_freeze_n1

/-- **dMMURedirect at N → IDEX at N+2 = init** (cycle-N+2 composite). -/
theorem idex_squash_at_N_plus_2_after_dMMURedirect {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze : Signal dom Bool)
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (flushDelay stallAndNotFreeze stallDelay : Signal dom Bool)
    (old new : Signal dom α) (init : α) (n : Nat)
    (h_dmmu_n : dMMURedirect.val n = true)
    (h_no_freeze_n1 : freeze.atTime (n + 1) = false)
    (h_flushDelay_def :
      ∀ t, flushDelay.val t = (Signal.register false
        (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
          idex_isSFenceVMA dMMURedirect)).val t) :
    let squashSig :=
      ⟨fun t => squashPure (stallAndNotFreeze.val t)
        (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
          (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
          (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
        (stallDelay.val t)⟩
    (idexLatchSignal freeze squashSig old new init).atTime (n + 2) = init := by
  have h_flushDelay_n1 : flushDelay.atTime (n + 1) = true := by
    unfold Signal.atTime
    rw [h_flushDelay_def (n + 1)]
    show (Signal.register false _).val (n + 1) = true
    show (flushSignal _ _ _ _ _ _ _).val n = true
    unfold flushSignal
    show (((((((branchTaken.val n || idex_jump.val n) || trap_taken.val n)
      || idex_isMret.val n) || idex_isSret.val n) || idex_isSFenceVMA.val n)
      || dMMURedirect.val n)) = true
    rw [h_dmmu_n]
    cases branchTaken.val n <;> cases idex_jump.val n <;>
      cases trap_taken.val n <;> cases idex_isMret.val n <;>
      cases idex_isSret.val n <;> cases idex_isSFenceVMA.val n <;> rfl
  exact idex_squash_persists_via_flushDelay freeze branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect flushDelay
    stallAndNotFreeze stallDelay old new init n h_flushDelay_n1 h_no_freeze_n1

/-- **idex_isMret at N → IDEX at N+2 = init** (cycle-N+2 composite). -/
theorem idex_squash_at_N_plus_2_after_mret {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze : Signal dom Bool)
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (flushDelay stallAndNotFreeze stallDelay : Signal dom Bool)
    (old new : Signal dom α) (init : α) (n : Nat)
    (h_mret_n : idex_isMret.val n = true)
    (h_no_freeze_n1 : freeze.atTime (n + 1) = false)
    (h_flushDelay_def :
      ∀ t, flushDelay.val t = (Signal.register false
        (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
          idex_isSFenceVMA dMMURedirect)).val t) :
    let squashSig :=
      ⟨fun t => squashPure (stallAndNotFreeze.val t)
        (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
          (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
          (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
        (stallDelay.val t)⟩
    (idexLatchSignal freeze squashSig old new init).atTime (n + 2) = init := by
  have h_flushDelay_n1 : flushDelay.atTime (n + 1) = true := by
    unfold Signal.atTime
    rw [h_flushDelay_def (n + 1)]
    exact flushDelayReg_set_after_mret branchTaken idex_jump trap_taken idex_isMret
      idex_isSret idex_isSFenceVMA dMMURedirect n h_mret_n
  exact idex_squash_persists_via_flushDelay freeze branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect flushDelay
    stallAndNotFreeze stallDelay old new init n h_flushDelay_n1 h_no_freeze_n1

/-- **branchTaken at N → IDEX at N+2 = init** (cycle-N+2 composite). -/
theorem idex_squash_at_N_plus_2_after_branchTaken {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze : Signal dom Bool)
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (flushDelay stallAndNotFreeze stallDelay : Signal dom Bool)
    (old new : Signal dom α) (init : α) (n : Nat)
    (h_branch_n : branchTaken.val n = true)
    (h_no_freeze_n1 : freeze.atTime (n + 1) = false)
    (h_flushDelay_def :
      ∀ t, flushDelay.val t = (Signal.register false
        (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
          idex_isSFenceVMA dMMURedirect)).val t) :
    let squashSig :=
      ⟨fun t => squashPure (stallAndNotFreeze.val t)
        (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
          (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
          (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
        (stallDelay.val t)⟩
    (idexLatchSignal freeze squashSig old new init).atTime (n + 2) = init := by
  have h_flushDelay_n1 : flushDelay.atTime (n + 1) = true := by
    unfold Signal.atTime
    rw [h_flushDelay_def (n + 1)]
    exact flushDelayReg_set_after_branchTaken branchTaken idex_jump trap_taken idex_isMret
      idex_isSret idex_isSFenceVMA dMMURedirect n h_branch_n
  exact idex_squash_persists_via_flushDelay freeze branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect flushDelay
    stallAndNotFreeze stallDelay old new init n h_flushDelay_n1 h_no_freeze_n1

/-- **idex_jump at N → IDEX at N+2 = init** (cycle-N+2 composite). -/
theorem idex_squash_at_N_plus_2_after_jump {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze : Signal dom Bool)
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (flushDelay stallAndNotFreeze stallDelay : Signal dom Bool)
    (old new : Signal dom α) (init : α) (n : Nat)
    (h_jump_n : idex_jump.val n = true)
    (h_no_freeze_n1 : freeze.atTime (n + 1) = false)
    (h_flushDelay_def :
      ∀ t, flushDelay.val t = (Signal.register false
        (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
          idex_isSFenceVMA dMMURedirect)).val t) :
    let squashSig :=
      ⟨fun t => squashPure (stallAndNotFreeze.val t)
        (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
          (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
          (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
        (stallDelay.val t)⟩
    (idexLatchSignal freeze squashSig old new init).atTime (n + 2) = init := by
  have h_flushDelay_n1 : flushDelay.atTime (n + 1) = true := by
    unfold Signal.atTime
    rw [h_flushDelay_def (n + 1)]
    exact flushDelayReg_set_after_jump branchTaken idex_jump trap_taken idex_isMret
      idex_isSret idex_isSFenceVMA dMMURedirect n h_jump_n
  exact idex_squash_persists_via_flushDelay freeze branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect flushDelay
    stallAndNotFreeze stallDelay old new init n h_flushDelay_n1 h_no_freeze_n1

/-- **idex_isSret at N → IDEX at N+2 = init** (cycle-N+2 composite). -/
theorem idex_squash_at_N_plus_2_after_sret {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze : Signal dom Bool)
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (flushDelay stallAndNotFreeze stallDelay : Signal dom Bool)
    (old new : Signal dom α) (init : α) (n : Nat)
    (h_sret_n : idex_isSret.val n = true)
    (h_no_freeze_n1 : freeze.atTime (n + 1) = false)
    (h_flushDelay_def :
      ∀ t, flushDelay.val t = (Signal.register false
        (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
          idex_isSFenceVMA dMMURedirect)).val t) :
    let squashSig :=
      ⟨fun t => squashPure (stallAndNotFreeze.val t)
        (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
          (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
          (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
        (stallDelay.val t)⟩
    (idexLatchSignal freeze squashSig old new init).atTime (n + 2) = init := by
  have h_flushDelay_n1 : flushDelay.atTime (n + 1) = true := by
    unfold Signal.atTime
    rw [h_flushDelay_def (n + 1)]
    exact flushDelayReg_set_after_sret branchTaken idex_jump trap_taken idex_isMret
      idex_isSret idex_isSFenceVMA dMMURedirect n h_sret_n
  exact idex_squash_persists_via_flushDelay freeze branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect flushDelay
    stallAndNotFreeze stallDelay old new init n h_flushDelay_n1 h_no_freeze_n1

/-- **idex_isSFenceVMA at N → IDEX at N+2 = init** (cycle-N+2 composite). -/
theorem idex_squash_at_N_plus_2_after_sfence {dom : DomainConfig} {α : Type}
    [DecidableEq α] [Inhabited α]
    (freeze : Signal dom Bool)
    (branchTaken idex_jump trap_taken idex_isMret idex_isSret
     idex_isSFenceVMA dMMURedirect : Signal dom Bool)
    (flushDelay stallAndNotFreeze stallDelay : Signal dom Bool)
    (old new : Signal dom α) (init : α) (n : Nat)
    (h_sfence_n : idex_isSFenceVMA.val n = true)
    (h_no_freeze_n1 : freeze.atTime (n + 1) = false)
    (h_flushDelay_def :
      ∀ t, flushDelay.val t = (Signal.register false
        (flushSignal branchTaken idex_jump trap_taken idex_isMret idex_isSret
          idex_isSFenceVMA dMMURedirect)).val t) :
    let squashSig :=
      ⟨fun t => squashPure (stallAndNotFreeze.val t)
        (flushOrDelayPure (branchTaken.val t) (idex_jump.val t)
          (trap_taken.val t) (idex_isMret.val t) (idex_isSret.val t)
          (idex_isSFenceVMA.val t) (dMMURedirect.val t) (flushDelay.val t))
        (stallDelay.val t)⟩
    (idexLatchSignal freeze squashSig old new init).atTime (n + 2) = init := by
  have h_flushDelay_n1 : flushDelay.atTime (n + 1) = true := by
    unfold Signal.atTime
    rw [h_flushDelay_def (n + 1)]
    exact flushDelayReg_set_after_sfence branchTaken idex_jump trap_taken idex_isMret
      idex_isSret idex_isSFenceVMA dMMURedirect n h_sfence_n
  exact idex_squash_persists_via_flushDelay freeze branchTaken idex_jump trap_taken
    idex_isMret idex_isSret idex_isSFenceVMA dMMURedirect flushDelay
    stallAndNotFreeze stallDelay old new init n h_flushDelay_n1 h_no_freeze_n1

end Sparkle.IP.RV32.Pipeline
