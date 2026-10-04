/-
  Signal.loop Characterization — closing the gap for feedback-circuit proofs.

  `Signal.loop` is now a *pure* definition (`⟨loopGo f⟩`, the strong-
  recursion fixpoint on the time index — see `Sparkle/Core/Signal.lean`),
  not an `opaque` wrapper.  Its execution is still the fast memoizing
  `loopImpl` via `@[implemented_by]`, but its *logical* value is the pure
  fixpoint, so `(Signal.loop f).val t` unfolds in the kernel.

  This file supplies the reduction from that fixpoint to a pure state
  iterate.  The key fact is the fixpoint equation `loop f = f (loop f)`,
  which holds for *strictly causal* `f` — every feedback path passes
  through a register, so the output at time `t` depends only on inputs
  strictly before `t`.

  `loop_unfold` used to be a trusted *axiom*; it is now a *theorem*
  (proved from `loopGo`'s defining equation + `StrictlyCausal`).  The
  only remaining trust base for this file is Lean's own `Quot.sound`
  (used by `funext`), which every Lean development already relies on.

  Why `StrictlyCausal` is needed.  An unrestricted `∀ f, loop f =
  f (loop f)` is FALSE: take `f s = ~~~s` (pointwise Bool negation); it
  has no fixpoint, and the equation would give `b = !b`, hence `False`.
  `loopGo` sidesteps this by feeding `f` a signal that is `default` at
  cycles `≥ t`; for a strictly causal `f` those placeholder cycles are
  never observed, so `loopGo` computes the genuine fixpoint and
  `loop_unfold` goes through.
-/
import Sparkle.Core.Signal

namespace Sparkle.Verification.LoopProps

open Sparkle.Core.Domain
open Sparkle.Core.Signal

variable {dom : DomainConfig} {α β : Type}

-- ============================================================================
-- .val reduction lemmas (kept local so this file has a light import surface)
-- ============================================================================

@[simp] theorem register_val_zero (init : α) (input : Signal dom α) :
    (Signal.register init input).val 0 = init := rfl

@[simp] theorem register_val_succ (init : α) (input : Signal dom α) (n : Nat) :
    (Signal.register init input).val (n + 1) = input.val n := rfl

@[simp] theorem bundle2_val (a : Signal dom α) (b : Signal dom β) (t : Nat) :
    (bundle2 a b).val t = (a.val t, b.val t) := rfl

@[simp] theorem bv_add_val {n} (a b : Signal dom (BitVec n)) (t : Nat) :
    (a + b).val t = a.val t + b.val t := rfl

@[simp] theorem fst_val (s : Signal dom (α × β)) (t : Nat) :
    (Signal.fst s).val t = (s.val t).1 := rfl

@[simp] theorem snd_val (s : Signal dom (α × β)) (t : Nat) :
    (Signal.snd s).val t = (s.val t).2 := rfl

@[simp] theorem mux_val (c : Signal dom Bool) (a b : Signal dom α) (t : Nat) :
    (Signal.mux c a b).val t = if c.val t then a.val t else b.val t := rfl

@[simp] theorem pure_val (v : α) (t : Nat) :
    (@Signal.pure dom α v).val t = v := rfl

@[simp] theorem map_val (f : α → β) (s : Signal dom α) (t : Nat) :
    (Signal.map f s).val t = f (s.val t) := rfl

-- Bitvector ops, Signal ⊕ Signal
@[simp] theorem bv_sub_val {n} (a b : Signal dom (BitVec n)) (t : Nat) :
    (a - b).val t = a.val t - b.val t := rfl
@[simp] theorem bv_or_val {n} (a b : Signal dom (BitVec n)) (t : Nat) :
    (a ||| b).val t = a.val t ||| b.val t := rfl
@[simp] theorem bv_and_val {n} (a b : Signal dom (BitVec n)) (t : Nat) :
    (a &&& b).val t = a.val t &&& b.val t := rfl
@[simp] theorem bv_shl_val {n} (a b : Signal dom (BitVec n)) (t : Nat) :
    (a <<< b).val t = a.val t <<< b.val t := rfl

-- Bitvector ops, mixed Signal ⊕ constant
@[simp] theorem bv_sub_valC {n} (a : Signal dom (BitVec n)) (b : BitVec n) (t : Nat) :
    (a - b).val t = a.val t - b := rfl
@[simp] theorem bv_sub_valCl {n} (a : BitVec n) (b : Signal dom (BitVec n)) (t : Nat) :
    (a - b).val t = a - b.val t := rfl
@[simp] theorem bv_shl_valC {n} (a : Signal dom (BitVec n)) (b : BitVec n) (t : Nat) :
    (a <<< b).val t = a.val t <<< b := rfl

-- Concatenation, mixed variants
@[simp] theorem append_valCl {m n} (a : BitVec m) (b : Signal dom (BitVec n)) (t : Nat) :
    (a ++ b).val t = a ++ b.val t := rfl
@[simp] theorem append_valC {m n} (a : Signal dom (BitVec m)) (b : BitVec n) (t : Nat) :
    (a ++ b).val t = a.val t ++ b := rfl

-- Equality, boolean ops, complement, negation
@[simp] theorem beq_val [BEq α] (a b : Signal dom α) (t : Nat) :
    (Signal.beq a b).val t = (a.val t == b.val t) := rfl
@[simp] theorem bool_and_val (a b : Signal dom Bool) (t : Nat) :
    (a &&& b).val t = (a.val t && b.val t) := rfl
@[simp] theorem bool_or_val (a b : Signal dom Bool) (t : Nat) :
    (a ||| b).val t = (a.val t || b.val t) := rfl
@[simp] theorem compl_bool_val (a : Signal dom Bool) (t : Nat) :
    (~~~a).val t = !(a.val t) := rfl
@[simp] theorem neg_bv_val {n} (a : Signal dom (BitVec n)) (t : Nat) :
    (-a).val t = -(a.val t) := rfl

/-- Signal extensionality: equal at every cycle ⇒ equal. -/
theorem signal_ext {a b : Signal dom α} (h : ∀ t, a.val t = b.val t) : a = b := by
  cases a; cases b; simp only [Signal.mk.injEq]; funext t; exact h t

-- ============================================================================
-- Causality and the fixpoint axiom
-- ============================================================================

/-- `f` is *strictly causal*: its output at time `t` depends only on the input
    at times strictly before `t`.  A loop body in which every feedback path
    passes through `Signal.register` satisfies this. -/
def StrictlyCausal (f : Signal dom α → Signal dom α) : Prop :=
  ∀ (s₁ s₂ : Signal dom α) (t : Nat),
    (∀ i, i < t → s₁.val i = s₂.val i) → (f s₁).val t = (f s₂).val t

/-- The fixpoint equation for `Signal.loop`.

    Previously a trusted *axiom*; now a *theorem*, because `Signal.loop`
    is defined as the pure strong-recursion fixpoint `⟨loopGo f⟩` (see
    `Sparkle/Core/Signal.lean`) rather than an `opaque` wrapper around
    the memoizing implementation.  The proof rewrites through
    `loopGo`'s defining equation and uses `StrictlyCausal` to discharge
    the `default` placeholder that `loopGo` supplies at cycles `≥ t`
    (those cycles are never observed by a strictly causal body).

    (`Signal.loop` still *executes* via the memoizing `loopImpl` through
    `@[implemented_by]`; that only affects compiled code, not this
    kernel-level equation.) -/
theorem loop_unfold [Inhabited α] (f : Signal dom α → Signal dom α)
    (hf : StrictlyCausal f) : Signal.loop f = f (Signal.loop f) := by
  have hval : ∀ t, Signal.loopGo f t = (f (Signal.loop f)).val t := by
    intro t
    rw [Signal.loopGo_eq]
    apply hf
    intro i hi
    show (if i < t then Signal.loopGo f i else default) = Signal.loopGo f i
    rw [if_pos hi]
  show (⟨Signal.loopGo f⟩ : Signal dom α) = f (Signal.loop f)
  have : Signal.loopGo f = (f (Signal.loop f)).val := funext hval
  rw [this]

-- ============================================================================
-- Master reduction: a Signal.loop of registers ≡ a pure state iterate
-- ============================================================================

/-- If a loop body `f` reduces, cycle-by-cycle, to a constant initial value `c0`
    at time 0 and to a pure transition `next t (s.val t)` at time `t+1`, then it
    is strictly causal.  Both hypotheses are exactly what `simp` produces after
    pushing `.val` through a register bundle. -/
theorem strictlyCausal_of_step (f : Signal dom α → Signal dom α)
    (c0 : α) (next : Nat → α → α)
    (h0 : ∀ s, (f s).val 0 = c0)
    (hS : ∀ s t, (f s).val (t + 1) = next t (s.val t)) :
    StrictlyCausal f := by
  intro s₁ s₂ t hagree
  cases t with
  | zero => rw [h0, h0]
  | succ u => rw [hS, hS, hagree u (Nat.lt_succ_self u)]

/-- **The gap-closer.**  Given a feedback circuit `Signal.loop f` whose body
    reduces to a constant `c0` at cycle 0 and to a pure one-step transition
    `next t (s.val t)` at cycle `t+1`, the loop's value at every cycle equals
    the pure iterate `st`, where `st 0 = c0` and `st (t+1) = next t (st t)`.

    In practice the caller proves `h0`/`hS` by `simp` (they are definitional
    once `.val` is pushed through the register bundle), defines `st` by the
    obvious recurrence, and gets a fully pure model of the circuit. -/
theorem loop_iterate [Inhabited α] (f : Signal dom α → Signal dom α)
    (c0 : α) (next : Nat → α → α) (st : Nat → α)
    (h0 : ∀ s, (f s).val 0 = c0)
    (hS : ∀ s t, (f s).val (t + 1) = next t (s.val t))
    (hst0 : st 0 = c0)
    (hstS : ∀ t, st (t + 1) = next t (st t)) :
    ∀ t, (Signal.loop f).val t = st t := by
  have hf : StrictlyCausal f := strictlyCausal_of_step f c0 next h0 hS
  have hfix := loop_unfold f hf
  -- key t : (loop f).val t = (f (loop f)).val t
  have key : ∀ t, (Signal.loop f).val t = (f (Signal.loop f)).val t :=
    fun t => congrFun (congrArg Signal.val hfix) t
  intro t
  induction t with
  | zero => rw [key 0, h0, hst0]
  | succ u ih => rw [key (u + 1), hS, ih, ← hstS u]

-- ============================================================================
-- Validation: a feedback counter built with Signal.loop
-- ============================================================================

section Validation

/-- A real `Signal.loop` feedback circuit: an 8-bit counter. -/
def counterLoop : Signal defaultDomain (BitVec 8) :=
  Signal.loop (fun s => Signal.register 0#8 (s + 1#8))

/-- Pure model of the counter. -/
def counterPure : Nat → BitVec 8
  | 0 => 0#8
  | t + 1 => counterPure t + 1#8

/-- The opaque `Signal.loop` counter equals its pure iterate at every cycle —
    the kind of statement that was previously out of reach. -/
theorem counterLoop_correct (t : Nat) : counterLoop.val t = counterPure t := by
  apply loop_iterate
    (f := fun s => Signal.register 0#8 (s + 1#8))
    (c0 := 0#8)
    (next := fun _ x => x + 1#8)
    (st := counterPure)
  · intro s; rfl
  · intro s t; simp
  · rfl
  · intro t; rfl

/-- And therefore it really does count: cycle `t` holds `t mod 256`. -/
theorem counterLoop_counts (t : Nat) : counterLoop.val t = BitVec.ofNat 8 t := by
  rw [counterLoop_correct]
  induction t with
  | zero => rfl
  | succ u ih => rw [counterPure, ih]; bv_omega

end Validation

end Sparkle.Verification.LoopProps
