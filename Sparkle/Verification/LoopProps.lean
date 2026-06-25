/-
  Signal.loop Characterization — closing the gap for feedback-circuit proofs.

  `Signal.loop` is declared `opaque` (its real implementation is an `unsafe`
  IO memoization that breaks combinational cycles), so `(Signal.loop f).val t`
  cannot be unfolded by the kernel.  That is why feedback circuits were listed
  as a *non-goal* in `Equivalence.lean`: nothing connected the opaque loop to a
  value we can compute with.

  This file supplies the missing connection.  The single trusted assumption is
  the fixpoint equation `loop f = f (loop f)`, valid ONLY for *strictly causal*
  `f` — every feedback path passes through a register, so the output at time `t`
  depends only on inputs strictly before `t`.

  Soundness.  An unrestricted `∀ f, loop f = f (loop f)` is FALSE: take
  `f s = ~~~s` (pointwise Bool negation); it has no fixpoint, and the equation
  would give `b = !b`, hence `False`.  Restricting to `StrictlyCausal f` is
  sound: such an endofunction on `Nat → α` has a *unique* fixpoint, definable by
  well-founded recursion on the time index, so a model interpreting the opaque
  `loop` as that fixpoint exists.  The unsafe memoizing implementation computes
  exactly this fixpoint; the axiom is the formal stand-in for it.
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

/-- THE trusted axiom.  For a strictly causal endofunction, `Signal.loop`
    satisfies the fixpoint equation.  Sound because a strictly causal `f` has a
    unique fixpoint; see the file header. -/
axiom loop_unfold [Inhabited α] (f : Signal dom α → Signal dom α)
    (hf : StrictlyCausal f) : Signal.loop f = f (Signal.loop f)

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
