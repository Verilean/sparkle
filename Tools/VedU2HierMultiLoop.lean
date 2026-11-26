import Sparkle.Core.Signal

/-!
# H3-open: a loop whose body reads a child's output at a signal computed from the loop's own state

`Signal.loop f` with `f live = F (Os live) live`: the body `F` takes the oracle values `o` (the outputs of the child
instances, free signals in the open parent) and the live state; `Os live` is the oracle the REAL children give when
their data inputs are computed from `live` (`Os live = (G e₁[live], …, G e_N[live])`).  The open parent of the
hierarchical checker is the loop with the oracle held FIXED, `loop (F o)`.

`loop_knot`: the declaration's loop `Q = loop (fun x => F (Os x) x)` IS the open loop with the oracle fixed at the
value it has along `Q`: `Q = loop (F (Os Q))`.  The three hypotheses are facts about the circuit body, proved by the
generated script for the concrete body:

* `hcF`: the body is causal in the state (the value at `t` reads `x` only below `t`: registers delay by one);
* `hcO`: the value at `t` reads the oracle only below `t` (`E o o' t`: the oracles agree below `t`);
* `hOs`: the oracle computed from the state at `s < t` reads the state at `s` only.

Nothing is assumed about the child: `Os` is the declaration's own term, `E` the generated agreement.
-/

namespace Tools.VedU2HierMulti

open Sparkle.Core.Domain Sparkle.Core.Signal

/-- A causal loop body has at most one fixed point, and it is the loop. -/
theorem loop_unique {dom : DomainConfig} {α : Type} [Inhabited α]
    (f : Signal dom α → Signal dom α)
    (hc : ∀ t (x y : Signal dom α), (∀ i, i < t → x.val i = y.val i) → (f x).val t = (f y).val t)
    (X : Signal dom α) (hX : ∀ t, (f X).val t = X.val t) :
    ∀ t, (Signal.loop f).val t = X.val t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    show Signal.loopGo f t = X.val t
    rw [Signal.loopGo_eq]
    have h1 := hc t ⟨fun i => if i < t then Signal.loopGo f i else default⟩ X (fun i hi => by
      show (if i < t then Signal.loopGo f i else default) = X.val i
      rw [if_pos hi]
      exact ih i hi)
    rw [h1]
    exact hX t

/-- The knot: see the module doc. -/
theorem loop_knot {dom : DomainConfig} {α : Type} [Inhabited α] {O : Type}
    (F : O → Signal dom α → Signal dom α) (Os : Signal dom α → O) (E : O → O → Nat → Prop)
    (hcF : ∀ o t (x y : Signal dom α), (∀ i, i < t → x.val i = y.val i) → (F o x).val t = (F o y).val t)
    (hcO : ∀ o o' (x : Signal dom α) t, E o o' t → (F o x).val t = (F o' x).val t)
    (hOs : ∀ t (x y : Signal dom α), (∀ i, i < t → x.val i = y.val i) → E (Os x) (Os y) t) :
    ∀ t, (Signal.loop (fun x => F (Os x) x)).val t
      = (Signal.loop (F (Os (Signal.loop (fun x => F (Os x) x))))).val t := by
  intro t0
  generalize hQ : Signal.loop (fun x => F (Os x) x) = Q
  have hfix : ∀ t, (F (Os Q) Q).val t = Q.val t := by
    intro t
    have hQt : Q.val t = (F (Os ⟨fun i => if i < t then Signal.loopGo (fun x => F (Os x) x) i else default⟩)
        ⟨fun i => if i < t then Signal.loopGo (fun x => F (Os x) x) i else default⟩).val t := by
      rw [← hQ]
      show Signal.loopGo (fun x => F (Os x) x) t = _
      rw [Signal.loopGo_eq]
    have hpre : ∀ i, i < t → Q.val i = (⟨fun i => if i < t then Signal.loopGo (fun x => F (Os x) x) i else default⟩ :
        Signal dom α).val i := by
      intro i hi
      rw [← hQ]
      show Signal.loopGo (fun x => F (Os x) x) i = (if i < t then Signal.loopGo (fun x => F (Os x) x) i else default)
      rw [if_pos hi]
    rw [hQt]
    calc (F (Os Q) Q).val t
        = (F (Os Q) ⟨fun i => if i < t then Signal.loopGo (fun x => F (Os x) x) i else default⟩).val t :=
          hcF _ t _ _ hpre
      _ = _ := hcO _ _ _ t (hOs t _ _ hpre)
  exact ((loop_unique (F (Os Q)) (hcF _) Q hfix t0).symm)

/-- Two signals with the same values are equal. -/
theorem signal_ext {dom : DomainConfig} {α : Type} {s s' : Signal dom α}
    (h : ∀ t, s.val t = s'.val t) : s = s' := by
  cases s; cases s'
  congr
  funext t
  exact h t

end Tools.VedU2HierMulti
