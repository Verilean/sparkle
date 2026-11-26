import Lean
import Sparkle.Core.Signal

/-!
# Congruence of a nested loop (`sparkle-ved-memory-rest`)

A `Signal.loop` inside the body of another loop is driven by the outer state `s`.  The side condition of the outer
loop's strong fixpoint equation (`Tools.VedMem.loop_val_unfold_strong`) compares the body over two signals `s₁`, `s₂`
that agree up to `t`, so the inner loop appears over both: `loop_val_congr_le` is the congruence for it, bounded
by the time `T` at which the inner loop is read.
-/

namespace Tools.VedMemNest

open Sparkle.Core.Signal Sparkle.Core.Domain

theorem loop_val_congr_le {dom : DomainConfig} {α : Type} [Inhabited α]
    (F G : Signal dom α → Signal dom α) (T : Nat)
    (h0 : ∀ a b : Signal dom α, (F a).val 0 = (G b).val 0)
    (hS : ∀ t : Nat, t < T → ∀ a b : Signal dom α, (∀ k, k ≤ t → a.val k = b.val k) →
      (F a).val (t + 1) = (G b).val (t + 1)) :
    ∀ t : Nat, t ≤ T → (Signal.loop F).val t = (Signal.loop G).val t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    show Signal.loopGo F t = Signal.loopGo G t
    rw [Signal.loopGo_eq F t, Signal.loopGo_eq G t]
    cases t with
    | zero => exact h0 _ _
    | succ u =>
      apply hS u (by omega)
      intro k hk
      show (if k < u + 1 then Signal.loopGo F k else default) = (if k < u + 1 then Signal.loopGo G k else default)
      rw [if_pos (Nat.lt_succ_of_le hk), if_pos (Nat.lt_succ_of_le hk)]
      exact ih k (by omega) (by omega)

end Tools.VedMemNest
