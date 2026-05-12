import Sparkle

/-!
# Chapter 7 — reference solutions
-/

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Solutions.Ch07

/-- Solution to Ch07 §7.5 — 2:1 mux equivalence.

    `Signal.mux` is defined exactly as the if-expression on the
    underlying stream, so the equivalence is by definition. -/
theorem mux2_eq_behavioral {dom : DomainConfig}
    (sel : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    ∀ t,
      (Signal.mux sel a b).val t =
        (if sel.val t then a.val t else b.val t) := by
  intro t
  rfl

end Notebooks.Solutions.Ch07
