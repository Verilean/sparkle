import Tools.ShippingLetsReaderInvPure
import Tools.ShippingReaderFuelVerbatim

/-! # Unit LC3 (pure facts, matcher-sensitive): the bare-register view

BUILT: lc3h3 exit 0. No `sorry`, no axiom, no `native_decide`.

`regView?` is one of the two matchers v4.32.1 cannot split (name literal + array literal patterns). It is
analysed from its definition with the technique of `regMatch_view`
(`Tools/ShippingReaderFuelVerbatim.lean`): unfold, split the scrutinees into constructors, unfold the sparse
case analyses, split the resulting `dite`s. -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel Tools.ShippingSparseCasesTac

set_option maxHeartbeats 16000000 in
theorem regView_ok (n : Nat) (fn : Lean.Expr) (args : Array Lean.Expr) (d α i x : Lean.Expr)
    (hall : ∀ a ∈ args, LetOk n a = true) (h : regView? fn args = some (d, α, i, x)) :
    LetOk n d = true ∧ LetOk n x = true := by
  revert h
  unfold regView?
  rcases args with ⟨L⟩
  cases fn with
  | const nm us =>
    rcases nm with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold_matchers_aux)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals first
      | (intro hh; cases hh; done)
      | (subst_vars; intro hh; cases hh; done)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, L'⟩⟩⟩⟩⟩ <;>
          first
            | (intro hh; cases hh; done)
            | (subst_vars; intro hh; cases hh; done)
            | (subst_vars; intro hh
               injection hh with h1
               injection h1 with hd h2
               injection h2 with hα h3
               injection h3 with hi hx
               subst hd
               subst hx
               exact ⟨hall a1 (by simp), hall a4 (by simp)⟩)
            | (exfalso; simp at *; done)
            | (exfalso; simp at *; omega))
  | _ => intro hh; cases hh

end Tools.ShippingLetsReaderInv
