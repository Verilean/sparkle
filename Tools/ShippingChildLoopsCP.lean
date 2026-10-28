import Tools.ShippingChildTranslateA
-- BUILT (unit A, round 2): a1 exit 1 (CanonKeyA print only; this file built in it), a10 exit 0. No `sorry`, no `axiom`, no `native_decide`, no law.
/-! # `forIn` and `fuelFixM` under `KeepsCP`

Law-free calculus lemmas for `CompilerM` programs under the restricted triple (`CtxOk`
contexts): `for` loops over a `List` / `Array` / `Std.Legacy.Range` (the body at every element
and accumulator), and the fuel induction of `fuelFixM` in `CompilerM` (fixed Meta/Core contexts:
the recursion never changes them). -/
namespace Tools.ShippingChildLoopsCP
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildTranslateA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem KeepsCP.forIn_list {α β : Type} {I : Void IO.RealWorld → Prop}
    (f : α → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCP mctx mref cctx cref I (f a b)) :
    ∀ (l : List α) (b : β), KeepsCP mctx mref cctx cref I (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact KeepsCP.pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine KeepsCP.bind (hf a b) (fun r => ?_)
    cases r with
    | done b' => exact KeepsCP.pure b'
    | yield b' => exact KeepsCP.forIn_list f hf l b'

theorem KeepsCP.forIn_array {α β : Type} {I : Void IO.RealWorld → Prop}
    (f : α → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCP mctx mref cctx cref I (f a b))
    (as : Array α) (b : β) : KeepsCP mctx mref cctx cref I (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact KeepsCP.forIn_list f hf _ b

theorem KeepsCP.forIn_range {β : Type} {I : Void IO.RealWorld → Prop}
    (f : Nat → β → CompilerM (ForInStep β))
    (hf : ∀ a b, KeepsCP mctx mref cctx cref I (f a b))
    (r : Std.Legacy.Range) (b : β) : KeepsCP mctx mref cctx cref I (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact KeepsCP.forIn_list f hf _ b

/-- `fuelFixM` in `CompilerM`: a step that keeps `I` whenever its recursive argument does (at
the same contexts) gives a fixpoint that keeps it at every fuel. -/
theorem KeepsCP.fuelFixM {I : Void IO.RealWorld → Prop} {α β : Type}
    (step : (α → CompilerM β) → α → CompilerM β)
    (hstep : ∀ rec : α → CompilerM β,
      (∀ a, KeepsCP mctx mref cctx cref I (rec a)) →
      ∀ a, KeepsCP mctx mref cctx cref I (step rec a)) :
    ∀ (k : Nat) (a : α), KeepsCP mctx mref cctx cref I (Sparkle.Compiler.Elab.fuelFixM step k a)
  | 0, a => by
    unfold Sparkle.Compiler.Elab.fuelFixM
    exact KeepsCP.throw _ (by okmsg)
  | k + 1, a => by
    unfold Sparkle.Compiler.Elab.fuelFixM
    exact hstep _ (KeepsCP.fuelFixM step hstep k) a

end Tools.ShippingChildLoopsCP
