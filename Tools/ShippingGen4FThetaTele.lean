import Tools.ShippingGen4FTheta
import Tools.ShippingLegacySemTelescopeN
set_option autoImplicit false
-- F-θ, `htele` from `LamTelescopeN` (option A of the reviewer consultation, 2026-11-05). No sorry / axiom / native_decide.

/-! # `htele` of `fTheta_natBinder` from the existing Meta-library fact `LamTelescopeN`

`lams_split`: every expression is a maximal lambda prefix `lams sp b` over a body `b` that is not a lambda (structural, by
induction on the expression). With it, `TelescopeIn e (fun _ _ _ => True)` for EVERY `e` follows from `LamTelescopeN`
(`Tools/ShippingLegacySemTelescopeN.lean`, an unproved Meta-library premise already taken by the legacy-walk theorems), the
`DeclsOpen` part being dropped. `fTheta_natBinderN` is `fTheta_natBinder` with `htele` replaced by `LamTelescopeN`.
Whether `LamTelescopeN` is counted as a ledger row is the reviewer's decision (it is in neither ledger today). -/

namespace Tools.ShippingGen4FTheta
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingLegacySem Tools.ShippingGen4ParamEntry

theorem lams_split : ∀ e : Lean.Expr, ∃ (sp : List (Name × Lean.Expr × BinderInfo)) (b : Lean.Expr),
    e = lams sp b ∧ b.isLambda = false
  | .lam n d body bi => by
    obtain ⟨sp, b, he, hb⟩ := lams_split body
    exact ⟨(n, d, bi) :: sp, b, by rw [he]; rfl, hb⟩
  | .bvar i => ⟨[], .bvar i, rfl, rfl⟩
  | .fvar i => ⟨[], .fvar i, rfl, rfl⟩
  | .mvar i => ⟨[], .mvar i, rfl, rfl⟩
  | .sort u => ⟨[], .sort u, rfl, rfl⟩
  | .const n us => ⟨[], .const n us, rfl, rfl⟩
  | .app f a => ⟨[], .app f a, rfl, rfl⟩
  | .forallE n d b bi => ⟨[], .forallE n d b bi, rfl, rfl⟩
  | .letE n t v b nd => ⟨[], .letE n t v b nd, rfl, rfl⟩
  | .lit l => ⟨[], .lit l, rfl, rfl⟩
  | .mdata m e => ⟨[], .mdata m e, rfl, rfl⟩
  | .proj s i e => ⟨[], .proj s i e, rfl, rfl⟩

theorem telescopeIn_of_lamTelescopeN (htel : LamTelescopeN) (e : Lean.Expr) :
    TelescopeIn e (fun _ _ _ => True) := by
  intro α k r hrun
  obtain ⟨sp, b, rfl, hb⟩ := lams_split e
  obtain ⟨mctx, ids, -, hk⟩ := htel sp b hb α k r hrun
  exact ⟨mctx, _, _, trivial, hk⟩

/-- `fTheta_natBinder` with `htele` supplied by `LamTelescopeN`. -/
theorem fTheta_natBinderN (htel : LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D)) :
    ∃ (body0 : Lean.Expr) (mctx : Meta.Context) (xs : Array Lean.Expr),
      MReturns (openRecordInputs dv.value) body0 ∧
      ∀ p ∈ parameters, ∃ x ∈ xs, NatBinderAt mctx p.1 x :=
  fTheta_natBinder (fun body0 _ => telescopeIn_of_lamTelescopeN htel (stripMemoizeWrappers body0)) hr

end Tools.ShippingGen4FTheta

#print axioms Tools.ShippingGen4FTheta.lams_split
#print axioms Tools.ShippingGen4FTheta.telescopeIn_of_lamTelescopeN
#print axioms Tools.ShippingGen4FTheta.fTheta_natBinderN
