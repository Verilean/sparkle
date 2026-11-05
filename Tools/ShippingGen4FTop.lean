import Tools.ShippingGen4FThetaTele
set_option autoImplicit false

/-! # F-top: the returned top module carries the name check and the parameter coverage (scripts/gen4/FTOP_FREEZE.md) -/

namespace Tools.ShippingGen4FTop
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingLegacySem Tools.ShippingGen4ParamEntry Tools.ShippingGen4FTheta

/-- the symbolic-mode body test of `finishSynth` -/
def SeqFree (m : Sparkle.IR.AST.Module) : Prop :=
  (m.body.any fun stmt => match stmt with
    | .register .. | .memory .. | .inst .. => true
    | _ => false) = false

theorem fTop_finish (htel : LamTelescopeN)
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Design}
    (hr : MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D)) :
    ∃ fcs : CircuitState,
      M = fcs.module.finalize ∧ D = fcs.design ∧
      Sparkle.IR.ModuleNameCheck.check (fcs.module :: fcs.design.modules) = true ∧
      (∀ p ∈ parameters, ∃ q ∈ fcs.module.parameters, q.name = p.1) ∧
      SeqFree fcs.module := by
  unfold synthesizeFromConst at hr
  simp only [certifiedShape_off true parameters (.defnInfo dv) (by simp),
    mixedCertifiedShape_off true parameters (.defnInfo dv) isInst (by simp), ite_self,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hr
  obtain ⟨y, hy, a3⟩ := MReturns.bind hr
  obtain rfl := MReturns.pure hy
  dsimp only at a3
  obtain ⟨y2, hy2, h2⟩ := MReturns.bind a3
  obtain rfl := MReturns.pure hy2
  dsimp only at h2
  obtain ⟨_, _, h5⟩ := MReturns.bind h2
  obtain ⟨_, _, h6⟩ := MReturns.bind h5
  obtain ⟨_, _, h7⟩ := MReturns.bind h6
  obtain ⟨_, _, h8⟩ := MReturns.bind h7
  obtain ⟨body0, hopen, h9⟩ := MReturns.bind h8
  obtain ⟨_, _, h10⟩ := MReturns.bind h9
  obtain ⟨_, _, h11⟩ := MReturns.bind h10
  obtain ⟨mctx, xs, inner, -, h12⟩ :=
    telescopeIn_of_lamTelescopeN htel (stripMemoizeWrappers body0) _ _ _ h11
  obtain ⟨_, _, h13⟩ := MRunsIn.bind h12
  obtain ⟨_, _, h14⟩ := MRunsIn.bind h13
  obtain ⟨_, _, h15⟩ := MRunsIn.bind h14
  obtain ⟨_, _, h16⟩ := MRunsIn.bind h15
  obtain ⟨_, _, h17⟩ := MRunsIn.bind h16
  obtain ⟨_, _, h18⟩ := MRunsIn.bind h17
  obtain ⟨⟨_, fcs⟩, _, h19⟩ := MRunsIn.bind h18
  obtain ⟨res, hfin, h20⟩ := MRunsIn.bind h19
  have e := MRunsIn.pure h20
  subst e
  obtain ⟨mref, cctx, cref, w, w', hrun⟩ := hfin
  obtain ⟨hb, hp, hc, hM, hD⟩ := finishSynth_symbolic hrun
  exact ⟨fcs, hM, hD, hc, hp, hb⟩

end Tools.ShippingGen4FTop
