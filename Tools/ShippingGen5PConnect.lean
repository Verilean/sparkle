import Tools.ShippingGen5PMinRoot
import Tools.ShippingGen5SM1
set_option autoImplicit false

/-! # Gen5 port, stage 2: the assembly from the parametric disjunct of `EntryWitness` (scripts/gen4/PARAM_ASSEMBLY.md §Gen5)

`EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D` (the hypothesis of `FG_COND`, `FGLedgerPremisesStmtG/H`) is
`Start L mctx cctx w ∧ (RunsTo (synthesizeCombinational ..) ∨ RunsTo (synthesizeCombinationalWithParameters declName parameters) ..) ∧ ReflectsAll ..`.
`entry_param_assembly` takes the witness and the parametric disjunct and gives `AllPos θ`, legality when the top does not collide with a
module of `D`, and `LegalBinding ↔ θ = []` when it does. `fgParamRoot` is the statement over the binders of H that carry the witness
(`ReflectsAll`, `L`, then the witness quantifiers of `FGLedgerPremisesStmtH`), proved from `MemoFamily`, `MsgMvK`, `LamTelescopeN` only. -/

namespace Tools.ShippingGen5PConnect
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingEntrySoundness Tools.Assume.MemoFamily
open Tools.ShippingGen4ParamAssembly Tools.ShippingGen4KWalkDiag Tools.ShippingLegacySem Tools.ShippingGen5FG

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- the assembly conclusion for a parametric run: `AllPos`, legality without a same-name collision, and the collision branch -/
def AssemblyConcl (M' : Sparkle.IR.AST.Module) (D' : Sparkle.IR.AST.Design) (θ : List (String × Nat)) : Prop :=
  Tools.ShippingGen4ParamLayerA.AllPos θ ∧
  (¬ Collides M' D' → Tools.ShippingGen4ParamIface.LegalBinding (Tools.ShippingGen4Shape.SpecDesign M' D') θ) ∧
  (Collides M' D' → (Tools.ShippingGen4ParamIface.LegalBinding (Tools.ShippingGen4Shape.SpecDesign M' D') θ ↔ θ = []))

/-- the assembly from the witness and its parametric disjunct (no `ReflectsAll` is used) -/
theorem entry_param_assembly {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    (M : MemoFamily L.O) (hmsg : MsgMvK L.O) (htel : LamTelescopeN)
    {declName : Name} {θ : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hE : EntryWitness ReflectsAll L declName θ mctx cctx w w' M' D')
    (hpar : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w') :
    AssemblyConcl M' D' θ :=
  legal_assembly M hmsg htel (Tools.ShippingGen4ParamFinal.start_kwd hE.1).1
    (Tools.ShippingGen4ParamFinal.start_kwd hE.1).2 hpar

/-- the witness is on one of the two routes: the default route, or the parametric route with the assembly -/
theorem entry_route {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    (M : MemoFamily L.O) (hmsg : MsgMvK L.O) (htel : LamTelescopeN)
    {declName : Name} {θ : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hE : EntryWitness ReflectsAll L declName θ mctx cctx w w' M' D') :
    RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w' ∨
      (RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' ∧ AssemblyConcl M' D' θ) :=
  hE.2.1.imp id fun hpar => ⟨hpar, entry_param_assembly M hmsg htel hE hpar⟩

/-- the same-name collision with a non-empty binding: `SpecDesign = D'`, and legality fails, so the real `specializeDesign` cannot succeed -/
theorem collision_not_legal {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    (M : MemoFamily L.O) (hmsg : MsgMvK L.O) (htel : LamTelescopeN)
    {declName : Name} {θ : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hE : EntryWitness ReflectsAll L declName θ mctx cctx w w' M' D')
    (hpar : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w')
    (hc : Collides M' D') (hne : θ ≠ []) :
    Tools.ShippingGen4Shape.SpecDesign M' D' = D' ∧
      ¬ Tools.ShippingGen4ParamIface.LegalBinding (Tools.ShippingGen4Shape.SpecDesign M' D') θ :=
  ⟨specDesign_of_collides hc, fun hl => hne ((entry_param_assembly M hmsg htel hE hpar).2.2 hc |>.mp hl)⟩

/-- the root over the witness binders of `FGLedgerPremisesStmtH`: on the parametric route, the specialization root conclusion -/
def FGParamRoot (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref) : Prop :=
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
    RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w' →
    ∀ e : Sparkle.IR.AST.Expr, Tools.ShippingGen4ParamBridgeSpecExpr.ExprOK parameters e → RootConcl b D parameters e

theorem fgParamRoot {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    (M : MemoFamily L.O) (hmsg : MsgMvK L.O) (htel : LamTelescopeN) : FGParamRoot ReflectsAll L :=
  fun _ _ _ _ _ _ _ _ hE hpar _ hok =>
    Tools.ShippingGen4ParamFinal.paramFinal_run M hmsg htel hE.1 hpar hok

/-- the comparison root over the same binders, with B.P-8 as the binder (`hpos` derived) -/
def FGParamRootMin (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref) : Prop :=
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
    RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w' →
    Tools.ShippingGen4ParamIface.LegalBinding (Tools.ShippingGen4Shape.SpecDesign b D) parameters →
    ∀ e : Sparkle.IR.AST.Expr, Tools.ShippingGen4ParamBridgeSpecExpr.ExprOK parameters e → RootConcl b D parameters e

theorem fgParamRootMin {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref} :
    FGParamRootMin ReflectsAll L :=
  fun _ _ _ _ _ _ _ _ hE hpar hL _ hok => Tools.ShippingGen5PMinRoot.paramFinal_min hE.1 hpar hL hok

end Tools.ShippingGen5PConnect

#print axioms Tools.ShippingGen5PConnect.entry_param_assembly
#print axioms Tools.ShippingGen5PConnect.entry_route
#print axioms Tools.ShippingGen5PConnect.collision_not_legal
#print axioms Tools.ShippingGen5PConnect.fgParamRoot
#print axioms Tools.ShippingGen5PConnect.fgParamRootMin
