-- Gen5 port of Tools.ShippingGen4ParamFinal (scripts/gen4/PARAM_ASSEMBLY.md §Gen5): copy for the gen5 Elab; only the marked parts differ.
import Tools.ShippingGen2Defs
import Tools.ShippingGen5PParamAssembly
set_option autoImplicit false

/-! # M4 parametric assembly, final-root form (scripts/gen4/PARAM_ASSEMBLY.md §Final)

The roots of `ShippingGen4ParamAssembly` take `O`, `hA`, `hw` as free binders. In the gen5 final statement (`FGLedgerPremisesStmtG/H (on the gen5 branch)`)
those are not free: `L : Laws` (A.P-01) gives `O := L.O`, and `Start L mctx cctx w` (A.P-02 = `AdmCtx ∧ JQC`, first conjunct of
`EntryWitness`) gives `hA` and `hw`. `start_kwd` is that bridge (no new assumption). `paramFinal_old` / `paramFinal_run` are the two
roots over the FG binders `L`, `hS : Start ..`, the run. -/

namespace Tools.ShippingGen4ParamFinal
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingEntrySoundness Tools.ShippingChildInvA Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalkDepth Tools.ShippingGen4KWalkDiag Tools.ShippingLegacySem Tools.ShippingGen4ParamAssembly

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- `Start` (A.P-02, `AdmCtx ∧ JQC`) gives the admissible context and the K start world of the run form. -/
theorem start_kwd {L : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld}
    (h : Start L mctx cctx w) :
    AdmCtx L.O.quiet mctx cctx ∧ KWD L.O (fun _ _ => True) 0 w :=
  ⟨h.1, ⟨h.2.1.1, h.2.1.2.1, trivial⟩, h.2.1.2.2⟩

/-- the FG-binder form with B.P-8 (`hL`) and B.P-1 (`hpos`) as binders -/
theorem paramFinal_old {L : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {declName : Name}
    {θ : List (String × Nat)} {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module}
    {D' : Sparkle.IR.AST.Design} {e : Sparkle.IR.AST.Expr}
    (hS : Start L mctx cctx w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w')
    (hL : Tools.ShippingGen4ParamIface.LegalBinding (Tools.ShippingGen4Shape.SpecDesign M' D') θ)
    (hpos : Tools.ShippingGen4ParamLayerA.AllPos θ)
    (hok : Tools.ShippingGen4ParamBridgeSpecExpr.ExprOK θ e) : RootConcl M' D' θ e :=
  paramRoot_old h hL hpos hok

/-- the FG-binder form from the run: `L`, `Start` and the run are the FG binders; B.P-8 / B.P-1 are derived -/
theorem paramFinal_run {L : Laws mref cref} (M : MemoFamily L.O) (hmsg : MsgMvK L.O) (htel : LamTelescopeN)
    {mctx : Meta.Context} {cctx : Core.Context} {declName : Name}
    {θ : List (String × Nat)} {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module}
    {D' : Sparkle.IR.AST.Design} {e : Sparkle.IR.AST.Expr}
    (hS : Start L mctx cctx w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w')
    (hok : Tools.ShippingGen4ParamBridgeSpecExpr.ExprOK θ e) : RootConcl M' D' θ e :=
  paramRoot_run M hmsg htel (start_kwd hS).1 (start_kwd hS).2 h hok

end Tools.ShippingGen4ParamFinal

#print axioms Tools.ShippingGen4ParamFinal.start_kwd
#print axioms Tools.ShippingGen4ParamFinal.paramFinal_old
#print axioms Tools.ShippingGen4ParamFinal.paramFinal_run
