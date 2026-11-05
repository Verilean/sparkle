import Tools.ShippingGen5PParamFinal
set_option autoImplicit false

/-! # Gen5 port, stage 1: the minimal old root (scripts/gen4/PARAM_ASSEMBLY.md §Gen5)

`legalBinding_allPos : LegalBinding D θ → AllPos θ` exists, so B.P-1 (`hpos`) is not an independent binder of the comparison root:
`paramFinal_min` keeps only `hL` (B.P-8) and derives `AllPos θ` from it. The binder difference to the run root `paramFinal_run`
is then `[hL]` removed against `[M, hmsg, htel]` added; the earlier `[hL, hpos]` is not counted as two. No new assumption. -/

namespace Tools.ShippingGen5PMinRoot
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingEntrySoundness Tools.ShippingGen4ParamAssembly

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- the comparison root: B.P-8 (`hL`) is the only ledger binder; `hpos` is derived by `legalBinding_allPos` -/
theorem paramFinal_min {L : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context} {declName : Name}
    {θ : List (String × Nat)} {w w' : Void IO.RealWorld} {M' : Sparkle.IR.AST.Module}
    {D' : Sparkle.IR.AST.Design} {e : Sparkle.IR.AST.Expr}
    (hS : Start L mctx cctx w)
    (h : RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w')
    (hL : Tools.ShippingGen4ParamIface.LegalBinding (Tools.ShippingGen4Shape.SpecDesign M' D') θ)
    (hok : Tools.ShippingGen4ParamBridgeSpecExpr.ExprOK θ e) : RootConcl M' D' θ e :=
  Tools.ShippingGen4ParamFinal.paramFinal_old hS h hL
    (Tools.ShippingGen4ParamBridgeLegal.legalBinding_allPos hL) hok

end Tools.ShippingGen5PMinRoot

#print axioms Tools.ShippingGen5PMinRoot.paramFinal_min
