import Tools.ShippingChildCanonKeyA
import Tools.ShippingChildLegacyCachedA
import Tools.ShippingChildDepthA
-- BUILT (unit A, round 2): c1 exit 1 (opens), c2 exit 0. No `sorry`, no `axiom`, no `native_decide`, no new law / boundary
-- field; law witness `O : RefLawsAOps MkRefd mref cref` only (no `RefLawsATele`).
/-! # The fallback / translator / certified body with two premises fewer

`legacyCachedA_of_impl` and `canonKeyA` discharge `LegacyCachedA` and `CanonKeyA`; the
corollaries below are the earlier theorems with those two arguments removed (the statements are
the old ones minus `hCached` / `hcanon`; nothing is restated). Remaining handler premises:
`LegacyImplA`, `ProjFieldNameA`, `ChildEntryA` (resp. `ChildKeepsA`). -/
namespace Tools.ShippingChildImplCorA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildVCA
open Tools.ShippingChildVertA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildDepthA
open Tools.ShippingChildLegacyCachedA
open Tools.ShippingChildCanonKeyA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The fallback**, premises `LegacyImplA`, `ProjFieldNameA`, `ChildEntryA` only. -/
theorem translateFallbackA_of_impl (O : RefLawsAOps MkRefd mref cref)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) (tenv : Lean.Environment)
    (hImpl : LegacyImplA O I) (hpf : ProjFieldNameA O I) (hchild : ChildEntryA O I)
    (rec : TranslateFn) (hrec : RecA O I rec) : RecA O I (translateFallback tenv rec) :=
  translateFallbackA O hS tenv hImpl (legacyCachedA_of_impl O hS hImpl) (canonKeyA O hS) hpf
    hchild rec hrec

/-- **The shipping translator keeps a stable `I`**, premises `LegacyImplA`, `ProjFieldNameA`,
`ChildEntryA` only. -/
theorem translate_keepsA_of_impl (O : RefLawsAOps MkRefd mref cref)
    {I : Void IO.RealWorld → Prop} (hS : StableA O.quiet I) (tenv : Lean.Environment)
    (hImpl : LegacyImplA O I) (hpf : ProjFieldNameA O I) (hchild : ChildEntryA O I) :
    RecA O I (fun e h t n => translateExprToWire tenv e h t n) :=
  translate_keepsA O hS tenv hImpl (legacyCachedA_of_impl O hS hImpl) (canonKeyA O hS) hpf hchild

/-- **The translator at `JQ O.quiet D`**, premises `LegacyImplA`, `ProjFieldNameA`,
`ChildKeepsA` only. -/
theorem translate_keepsJQ_of_impl (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (tenv : Lean.Environment) (hImpl : LegacyImplA O (JQ O.quiet D))
    (hpf : ProjFieldNameA O (JQ O.quiet D)) (hC : ChildKeepsA O D) :
    RecA O (JQ O.quiet D) (fun e h t n => translateExprToWire tenv e h t n) :=
  translate_keepsJQ O D tenv hImpl (legacyCachedA_of_impl O (stableA_JQ _ D) hImpl)
    (canonKeyA O (stableA_JQ _ D)) hpf hC

/-- **`bodyStepA_certified` with `hCached` and `hcanon` discharged**: premises `LegacyImplA`,
`ProjFieldNameA`, `ChildKeepsA` only. -/
theorem bodyStepA_certified' (O : RefLawsAOps MkRefd mref cref) (D : Nat)
    (hImpl : LegacyImplA O (JQ O.quiet D)) (hpf : ProjFieldNameA O (JQ O.quiet D))
    (hC : ChildKeepsA O D) (mctx : Meta.Context) (cctx : Core.Context)
    (hA : AdmCtx O.quiet mctx cctx) (declName : Name) (tenv : Lean.Environment) (b : Bool)
    (ci : ConstantInfo) (isInst : Lean.Expr → Bool) {bs : List (Name × GateBinder)}
    {body : Lean.Expr} (hshape : certifiedShape? false [] ci = some (bs, body)) :
    Keeps mctx mref cctx cref (JQ O.quiet D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false true ci isInst) :=
  bodyStepA_certified O D hImpl (legacyCachedA_of_impl O (stableA_JQ _ D) hImpl)
    (canonKeyA O (stableA_JQ _ D)) hpf hC mctx cctx hA declName tenv b ci isInst hshape

end Tools.ShippingChildImplCorA
