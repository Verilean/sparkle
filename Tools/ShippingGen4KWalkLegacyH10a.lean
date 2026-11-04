import Tools.ShippingGen4KWalkLegacyH9
-- NOT BUILT, NOT IN THE LAKEFILE (rt176): LegacyImplK part 10a: `getPrimitiveNameFromLambda`.
-- Takes `MemoFamily` (TRUSTED, approved) and `MsgMvK` as HYPOTHESES; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyH10a
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildPathA
open Tools.ShippingChildTranslateA
open Tools.ShippingGen4KWalkTac2
open Tools.ShippingChildWalkA
open Tools.Assume.MemoFamily
open Tools.ShippingGen4KWalk
open Tools.ShippingGen4KWalkPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4KWalkLegacyH8a
open Tools.ShippingGen4KWalkLegacyH8
open Tools.ShippingGen4KWalkLegacyH3
open Tools.ShippingGen4KWalkLegacyH5
open Tools.ShippingGen4KWalkLegacyH6
open Tools.ShippingGen4KWalkLegacyH9
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4KWalkTranslate

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H10
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvK O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O)
include M hpp hS hmsg

theorem getPrimK (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCP mctx mref cctx cref I (Rec.getPrimitiveNameFromLambda e) := by
  induction e with
  | lam _ _ body _ _ ih => unfold Rec.getPrimitiveNameFromLambda; exact ih
  | _ => unfold Rec.getPrimitiveNameFromLambda; kwAll3

end H10

end Tools.ShippingGen4KWalkLegacyH10a
