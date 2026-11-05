import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH9
import Tools.ShippingGen4FKidsLegacyH9
-- NOT BUILT, NOT IN THE LAKEFILE (rt176): LegacyImplKS part 10b: `toIR` (induction on a size bound).
-- Takes `MemoFamily` (TRUSTED, approved) and `MsgMvK` as HYPOTHESES; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH10b
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
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4KWalkHelpers
open Tools.ShippingGen4FKidsHelpers
open Tools.ShippingChildLegacyHelpersA
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkEmit
open Tools.ShippingGen4FKidsEmit
open Tools.ShippingGen4KWalkLegacyRules
open Tools.ShippingGen4FKidsLegacyRules
open Tools.ShippingGen4KWalkLegacyH4
open Tools.ShippingGen4FKidsLegacyH4
open Tools.ShippingGen4KWalkCanon
open Tools.ShippingGen4FKidsCanon
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4FKidsLegacyH7
open Tools.ShippingGen4KWalkLegacyH1
open Tools.ShippingGen4FKidsLegacyH1
open Tools.ShippingGen4KWalkLegacyH2
open Tools.ShippingGen4FKidsLegacyH2
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField
open Tools.ShippingGen4KWalkDiag
open Tools.ShippingGen4FKidsDiag
open Tools.ShippingGen4KWalkLegacyH8a
open Tools.ShippingGen4FKidsLegacyH8a
open Tools.ShippingGen4KWalkLegacyH8
open Tools.ShippingGen4FKidsLegacyH8
open Tools.ShippingGen4KWalkLegacyH3
open Tools.ShippingGen4FKidsLegacyH3
open Tools.ShippingGen4KWalkLegacyH5
open Tools.ShippingGen4FKidsLegacyH5
open Tools.ShippingGen4KWalkLegacyH6
open Tools.ShippingGen4FKidsLegacyH6
open Tools.ShippingGen4KWalkLegacyH9
open Tools.ShippingGen4FKidsLegacyH9
open Tools.ShippingGen4KWalkLegacyH7
open Tools.ShippingGen4FKidsLegacyH7
open Tools.ShippingGen4KWalkTranslate
open Tools.ShippingGen4FKidsTranslate

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H10
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) (hpp : PpMvKS O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I) (hmsg : MsgMvK O)
include M hpp hS hmsg

theorem toIRK_boundS (wireS : String) (fvarId : FVarId) :
    ∀ (n : Nat) (e : Lean.Expr), sizeOf e < n →
      ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        KeepsCS mctx mref cctx cref I (Rec.translateExprToWireImpl.toIR wireS fvarId e)
  | 0, _, h => by omega
  | n + 1, e, h => by
    intro mctx cctx hA
    have ih := fun (mctx : Meta.Context) (cctx : Core.Context)
      (hA : AdmCtx O.quiet mctx cctx) e' (h' : sizeOf e' < n) => toIRK_boundS wireS fvarId n e' h' mctx cctx hA
    unfold Rec.translateExprToWireImpl.toIR
    kwAll3

theorem toIRKS (wireS : String) (fvarId : FVarId) (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) :
    KeepsCS mctx mref cctx cref I (Rec.translateExprToWireImpl.toIR wireS fvarId e) :=
  toIRK_boundS M hpp hS hmsg wireS fvarId (sizeOf e + 1) e (Nat.lt_succ_self _) mctx cctx hA

end H10

end Tools.ShippingGen4FKidsLegacyH10b
