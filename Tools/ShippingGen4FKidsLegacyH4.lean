import Tools.ShippingGen4FKidsTac
import Tools.ShippingGen4FKidsTele
import Tools.ShippingGen4FKidsCanon
import Tools.ShippingGen4KWalkLegacyH1
import Tools.ShippingGen4FKidsLegacyH1
import Tools.ShippingGen4KWalkLegacyH2
import Tools.ShippingGen4FKidsLegacyH2
import Tools.ShippingGen4KWalkEmit
import Tools.ShippingGen4FKidsEmit
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH4 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplKS part 4: the CompilerM-level telescope shims (`CompilerM.withLocalDecl`, `CompilerM.withLetDecl`) from `MemoTele.localDecl` / `MemoTele.letDecl`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4FKidsLegacyH4
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
open Tools.ShippingGen4KWalkProjField
open Tools.ShippingGen4FKidsProjField

open Tools.ShippingGen4FKids
open Tools.ShippingGen4FKidsCalc
open Tools.ShippingGen4FKidsPrims
open Tools.ShippingGen4FKidsTac
open Tools.ShippingGen4FKidsTele

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section H4
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hS

theorem withLocalDeclPKS (hA : AdmCtx O.quiet mctx cctx) {α : Type} (n : Name) (ty : Lean.Expr)
    (k : Lean.Expr → CompilerM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' → ∀ x,
      KeepsCS mctx' mref cctx' cref I (k x)) :
    KeepsCS mctx mref cctx cref I (CompilerM.withLocalDecl n ty k) := by
  intro ctx st hc
  unfold CompilerM.withLocalDecl
  exact Keeps.bind (KeepsCS.lift (M.tele.localDecl I hA hS.1 hS.2 n ty (fun fvar => (k fvar ctx).run st)
    (fun mctx' cctx' x hA' => hk mctx' cctx' hA' x ctx st hc)) ctx st hc) (fun p => Keeps.pure _)

theorem withLetDeclPKS (hA : AdmCtx O.quiet mctx cctx) {α : Type} (n : Name) (ty v : Lean.Expr)
    (k : Lean.Expr → CompilerM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' → ∀ x,
      KeepsCS mctx' mref cctx' cref I (k x)) :
    KeepsCS mctx mref cctx cref I (CompilerM.withLetDecl n ty v k) := by
  intro ctx st hc
  unfold CompilerM.withLetDecl
  exact Keeps.bind (KeepsCS.lift (M.tele.letDecl I hA hS.1 hS.2 n ty v (fun fvar => (k fvar ctx).run st)
    (fun mctx' cctx' x hA' => hk mctx' cctx' hA' x ctx st hc)) ctx st hc) (fun p => Keeps.pure _)

end H4

end Tools.ShippingGen4FKidsLegacyH4
