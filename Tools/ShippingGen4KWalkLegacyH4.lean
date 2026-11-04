import Tools.ShippingGen4KWalkLegacyH1
import Tools.ShippingGen4KWalkLegacyH2
import Tools.ShippingGen4KWalkEmit
-- BUILT: kjob lake build Tools.ShippingGen4KWalkLegacyH4 exit 0 (rt174, source as of d8c3ec7b); clean build is the coder's. LegacyImplK part 4: the CompilerM-level telescope shims (`CompilerM.withLocalDecl`, `CompilerM.withLetDecl`) from `MemoTele.localDecl` / `MemoTele.letDecl`.
-- Takes `MemoFamily` (TRUSTED, approved) as a HYPOTHESIS `M`; adds NO premise, NO law, NO axiom. No `sorry`, no `native_decide`. Ledger delta: FG -0 +0 / T1 -0 +0.
namespace Tools.ShippingGen4KWalkLegacyH4
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
open Tools.ShippingGen4KWalkProjField

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

section H4
variable {O : RefLawsAOps MkRefd mref cref} (M : MemoFamily O) {I : Void IO.RealWorld → Prop}
  (hS : StableK O.quiet I)
include M hS

theorem withLocalDeclPK (hA : AdmCtx O.quiet mctx cctx) {α : Type} (n : Name) (ty : Lean.Expr)
    (k : Lean.Expr → CompilerM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' → ∀ x,
      KeepsCP mctx' mref cctx' cref I (k x)) :
    KeepsCP mctx mref cctx cref I (CompilerM.withLocalDecl n ty k) := by
  intro ctx st hc
  unfold CompilerM.withLocalDecl
  exact Keeps.bind (KeepsCP.lift (M.tele.localDecl I hA hS.1 hS.2 n ty (fun fvar => (k fvar ctx).run st)
    (fun mctx' cctx' x hA' => hk mctx' cctx' hA' x ctx st hc)) ctx st hc) (fun p => Keeps.pure _)

theorem withLetDeclPK (hA : AdmCtx O.quiet mctx cctx) {α : Type} (n : Name) (ty v : Lean.Expr)
    (k : Lean.Expr → CompilerM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' → ∀ x,
      KeepsCP mctx' mref cctx' cref I (k x)) :
    KeepsCP mctx mref cctx cref I (CompilerM.withLetDecl n ty v k) := by
  intro ctx st hc
  unfold CompilerM.withLetDecl
  exact Keeps.bind (KeepsCP.lift (M.tele.letDecl I hA hS.1 hS.2 n ty v (fun fvar => (k fvar ctx).run st)
    (fun mctx' cctx' x hA' => hk mctx' cctx' hA' x ctx st hc)) ctx st hc) (fun p => Keeps.pure _)

end H4

end Tools.ShippingGen4KWalkLegacyH4
