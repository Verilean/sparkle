import Tools.ShippingChildDepthC
import Tools.ShippingChildFrontCP
import Tools.ShippingChildLegacyImplA
import Tools.ShippingChildLegacyCachedA
import Tools.ShippingChildCanonKeyA
import Tools.ShippingChildProjFieldA
-- BUILT (unit E2, par/u-e2): e4 exit 1 (MkRefd ambiguity), e5 exit 0; audit build e6. No `sorry`, no `axiom`, no `native_decide`, no new law.
-- What this does NOT show: the laws (`RefLawsAOps` fields, `RefLawsATele`) describe a NON-TRIVIAL
-- runtime model of MetaM/IO; that the real runtime satisfies them (runtime fit) is NOT PROVEN, and
-- their joint satisfiability is NOT PROVEN. `RealChildA` is a history of past synthesis results,
-- not semantic correctness in the current environment.
-- Remaining premises: `O`, `hA : AdmCtx`, the added telescope boundary `T : RefLawsATele`, and
-- `LegacyTailC O D` (the legacy tail at `JQC`; B3's generic-in-`I` statement is not available
-- yet, so this is the JQC analogue of `LegacyTailA`, asked for constants where both gates miss).

/-! # The JQC depth induction with the handler premises discharged inside each step

Same shape as `Tools.ShippingChildComposeA` at `I := JQC O D`. Inside the step at `D`, from
`hC : ChildKeepsC O D` (= `ChildSynthA O (JQC O D)`):

    hC ─(D2 childEntryA_JQC_of_childSynthA)→ ChildEntryA O (JQC D)
       ─(B legacyImplA_of_tele, A canonKeyA, T)→ LegacyImplA O (JQC D)
       ─(A legacyCachedA_of_impl)→ LegacyCachedA;  C projFieldNameA T → ProjFieldNameA
       ─(D fromConst_frontends_of_handlers, generic in I, hsv = JQ half of JQC)→ BodyKeepsC O D

Everything used is generic in `I` (`StableA O.quiet I`); nothing is JQ-only. The handlers are
NOT assumed `∀ D` up front. -/

namespace Tools.ShippingChildComposeC
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildFresh
open Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The legacy tail at `JQC O D` (PREMISE): the entry with the certified front end OFF keeps
`JQC O D`, asked only of constants on which both gates miss. -/
def LegacyTailC (O : RefLawsAOps MkRefd mref cref) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo)
      (isInst : Lean.Expr → Bool),
    certifiedShape? false [] ci = none → mixedCertifiedShape? false [] ci isInst = none →
    Keeps mctx mref cctx cref (JQC O D)
      (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
        declName [] false false ci isInst)

/-- **One depth step at `JQC` with the handlers discharged locally** (from `ChildKeepsC O D`). -/
theorem bodyKeepsC_of_tele (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (D : Nat) (hC : ChildKeepsC O D) (hlegacy : LegacyTailC O D) : BodyKeepsC O D :=
  have hS := stableA_JQC O D
  have hchild : ChildEntryA O (JQC O D) := childEntryA_JQC_of_childSynthA O D hC
  have hcanon : CanonKeyA O (JQC O D) := Tools.ShippingChildCanonKeyA.canonKeyA O hS
  have hImpl : LegacyImplA O (JQC O D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele O hS T hcanon hchild
  fun mctx cctx hA declName tenv b ci isInst =>
    fromConst_frontends_of_handlers O hA hS hImpl
      (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl O hS hImpl) hcanon
      (Tools.ShippingChildProjFieldA.projFieldNameA O T hS) hC (fun _ h => h.1.2.1)
      tenv b declName ci isInst (hlegacy mctx cctx hA declName tenv b ci isInst)

/-- **`BodyStepC` from `T` and the legacy tail only.** -/
theorem bodyStepC_of_tele (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hlegacy : ∀ D, LegacyTailC O D) : BodyStepC O :=
  fun D _ hC => bodyKeepsC_of_tele O T D hC (hlegacy D)

/-- **The child entry at `JQC` at every depth `D ≥ 1`.** -/
theorem childKeepsC_all_of_tele (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hlegacy : ∀ D, LegacyTailC O D) :
    ∀ D, 1 ≤ D → ChildKeepsC O D :=
  childKeepsC_all O (bodyStepC_of_tele O T hlegacy)

/-- **Outermost core entry** (JQ in; success `JQC O 0` after the clear; exceptions `EQ`). -/
theorem core_tripleAC_of_tele (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) (hlegacy : ∀ D, LegacyTailC O D) (declName : Name) :
    Triple mctx mref cctx cref (JQ O.quiet 0) (synthesizeCombinationalCore declName [] false)
      (fun _ => JQC O 0) (EQ O.quiet 0) :=
  core_tripleAC_of_bodies O hA declName (bodyStepC_of_tele O T hlegacy)

/-- **Outermost full entry.** -/
theorem full_tripleAC_of_tele (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) (hlegacy : ∀ D, LegacyTailC O D) (declName : Name) :
    Triple mctx mref cctx cref (JQ O.quiet 0) (synthesizeCombinational declName)
      (fun _ => JQC O 0) (EQ O.quiet 0) :=
  full_tripleAC_of_bodies O hA declName (bodyStepC_of_tele O T hlegacy)

end Tools.ShippingChildComposeC
