import Tools.ShippingChildFrontCP
import Tools.ShippingChildLegacyImplA
import Tools.ShippingChildLegacyCachedA
import Tools.ShippingChildCanonKeyA
import Tools.ShippingChildProjFieldA
-- BUILT (e7 exit 0, unit E2 added `open Tools.ShippingChildFresh` for the MkRefd ambiguity); originally UNBUILT (integrator, par/int-r2). No `sorry`, no `axiom`, no `native_decide`, no new law.
-- What this does NOT show: the laws (`RefLawsAOps` fields, `RefLawsATele`) describe a NON-TRIVIAL
-- runtime model of MetaM/IO; that the real runtime satisfies them (runtime fit) is NOT PROVEN, and
-- their joint satisfiability is NOT PROVEN (only the degenerate `quiet = False` model is exhibited).
-- The child-cache invariant (JQC) and the semantic-preservation endpoint are SEPARATE (not here).
-- Remaining premises of `core_tripleA_of_tele`: `O`, `hA : AdmCtx`, the start `OutQ`, `T`, and
-- `∀ D, LegacyTailA O D` (to be built inside the step from `hC`, unit B3).
-- Boundary: `O : RefLawsAOps MkRefd mref cref`, `hA : AdmCtx O.quiet mctx cctx`, and the ADDED,
-- unproved telescope family `T : RefLawsATele O.quiet mref cref` (logical inconsistency NOT PROVEN).

/-! # The JQ depth induction with the handler premises discharged inside each depth step

`bodyStepA_of_handlers` (FrontCP) asks `∀ D, LegacyImplA O (JQ O.quiet D)` up front — but the
legacy body's proof (`legacyImplA_of_tele`, unit B) needs `ChildEntryA O (JQ O.quiet D)`, which
holds only under the step's own hypothesis `ChildKeepsA O D`. So the handlers are NOT assumed at
every depth here: inside the step at `D`, from `hC : ChildKeepsA O D`,

    hC ─(D2 bridge childEntryA_JQ_of_childSynthA)→ ChildEntryA O (JQ D)
       ─(B legacyImplA_of_tele, with A canonKeyA, T)→ LegacyImplA O (JQ D)
       ─(A legacyCachedA_of_impl)→ LegacyCachedA O (JQ D);  C projFieldNameA T → ProjFieldNameA
       ─(D bodyKeepsA_frontends, with LegacyTailA)→ BodyKeepsA O D,

and the induction (`childKeepsA_all`, DepthA) runs on that step. Remaining premises:
`T` (the added telescope boundary) and `LegacyTailA O D` for every `D` (a premise about EVERY
constant on which both gates miss — it stays in the type also for machine-route constants).
NOT here: the child-cache invariant (`JQC`, unit E), runtime fit of the laws, the model→ST
correspondence (open). -/

namespace Tools.ShippingChildComposeA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh
open Tools.ShippingChildVCA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildDepthA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **One depth step with the handlers discharged locally** (from `ChildKeepsA O D`). -/
theorem bodyKeepsA_of_tele (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (D : Nat) (hC : ChildKeepsA O D) (hlegacy : LegacyTailA O D) : BodyKeepsA O D :=
  have hS := stableA_JQ O.quiet D
  have hchild : ChildEntryA O (JQ O.quiet D) := childEntryA_JQ_of_childSynthA O D hC
  have hcanon : CanonKeyA O (JQ O.quiet D) := Tools.ShippingChildCanonKeyA.canonKeyA O hS
  have hImpl : LegacyImplA O (JQ O.quiet D) :=
    Tools.ShippingChildLegacyImplA.legacyImplA_of_tele O hS T hcanon hchild
  bodyKeepsA_frontends O D hImpl
    (Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl O hS hImpl) hcanon
    (Tools.ShippingChildProjFieldA.projFieldNameA O T hS) hC hlegacy

/-- **`BodyStepA` from `T` and the legacy tail only.** -/
theorem bodyStepA_of_tele (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hlegacy : ∀ D, LegacyTailA O D) : BodyStepA O :=
  fun D _ hC => bodyKeepsA_of_tele O T D hC (hlegacy D)

/-- **The child entry at every depth `D ≥ 1`** (the induction of DepthA on the step above). -/
theorem childKeepsA_all_of_tele (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hlegacy : ∀ D, LegacyTailA O D) :
    ∀ D, 1 ≤ D → ChildKeepsA O D :=
  childKeepsA_all O (bodyStepA_of_tele O T hlegacy)

/-- **`core_tripleA` with `hbody` discharged** from `T` and the legacy tail only (JQ level; the
child-cache invariant is unit E's). -/
theorem core_tripleA_of_tele (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) (hlegacy : ∀ D, LegacyTailA O D) (declName : Name) :
    Triple mctx mref cctx cref (OutQ O.quiet) (synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e) :=
  core_tripleA_of_bodies O hA declName (bodyStepA_of_tele O T hlegacy)

end Tools.ShippingChildComposeA
