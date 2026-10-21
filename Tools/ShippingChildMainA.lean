import Tools.ShippingChildComposeA
-- UNBUILT (unit F2): build names and exits are in REPORT-F2.md. No `sorry`, no `axiom`,
-- no `native_decide`, no new law. Boundary: `O : RefLawsAOps MkRefd mref cref`,
-- `hA : AdmCtx O.quiet mctx cctx`, the ADDED unproved `T : RefLawsATele O.quiet mref cref`
-- (logical inconsistency NOT PROVEN), and ONE legacy-tail hypothesis `hTail` (below).

/-! # The JQ-level main theorem (unit F2)

Built on `Tools.ShippingChildComposeA`: every depth step discharges the handler premises INSIDE the
induction (ChildKeepsA D → D2 bridge → B `legacyImplA_of_tele` → A / C → D `bodyKeepsA_frontends`).
No abstract `H`/`Lg`/`BS` and no per-export hypotheses remain.

Remaining premises of `core_tripleA_main`: `O`, `hA`, `T`, and
`hTail : LegacyTailStepA O` — the legacy tail built from the step's own `hC : ChildKeepsA O D`
(statement of unit B3's `legacyTailA_of_step … (hC : ChildKeepsA O D) : LegacyTailA O D`, until it
lands). `hTail` is a premise about EVERY constant on which both gates miss; it does not assume
`∀ D, LegacyTailA O D` outright. The start `OutQ O.quiet w` is the `Triple` precondition.

NOT here (separate, not claimed): the child-cache invariant `JQC` and unit E's depth-0
initialisation; the connection to semantic preservation / the old `ChildBnd` endpoint; runtime fit
of `O` and `T`; the model→ST correspondence. -/

namespace Tools.ShippingChildMainA
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildFresh
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildFallbackA
open Tools.ShippingChildFrontCP
open Tools.ShippingChildDepthA
open Tools.ShippingChildComposeA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The legacy-tail premise in its per-step form: at every depth `D ≥ 1`, from the child entry at
`D`, the legacy tail at `D`. ONE hypothesis (to be replaced by B3's generic tail lemma). -/
def LegacyTailStepA (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ D, 1 ≤ D → ChildKeepsA O D → LegacyTailA O D

/-- **`BodyStepA O` from `T` and the step-form tail only.** -/
theorem bodyStepA_main (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hTail : LegacyTailStepA O) : BodyStepA O :=
  fun D hD hC => bodyKeepsA_of_tele O T D hC (hTail D hD hC)

/-- **The child entry at every depth `D ≥ 1`** (JQ level). -/
theorem childKeepsA_main (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hTail : LegacyTailStepA O) : ∀ D, 1 ≤ D → ChildKeepsA O D :=
  childKeepsA_all O (bodyStepA_main O T hTail)

/-- **Main theorem (JQ level).** From `OutQ O.quiet` the core entry keeps `OutQ` on every
outcome (success: `OutQ`; exception: `OutQ ∧ OkExc`). Premises: `O`, `hA`, `T`, `hTail`. -/
theorem core_tripleA_main (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) (hTail : LegacyTailStepA O) (declName : Name) :
    Triple mctx mref cctx cref (OutQ O.quiet) (synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e) :=
  core_tripleA_of_bodies O hA declName (bodyStepA_main O T hTail)

end Tools.ShippingChildMainA
