import Tools.ShippingChildComposeA
import Tools.ShippingChildLegacyTailA
-- UNBUILT after the integrator's final connection (par/int-r3): the step-form tail hypothesis was
-- replaced by B3's `legacyTailA_of_step`. Earlier: BUILT (unit F2) f2b/f2c exit 0, int-r2f exit 0.
-- no `native_decide`, no new law. Boundary: `O : RefLawsAOps MkRefd mref cref`,
-- `hA : AdmCtx O.quiet mctx cctx`, the ADDED unproved `T : RefLawsATele O.quiet mref cref`
-- (logical inconsistency NOT PROVEN).

/-! # The JQ-level main theorem (unit F2)

Built on `Tools.ShippingChildComposeA`: every depth step discharges the handler premises INSIDE the
induction (ChildKeepsA D → D2 bridge → B `legacyImplA_of_tele` → A / C → D `bodyKeepsA_frontends`).
No abstract `H`/`Lg`/`BS` and no per-export hypotheses remain.

The legacy tail is built in the same step from `hC` (B3 `legacyTailA_of_step`). Remaining premises
of `core_tripleA_main`: `O`, `hA : AdmCtx`, `T` (added, unproved), and the start `OutQ O.quiet w`
(the `Triple` precondition). The handler and tail premises are GONE; this is invariant preservation
of the compiler's run under the boundary laws — NOT RTL semantic preservation, NOT runtime fit.

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

/-- **`BodyStepA O` from `T` alone**: each depth step builds the handlers and the legacy tail
from its own `hC : ChildKeepsA O D`. -/
theorem bodyStepA_main (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) :
    BodyStepA O :=
  fun D _ hC => bodyKeepsA_of_tele O T D hC
    (Tools.ShippingChildLegacyTailA.legacyTailA_of_step O T D hC)

/-- **The child entry at every depth `D ≥ 1`** (JQ level). -/
theorem childKeepsA_main (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) :
    ∀ D, 1 ≤ D → ChildKeepsA O D :=
  childKeepsA_all O (bodyStepA_main O T)

/-- **Main theorem (JQ level).** From `OutQ O.quiet` the core entry keeps `OutQ` on every
outcome (success: `OutQ`; exception: `OutQ ∧ OkExc`). Premises: `O`, `hA`, `T`. -/
theorem core_tripleA_main (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref) (declName : Name) :
    Triple mctx mref cctx cref (OutQ O.quiet) (synthesizeCombinationalCore declName [] false)
      (fun _ => OutQ O.quiet) (fun e w => OutQ O.quiet w ∧ OkExc e) :=
  core_tripleA_of_bodies O hA declName (bodyStepA_main O T)

end Tools.ShippingChildMainA
