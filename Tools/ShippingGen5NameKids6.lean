import Tools.ShippingGen5NameKids3
import Tools.ShippingSrm15Graph
set_option autoImplicit false
-- Reviewed build ba13v-b07cfcec (approved at b07cfcec): exit 0, 724 jobs. 1 theorem, 0 new definitions.
-- Conditional reduction only: `hnd` (names of ds pairwise distinct) and `hr` (rank of the root within B) are premises and are NOT supplied here for the production program. The rank half of InClass, hfo, ReachSpans, production bridge, N1 / G5 / G7 / M5 / FG are unsupplied.
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U6: `InClass (graphOf ds) B top` from `hnd` and `hr`

Conditional statement (freeze U6 §2). No Laws, no runtime, no compiler definition, no new TRUSTED row. -/

namespace Tools.ShippingGen5NameKids6
open Lean
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm15Graph (graphOf)
open Tools.ShippingSrm7Rank (InClass WfG declRank)

theorem inClass_graphOf {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hnd : (ds.map Prod.fst).eraseDups.length = ds.length)
    (hr : (declRank (graphOf ds) B top).isSome = true) :
    InClass (graphOf ds) B top = true := by
  unfold InClass WfG graphOf
  simp only [List.map_map, List.length_map]
  have h1 : ((fun p : Name × List _ => p.1) ∘ fun p : Name × MachineData => (p.1, p.2.shape.instTagged)) = Prod.fst := rfl
  simp only [h1, hnd, beq_self_eq_true, Bool.true_and]
  exact hr

end Tools.ShippingGen5NameKids6
