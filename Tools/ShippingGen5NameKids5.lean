import Tools.ShippingGen5NameKids3
import Tools.ShippingSrm15Graph
set_option autoImplicit false
-- NOT BUILT (U5 implementation; build pending). 1 theorem, 0 new definitions.
-- `hfo` is a sufficient condition (a reached entry exists with FirstOcc and S c = some d.shape); it is NOT equivalent to GraphAgrees (which also allows none on both sides). Its supply from the production ds / Reach / S, InClass, ReachSpans, production bridge, N1 / G5 / G7 / M5 / FG are unsupplied.
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U5: `GraphAgrees` of `graphOf ds` from first occurrences

Conditional statement (freeze U5 §2). The premise `hfo` is NOT supplied here.
No Laws, no runtime, no compiler definition, no new TRUSTED row. -/

namespace Tools.ShippingGen5NameKids5
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm15Graph (graphOf FirstOcc callees_graphOf)
open Tools.ShippingGen5NameKids3 (GraphAgrees)

theorem graphAgrees_of_firstOcc {ds : List (Name × MachineData)} {Reach : Name → Prop}
    {S : Name → Option MachineShape}
    (hfo : ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape) :
    GraphAgrees (graphOf ds) Reach S := by
  intro c hc
  obtain ⟨d, hfd, hS⟩ := hfo c hc
  rw [callees_graphOf ds c d hfd, hS]
  rfl

end Tools.ShippingGen5NameKids5
