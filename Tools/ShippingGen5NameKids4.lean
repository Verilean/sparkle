import Tools.ShippingGen5NameKids3
import Tools.ShippingReaderFuelShapeProv
set_option autoImplicit false
-- Reviewed build: ba9v-39c565c4 (exit 0, 735 jobs, approved at 39c565c4; src=base=end, dirty=false; clean issue-linked build). 2 theorems, 0 new definitions. TYPE 2 / MUTANT 7 / AXIOMS 2 (standard only). The audit is over kernel types/values, not a proof of the runtime extern implementation.
-- `hF` (hmem_of_machineShapeF) is an existence premise over arbitrary ci / senv / ...; it does not fix the witness of any actual run, so it is NOT the production bridge. The link machineShape? <-> machineShapeF, GraphAgrees / InClass / ReachSpans, N1 / G5 / G7 / M5 / FG are unsupplied or unfinished.
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U4: `MemTagsNamed` of a `machineShapeF` output, and the `hmem` binder of U3

Conditional statements (freeze U4 §2). The premise `machineShapeF … = some (some sp)` (resp. `hF`) is NOT supplied here.
No Laws, no runtime, no compiler definition, no new TRUSTED row. -/

namespace Tools.ShippingGen5NameKids4
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel (machineShapeF)
open Tools.ShippingReaderFuelShapeProv
open Tools.ShippingGen5NameKids2 (MemTagsNamed)

theorem memTagsNamed_of_machineShapeF {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) : MemTagsNamed sp := by
  intro k hk cb aw dw ho
  have hk' : k < sp.instOrigins.length := by
    rw [machineShapeF_instOrigins_length h]; exact hk
  have h1 : sp.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord =
      Sparkle.Compiler.MachInstOrigin.InstOrigin.mem cb aw dw := ho
  rw [instOrigins_getD_eq h hk] at h1
  have h2 : sp.instOrigins[k]? = some (Sparkle.Compiler.MachInstOrigin.InstOrigin.mem cb aw dw) := by
    rw [List.getElem?_eq_getElem hk', h1]
  exact (machineShapeF_tag_mem h (List.getElem?_eq_getElem hk) h2).1

theorem hmem_of_machineShapeF {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hF : ∀ c, Reach c → ∀ sp, S c = some sp →
      ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool),
        machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp := by
  intro c hc sp hS
  obtain ⟨_, _, _, _, _, _, h⟩ := hF c hc sp hS
  exact memTagsNamed_of_machineShapeF h

end Tools.ShippingGen5NameKids4
