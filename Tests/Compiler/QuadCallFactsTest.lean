import Tests.Compiler.QuadCallsTest
import Tools.ShippingQuadCallFacts
-- BUILT (unit SR17): c8 exit 0 (Tools.ShippingQuadCallFacts c3; QuadCallFactsTest c8); final-SHA rebuild in REPORT-SR17.md.
-- SCOPE (binding, ledger L8aw): `CallFactF` of the callees and parents of `topshare` and `topshare2` re-derived through the GENERIC `callFactF_of_fam` (dispatch `hS` PROVED generically:
-- `quadSrcF_eq` / `leafSrcC_eq`; the decoding equations `Hb`/`Hv` are the generator's own `gfHb*`/`gfHv*`, extracted typed by `oldGroupFact%`; the output defeq is `rfl` in the instance).
-- Each statement is `isDefEq` to the SR16 one (audit below) with a mismatch pair.  `hext`/`hextB` of the four callees are proved here DIRECTLY from the generated `machineExt`/`machineExtB`
-- definitions (`extendBits_of_ne`), not extracted from `seq_child_runN_ofR1`.  TWO instances do NOT make the class complete.  No sorry / axiom / native_decide.
section
open Tools.ShippingQuadCalls Tools.ShippingQuadComposed Tools.ShippingQuadCallFacts
open Tools.ShippingSeqOldPieces Tools.ShippingMachineAuto Tools.ShippingMachineCausal Tools.ShippingMachineSource
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tests.Compiler.QuadComposedTest
set_option maxHeartbeats 4000000
set_option Elab.async false
namespace Tests.Compiler.QuadCallsTest

theorem c_wrap_hF : type_of% a_wrap_hF := by
  refine callFactF_of_fam _ _ (fun i => i) (fun _ => (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData).bsIn) (leafSrcA ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineSource) (fun i n v => leafSrcC_eq _ _ _ i n v) ?_
  intro i bools bits k hk
  have hl : (Tests.Compiler.SeqDeepGenInstTest.wrap.machineData).shape.insts.length = 2 := by decide
  have Hb0 := oldGroupFact% (_) Tests.Compiler.SeqDeepGenInstTest.wrap.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
  have Hv0 := oldGroupFact% (_) Tests.Compiler.SeqDeepGenInstTest.wrap.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0
  rcases k with _ | _ | k
  all_goals first
    | omega
    | (refine ⟨_, _, Hb0, Hv0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb0, Hv0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)

theorem c_wrap3_hF : type_of% a_wrap3_hF := by
  refine callFactF_of_fam _ _ (fun i => i) (fun _ => (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData).bsIn) (leafSrcA ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineSource) (fun i n v => leafSrcC_eq _ _ _ i n v) ?_
  intro i bools bits k hk
  have hl : (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData).shape.insts.length = 2 := by decide
  have Hb0 := oldGroupFact% (_) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
  have Hv0 := oldGroupFact% (_) Tests.Compiler.SeqDeepGenDiffTest.wrap3.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0
  rcases k with _ | _ | k
  all_goals first
    | omega
    | (refine ⟨_, _, Hb0, Hv0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb0, Hv0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)

theorem c_topshare_hFP : type_of% a_topshare_hFP := by
  refine callFactF_of_fam _ _ (fun _ => defaultDomain) (quadBsOf ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData 3 3) (quadSrcA ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource) (fun i n v => quadSrcF_eq _ _ _ _ _ _ _ _ i n v) ?_
  intro i bools bits k hk
  have hl : (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData).shape.insts.length = 4 := by decide
  have Hb0 := oldGroupFact% (_) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
  have Hv0 := oldGroupFact% (_) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0
  have Hb1 := oldGroupFact% (_) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb1
  have Hv1 := oldGroupFact% (_) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv1
  rcases k with _ | _ | _ | _ | k
  all_goals first
    | omega
    | (refine ⟨_, _, Hb0, Hv0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb0, Hv0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb1, Hv1, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb1, Hv1, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)

open Tests.Compiler.SharedLeafGenTest in
theorem d_wrapQ_hF : type_of% b_wrapQ_hF := by
  refine callFactF_of_fam _ _ (fun i => i) (fun _ => (Tests.Compiler.SharedLeafGenTest.leaf16.machineData).bsIn) (leafSrcA ``Tests.Compiler.SharedLeafGenTest.leaf16 Tests.Compiler.SharedLeafGenTest.leaf16.machineSource) (fun i n v => leafSrcC_eq _ _ _ i n v) ?_
  intro i bools bits k hk
  have hl : (wrapQ.machineData).shape.insts.length = 2 := by decide
  have Hb0 := oldGroupFact% (_) wrapQ.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
  have Hv0 := oldGroupFact% (_) wrapQ.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0
  rcases k with _ | _ | k
  all_goals first
    | omega
    | (refine ⟨_, _, Hb0, Hv0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb0, Hv0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)

open Tests.Compiler.SharedLeafGenTest in
theorem d_wrapP_hF : type_of% b_wrapP_hF := by
  refine callFactF_of_fam _ _ (fun i => i) (fun _ => (Tests.Compiler.SharedLeafGenTest.leaf16.machineData).bsIn) (leafSrcA ``Tests.Compiler.SharedLeafGenTest.leaf16 Tests.Compiler.SharedLeafGenTest.leaf16.machineSource) (fun i n v => leafSrcC_eq _ _ _ i n v) ?_
  intro i bools bits k hk
  have hl : (wrapP.machineData).shape.insts.length = 4 := by decide
  have Hb0 := oldGroupFact% (_) wrapP.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
  have Hv0 := oldGroupFact% (_) wrapP.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0
  have Hb1 := oldGroupFact% (_) wrapP.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb1
  have Hv1 := oldGroupFact% (_) wrapP.machine_composedNR1 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv1
  rcases k with _ | _ | _ | _ | k
  all_goals first
    | omega
    | (refine ⟨_, _, Hb0, Hv0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb0, Hv0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb1, Hv1, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb1, Hv1, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)

open Tests.Compiler.SharedLeafGenTest in
theorem d_topshare2_hFP : type_of% b_topshare2_hFP := by
  refine callFactF_of_fam _ _ (fun _ => defaultDomain) (quadBsOf ``wrapQ ``wrapP wrapQ.machineData wrapP.machineData 3 3) (quadSrcA ``wrapQ ``wrapP wrapQ.machineSource wrapP.machineSource) (fun i n v => quadSrcF_eq _ _ _ _ _ _ _ _ i n v) ?_
  intro i bools bits k hk
  have hl : (topshare2.machineData).shape.insts.length = 4 := by decide
  have Hb0 := oldGroupFact% (_) topshare2.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
  have Hv0 := oldGroupFact% (_) topshare2.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0
  have Hb1 := oldGroupFact% (_) topshare2.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb1
  have Hv1 := oldGroupFact% (_) topshare2.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv1
  rcases k with _ | _ | _ | _ | k
  all_goals first
    | omega
    | (refine ⟨_, _, Hb0, Hv0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb0, Hv0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb1, Hv1, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)
    | (refine ⟨_, _, Hb1, Hv1, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; rfl)

theorem c_wrap_hextB : type_of% wrap_hextB := by
  intro i bools bits j hj
  unfold Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB
  repeat rw [extendBools_of_ne _ _ (by omega)]
  try rfl

theorem c_wrap_hext : type_of% wrap_hext := by
  intro i bools bits j n' hj
  unfold Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt
  repeat rw [extendBits_of_ne _ _ (by omega)]

theorem c_wrap3_hextB : type_of% wrap3_hextB := by
  intro i bools bits j hj
  unfold Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB
  repeat rw [extendBools_of_ne _ _ (by omega)]
  try rfl

theorem c_wrap3_hext : type_of% wrap3_hext := by
  intro i bools bits j n' hj
  unfold Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt
  repeat rw [extendBits_of_ne _ _ (by omega)]

open Tests.Compiler.SharedLeafGenTest in
theorem d_wrapQ_hextB : type_of% b_wrapQ_hextB := by
  intro i bools bits j hj
  unfold wrapQ.machineExtB
  repeat rw [extendBools_of_ne _ _ (by omega)]
  try rfl

open Tests.Compiler.SharedLeafGenTest in
theorem d_wrapQ_hext : type_of% b_wrapQ_hext := by
  intro i bools bits j n' hj
  unfold wrapQ.machineExt
  repeat rw [extendBits_of_ne _ _ (by omega)]

open Tests.Compiler.SharedLeafGenTest in
theorem d_wrapP_hextB : type_of% b_wrapP_hextB := by
  intro i bools bits j hj
  unfold wrapP.machineExtB
  repeat rw [extendBools_of_ne _ _ (by omega)]
  try rfl

open Tests.Compiler.SharedLeafGenTest in
theorem d_wrapP_hext : type_of% b_wrapP_hext := by
  intro i bools bits j n' hj
  unfold wrapP.machineExt
  repeat rw [extendBits_of_ne _ _ (by omega)]


/-! ## The parent blocks (`composedA`) from the NARROWED premises: statements `isDefEq` to the generated / old ones -/

local notation "accHcl2" => (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _)
local notation "leaf16Hcl" => (fun mc cc => Tests.Compiler.SharedLeafGenTest.leaf16.machine_closes mc _ cc _)

set_option maxHeartbeats 0 in
quad_audit c_parent_composedA ≡ Tests.Compiler.TopShareComposedTest.ts_composedA :=
  quad_composed_split topshare_quadAll topshare_gen wrap_gen wrap3_gen a_acc_run c_wrap_hF c_wrap3_hF c_topshare_hFP c_wrap_hextB c_wrap_hext c_wrap3_hextB c_wrap3_hext accHcl2
    hcore entry ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩

open Tests.Compiler.SharedLeafGenTest in
set_option maxHeartbeats 0 in
quad_audit d_composedA ≡ Tests.Compiler.SharedLeafGenTest.topshare2.epD2M_composedA :=
  quad_composed_split b_quadAll b_gen b_wrapQ_gen b_wrapP_gen b_leaf_run d_wrapQ_hF d_wrapP_hF d_topshare2_hFP d_wrapQ_hextB d_wrapQ_hext d_wrapP_hextB d_wrapP_hext leaf16Hcl
    hcore entry ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩

#print axioms Tests.Compiler.QuadCallsTest.c_wrap_hF
#print axioms Tests.Compiler.QuadCallsTest.c_topshare_hFP
#print axioms Tests.Compiler.QuadCallsTest.d_topshare2_hFP
#print axioms Tests.Compiler.QuadCallsTest.c_wrap_hext
#print axioms Tests.Compiler.QuadCallsTest.c_wrap_hextB
#print axioms Tests.Compiler.QuadCallsTest.d_wrapP_hext
#print axioms Tests.Compiler.QuadCallsTest.c_parent_composedA
#print axioms Tests.Compiler.QuadCallsTest.d_composedA
end Tests.Compiler.QuadCallsTest
end
