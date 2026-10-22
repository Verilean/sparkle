import Tests.Compiler.QuadCallsTest
import Tools.ShippingQuadCallFacts
-- UNBUILT (unit SR17): see REPORT-SR17.md.
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

end Tests.Compiler.QuadCallsTest
end
