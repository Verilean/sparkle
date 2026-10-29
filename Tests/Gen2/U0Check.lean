import Tools.ShippingGen2Keep
import Tools.ShippingGen2Data
import Tests.Compiler.Srm4ParentTest
import Tests.Compiler.SharedLeafMemKidEntryTest
set_option autoImplicit false

/-! # Gen2 U0 acceptance checks (GENERAL_SPEC.md §8.1)

* non-vacuity: a real generated package (`topshareM`) satisfies `DataOk`;
* the axioms of the new roots. -/
namespace Tests.Gen2.U0Check
open Tools.ShippingGen2
open Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidTest

/-- `topshareM`'s generated package (its `GenFacts` from the declaration's own `machine_*` theorems). -/
noncomputable def tmPkg : SrcPkg Unit (fun _ => Sparkle.Core.Domain.defaultDomain) :=
  { decl := ``topshareM, d := topshareM.machineData, kD := 4, ρ := _, inh := topshareM_inhab,
    inits := topshareM.machineInits, body := topshareM.machineBody, obsR := topshareM.machineResult,
    ext := topshareM.machineExt, extB := topshareM.machineExtB, src := topshareM.machineSource,
    gen := topshareM_gen }

/-- **Non-vacuity of `DataOk`**: the concrete conjunction holds of a real package. -/
theorem tmPkg_dataOk : DataOk tmPkg := by
  have h := Tests.Compiler.SharedLeafMemKidEntryTest.topshareM_parentData
  unfold DataOk DataOkB
  simp only [tmPkg, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨h.ok, h.alias⟩, h.callsOk⟩, h.slots⟩, topshareM_outTy⟩, h.outHead⟩

#print axioms Tools.ShippingGen2Consumer.machine_linkedT_callsServed
#print axioms Tools.ShippingGen2.seqFactsRN_of_callDec
#print axioms Tools.ShippingGen2.stableA_invAt
#print axioms Tools.ShippingGen2.servedRealA_of_servedP
#print axioms Tools.ShippingGen2.memFacts_of_memDec
#print axioms Tools.ShippingGen2.machineTraceLBX_mono
#print axioms Tools.ShippingGen2.keepBody
#print axioms tmPkg_dataOk

end Tests.Gen2.U0Check
