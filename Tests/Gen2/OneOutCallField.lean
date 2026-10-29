import Tools.ShippingGen2CallField
import Tests.Compiler.ShippingMachineLinkedTest
set_option autoImplicit false

/-! # G-ONEOUT `CallField` on real data (scripts/gen2/CALLFIELD_FREEZE.md §5)

The one-output parent `callerL` (Tests/Compiler/ShippingMachineLinkedTest.lean:31; `instFields = []`, one call of
`pickByteH`, closed by `closeInsts`) and its callee `pickByteH` (the `.comb` package over the comb endpoint's
generated facts, the `pbhC` pattern of Tests/Gen2/SlotlessLeafInstance.lean).

Parent side, Pkg-free: this unit does NOT construct a `callerL` package (whether one can be built from its generated
facts is not decided here; no existing `GenFacts` bundle of it was found in the tree). The `CallField` check is therefore stated (a) directly on
`callerL.machineData` (`callerL_callField_data`, the `CallField` body with `p.d := callerL.machineData`), and (b) for
EVERY parent package whose data is `callerL.machineData` (`callerL_callField`; a premise `p.d = callerL.machineData`,
for which no package is exhibited here).

Control: the OLD name conjunct fails for the same pair (as gen4's `oneout_name_mismatch`).

This shows only that the new conjunct is satisfiable on this pair. It does NOT show the whole `CallDec` (argument,
range and output-equation conjuncts), nor that a run exists. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen2.OneOutCallField
open Tools.ShippingGen2
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Sparkle.Core.Domain

abbrev U := fun _ : Unit => defaultDomain

/-- `pickByteH`'s comb package (as `Tests.Gen2.SlotlessLeafInstance.pbhC`). -/
noncomputable def pbhC : CombPkg Unit U :=
  { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length,
    inits := pickByteH.machineInits, src := pickByteH.machineSource,
    facts := ⟨pickByteH.machine_ok, pickByteH.machine_body, pickByteH.machine_inits, pickByteH.machine_next,
      pickByteH.machine_result⟩ }

noncomputable abbrev pbhPkg : Pkg Unit U := .comb pbhC

/-- The parent is a one-output parent. -/
theorem callerL_noFields : callerL.machineData.shape.instFields = [] := by
  first | rfl | decide | decide +kernel

/-- Its call 0 is a call of `pickByteH`. -/
theorem callerL_calls_pbh : (callerL.machineData.shape.insts.map (·.1))[0]? = some ``pickByteH := by
  first | rfl | decide | decide +kernel

theorem pbh_outs_len : pickByteH.machineData.shape.layout.outs.length = 1 := by
  first | rfl | decide | decide +kernel

/-- The callee's layout outputs are a singleton. -/
theorem pbh_outs_single : ∃ o, pickByteH.machineData.shape.layout.outs = [o] := by
  have h := pbh_outs_len
  revert h
  generalize pickByteH.machineData.shape.layout.outs = l
  intro h
  rcases l with _ | ⟨o, _ | ⟨o2, l⟩⟩
  · exact absurd h (by decide)
  · exact ⟨o, rfl⟩
  · exact absurd h (by first | (simp; done) | (simp only [List.length_cons]; omega))

/-- **(a) The new conjunct holds, Pkg-free**: `CallField`'s body at `p.d := callerL.machineData`,
`q.d := pickByteH.machineData`, call `0`. -/
theorem callerL_callField_data : ∃ o, pickByteH.machineData.shape.layout.outs = [o] ∧
    (if callerL.machineData.shape.instFields = [] then pickByteH.machineData.shape.layout.outs = [o]
      else o.name = callerL.machineData.shape.instFields.getD 0 "") := by
  obtain ⟨o, ho⟩ := pbh_outs_single
  exact ⟨o, ho, by rw [if_pos callerL_noFields]; exact ho⟩

/-- **(b) The new conjunct holds** for every parent package with `callerL`'s data and `pickByteH`'s `.comb`
package, through `callField_one`. -/
theorem callerL_callField (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    ∃ o, pickByteH.machineData.shape.layout.outs = [o] ∧ CallField p pbhPkg 0 o := by
  obtain ⟨o, ho⟩ := pbh_outs_single
  have h1 : p.d.shape.instFields = [] :=
    (congrArg (fun (d : Tools.ShippingMachineAuto.MachineData) => d.shape.instFields) hp).trans callerL_noFields
  exact ⟨o, ho, (callField_one (q := pbhPkg) (k := 0) (o := o) h1).mpr ho⟩

/-- **Control**: the OLD name conjunct fails for the same pair. -/
theorem oneout_old_name_fails :
    ∀ o ∈ pickByteH.machineData.shape.layout.outs, o.name ≠ callerL.machineData.shape.instFields.getD 0 "" := by
  decide

/-- The control at the package level: for the output `CallField` selects, the old conjunct (`CallDecOld`'s) is false. -/
theorem callerL_old_conjunct_fails (p : Pkg Unit U) (hp : p.d = callerL.machineData) (o : Sparkle.IR.Machine.OutField)
    (ho : pbhPkg.d.shape.layout.outs = [o]) : ¬ (o.name = p.d.shape.instFields.getD 0 "") := by
  have ho' : pickByteH.machineData.shape.layout.outs = [o] := ho
  have hm : o ∈ pickByteH.machineData.shape.layout.outs := by
    rw [ho']; exact List.mem_singleton_self o
  rw [hp]
  exact oneout_old_name_fails o hm

#print axioms Tools.ShippingGen2.callField_group
#print axioms Tools.ShippingGen2.callField_one
#print axioms Tools.ShippingGen2.callDec_group_old
#print axioms Tools.ShippingGen2.callDecOld_group
#print axioms Tools.ShippingGen2.hPointAt_of_hPointG_group
#print axioms Tools.ShippingGen2.hPointG_of_hPointAt_group
#print axioms Tools.ShippingGen2.callFactF_of_callOutG_group
#print axioms Tools.ShippingGen2.callOutG_of_callFactF_group
#print axioms Tools.ShippingGen2.callDec_of_hPointG_at
#print axioms Tools.ShippingGen2.oneOutCall_of_callDec
#print axioms Tools.ShippingGen2.oneOut_outputs
#print axioms Tools.ShippingGen2.seqFactsRN_of_callDec
#print axioms Tools.ShippingGen2.callDec_of_callFactF
#print axioms Tools.ShippingGen2.callDec_of_hPointAt_at
#print axioms callerL_noFields
#print axioms callerL_calls_pbh
#print axioms pbh_outs_single
#print axioms callerL_callField_data
#print axioms callerL_callField
#print axioms oneout_old_name_fails
#print axioms callerL_old_conjunct_fails

end Tests.Gen2.OneOutCallField
