import Tests.Compiler.SharedLeafMemKidIfaceTest
import Tools.ShippingSrm4Run
import Tools.ShippingSeqParentGenD2MSD
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (residue R3): `Tools.ShippingSrm4Run.memCallee_seqChildRunN` HAND-APPLIED to `leafM` of `Tests/Compiler/SharedLeafMemKidTest.lean` (a register machine whose ONE call is the synchronous 4/8 memory; its endpoint is built from
-- `machine_trace_of_data_causal`, where `generateSeqChildN` refuses it).  The statement of `leafM_seqChildRunN` is the type of `leafM.seq_child_runN_ofR{n+1}` (a run of the served callee, every depth).
-- PREMISES kept (named): `leafM_gen` (the generated `machine_*` facts, assembled from the declaration's own theorems), `leafM_memcalls` (per-call `MemFacts`, kernel `rfl` / `decide`), `leafM_hext(B)` (the generated extension reads the
-- declared inputs), `hrun` (`MachineRunNCA`, a history of past synthesis results).  An example does not make the class complete.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Run Tools.ShippingMachineDepthRunRA
open Tools.ShippingQuadComposed (GenFacts)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tests.Compiler.SharedLeafMemKidTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

noncomputable instance leafM_inhab : Inhabited (HList (tys leafM.machineData.ss)) :=
  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩

theorem leafM_gen : GenFacts leafM.machineData (fun i : DomainConfig => i) leafM.machineInits leafM.machineBody leafM.machineResult
    leafM.machineExt leafM.machineExtB leafM.machineSource :=
  ⟨leafM.machine_ok, leafM.machine_body, leafM.machine_inits, leafM.machine_writes, leafM.machine_result, leafM.machine_source,
   fun i bools bits S S' t h =>
    leafM.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

#reduce (leafM.machineData.ls.length, leafM.machineData.shape.insts.map (·.2.1), leafM.machineData.bsIn.length)

theorem leafM_memcalls : MemCalls leafM.machineData 4 leafM.machineInits leafM.machineBody leafM.machineExt leafM.machineExtB := by
  intro i bools bits k c hc
  cases k with
  | zero =>
    refine ⟨false, 4, 8, ?A, ?D, ?E, ?R, 0, 1, 2, 0, rfl, rfl, ?h0, by decide, ?h1, by decide, ?h2, by decide, ?h3, by decide, rfl, ?hx⟩
    case hx => intro j; rfl
    all_goals rfl
  | succ k => rw [leafM_mem] at hc; simp at hc

theorem leafM_hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < 4 →
    leafM.machineExtB i bools bits (stateLoop leafM.machineInits (leafM.machineBody i bools bits)) j = bools j := by
  intro i bools bits j hj
  rfl

theorem leafM_hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < 4 →
    leafM.machineExt i bools bits (stateLoop leafM.machineInits (leafM.machineBody i bools bits)) j n' = bits j n' := by
  intro i bools bits j n' hj
  delta leafM.machineExt
  simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
  (repeat' split) <;> first | rfl | (exfalso; omega)

theorem leafM_outOk : ∀ o ∈ leafM.machineData.shape.layout.outs, outNameOk o.name = true := by
  first | decide | decide +kernel

/-- **`leafM` (a register machine whose one call is a memory), the run theorem at every depth** (the `seq_child_runN` the machine route asks of a memory-bearing leaf; `MachineClosesAtA` of `leafM` is DERIVED). -/
theorem leafM_seqChildRunN (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (BndA : Lean.Meta.Context → Lean.Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop)
    (i : DomainConfig) (depth : Nat) {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hrun : MachineRunNCA O ``leafM leafM.machineData.shape BndA mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (Tools.ShippingMachineLinked.childMap design.modules) design (depth + 1) mc
      (List.take 4 leafM.machineData.bsIn) leafM.machineData.shape.layout.outs
      (fun vals => leafM.machineSource i
        (Tools.ShippingMachineChild.boolsOf (List.take 4 leafM.machineData.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take 4 leafM.machineData.bsIn) vals)) :=
  memCallee_seqChildRunN O T leafM_memCallee leafM_outOk leafM_gen leafM_memcalls leafM_hextB leafM_hext BndA i depth hrun

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.leafM_seqChildRunN
#print axioms Tools.ShippingSrm4Run.memCallee_seqChildRunN
#print axioms Tools.ShippingSrm4Run.memCallee_composedNW
