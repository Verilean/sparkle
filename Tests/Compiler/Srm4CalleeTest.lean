import Tests.Compiler.Srm4KidTest
import Tests.Compiler.Srm4RunTest
import Tools.ShippingSrm4Callee
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (residue R5, semantic half): `Tools.ShippingSrm4Callee.memLeafCallee_seqChildRunN2` HAND-APPLIED to `wrapM` (a callee whose two calls are the memory-bearing leaf `leafM`, `Tests/Compiler/SharedLeafMemKidTest.lean`).  The
-- leaf's run is `Tests/Compiler/Srm4RunTest.lean` (`leafM_seqChildRunN`).
-- PREMISES kept (named): `hF` (`CallFactF`: the output equation at the call-output position under the GENERATED `machineExt`; text-supplied, NOT discharged here for the memory leaf — the generator's `hPoint` templates are stated
-- for a plain leaf's whole `bsIn`), `hR0` (`MachineDefines` of `leafM`), `O`, `T`, `hrun` (`MachineRunNCA` of the served run, a history).  The decidable data are by `decide`.  An example does not make the class complete.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tests.Compiler.SharedLeafMemKidIfaceTest
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Callee Tools.ShippingSrm4Run
open Tools.ShippingQuadComposed (GenFacts)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineDepthRunRA
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (memKey)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

noncomputable instance wrapM_inhab : Inhabited (HList (tys wrapM.machineData.ss)) :=
  ⟨Tools.ShippingSeqParentGenD2MSD.defaultHList _⟩

theorem wrapM_gen : GenFacts wrapM.machineData (fun i : DomainConfig => i) wrapM.machineInits wrapM.machineBody wrapM.machineResult
    wrapM.machineExt wrapM.machineExtB wrapM.machineSource :=
  ⟨wrapM.machine_ok, wrapM.machine_body, wrapM.machine_inits, wrapM.machine_writes, wrapM.machine_result, wrapM.machine_source,
   fun i bools bits S S' t h =>
    wrapM.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem wrapM_hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < 4 →
    wrapM.machineExtB i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)) j = bools j := by
  intro i bools bits j hj
  first
    | rfl
    | (delta wrapM.machineExtB
       simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
       (repeat' split) <;> first | rfl | (exfalso; omega))

theorem wrapM_hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < 4 →
    wrapM.machineExt i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)) j n' = bits j n' := by
  intro i bools bits j n' hj
  delta wrapM.machineExt
  simp only [Tools.ShippingMachineAuto.extendBits]
  (repeat' split) <;> first | rfl | (exfalso; omega)

theorem wrapM_outOk : ∀ o ∈ wrapM.machineData.shape.layout.outs, outNameOk o.name = true := by
  first | decide | decide +kernel

theorem wrapM_kids' : ∀ (k : Nat) (hk : k < wrapM.machineData.shape.insts.length),
    (wrapM.machineData.shape.insts[k]).1 = ``leafM ∧ memKey (originAt wrapM.machineData.shape k) = none := by
  first | decide | decide +kernel

theorem wrapM_argsN : ∀ (k : Nat) (hk : k < wrapM.machineData.shape.insts.length),
    (wrapM.machineData.shape.insts[k]).2.1.length = ((leafM.machineData.bsIn.take 4).filter Tools.ShippingPortWidthsPure.nonDom).length := by
  first | decide | decide +kernel

theorem wrapM_wid : Tools.ShippingPortsMatchRaw.callArgsOk wrapM.machineData 4 (fun _ => Tools.ShippingCallsChildPorts.argWidths leafM.machineData 4) = true := by
  first | decide | decide +kernel

/-- **`wrapM`: `SeqChildRunN` at depth 2 of a served run** (a callee over a memory-bearing leaf).  Premises: `hF`, `hR0`, `O`, `T`, the served run `h`. -/
theorem wrapM_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hR0 : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (hFF : Tools.ShippingQuadCalls.CallFactF wrapM.machineData 4
      (Tools.ShippingMachineCausal.letObsB wrapM.machineData (fun i : DomainConfig => i) wrapM.machineInits wrapM.machineBody wrapM.machineExt wrapM.machineExtB)
      (fun i bools bits => wrapM.machineExt i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
      (fun i bools bits => wrapM.machineExtB i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits)))
      (memLeafOutsC ``leafM leafM.machineData) (memLeafSrcC ``leafM leafM.machineData 4 leafM.machineSource))
    (i : DomainConfig) {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : MachineRunNCA O ``wrapM wrapM.machineData.shape (fun mctx cctx _ _ _ => MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape) mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (Tools.ShippingMachineLinked.childMap design.modules) design 2 mc (List.take 4 wrapM.machineData.bsIn)
      wrapM.machineData.shape.layout.outs
      (fun vals => wrapM.machineSource i
        (Tools.ShippingMachineChild.boolsOf (List.take 4 wrapM.machineData.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take 4 wrapM.machineData.bsIn) vals)) :=
  memLeafCallee_seqChildRunN2 (srcG := leafM.machineSource) O T wrapM_memCallee wrapM_outOk (fun k hk => (wrapM_kids' k hk).1) wrapM_gen hR0
    (fun m c hA => leafM_closesA O T hA) leafM_insts_ne (fun m design => memLeafCallee_hcalls (srcG := leafM.machineSource) O wrapM_memCallee wrapM_kids' wrapM_argsN wrapM_wid
      (fun i design mc h => leafM_seqChildRunN O T (fun _ _ _ _ _ => True) i 0 h) hFF m design) wrapM_hextB wrapM_hext i h

end Tests.Compiler.SharedLeafMemKidIfaceTest

#print axioms Tests.Compiler.SharedLeafMemKidIfaceTest.wrapM_seqChildRunN2
