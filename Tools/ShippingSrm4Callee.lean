import Tools.ShippingSrm4Run
import Tools.ShippingSrm4Kid
import Tools.ShippingQuadCalls
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (binding, residues R3/R5): a CALLEE `C` whose calls are all ordinary calls of ONE leaf `G` that itself has MEMORY children (`G` as `leafM`): the generic forms of `leafCallee_hcalls` / `leafCallee_composedA` /
-- `leafCallee_seqChildRunN2` of `Tools/ShippingQuadCalls.lean` / `Tools/ShippingQuadComposed.lean` for a leaf WITH calls.  The leaf's run is its `SeqChildRunN` at depth 1 from `MachineRunNCA` (`Tools.ShippingSrm4Run.memCallee_seqChildRunN`),
-- not `LeafSeqRunN` (a plain leaf's run at every depth, impossible for a leaf with an instance).
-- PROVED: `memLeafCallee_hcalls` (the callee's per-call `SeqFactsRN`), `memLeafCallee_composedNW` (`ComposedNW 1` of the callee's served run), `memLeafCallee_seqChildRunN2` (`SeqChildRunN` at depth 2).
-- PREMISES (named): `MemCalleeData` of the callee and the per-call facts `hkids` / `hargsN` / `hwid` (decidable), `GenFacts` of the callee, `hF` (`CallFactF`: the output equation at the call-output position under the GENERATED `machineExt`, text-supplied as for
-- a plain leaf), `hrun` (the leaf's `SeqChildRunN` at depth 1 from `MachineRunNCA`), `hGcloses` (`MachineClosesAtA` of the leaf in admissible contexts), `hR0` (`MachineDefines` of the leaf), `hGins` (the leaf has calls), `hcloses` (`MachineClosesAtA` of the callee).
-- `RealChildA` / `ServedRealA` / `JQC` / `MachineRunNCA` are histories of past synthesis results, not freshness or semantic correctness in the current environment.  An example does not make the class complete.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field, no heartbeat option.

namespace Tools.ShippingSrm4Callee
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned
open Tools.ShippingTopShareRun
open Tools.ShippingMemCloses
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC
open Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses
open Tools.ShippingMachineAuto
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA Tools.ShippingServedRealA
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingSeqParentLemmas
open Tools.ShippingMachineCallsLinkedT
open Tools.ShippingQuadComposed
open Tools.ShippingQuadCalls
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Run
open Tools.ShippingPortWidthsPure (nonDom)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- the child tables of a callee whose calls are all the leaf `G`, whose interface is its first `nG` binders (the declared inputs; the binders after them are its calls' outputs) -/
def memLeafBsC (G : Name) (dG : MachineData) (nG : Nat) : Name → List (Name × MixedGateBinder) :=
  fun n => if n = G then dG.bsIn.take nG else []
def memLeafOutsC (G : Name) (dG : MachineData) : Name → List OutField :=
  fun n => if n = G then dG.shape.layout.outs else []
def memLeafSrcC (G : Name) (dG : MachineData) (nG : Nat)
    (srcG : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)) :
    DomainConfig → Name → (Nat → List Nat) → List (Nat → Nat) :=
  fun i n => if n = G then fun vals => srcG i (Tools.ShippingMachineChild.boolsOf (dG.bsIn.take nG) vals) (Tools.ShippingMachineChild.bitsOf (dG.bsIn.take nG) vals)
    else fun _ => []
/-- what a served run of the leaf must establish: the leaf's `MachineRunNCA` at the callee's design -/
def memLeafPC (O : RefLawsAOps MkRefd mref cref) (G : Name) (dG : MachineData) (design : Sparkle.IR.AST.Design) :
    Name → Sparkle.IR.AST.Module → Prop :=
  fun _ mc => MachineRunNCA O G dG.shape (fun _ _ _ _ _ => True) mc design

section Callee
variable {dC dG : MachineData} {C G : Name} {nC nG : Nat} [Inhabited (HList (tys dC.ss))] {ρ : DomainConfig → Type}
  {initsC : HList (tys dC.ss)}
  {bodyC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys dC.ss)) (Circuit.SigList i (tys dC.ss)) (tys dC.ss) →
      Circuit i (Circuit.SigList i (tys dC.ss)) (ρ i)}
  {obsRC : (i : DomainConfig) → ρ i → List (Nat → Nat)}
  {extC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n)}
  {extBC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → Nat → Signal i Bool}
  {srcC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}
  {srcG : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat)}

/-- **The callee's `hcalls` over a leaf WITH calls, split per call and DERIVED** (`leafCallee_hcalls` with the leaf's run at depth 1 from `MachineRunNCA`). -/
theorem memLeafCallee_hcalls (O : RefLawsAOps MkRefd mref cref)
    {nameK : Nat → String} {nk : Nat → Nat} {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData dC C nC nameK nk outsK namesK names)
    (hkids : ∀ (k : Nat) (hk : k < dC.shape.insts.length), (dC.shape.insts[k]).1 = G ∧ memKey (originAt dC.shape k) = none)
    (hargsN : ∀ (k : Nat) (hk : k < dC.shape.insts.length),
      (dC.shape.insts[k]).2.1.length = ((dG.bsIn.take nG).filter nonDom).length)
    (hwid : Tools.ShippingPortsMatchRaw.callArgsOk dC nC (fun _ => Tools.ShippingCallsChildPorts.argWidths dG nG) = true)
    (hrun : ∀ (i : DomainConfig) (design : Sparkle.IR.AST.Design) (mc : Sparkle.IR.AST.Module),
      MachineRunNCA O G dG.shape (fun _ _ _ _ _ => True) mc design →
      SeqChildRunN (childMap design.modules) design 1 mc (dG.bsIn.take nG) dG.shape.layout.outs
        (fun vals => srcG i (Tools.ShippingMachineChild.boolsOf (dG.bsIn.take nG) vals) (Tools.ShippingMachineChild.bitsOf (dG.bsIn.take nG) vals)))
    (hF : CallFactF dC nC (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (memLeafOutsC G dG) (memLeafSrcC G dG nG srcG))
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 dC design m (dom := fun i : DomainConfig => i)
      (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC)
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits)))
      nC (memLeafBsC G dG nG) (memLeafOutsC G dG) (memLeafSrcC G dG nG srcG) (memLeafPC O G dG design) := by
  intro i bools bits k c hc
  have hlt : k < dC.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
  have hcG : (dC.shape.insts[k]).1 = G := (hkids k hlt).1
  have hck : (dC.shape.insts[k]).1 = c := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt] at hc; simpa using hc
  subst hck
  right
  have hR := call_inRange dC hC.ok hC.hkD hC.hIlen hC.slots hC.callsOk (fun _ => Tools.ShippingCallsChildPorts.argWidths dG nG) hwid (memLeafBsC G dG nG)
    (fun k hk => by
      rw [(hkids k hk).1]; unfold memLeafBsC; rw [if_pos rfl]
      simp [Tools.ShippingCallsChildPorts.argWidths, List.map_map, Function.comp_def]; rfl)
    (fun k hk => by
      rw [(hkids k hk).1]; unfold memLeafBsC; rw [if_pos rfl]
      exact hargsN k hk)
    _ (letObsB_hl dC (fun i : DomainConfig => i) initsC bodyC extC extBC i bools bits) k hlt
  unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
  refine ⟨origin_child_none _ (hkids k hlt).2, (dC.shape.insts[k]).2.1,
    by simp [List.getElem?_map, List.getElem?_eq_getElem hlt], ?_,
    Tools.ShippingMachineCallsLinkedT.args_facts (callsOk_args dC nC hC.callsOk k hlt) (by simp [Tools.ShippingMachineCausal.letObsB]), hR, hF i bools bits k hlt⟩
  intro mc hmc
  have hr := hrun i design mc hmc
  rw [hcG]
  refine ⟨?_, ?_⟩
  · unfold memLeafBsC memLeafOutsC memLeafSrcC; simp only [↓reduceIte]; exact hr
  · rw [hr.2.2.2.2.2.1]; exact (hargsN k hlt).symm

end Callee

end Tools.ShippingSrm4Callee
