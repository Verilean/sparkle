import Tools.ShippingSrm3Callee
import Tools.ShippingQuadComposed
-- UNBUILT (unit SRM4): see STATUS-SRM4.md / REPORT-SRM4.md for the run names and exits.
-- SCOPE (binding, residue R3): the run theorem of a register machine (a `circuit do`, head `machine_trace_of_data_causal`) whose calls are ALL memory entries (the origin builds the memory module), at every depth,
-- proved GENERICALLY from the existing composition results `machine_linkedT_callsRNA` (the memory half `MemFacts` of its per-call disjunction) and `seqChildRunN_of_composedCA`.  No generator change:
-- `generateSeqChildN` / `#machine_composedT` do not accept the head `machine_trace_of_data_causal` for such a machine (SRM1 evidence), this is the statement they would produce, as a theorem.
-- PROVED: `memCallee_composedNW` (`ComposedNW n` of the served run), `memCallee_seqChildRunN` (`SeqChildRunN … (n + 1)`, every `n`).  Depth 0 is not covered (a module with an instance is not instance-free).
-- PREMISES (named): `GenFacts` (the elaborator-generated `X.machine_*` facts of the declaration), `MemFacts` of every call (`hmem`: the per-call operand / read-kind facts; kernel `rfl` / `decide` in an instance, as the generator's `memTactic`),
-- the decidable data (`MemCalleeData`, `outNameOk`, `hext` / `hextB`), `entry` (`MachineDefines`), `MachineClosesAtA` of the callee (`memCallee_closesA`: DERIVED from `MemCalleeData` when every call is a memory entry).
-- `RealChildA` / `ServedRealA` / `JQC` / `MachineRunNCA` are histories of past synthesis results, not freshness or semantic correctness in the current environment.  An example does not make the class complete.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field; no heartbeat option.

namespace Tools.ShippingSrm4Run
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildBndCore Tools.ShippingChildRunAKids
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineAuto Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA Tools.ShippingServedRealA
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCallsLinkedT (MemFacts)
open Tools.ShippingQuadComposed (GenFacts genTrace bsIn_drop_nodomain)
open Tools.ShippingSrm3Callee

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Callee
variable {dC : MachineData} {C : Name} [Inhabited (HList (tys dC.ss))] {ρ : DomainConfig → Type}
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

/-- the per-call memory facts of a generated declaration, in the form `machine_linkedT_callsRNA` asks (`MemFacts` at the let observations and the extension at the state loop) -/
def MemCalls (dC : MachineData) (n : Nat) {ρ : DomainConfig → Type} [Inhabited (HList (tys dC.ss))] (initsC : HList (tys dC.ss))
    (bodyC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      RegList i (HList (tys dC.ss)) (Circuit.SigList i (tys dC.ss)) (tys dC.ss) →
      Circuit i (Circuit.SigList i (tys dC.ss)) (ρ i))
    (extC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → (j : Nat) → (n : Nat) → Signal i (BitVec n))
    (extBC : (i : DomainConfig) → (Nat → Signal i Bool) →
      ((j : Nat) → (n : Nat) → Signal i (BitVec n)) →
      Signal i (HList (tys dC.ss)) → Nat → Signal i Bool) : Prop :=
  ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (k : Nat) (c : Name),
    (dC.shape.insts.map (·.1))[k]? = some c →
    MemFacts dC.shape (letObsB dC (fun i : DomainConfig => i) initsC bodyC extC extBC i bools bits) dC.ls.length
      (dC.bsIn.drop n) n (extC i bools bits (stateLoop initsC (bodyC i bools bits))) k c

/-- a memory call has a built child, so the origin is not an ordinary one -/
theorem MemCalls.child_ne_none {n : Nat} (h : MemCalls dC n initsC bodyC extC extBC) {k : Nat} {c : Name}
    (hc : (dC.shape.insts.map (·.1))[k]? = some c) : (dC.shape.instOrigins.getD k .ord).child? ≠ none := by
  have := h defaultDomain (fun _ => ⟨fun _ => false⟩) (fun _ _ => ⟨fun _ => 0⟩) k c hc
  obtain ⟨cb, aw, dw, A, Dd, E, R, l0, l1, l2, l3, hch, -⟩ := this
  rw [hch]; exact fun h => nomatch h

/-- **`ComposedNW n` of the served run of a callee whose calls are all memory entries** (head `machine_trace_of_data_causal`, via `genTrace`; the calls by `MemFacts`).  Every depth `n`. -/
theorem memCallee_composedNW (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {nameK : Nat → String} {nk : Nat → Nat} {outsK namesK : Nat → List String} {names : List String} {n : Nat}
    (hC : MemCalleeData dC C n nameK nk outsK namesK names)
    (GF : GenFacts dC (fun i : DomainConfig => i) initsC bodyC obsRC extC extBC srcC)
    (hmem : MemCalls dC n initsC bodyC extC extBC) (depth : Nat)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore C [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref C dC.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx C dC.shape) :
    Tools.ShippingMachineDepthRun.ComposedNW depth C dC n m design (fun i : DomainConfig => i) srcC
      (fun i bools bits => extC i bools bits (stateLoop initsC (bodyC i bools bits)))
      (fun i bools bits => extBC i bools bits (stateLoop initsC (bodyC i bools bits))) := by
  have h := genTrace O T hA dC (fun i : DomainConfig => i) GF (machineRunJQC_of_closesA O hA hcore entry closes hw hc)
  exact machine_linkedT_callsRNA depth O h hC.fne n hC.hkD (bsIn_drop_nodomain dC n hC.domB) hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn
    (fun _ => []) (fun _ => []) (fun _ _ _ => []) (fun _ _ => True)
    (fun i bools bits k c hk => Or.inl (hmem i bools bits k c hk))
    (fun k c hk hnone => absurd hnone (hmem.child_ne_none hk))

/-- **`SeqChildRunN` at depth `depth + 1` of a callee whose calls are all memory entries** (the `seq_child_runN` of a memory-bearing register machine, any `depth`).  `hrun` is the served callee run of the
`MachineRunNCA` boundary (a history, as `leafCallee_runNCA`); the boundary `BndA` is not read by the composed theorem. -/
theorem memCallee_seqChildRunN (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {nameK : Nat → String} {nk : Nat → Nat} {outsK namesK : Nat → List String} {names : List String} {n : Nat}
    (hC : MemCalleeData dC C n nameK nk outsK namesK names)
    (hOk : ∀ o ∈ dC.shape.layout.outs, outNameOk o.name = true)
    (GF : GenFacts dC (fun i : DomainConfig => i) initsC bodyC obsRC extC extBC srcC)
    (hmem : MemCalls dC n initsC bodyC extC extBC)
    (hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < n →
      extBC i bools bits (stateLoop initsC (bodyC i bools bits)) j = bools j)
    (hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool)
      (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < n →
      extC i bools bits (stateLoop initsC (bodyC i bools bits)) j n' = bits j n')
    (BndA : Meta.Context → Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop)
    (i : DomainConfig) (depth : Nat) {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hrun : MachineRunNCA O C dC.shape BndA mc design)
    :
    Tools.ShippingMachineDepth.SeqChildRunN (childMap design.modules) design (depth + 1) mc (List.take n dC.bsIn) dC.shape.layout.outs
      (fun vals => srcC i
        (Tools.ShippingMachineChild.boolsOf (List.take n dC.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take n dC.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O depth BndA
    (fun hcore hadm hjqc ent cl _ =>
      memCallee_composedNW O T hadm hC GF hmem depth hjqc.1 (Or.inr hjqc.2) hcore ent cl)
    hC.outTy hOk hC.slotsNe (Nat.pos_of_ne_zero (fun h0 => hC.insts_ne (List.eq_nil_of_length_eq_zero h0)))
    hC.hkD hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn hextB hext i hrun

end Callee

end Tools.ShippingSrm4Run
