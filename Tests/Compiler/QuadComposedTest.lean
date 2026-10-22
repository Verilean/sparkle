import Tests.Compiler.QuadReturnedTest
import Tests.Compiler.TopShareComposedTest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingQuadComposed
-- BUILT (unit SR15): t7 exit 0 (dev run, all in-file statement / mismatch / closure audits pass); the final-SHA rebuild is in REPORT-SR15.md.
-- SCOPE (binding, ledger L8au): the `topshare` INSTANCES of the GENERIC per-callee / per-parent blocks of `Tools/ShippingQuadComposed.lean`.  For the real declarations
-- (`topshare`; callees `wrap`, `wrap3`; shared leaf `acc`) each OLD hand-pasted block of `Tests/Compiler/TopShareComposedTest.lean` (the generated `ts0_*` / `ts1_*` text and the
-- parent's `ts_*` text) is RE-DERIVED from the generic lemma + decided data facts + the named text-supplied premises; the statement of each re-derived theorem is INFERRED
-- from the generic lemma (the binders of the old theorem are used, the body is the generic application) and compared with the OLD statement by `isDefEq` (old theorems untouched).
-- Then `topshare_returned3` / `topshare_wired3` apply the generic `quad_returned` / `quad_wired` with `soundL` / `composed` / the four checks taken from the GENERIC lemmas (not from the
-- `ts_*` blocks); a closure audit checks that none of the old `ts_soundLA` / `ts_composedA` / `ts_traceXA` / `ts_ranA` / `ts_hkid` / `ts_runFacts` / `ts_outsCheck` / `ts_kidsMasked` /
-- `ts_designCheck` / `ts0_C_closesA` / `ts0_C_hsep` / `ts0_C_kidFactsA` / `ts0_C_composedA` / `ts0_C_seqChildRunN2` / … (and the `ts1_*` ones) is in the closure.
-- TEXT-SUPPLIED premises that remain (named, NOT derived generically): `GenFacts` of `topshare` / `wrap` / `wrap3` (the generated `machine_*` facts), `hcalls` of `wrap` / `wrap3`
-- (`ts0_C_hcalls` / `ts1_C_hcalls`: the old chain's `old_seqparent% hcalls`), `hextB` / `hext` of the callees (`seq_child_runN_ofR1`), `QuadGroupFacts` of the parent (the old chain's
-- `gfR*` / `gfHb*` / `gfHv*`, extracted by `oldGroupFact%`), the `Inhabited` instances, and the decided data facts.  `O`, `T`, `hA`, `MachineDefines`, `JQC O 0 w`, `MachineCloses` of the leaf stay premises.
-- `RealChildA` / `ServedRealA` / `JQC` / `MachineRunNCA` are histories of past synthesis results, not freshness or semantic correctness in the current environment.
-- No `sorry`, no `axiom`, no `native_decide`.
open Tests.Compiler.SeqDeepGenDiffTest Tests.Compiler.SeqDeepGenInstTest
section
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingTopShareRun
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadReturned Tools.ShippingQuadComposed Tests.Compiler.QuadLeafGenericTest
open Tools.ShippingSeqOldPieces
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineCausal Tools.ShippingMachineSource
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace Tests.Compiler.QuadComposedTest

local notation "leafD" => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData

/-! ## Decided data facts -/

theorem acc_leafKid : LeafKidData leafD := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel | exact fun h0 => absurd (congrArg List.length h0) (by decide)

theorem wrap_calleeExtra : LeafCalleeExtra Tests.Compiler.SeqDeepGenInstTest.wrap.machineData leafD 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | decide +kernel

theorem wrap3_calleeExtra : LeafCalleeExtra wrap3.machineData leafD 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | decide +kernel

theorem topshare_parentExtra : QuadParentExtra topshare.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machineData wrap3.machineData
    ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 3 3 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | decide +kernel | exact fun h0 => absurd (congrArg List.length h0) (by decide)

theorem topshare_quadAll : QuadAll topshare.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machineData wrap3.machineData leafD
    ``Tests.Compiler.SeqDeepGenDiffTest.topshare ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc 3 3 3 :=
  ⟨topshare_quadData, topshare_parentExtra, acc_leafData, acc_leafKid, wrap_calleeData, wrap_calleeExtra, wrap3_calleeData, wrap3_calleeExtra⟩

/-! ## The text-supplied facts of the generated declarations -/

theorem topshare_gen : GenFacts topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineInits topshare.machineBody
    topshare.machineResult topshare.machineExt topshare.machineExtB topshare.machineSource :=
  ⟨topshare.machine_ok, topshare.machine_body, topshare.machine_inits, topshare.machine_writes, topshare.machine_result, topshare.machine_source,
   fun i bools bits S S' t h =>
    topshare.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem wrap_gen : GenFacts Tests.Compiler.SeqDeepGenInstTest.wrap.machineData (fun i : DomainConfig => i) Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits
    Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody Tests.Compiler.SeqDeepGenInstTest.wrap.machineResult Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt
    Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource :=
  ⟨Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ok, Tests.Compiler.SeqDeepGenInstTest.wrap.machine_body, Tests.Compiler.SeqDeepGenInstTest.wrap.machine_inits,
   Tests.Compiler.SeqDeepGenInstTest.wrap.machine_writes, Tests.Compiler.SeqDeepGenInstTest.wrap.machine_result, Tests.Compiler.SeqDeepGenInstTest.wrap.machine_source,
   fun i bools bits S S' t h =>
    Tests.Compiler.SeqDeepGenInstTest.wrap.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem wrap3_gen : GenFacts wrap3.machineData (fun i : DomainConfig => i) wrap3.machineInits wrap3.machineBody wrap3.machineResult wrap3.machineExt
    wrap3.machineExtB wrap3.machineSource :=
  ⟨wrap3.machine_ok, wrap3.machine_body, wrap3.machine_inits, wrap3.machine_writes, wrap3.machine_result, wrap3.machine_source,
   fun i bools bits S S' t h =>
    wrap3.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
      (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)⟩

theorem wrap_hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < 3 →
    Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB i bools bits (stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits
      (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)) j = bools j :=
  oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j : Nat), j < 3 →
        Tests.Compiler.SeqDeepGenInstTest.wrap.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)) j = bools j)
      Tests.Compiler.SeqDeepGenInstTest.wrap.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hextB

theorem wrap_hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < 3 →
    Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt i bools bits (stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)) j n' = bits j n' :=
  oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j n' : Nat), j < 3 →
        Tests.Compiler.SeqDeepGenInstTest.wrap.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenInstTest.wrap.machineInits (Tests.Compiler.SeqDeepGenInstTest.wrap.machineBody i bools bits)) j n' = bits j n')
      Tests.Compiler.SeqDeepGenInstTest.wrap.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hext

theorem wrap3_hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat), j < 3 →
    Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB i bools bits (stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)) j = bools j :=
  oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j : Nat), j < 3 →
        Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)) j = bools j)
      Tests.Compiler.SeqDeepGenDiffTest.wrap3.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hextB

theorem wrap3_hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat), j < 3 →
    Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt i bools bits (stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)) j n' = bits j n' :=
  oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j n' : Nat), j < 3 →
        Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineInits (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineBody i bools bits)) j n' = bits j n')
      Tests.Compiler.SeqDeepGenDiffTest.wrap3.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hext

/-- The parent's `QuadGroupFacts` for `topshare`: the old chain's `gfR*` / `gfHb*` / `gfHv*` facts (extracted by `oldGroupFact%` from the OLD generated
`topshare.machine_composedNR2`) assembled per call; the remaining parts of `SeqFactsRN` are derived by `quad_composed`. -/
theorem qc_hgrp : QuadGroupFacts Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData 3
    (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB)
    (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt i bools bits (stateLoop Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody i bools bits)))
    (fun i bools bits => Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits (stateLoop Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits (Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody i bools bits)))
    (quadBsF ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData 3 3) (quadOutsOf ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData)
    (quadSrcF ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData 3 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource) := by
  intro i bools bits k hk
  have h4 : Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData.shape.insts.length = 4 := topshare_quadData.len4
  have R0 : ∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat) τ)
      ((List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn).filter fun b => b.2 != .domain) :=
    oldGroupFact% (∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat) τ)
      ((List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn).filter fun b => b.2 != .domain)) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfR0
  have Hb0 : Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
      (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat)) = _ :=
    oldGroupFact% (Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
      (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat)) = _) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
  have Hv0 : Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
      (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat)) = _ :=
    oldGroupFact% (Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.bsIn)
      (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([0, 1] : List Nat)) = _) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0

  have R1 : ∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat) τ)
      ((List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn).filter fun b => b.2 != .domain) :=
    oldGroupFact% (∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat) τ)
      ((List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn).filter fun b => b.2 != .domain)) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfR1
  have Hb1 : Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
      (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat)) = _ :=
    oldGroupFact% (Tools.ShippingMachineChild.boolsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
      (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat)) = _) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb1
  have Hv1 : Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
      (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat)) = _ :=
    oldGroupFact% (Tools.ShippingMachineChild.bitsOf (List.take 3 Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineData.bsIn)
      (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Tests.Compiler.SeqDeepGenDiffTest.topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Tests.Compiler.SeqDeepGenDiffTest.topshare.machineInits Tests.Compiler.SeqDeepGenDiffTest.topshare.machineBody Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExt Tests.Compiler.SeqDeepGenDiffTest.topshare.machineExtB i bools bits) ([1, 0] : List Nat)) = _) Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv1
  rcases k with _ | _ | _ | _ | k
  · first
      | (refine ⟨R0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain) Hb0 Hv0)).trans rfl)
      | (refine ⟨R0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain) Hb0 Hv0)).trans rfl)
  · first
      | (refine ⟨R0, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain) Hb0 Hv0)).trans rfl)
      | (refine ⟨R0, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenInstTest.wrap.machineSource Sparkle.Core.Domain.defaultDomain) Hb0 Hv0)).trans rfl)
  · first
      | (refine ⟨R1, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain) Hb1 Hv1)).trans rfl)
      | (refine ⟨R1, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain) Hb1 Hv1)).trans rfl)
  · first
      | (refine ⟨R1, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain) Hb1 Hv1)).trans rfl)
      | (refine ⟨R1, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Tests.Compiler.SeqDeepGenDiffTest.wrap3.machineSource Sparkle.Core.Domain.defaultDomain) Hb1 Hv1)).trans rfl)
  · omega

/-! ## Re-derivation of the Tests.Compiler.TopShareComposedTest. blocks, with a statement audit -/

open Lean Elab Command Meta Term in
/-- `quad_audit new ≡ old := body`: the binders of the Tests.Compiler.TopShareComposedTest. theorem `old` are introduced (with their names), `body` is elaborated WITHOUT an expected type (so the statement of the new theorem
is INFERRED from the generic lemma applied in `body`), its type is checked by `isDefEq` against the Tests.Compiler.TopShareComposedTest. conclusion, and the theorem `new` (binders + inferred type) is added. -/
elab "quad_audit " new:ident " ≡ " old:ident " := " body:term : command => do
  let ns ← getCurrNamespace
  liftTermElabM do
    let oldN ← realizeGlobalConstNoOverloadWithInfo old
    let oldTy := (← getConstInfo oldN).type
    forallTelescope oldTy fun xs concl => do
      let e ← elabTerm body none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars (← inferType e)
      if e.hasMVar || ty.hasMVar then throwError "SR15: unassigned metavariables in the instance term of {new.getId}"
      unless (← isDefEq ty concl) do
        throwError "SR15 statement audit: {new.getId} differs from {oldN}\ninferred:{indentExpr ty}\nold:{indentExpr concl}"
      let v ← mkLambdaFVars xs e
      let t ← mkForallFVars xs ty
      addAndCompile <| .thmDecl { name := ns ++ new.getId, levelParams := [], type := t, value := v }
      logInfo m!"SR15: statement of {ns ++ new.getId} (generic lemma, inferred) ≡ statement of {oldN} ({xs.size} binders)"

local notation "accHcl" => (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _)

/-! ### the leaf and the callees -/

quad_audit leaf0_kidFactsA ≡ Tests.Compiler.TopShareComposedTest.ts0_G_kidFactsA := leaf_kidFactsA O acc_leafData acc_leafKid hR0 accHcl n
quad_audit leaf1_kidFactsA ≡ Tests.Compiler.TopShareComposedTest.ts1_G_kidFactsA := leaf_kidFactsA O acc_leafData acc_leafKid hR0 accHcl n
quad_audit wrap_kidFactsA ≡ Tests.Compiler.TopShareComposedTest.ts0_C_kidFactsA := leafCallee_kidFactsA O T acc_leafData acc_leafKid wrap_calleeData wrap_calleeExtra entry hR0 accHcl n
quad_audit wrap3_kidFactsA ≡ Tests.Compiler.TopShareComposedTest.ts1_C_kidFactsA := leafCallee_kidFactsA O T acc_leafData acc_leafKid wrap3_calleeData wrap3_calleeExtra entry hR0 accHcl n
quad_audit wrap_traceXA ≡ Tests.Compiler.TopShareComposedTest.ts0_C_traceXA := leafCallee_traceXA O T hA acc_leafData wrap_calleeData hR0 accHcl wrap_gen hw hc hcore entry
quad_audit wrap3_traceXA ≡ Tests.Compiler.TopShareComposedTest.ts1_C_traceXA := leafCallee_traceXA O T hA acc_leafData wrap3_calleeData hR0 accHcl wrap3_gen hw hc hcore entry
quad_audit wrap_composedA ≡ Tests.Compiler.TopShareComposedTest.ts0_C_composedA :=
  leafCallee_composedA O T hA acc_leafData wrap_calleeData hR0 accHcl wrap_gen Tests.Compiler.TopShareComposedTest.ts0_C_hcalls hw hc hcore entry
quad_audit wrap3_composedA ≡ Tests.Compiler.TopShareComposedTest.ts1_C_composedA :=
  leafCallee_composedA O T hA acc_leafData wrap3_calleeData hR0 accHcl wrap3_gen Tests.Compiler.TopShareComposedTest.ts1_C_hcalls hw hc hcore entry
quad_audit wrap_seqChildRunN2 ≡ Tests.Compiler.TopShareComposedTest.ts0_C_seqChildRunN2 :=
  leafCallee_seqChildRunN2 O T acc_leafData wrap_calleeData wrap_calleeExtra accHcl wrap_gen Tests.Compiler.TopShareComposedTest.ts0_C_hcalls wrap_hextB wrap_hext h
quad_audit wrap3_seqChildRunN2 ≡ Tests.Compiler.TopShareComposedTest.ts1_C_seqChildRunN2 :=
  leafCallee_seqChildRunN2 O T acc_leafData wrap3_calleeData wrap3_calleeExtra accHcl wrap3_gen Tests.Compiler.TopShareComposedTest.ts1_C_hcalls wrap3_hextB wrap3_hext h

/-! ### the parent -/

quad_audit parent_hkid ≡ Tests.Compiler.TopShareComposedTest.ts_hkid := quad_hkid O T topshare_quadAll hM0 hM1 hR0 accHcl n k hk
quad_audit parent_ranA ≡ Tests.Compiler.TopShareComposedTest.ts_ranA := quad_ranA O T hA topshare_quadAll hM0 hM1 hR0 accHcl hcore entry hw
quad_audit parent_runFacts ≡ Tests.Compiler.TopShareComposedTest.ts_runFacts := quad_runFacts O T n hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw
quad_audit parent_outsCheck ≡ Tests.Compiler.TopShareComposedTest.ts_outsCheck := quad_outsCheck O T n hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw
quad_audit parent_kidsMasked ≡ Tests.Compiler.TopShareComposedTest.ts_kidsMasked := quad_kidsMasked O T n hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw
quad_audit parent_designCheck ≡ Tests.Compiler.TopShareComposedTest.ts_designCheck := quad_designCheck O T n hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw
quad_audit parent_traceXA ≡ Tests.Compiler.TopShareComposedTest.ts_traceXA := quad_traceXA O T hA topshare_quadAll topshare_gen entry hM0 hM1 hR0 accHcl hw hcore
quad_audit parent_soundLA ≡ Tests.Compiler.TopShareComposedTest.ts_soundLA := quad_soundLA O T hA topshare_quadAll topshare_gen entry hM0 hM1 hR0 accHcl hw hcore
set_option maxHeartbeats 0 in
quad_audit parent_composedA ≡ Tests.Compiler.TopShareComposedTest.ts_composedA :=
  quad_composed topshare_quadAll topshare_gen wrap_gen wrap3_gen Tests.Compiler.TopShareComposedTest.ts0_C_hcalls Tests.Compiler.TopShareComposedTest.ts1_C_hcalls wrap_hextB wrap_hext wrap3_hextB wrap3_hext qc_hgrp accHcl
    hcore entry ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩

/-! ## `quad_returned` / `quad_wired` with the blocks taken from the GENERIC lemmas -/

open Lean Elab Command Meta Term in
set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let stx ← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare) mctx mref cctx cref w y w') =>
    @Tools.ShippingQuadReturned.quad_returned _ _ _ _ topshare.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machineData wrap3.machineData
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc 3 3 3 2 3 Unit (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineInits
        topshare.machineBody topshare.machineExt topshare.machineExtB)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun hcore entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_soundLA O T hA topshare_quadAll topshare_gen entry hM0 hM1 hR0 accHcl hw hcore)
      (fun hcore entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_composed topshare_quadAll topshare_gen wrap_gen wrap3_gen Tests.Compiler.TopShareComposedTest.ts0_C_hcalls Tests.Compiler.TopShareComposedTest.ts1_C_hcalls wrap_hextB wrap_hext wrap3_hextB wrap3_hext qc_hgrp accHcl hcore entry ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩)
      topshare_quadAll.hPX.outTy
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_runFacts O T 1 hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw)
      (fun hcore hpost entry _ hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_outsCheck O T 1 hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_kidsMasked O T 1 hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_designCheck O T 1 hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw)
      O T hA topshare_quadData acc_leafData wrap_calleeData wrap3_calleeData entryT entryW entryW3 hR0
      (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) w w' y hw h)
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  if e.hasMVar || ty.hasMVar then throwError "unassigned mvars in the instance term"
  addAndCompile <| .thmDecl { name := `Tests.Compiler.QuadComposedTest.topshare_returned3, levelParams := [], type := ty, value := e }
  -- statement audit: the instance's statement is `isDefEq` (same binders) to the OLD hand-written theorem
  let tb := (← getConstInfo ``Tests.Compiler.TopShareReturnedTest.topshare_returned).type
  forallTelescope ty fun xs ca => do
    let cb ← instantiateForall tb xs
    unless (← isDefEq ca cb) do throwError "SR15 statement audit: Tests.Compiler.QuadComposedTest.topshare_returned3 differs from Tests.Compiler.TopShareReturnedTest.topshare_returned"
    logInfo m!"SR15: statement of Tests.Compiler.QuadComposedTest.topshare_returned3 ≡ statement of Tests.Compiler.TopShareReturnedTest.topshare_returned ({xs.size} binders)"
#print axioms Tests.Compiler.QuadComposedTest.topshare_returned3

open Lean Elab Command Meta Term in
set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let stx ← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryT : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.topshare topshare.machineData.shape)
    (entryW : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenInstTest.wrap Tests.Compiler.SeqDeepGenInstTest.wrap.machineData.shape)
    (entryW3 : MachineDefines mctx mref cctx cref ``Tests.Compiler.SeqDeepGenDiffTest.wrap3 wrap3.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinational ``Tests.Compiler.SeqDeepGenDiffTest.topshare) mctx mref cctx cref w y w') =>
    @Tools.ShippingQuadReturned.quad_wired _ _ _ _ topshare.machineData Tests.Compiler.SeqDeepGenInstTest.wrap.machineData wrap3.machineData
      Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machineData
      ``Tests.Compiler.SeqDeepGenDiffTest.topshare ``Tests.Compiler.SeqDeepGenInstTest.wrap ``Tests.Compiler.SeqDeepGenDiffTest.wrap3
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc 3 3 3 2 3 Unit (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshare.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshare.machineInits
        topshare.machineBody topshare.machineExt topshare.machineExtB)
      topshare.machineSource
      (fun i bools bits => topshare.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun i bools bits => topshare.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop topshare.machineInits (topshare.machineBody i bools bits)))
      (fun hcore entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_soundLA O T hA topshare_quadAll topshare_gen entry hM0 hM1 hR0 accHcl hw hcore)
      (fun hcore entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_composed topshare_quadAll topshare_gen wrap_gen wrap3_gen Tests.Compiler.TopShareComposedTest.ts0_C_hcalls Tests.Compiler.TopShareComposedTest.ts1_C_hcalls wrap_hextB wrap_hext wrap3_hextB wrap3_hext qc_hgrp accHcl hcore entry ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩)
      topshare_quadAll.hPX.outTy
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_runFacts O T 1 hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw)
      (fun hcore hpost entry _ hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_outsCheck O T 1 hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_kidsMasked O T 1 hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw)
      (fun hcore hpost entry hB => by
        obtain ⟨O, T, hA, hM0, hR0, hM1, hR1, hw⟩ := hB
        exact quad_designCheck O T 1 hA topshare_quadAll hM0 hM1 hR0 accHcl hcore hpost entry hw)
      O T hA topshare_quadData acc_leafData wrap_calleeData wrap3_calleeData entryT entryW entryW3 hR0
      (fun mc cc => Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc.machine_closes mc _ cc _) w w' y hw h)
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  if e.hasMVar || ty.hasMVar then throwError "unassigned mvars in the instance term"
  addAndCompile <| .thmDecl { name := `Tests.Compiler.QuadComposedTest.topshare_wired3, levelParams := [], type := ty, value := e }
  -- statement audit: the instance's statement is `isDefEq` (same binders) to the OLD hand-written theorem
  let tb := (← getConstInfo ``Tests.Compiler.TopShareComposedTest.topshare_wired).type
  forallTelescope ty fun xs ca => do
    let cb ← instantiateForall tb xs
    unless (← isDefEq ca cb) do throwError "SR15 statement audit: Tests.Compiler.QuadComposedTest.topshare_wired3 differs from Tests.Compiler.TopShareComposedTest.topshare_wired"
    logInfo m!"SR15: statement of Tests.Compiler.QuadComposedTest.topshare_wired3 ≡ statement of Tests.Compiler.TopShareComposedTest.topshare_wired ({xs.size} binders)"
#print axioms Tests.Compiler.QuadComposedTest.topshare_wired3


/-! ## the audit discriminates: swapped declarations / different blocks are NOT `isDefEq` -/

open Lean Elab Command Meta in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let T (n : Name) : MetaM Lean.Expr := do pure (← getConstInfo n).type
  let ns := `Tests.Compiler.QuadComposedTest
  let old := `Tests.Compiler.TopShareComposedTest
  let pairs : List (Name × Name) :=
    [(ns ++ `wrap_kidFactsA, old ++ `ts1_C_kidFactsA), (ns ++ `wrap3_kidFactsA, old ++ `ts0_C_kidFactsA),
     (ns ++ `wrap_traceXA, old ++ `ts1_C_traceXA), (ns ++ `wrap_composedA, old ++ `ts1_C_composedA),
     (ns ++ `wrap3_composedA, old ++ `ts0_C_composedA), (ns ++ `wrap_seqChildRunN2, old ++ `ts1_C_seqChildRunN2),
     (ns ++ `leaf0_kidFactsA, old ++ `ts0_C_kidFactsA),
     (ns ++ `parent_runFacts, old ++ `ts_designCheck), (ns ++ `parent_outsCheck, old ++ `ts_kidsMasked),
     (ns ++ `parent_composedA, old ++ `ts_soundLA), (ns ++ `parent_soundLA, old ++ `ts_composedA),
     (ns ++ `parent_traceXA, old ++ `ts_composedA)]
  for (a, b) in pairs do
    let ta ← T a
    let tb ← T b
    if (← isDefEq ta tb) then throwError "SR15 AUDIT FAILED: the statements of {a} and {b} were judged equal (the statement audit would not discriminate)"
  logInfo m!"SR15: the statement audit discriminates: {pairs.length} type-correct mismatched pairs (callee swapped / different block) are rejected"

/-! ## closure audit -/

open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for c in [``Tests.Compiler.QuadComposedTest.topshare_returned3, ``Tests.Compiler.QuadComposedTest.topshare_wired3] do
    stdAxioms c
    let cl ← depClosure c
    let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
      `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
    for f in forbidden do
      unless (← getEnv).contains f do throwError "SR15 AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
    let bad := hits cl ++ cl.toList.filter fun x => forbidden.any (·.isPrefixOf x)
    unless bad.isEmpty do throwError "SR15 AUDIT FAILED: old boundary / old child predicate in the closure of {c}: {bad}"
    -- the OLD hand-pasted per-callee / per-parent blocks are NOT in the closure
    let oldBlocks : List Name :=
      [`ts_soundLA, `ts_composedA, `ts_traceXA, `ts_ranA, `ts_hkid, `ts_runFacts, `ts_outsCheck, `ts_kidsMasked, `ts_designCheck, `ts_houtTy,
       `ts0_C_closesA, `ts0_C_hsep, `ts0_C_kidFactsA, `ts0_G_kidFactsA, `ts0_C_hgk, `ts0_C_ifaceP, `ts0_C_traceXA, `ts0_C_composedA, `ts0_C_seqChildRunN2,
       `ts1_C_closesA, `ts1_C_hsep, `ts1_C_kidFactsA, `ts1_G_kidFactsA, `ts1_C_hgk, `ts1_C_ifaceP, `ts1_C_traceXA, `ts1_C_composedA, `ts1_C_seqChildRunN2,
       `topshare_noShips_noBd_dc]
    for b in oldBlocks do
      let n := `Tests.Compiler.TopShareComposedTest ++ b
      unless (← getEnv).contains n do throwError "SR15 AUDIT FAILED: {n} does not exist (the audit would check nothing)"
      if cl.contains n then throwError "SR15 AUDIT FAILED: the old pasted block {n} is in the closure of {c}"
    for n in [`Tests.Compiler.TopShareTraceTest.topshare_closes0, `Tests.Compiler.TopShareTraceTest.topshare_machineRun,
        `Tests.Compiler.SeqDeepGenDiffTest.topshare.machine_design_svNR2] do
      unless (← getEnv).contains n do throwError "SR15 AUDIT FAILED: {n} does not exist (the audit would check nothing)"
      if cl.contains n then throwError "SR15 AUDIT FAILED: {n} is in the closure of {c}"
    for must in [(if c == ``Tests.Compiler.QuadComposedTest.topshare_returned3 then ``Tools.ShippingQuadReturned.quad_returned else ``Tools.ShippingQuadReturned.quad_wired),
        ``Tools.ShippingQuadReturned.quad_returned, ``Tools.ShippingQuadComposed.quad_composed, ``Tools.ShippingQuadComposed.quad_soundLA,
        ``Tools.ShippingQuadComposed.quad_runFacts, ``Tools.ShippingQuadComposed.quad_outsCheck, ``Tools.ShippingQuadComposed.quad_kidsMasked,
        ``Tools.ShippingQuadComposed.quad_designCheck, ``Tools.ShippingQuadComposed.leafCallee_seqChildRunN2, ``Tools.ShippingQuadComposed.leaf_kidFactsA,
        ``Tools.ShippingQuadComposed.leafCallee_kidFactsA, ``Tools.ShippingQuadComposed.leafCallee_runNCA,
        ``Tools.ShippingSeqParentAt.machine_design_noShips_noBd_dc_at] do
      unless cl.contains must do throwError "SR15 AUDIT FAILED: {must} not in the closure of {c}"
    let remaining := cl.toList.filter fun x => (`Tests.Compiler.TopShareComposedTest).isPrefixOf x
    logInfo m!"SR15 CLOSURE AUDIT: {c}: standard axioms; closure {cl.size} constants; no old pasted ts_/ts0_/ts1_ block; the generic quad_composed / quad_soundLA / four checks / callee lemmas are in it; remaining TopShareComposedTest constants (the named text-supplied premises): {remaining}"

end Tests.Compiler.QuadComposedTest
end
