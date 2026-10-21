import Tests.Compiler.SeqDeepGrandKidFactsTest
import Tests.Compiler.SeqParentGenTest
import Tests.Compiler.ParentSeqComposedATest
import Tools.ShippingSeqChildDeepRunA
import Tools.ShippingSeqOldPieces
-- PREMISES carried INSIDE `BndAg` (an existential that stays in the conclusion; none is supplied here): `O : RefLawsAOps` and
-- `T : RefLawsATele` (ADDED boundary), `AdmCtx O.quiet mctx cctx`, `MachineDefines` of `mid` and of `cnt`, a start world with
-- `JQ O.quiet D₀ w`, and the cache invariant `D₀ = 0 ∨ CacheInvA O (cv w)`.  Outer Prop premises: `hr`, `entry`, `closes : True`.
-- This is ONE concrete endpoint for `grand`, NOT a general depth-2 generator (the generator stays REFUSED).
-- BUILT (unit SR3s): s4 exit 0 (mid part), s6 exit 0 (grand trace/soundL/composed), s8 exit 0 (hcalls on MachineRunNCA), s9 exit 0 (endpoint), s11 exit 0 (in-test audit), s13 exit 0 (final). Earlier runs of the same names exit 1 (missing opens, duplicated block, `interval_cases`, decoded_eq source).  In-test audit THROWS on failure.
-- SCOPE (binding): `grand -> mid -> cnt`, from ONE core run of `grand`: the trace `ServedRealA`, `soundL` (MachineTraceLB) and
-- `composed` (depth 2, `ComposedG`) of `grand`, on the new boundary.  The depth-1 `composed` of the child `mid` is proved on the new
-- boundary (`mid_composedA`, with its own callee `cnt`), turned into `SeqChildRunN` at depth 2 (`seqChildRunN_of_composedCA`), and
-- enters `grand`'s `hcalls` through `seqFactsRN_of_conv`.  `RealChildA` is a history of past synthesis results; `T` is an ADDED boundary.
namespace Tests.Compiler.SeqDeepGrandEndpointTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildVCA Tools.ShippingChildBndCore
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineLinked
open Tools.ShippingParentSeqComposedA Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA
open Tools.ShippingServedRealA Tools.ShippingChildDepthC Tools.ShippingChildTranslateA Tools.ShippingParentRanA
open Tools.ShippingMachineShipsHier Tools.ShippingChildComposeC Tools.ShippingChildRunAMain Tools.ShippingMachineShipsDepth Tools.ShippingHierStateG Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tests.Compiler.SeqDeepMidTest Tests.Compiler.SeqDeepMidFactsTest Tests.Compiler.SeqDeepGrandKidFactsTest
open Tools.ShippingSeqParentLemmas

-- unit SR3t, step 1: the pieces of the OLD generated composed theorems are read through the TYPED helpers of
-- `Tools/ShippingSeqOldPieces.lean` (by binder name / binder kind, each with an explicit expected type, `isDefEq`-checked); the
-- trace arguments are the generated `machine_*` theorems by name, the `decide` facts are `decide` (as the old chain's proof terms were).
local instance midInhabHL : Inhabited (HList (Tools.ShippingMachineDenote.tys mid.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys mid.machineData.ss)))
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_composedNR1 Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA
local instance grandInhabHL : Inhabited (HList (Tools.ShippingMachineDenote.tys grand.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys grand.machineData.ss)))
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA

section
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- The run boundary of the CHILD `mid` (new boundary): the grandchild `cnt`'s reflection at the run's contexts.  The start-world
data (`JQC`) and `AdmCtx` are fields of `MachineRunNCA`/the composed's premises. -/
def midBndA (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) :
    Lean.Meta.Context → Lean.Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop :=
  fun mctx cctx _ _ _ =>
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape

theorem mid_hcausal : HCausalOf Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData (fun i => i) Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExtB :=
  fun i bools bits S S' t h =>
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem grand_hcausal : HCausalOf Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB := fun i bools bits S S' t h =>
  Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem mid_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape m design)
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData m design (fun i => i) Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody i bools bits)))
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody i bools bits)))
      (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData (fun i => i) Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits
        Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData
    (fun i => i) Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineResult
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExtB Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_ok Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_body Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_inits
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_writes Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_result Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machine_source mid_hcausal
    O (bodyStepC_of_tele O T) hA (n := D₀ + 1) (htr_of_tele O hA T D₀) (m := m) (design := design)
    (machineRunJQC_of_closesA O hA hcore entry (mid_closesA O T hA hR0) hw hc)

theorem mid_hcalls (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData design m (dom := fun i => i)
      (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData (fun i => i) Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExtB)
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody i bools bits)))
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody i bools bits)))
      2
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.bsIn else [])
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape.layout.outs else [])
      (fun i n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then fun vals => Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineSource i
        (Tools.ShippingMachineChild.boolsOf Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.bsIn vals) else fun vals => [])
      (fun n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape mc)) :=
  (old_seqparent% hcalls Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid) m design

theorem mid_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape) :
    Tools.ShippingMachineDepthRun.ComposedNW 1 ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData 2 m design
      (fun i => i) Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody i bools bits)))
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody i bools bits))) := by
  have h := mid_traceXA O T hA hR0 hw hc hcore entry
  exact machine_linkedT_callsRNA 1 O h (by first | decide | decide +kernel) 2 (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.bsIn else [])
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape.layout.outs else [])
    (fun i n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then fun vals => Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineSource i
        (Tools.ShippingMachineChild.boolsOf Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.bsIn vals) else fun vals => [])
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt then (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape mc))
    (mid_hcalls m design)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact mid_insts_cnt k hk
      subst hck
      have hmr : Tools.ShippingGateChild.MachineRun ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0,
          Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_closes mctx' _ cctx' _⟩
      split <;> exact hmr)

theorem mid_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape (midBndA mref cref) mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (childMap design.modules) design 2 mc (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn)
      Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape.layout.outs
      (fun vals => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource Sparkle.Core.Domain.defaultDomain
        (Tools.ShippingMachineChild.boolsOf (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O 1 (midBndA mref cref)
    (fun hcore hadm hjqc entry _ hB => mid_composedA O T hadm hB hjqc.1 (Or.inr hjqc.2) hcore entry)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j : Nat), j < 2 →
        Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody i bools bits)) j = bools j)
      Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hextB)
    (oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j n' : Nat), j < 2 →
        Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineBody i bools bits)) j n' = bits j n')
      Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hext)
    Sparkle.Core.Domain.defaultDomain h

theorem grand_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData.shape m design)
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineSource
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody i bools bits)))
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody i bools bits)))
      (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits
        Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData
    (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineResult
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineSource Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_ok Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_body Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_inits
    Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_writes Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_result Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_source grand_hcausal
    O (bodyStepC_of_tele O T) hA (n := D₀ + 1) (htr_of_tele O hA T D₀) (m := m) (design := design)
    (machineRunJQC_of_closesA O hA hcore entry (grand_closesA O T hA hM hR0) hw hc)


/-- **`soundL` for `grand`** (MachineTraceLB): `grand_traceXA` with `ServedRealA` forgotten. -/
theorem grand_soundLA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``mid mid.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``grand [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``grand grand.machineData.shape) :
    Tools.ShippingMachineAuto.MachineTraceLB ``grand grand.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      grand.machineSource
      (fun i bools bits => grand.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits)))
      (fun i bools bits => grand.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop grand.machineInits (grand.machineBody i bools bits)))
      (letObsB grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) grand.machineInits
        grand.machineBody grand.machineExt grand.machineExtB) := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    grand_traceXA O T hA hM hR0 hw hc hcore entry
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

theorem grand_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData.shape) :
    ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData 1 m design
      (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineSource
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody i bools bits)))
      (fun i bools bits => Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits (Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody i bools bits))) := by
  have h := grand_traceXA O T hA hM hR0 hw hc hcore entry
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact machine_linkedT_callsRNA 2 O h (by first | decide | decide +kernel) 1 (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid then List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn else [])
    (fun n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid then Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape.layout.outs else [])
    (fun i n => if n = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid then fun vals => Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource Sparkle.Core.Domain.defaultDomain
      (Tools.ShippingMachineChild.boolsOf (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn) vals)
      (Tools.ShippingMachineChild.bitsOf (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn) vals) else fun vals => [])
    (fun _ mc => Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.shape (midBndA mref cref) mc design)
    (fun i bools bits k c hk => by
      have hk' : k < Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1; simpa using this
      have hck : c = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk'] at hk
        rw [← Option.some.inj hk]
        exact (grand_insts_mid k hk').1
      subst hck
      -- the group facts of the generated proof that do not mention the child predicate
      have L : ∀ (q : Nat) (hq : q < ([0] : List Nat).length), ([0] : List Nat)[q] < Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData.ls.length ∧
          ∃ g, (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits)[([0] : List Nat)[q]]? = some g :=
        oldGroupFact% (∀ (q : Nat) (hq : q < ([0] : List Nat).length), ([0] : List Nat)[q] < Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData.ls.length ∧
          ∃ g, (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits)[([0] : List Nat)[q]]? = some g) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfL0
      have R : ∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits) ([0] : List Nat) τ)
          ((List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn).filter fun b => b.2 != .domain) :=
        oldGroupFact% (∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits) ([0] : List Nat) τ)
          ((List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn).filter fun b => b.2 != .domain)) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfR0
      have Hb : Tools.ShippingMachineChild.boolsOf (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits) ([0] : List Nat)) = _ :=
        oldGroupFact% (Tools.ShippingMachineChild.boolsOf (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits) ([0] : List Nat)) = _) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
      have Hv : Tools.ShippingMachineChild.bitsOf (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits) ([0] : List Nat)) = _ :=
        oldGroupFact% (Tools.ShippingMachineChild.bitsOf (List.take 2 Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineInits Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineBody Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExt Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineExtB i bools bits) ([0] : List Nat)) = _) Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0
      have hlt : k < 2 := by
        have : Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData.shape.insts.length = 2 := by first | decide | decide +kernel
        omega
      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      rcases k with _ | _ | k
      · first
          | (refine ⟨rfl, [0], rfl, (fun mc hmc => ⟨mid_seqChildRunN2 O T hmc, by rw [(mid_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L, R, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource Sparkle.Core.Domain.defaultDomain) Hb Hv)).trans rfl)
          | (refine ⟨rfl, [0], rfl, (fun mc hmc => ⟨mid_seqChildRunN2 O T hmc, by rw [(mid_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L, R, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource Sparkle.Core.Domain.defaultDomain) Hb Hv)).trans rfl)
      · first
          | (refine ⟨rfl, [0], rfl, (fun mc hmc => ⟨mid_seqChildRunN2 O T hmc, by rw [(mid_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L, R, 0, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[0]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource Sparkle.Core.Domain.defaultDomain) Hb Hv)).trans rfl)
          | (refine ⟨rfl, [0], rfl, (fun mc hmc => ⟨mid_seqChildRunN2 O T hmc, by rw [(mid_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L, R, 1, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[1]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid.machineSource Sparkle.Core.Domain.defaultDomain) Hb Hv)).trans rfl)
      · omega)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact (grand_insts_mid k hk).1
      subst hck
      exact Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main O T
        (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons hM
        (fun mctx cctx _ w raw D _ => Tools.ShippingReflectCtx.MachineDefines.ctx hR0)
        (fun mctx cctx w raw D hin _ => by
          obtain ⟨_, _, _, hadm', _⟩ := hin
          exact mid_closesA O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))
        (by first | decide | decide +kernel))


end


/-- The run boundary of the NEW depth-2 endpoint of `grand`: laws `O`, `T` (PREMISES, a separate assumption family), the admissible
contexts, `MachineDefines` of the callee `mid` AND of its callee `cnt`, and a start world in `JQ`.  It replaces `ChildBnd`. -/
def BndAg : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``mid mid.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape ∧
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))

theorem grand_houtTy : ∀ o ∈ grand.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

open Lean Elab Command Meta Term in
set_option maxHeartbeats 4000000 in
/- **`grand`'s depth-2 endpoint on the new boundary, with `soundL`, `composed`, `houtTy` and the four checks SUPPLIED**:
`machine_design_noShips_noBd_dc` at `n := 2`, `kD := 1`, `C := True`, `Bnd := BndAg`; `soundL` := `grand_soundLA`, `composed` :=
`grand_composedA`, `hFacts` / `hOuts` / `hBdRun` / `hdc` := `grand_runFacts` / `grand_outsCheck` / `grand_kidsMasked` /
`grand_designCheck` (SR3r) at `n := 1` (their depth is `n + 1 = 2`), all from the SAME core run.  The theorem `grand_noShips_noBdA_dcH` is
ADDED by this command (its type is the inferred type of the term; the audit reads it back). Remaining premises: `hr`, `entry`,
`closes` (the trivial `True`); `BndAg` (existential over `O`/`T`/`AdmCtx`/`MachineDefines mid`/`MachineDefines cnt`/start world)
stays in the conclusion. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let stx ← `(@Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc 2 BndAg (fun _ _ _ _ => True)
    ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machineData 1 Unit
    (fun _ => Sparkle.Core.Domain.defaultDomain) _ _ _ _ _ _ _
    (fun hcore entry _ hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_soundLA O T hA hM hR0 hw hc hcore entry)
    (fun hcore entry _ hB _ => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_composedA O T hA hM hR0 hw hc hcore entry)
    grand_houtTy
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_runFacts O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry _ hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_outsCheck O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_kidsMasked O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact grand_designCheck O T 1 hA hM hR0 hcore hpost entry hw hc))
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  if e.hasMVar || ty.hasMVar then throwError "unassigned mvars in the endpoint term"
  addAndCompile <| .thmDecl { name := `Tests.Compiler.SeqDeepGrandEndpointTest.grand_noShips_noBdA_dcH, levelParams := [], type := ty, value := e }

#print axioms grand_soundLA
#print axioms grand_composedA
#print axioms Tests.Compiler.SeqDeepGrandEndpointTest.grand_noShips_noBdA_dcH


open Lean Elab Command Meta in
open Tests.Compiler.ChildVertAuditTest in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let new := `Tests.Compiler.SeqDeepGrandEndpointTest.grand_noShips_noBdA_dcH
  for nm in [new, ``grand_soundLA, ``grand_composedA, ``grand_traceXA, ``mid_composedA, ``mid_seqChildRunN2] do
    stdAxioms nm
  let ty := (← getConstInfo new).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : True"]
  unless premises.toList == expected do throwError "SR3s AUDIT FAILED: outer Prop premises are {premises}, expected {expected}"
  let cl ← depClosure new
  -- the forbidden names are RESOLVED first: a name that does not exist would audit nothing
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SR3s AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
  let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{new}: old boundary / old child predicate in closure: {bad}"
  for must in [``grand_soundLA, ``grand_composedA, ``grand_traceXA, ``mid_composedA, ``mid_seqChildRunN2, ``grand_designCheck,
      ``grand_runFacts, ``grand_outsCheck, ``grand_kidsMasked, ``grand_closesA, ``mid_ifaceP, ``Tests.Compiler.SeqDeepMidKidFactsTest.mid_kidFactsA,
      ``Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA, ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
      ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main, ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
      ``Tools.ShippingParentRanA.machineRanA_main, ``Tools.ShippingMachineShipsDepth.composedG_of_NW,
      ``Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc] do
    unless cl.contains must do throwError "SR3s AUDIT FAILED: {must} not in the closure"
  -- the old composed theorem of grand supplies only PC-free subterms (its L, R, Hb, Hv): the theorem itself is not in the closure
  unless !cl.contains `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand.machine_composedNR2 do
    throwError "SR3s AUDIT FAILED: the old grand.machine_composedNR2 constant is in the closure"
  let (_, concl) ← forallTelescope ty fun _ c => pure ((), c)
  unless (concl.find? (·.isConstOf ``BndAg)).isSome do throwError "SR3s AUDIT FAILED: BndAg not in the conclusion"
  logInfo m!"SR3s AUDIT OK: {new}: standard axioms; outer Prop premises ASSERTED {premises}; soundL, composed, houtTy and the four checks are no longer premises; closure {cl.size} constants, none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC (each forbidden name resolved in the environment first); BndAg stays in the conclusion"

end Tests.Compiler.SeqDeepGrandEndpointTest
