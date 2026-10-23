import Tools.ShippingChildVertA
import Tools.ShippingChildPathA
import Tools.ShippingChildCacheA
import Tools.ShippingChildCoreC
import Tools.ShippingChildFrontA
import Tools.ShippingChildDepthA
import Tools.ShippingChildTeleCP
import Tools.ShippingChildProjFieldA
import Tools.ShippingChildFrontCP
import Tools.ShippingChildImplCorA
import Tools.ShippingChildLegacyImplA
import Tools.ShippingChildComposeA
import Tools.ShippingChildDepthC
import Tools.ShippingChildComposeC
import Tools.ShippingChildMainA
import Tools.ShippingChildLegacyTailA
import Tools.ShippingChildRunA
import Tools.ShippingChildRunAKids
import Tools.ShippingChildRunAMain
import Tools.ShippingChildLinkA
import Tools.ShippingMachineOutcomeA
import Tools.ShippingMachineOutcomeA3
import Tools.ShippingMachineOutcomeA4
import Tools.ShippingLetsCloseRoute
import Tools.ShippingLetsAliasInv
import Tools.ShippingLetsReaderInvMain
import Tools.ShippingLetsSigTy
import Tools.ShippingLetsExternSpec
import Tools.ShippingBundleIotaRange
import Tools.ShippingLetsReaderInvPure2
import Tools.ShippingCallWidthsChildRealA
import Tools.ShippingChildTeleLocalA
import Tools.ShippingChildTeleMainA
import Tools.ShippingCallWidthsChildRealAMain
import Tools.ShippingCallWidthsChildRealATl
import Tools.ShippingLeafInputWidthsA
import Tools.ShippingServedRealA
import Tools.ShippingServedRealATrace
import Tools.ShippingMachineDepthRunRA
import Tools.ShippingMachineComposeRA
import Tools.ShippingCallsCloseA
import Tools.ShippingCallsGateA
import Tools.ShippingChildPinC
import Tools.ShippingCallsGatePin
import Tools.ShippingCallsGatePinned
import Tools.ShippingCallsMemA
import Tests.Compiler.CallsMemAMemWideTest
import Tests.Compiler.CallerTwiceATest
import Tools.ShippingCallsMemPinned
import Tools.ShippingSeqChildIfaceA
import Tools.ShippingSeqChildIfaceDeepA
import Tools.ShippingSeqChildDeepConsumerA
import Tools.ShippingSeqChildDeepMaskedA
import Tools.ShippingSeqChildDeepFactsA
import Tools.ShippingSeqChildDeepKidCheckA
import Tools.ShippingSeqChildDeepKidFactsA
import Tools.ShippingSeqParentKidFactsA
import Tools.ShippingSeqChildDeepIfacePA
import Tools.ShippingSeqChildDeepRunA
import Tools.ShippingParentGateA
import Tools.ShippingRanABridge
import Tools.ShippingKidsSelfA
import Tools.ShippingParentRunFactsA
import Tools.ShippingMachineComposeRM
import Tools.ShippingEntryDefinesRun
import Tools.ShippingEntryReadsLinked
import Tools.ShippingLeafTermKeeps
import Tools.ShippingSharedLeafHit
import Tools.ShippingSharedLeafExt
import Tools.ShippingSharedLeafNL
import Tools.ShippingTopShareRun
import Tools.ShippingTopShareRet
import Tools.ShippingTopShareRan
import Tools.ShippingSeqParentAt
import Tools.ShippingTopShareNoParent
import Tools.ShippingQuadLeafGeneric
import Tools.ShippingQuadReturned
import Tools.ShippingQuadComposed
import Tools.ShippingQuadCalls
import Tools.ShippingQuadCallFacts
import Tools.ShippingQuadHPoint
import Tools.ShippingKaryRun
import Tools.ShippingKaryEntry
import Tools.ShippingKaryLeafGeneric
import Tools.ShippingKaryComposed
import Tools.ShippingKaryCalls
import Tools.ShippingKaryFacts
import Tools.ShippingKaryBridge
import Tools.ShippingKaryReturned
import Tools.ShippingMemLeafCache
import Tools.ShippingMemLeafRun
import Tools.ShippingNmGroup
import Tools.ShippingNmEntry
import Tools.ShippingSrm3Iface
import Tools.ShippingSrm3Callee
import Tools.ShippingSrm4Run
import Tools.ShippingSrm4Core1
import Tools.ShippingSrm4Core2
import Tools.ShippingSrm4Core3
import Tools.ShippingSrm4Core4
import Tools.ShippingSrm4Core5
import Tools.ShippingSrm4Core6
import Tools.ShippingSrm4Check
import Tools.ShippingSrm4Kid
import Tools.ShippingSrm4Callee
import Tools.ShippingSrm4Parent
import Tools.ShippingSrm4Mixed
import Tools.ShippingSrm5Height
import Tools.ShippingSrm5Ident
import Tools.ShippingSrm5Transfer
import Tools.ShippingSrm5TransferM
import Tools.ShippingSrm5Deep
import Tools.ShippingSrm7Rank
import Tools.ShippingSrm10Outs
import Tools.ShippingSrm11Bounds
import Tools.ShippingSrm12Corr

/-! # Audit: the vertical path does not use the old boundary (round par/vert)

BUILT by the integrator: vt3 exit 0 (audit passed: no RefLaws / RefLawsCore / toAOps / toA in the closures; axioms standard) (round par/vert, base 777630e9); revised round par/audit2 (opaque bodies read, boundary report, hidden-wrapper controls). Registered in `Tests.AllTests` (all9).

For each audited theorem of the vertical migration
(`Tools/ShippingChildVertA.lean`, `Tools/ShippingChildVCA.lean`,
`Tools/ShippingChildFresh.lean`) this file:

* prints its axioms (`#print axioms`) and THROWS unless they are standard;
* walks the TRANSITIVE closure of the constants its type and value mention
  (a worklist over `ConstantInfo.type` / `ConstantInfo.value? (allowOpaque := true)`
  with a visited set; inductive types also contribute their constructors' types)
  and THROWS if the closure contains `Tools.ShippingChildInv.RefLaws` (or any
  constant under that name, e.g. its fields), `Tools.ShippingChildBndCore.RefLawsCore`
  (or under it), `Tools.ShippingChildInvA.RefLawsCore.toAOps` or
  `Tools.ShippingChildInvA.RefLawsCore.toA`.

**What the walk reads, and its boundary.** `value? (allowOpaque := true)` reads
the bodies of definitions, theorems AND `opaque` constants (the default
`value?` skips `opaque` bodies; the first version of this file used the default,
so a body hidden behind `opaque` was not read — control (c) below). What it
CANNOT read, and REPORTS per theorem (`boundary`): axioms (here only the
standard ones, checked), `opaque` constants whose stored value is the default
inhabitant (e.g. `@[extern]` primitives such as `ST.Prim.Ref.get`: the stored
value is not the runtime behaviour), constants with `@[extern]`, and
`@[implemented_by]` targets (the compiled code is NOT part of the kernel term;
the walk follows the logical value of the attributed constant, not the
implementation; the implementation names are listed). Inductives, constructors,
recursors and quotients have no body to read. In this project the
opaque constants of the closures are `partial def`s (e.g. `machNorm`,
`stripMemoizeWrappers`: the kernel sees an opaque constant, not the recursive
code) and the `initialize` refs (`sparkleSynthDepth`, …); they are logged as
`PROJECT OPAQUE`. So "the closure contains no old
boundary" is a statement about the KERNEL terms; it says nothing about what the
extern / implemented_by code does at runtime (that is the runtime-fit item). The logged opaque / extern / implemented_by
counts are STRUCTURAL dependency counts, not a runtime-fit proof.

Positive controls (each THROWS if the walker misses it):
(a) the closure of `Tools.ShippingChildInvA.RefLawsCore.toAOps` contains
    `Tools.ShippingChildBndCore.RefLawsCore`;
(b) a theorem whose TYPE mentions only a local wrapper definition whose VALUE
    mentions `RefLawsCore` (`hiddenWrap`) is flagged;
(c) a theorem whose PROOF mentions only a local `opaque` constant whose stored
    value mentions `RefLawsCore` (`hiddenOpaque`) is flagged — and the default
    `value?` walk (opaque bodies skipped) does NOT flag it (logged: the gap the
    revision closes).

Writing-time guesses: `Expr.getUsedConstants` (Lean core) returns the
constants of an expression; `InductiveVal.ctors`; `Name.isPrefixOf`;
`Lean.isExtern`; `Lean.Compiler.implementedByAttr.getParam?`. -/

namespace Tests.Compiler.ChildVertAuditTest
open Lean Meta

/-- Standard axioms only, an error otherwise. -/
def stdAxioms (n : Name) : MetaM Unit := do
  for ax in ← Lean.collectAxioms n do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{n} uses a non-standard axiom: {ax}"

/-- The transitive closure of the constants `n` depends on (type, value —
opaque bodies included when `readOpaque := true` — constructors of inductives),
`n` included. -/
partial def depClosureWith (readOpaque : Bool) (n : Name) : MetaM NameSet := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => pure ()
    | some ci =>
      let mut used := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := readOpaque) then
        used := used ++ v.getUsedConstants
      if let .inductInfo iv := ci then
        used := used ++ iv.ctors.toArray
      for u in used do
        unless seen.contains u do
          todo := todo.push u
  return seen

def depClosure (n : Name) : MetaM NameSet := depClosureWith true n

/-- The constants of a closure whose behaviour the walk cannot read from a
kernel body: axioms, `opaque` constants, `@[extern]` constants, and
`@[implemented_by]`-attributed constants (with their implementation names). -/
def boundary (s : NameSet) : MetaM (List Name × List Name × List Name × List (Name × Name)) := do
  let env ← getEnv
  let mut axs : List Name := []
  let mut ops : List Name := []
  let mut exts : List Name := []
  let mut impls : List (Name × Name) := []
  for c in s.toList do
    match env.find? c with
    | some (.axiomInfo _) => axs := c :: axs
    | some (.opaqueInfo _) => ops := c :: ops
    | _ => pure ()
    if Lean.isExtern env c then exts := c :: exts
    if let some i := Lean.Compiler.implementedByAttr.getParam? env c then impls := (c, i) :: impls
  return (axs, ops, exts, impls)

/-- The old-boundary names: any constant equal to or under these. -/
def forbiddenRoots : List Name :=
  [`Tools.ShippingChildInv.RefLaws, `Tools.ShippingChildBndCore.RefLawsCore,
   `Tools.ShippingChildInvA.RefLawsCore.toAOps, `Tools.ShippingChildInvA.RefLawsCore.toA]

def hits (s : NameSet) : List Name :=
  s.toList.filter fun c => forbiddenRoots.any fun r => r.isPrefixOf c

/-- The audited theorems. -/
def audited : List Name :=
  [``Tools.ShippingChildTeleLocalA.localDecl_of_O, ``Tools.ShippingChildTeleLocalA.letDecl_of_O,
   ``Tools.ShippingChildTeleCP.keeps_forallTelescopeReducing,
   ``Tools.ShippingChildTeleCP.keeps_lambdaTelescope, ``Tools.ShippingChildTeleCP.keeps_withLocalDeclD,
   ``Tools.ShippingChildTeleCP.keeps_withLetDecl,
   ``Tools.ShippingChildTeleCP.keepsCP_forallTelescopeReducing,
   ``Tools.ShippingChildTeleCP.keepsCP_lambdaTelescope, ``Tools.ShippingChildTeleCP.keepsCP_withLocalDeclD,
   ``Tools.ShippingChildTeleCP.keepsCP_withLetDecl,
   ``Tools.ShippingChildProjFieldA.projFieldNameA,
   ``Tools.ShippingChildVertA.core_tripleA, ``Tools.ShippingChildVertA.certified_keepsA,
   ``Tools.ShippingChildVertA.finA,
   ``Tools.ShippingChildVCA.keepsA_mkExprCache_bind, ``Tools.ShippingChildVCA.keepsA_exprCacheGet,
   ``Tools.ShippingChildFresh.runsTo_mkRef_bind, ``Tools.ShippingChildFresh.runsTo_mkRefIO_bind,
   ``Tools.ShippingChildPathA.certRest_keepsA, ``Tools.ShippingChildPathA.emitLeavesA,
   ``Tools.ShippingChildPathA.bindCertifiedInputsA, ``Tools.ShippingChildPathA.finishSynthA,
   ``Tools.ShippingChildPathA.certified_keepsA_of_translate,
   ``Tools.ShippingChildPathA.fromConst_certified_keepsA,
   ``Tools.ShippingChildPathA.fromConst_certified_keepsJQ,
   ``Tools.ShippingChildPathA.fromConst_certified_hbody,
   ``Tools.ShippingChildCacheA.stableA_JQC, ``Tools.ShippingChildCacheA.jqc_cacheGet,
   ``Tools.ShippingChildCacheA.tripleC_clear, ``Tools.ShippingChildCacheA.tripleC_depthSet,
   ``Tools.ShippingChildCacheA.tripleC_depthModify, ``Tools.ShippingChildCacheA.tripleC_insert,
   ``Tools.ShippingChildCacheA.synthesizeChild_realA,
   ``Tools.ShippingChildCacheA.synthesizeChild_tripleC,
   ``Tools.ShippingChildCacheA.closeInstsM_realA,
   ``Tools.ShippingChildCoreC.finC, ``Tools.ShippingChildCoreC.core_tripleAC,
   ``Tools.ShippingChildCoreC.full_tripleAC, ``Tools.ShippingChildCoreC.hentryT_of_body,
   ``Tools.ShippingChildCoreC.hentry_of_body, ``Tools.ShippingChildCoreC.synthesizeChild_realA',
   ``Tools.ShippingChildCoreC.synthesizeChild_tripleC',
   ``Tools.ShippingChildCoreC.closeInstsM_realA',
   ``Tools.ShippingChildFrontA.mixed_keepsA, ``Tools.ShippingChildFrontA.machineCert_keepsA,
   ``Tools.ShippingChildFrontA.fromConst_mixed_keepsA,
   ``Tools.ShippingChildFrontA.fromConst_machine_keepsA,
   ``Tools.ShippingChildFrontA.fromConst_frontends_keepsA,
   ``Tools.ShippingChildFrontA.fromConst_hbody_frontends,
   ``Tools.ShippingChildFrontA.core_tripleA_frontends,
   ``Tools.ShippingChildTranslateA.translateStepWithA,
   ``Tools.ShippingChildTranslateA.translateA_of_fallback,
   ``Tools.ShippingChildFallbackA.translateFallbackA,
   ``Tools.ShippingChildFallbackA.translate_keepsA,
   ``Tools.ShippingChildFallbackA.translate_keepsJQ,
   ``Tools.ShippingChildTranslatePathA.certRest_keepsAP,
   ``Tools.ShippingChildTranslatePathA.fromConst_certified_hbody_of_handlers,
   ``Tools.ShippingChildDepthA.coreN_keepsA,
   ``Tools.ShippingChildDepthA.childKeepsA_all,
   ``Tools.ShippingChildDepthA.core_tripleA_of_bodies,
   ``Tools.ShippingChildFrontCP.mixed_keepsAP,
   ``Tools.ShippingChildFrontCP.machineCert_keepsAP,
   ``Tools.ShippingChildFrontCP.fromConst_mixed_keepsAP,
   ``Tools.ShippingChildFrontCP.fromConst_machine_keepsAP,
   ``Tools.ShippingChildFrontCP.childEntryA_of_childSynthA,
   ``Tools.ShippingChildFrontCP.childEntryA_JQ_of_childSynthA,
   ``Tools.ShippingChildFrontCP.childEntryA_JQC_of_childSynthA,
   ``Tools.ShippingChildFrontCP.fromConst_frontends_keepsCP,
   ``Tools.ShippingChildFrontCP.fromConst_frontends_of_handlers,
   ``Tools.ShippingChildFrontCP.bodyKeepsA_frontends,
   ``Tools.ShippingChildFrontCP.bodyStepA_of_handlers,
   ``Tools.ShippingChildLoopsCP.KeepsCP.fuelFixM,
   ``Tools.ShippingChildCanonKeyA.canonHardwareExprStepA,
   ``Tools.ShippingChildCanonKeyA.canonHardwareKeyA, ``Tools.ShippingChildCanonKeyA.canonKeyA,
   ``Tools.ShippingChildLegacyCachedA.translateExprToWireCachedA,
   ``Tools.ShippingChildLegacyCachedA.legacyCachedA_of_impl,
   ``Tools.ShippingChildImplCorA.translateFallbackA_of_impl,
   ``Tools.ShippingChildImplCorA.translate_keepsA_of_impl,
   ``Tools.ShippingChildImplCorA.translate_keepsJQ_of_impl,
   ``Tools.ShippingChildImplCorA.bodyStepA_certified',
   ``Tools.ShippingChildLegacyImplA.legacyImplA_of_handlers,
   ``Tools.ShippingChildLegacyImplA.legacyImplA_of_tele,
   ``Tools.ShippingChildLegacyHandlersA.translateExprToWireApp_keepsCP,
   ``Tools.ShippingChildLegacyHandlersA.handleDefinitionUnfold_keepsCP,
   ``Tools.ShippingChildLegacyHandlersA.tryInlineUnfold_tripleCP,
   ``Tools.ShippingChildComposeA.bodyKeepsA_of_tele,
   ``Tools.ShippingChildDepthC.childKeepsC_of_body,
   ``Tools.ShippingChildDepthC.childKeepsC_all,
   ``Tools.ShippingChildDepthC.childEntryA_of_childKeepsC,
   ``Tools.ShippingChildDepthC.core0_tripleAC,
   ``Tools.ShippingChildDepthC.full0_tripleAC,
   ``Tools.ShippingChildDepthC.core_tripleAC_of_bodies,
   ``Tools.ShippingChildDepthC.full_tripleAC_of_bodies,
   ``Tools.ShippingChildDepthC.synthesizeChild_realC,
   ``Tools.ShippingChildDepthC.closeInstsM_realC,
   ``Tools.ShippingChildDepthC.bodyStepC_certified,
   ``Tools.ShippingChildComposeC.bodyKeepsC_of_tele, ``Tools.ShippingChildComposeC.bodyStepC_of_tele,
   ``Tools.ShippingChildComposeC.childKeepsC_all_of_tele, ``Tools.ShippingChildComposeC.core_tripleAC_of_tele,
   ``Tools.ShippingChildComposeC.full_tripleAC_of_tele,
   ``Tools.ShippingChildMainA.bodyStepA_main, ``Tools.ShippingChildMainA.childKeepsA_main,
   ``Tools.ShippingChildMainA.core_tripleA_main,
   ``Tools.ShippingChildLegacyTailA.legacyTailA_generic,
   ``Tools.ShippingChildLegacyTailA.legacyTailA_of_step,
   ``Tools.ShippingChildRunA.core_reads_invA, ``Tools.ShippingChildRunA.synthesizeFromConst_machine_invA,
   ``Tools.ShippingChildRunA.machine_run_of_coreA,
   ``Tools.ShippingChildRunAKids.closeInstsGM_realC, ``Tools.ShippingChildRunAKids.synthesizeMachineCertified_runsA,
   ``Tools.ShippingChildRunAKids.machine_children_realA',
   ``Tools.ShippingChildLinkA.childLink_realA,
   ``Tools.ShippingChildLinkA.entryStrict_realA, ``Tools.ShippingChildLinkA.childLink_realFA,
   ``Tools.ShippingChildComposeC.translate_keepsC_of_tele,
   ``Tools.ShippingChildRunAMain.htr_of_tele,
   ``Tools.ShippingChildRunAMain.machine_children_realA_main,
   ``Tools.ShippingCallWidthsChildRealA.realChildA_of_childrenRealA,
   ``Tools.ShippingCallWidthsChildRealA.callWidthsStrict_realA,
   ``Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA,
   ``Tools.ShippingCallWidthsChildRealA.children_widths_realA,
   ``Tools.ShippingCallWidthsChildRealA.parent_children_widths_realA,
   ``Tools.ShippingCallWidthsChildRealA.parent_children_widths_realA_of_run,
   ``Tools.ShippingChildTeleMainA.RefLawsATele.ofTeleLam,
   ``Tools.ShippingChildTeleMainA.core_tripleA_main_tl,
   ``Tools.ShippingChildTeleMainA.core_tripleAC_of_tele_tl,
   ``Tools.ShippingChildTeleMainA.full_tripleAC_of_tele_tl,
   ``Tools.ShippingChildTeleMainA.htr_of_tele_tl,
   ``Tools.ShippingChildTeleMainA.machine_children_realA_main_tl,
   ``Tools.ShippingCallWidthsChildRealAMain.parent_children_widths_realA_main,
   ``Tools.ShippingCallWidthsChildRealATl.parent_children_widths_realA_main_tl,
   ``Tools.ShippingLeafInputWidthsA.leaf_core_factsA,
   ``Tools.ShippingLeafInputWidthsA.leaf_namesA,
   ``Tools.ShippingLeafInputWidthsA.leaf_input_widthsA,
   ``Tools.ShippingLeafInputWidthsA.leaf_sat_design_closedA,
   ``Tools.ShippingLeafInputWidthsA.leaf_sat_design_closed5A,
   ``Tools.ShippingServedRealA.machineRunJQC_of_closesA,
   ``Tools.ShippingServedRealA.synthesizeCombinationalCore_machine_soundRA_ranA,
   ``Tools.ShippingServedRealA.synthesizeCombinationalCore_machine_soundRA_A,
   ``Tools.ShippingServedRealA.realChildA_inv,
   ``Tools.ShippingServedRealA.synthesizeCombinationalCore_machine_soundRA_main,
   ``Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_main,
   ``Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_ranA,
   ``Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_A,
   ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real,
   ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main,
   ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
   ``Tools.ShippingMachineComposeRA.machine_linked_callsRA,
   ``Tools.ShippingMachineComposeRM.machine_traceL_of_data_extRM,
   ``Tools.ShippingMachineComposeRA.machineRunNA_of_NCA,
   ``Tools.ShippingMachineComposeRA.machineRunNCA_of_NA,
   ``Tools.ShippingMachineOutcomeA.synthesizeFromConst_machine_splitA,
   ``Tools.ShippingMachineOutcomeA.core_machine_outcomeA,
   ``Tools.ShippingCallsCloseA.closeInstsM_runC,
   ``Tools.ShippingCallsCloseA.closeInstsGM_runC,
   ``Tools.ShippingCallsCloseA.machineClosesAtA_of_pure,
   ``Tools.ShippingCallsCloseA.machineClosesAtA_of_tele,
   ``Tools.ShippingCallsGateA.callsPureA_of_gateKids,
   ``Tools.ShippingCallsGateA.machineClosesAtA_of_gateKids,
   ``Tools.ShippingChildPinC.synthesizeChild_pinned,
   ``Tools.ShippingChildPinC.childKeepsP_all_of_tele,
   ``Tools.ShippingCallsGatePin.callsPureP_of_gateKids,
   ``Tools.ShippingCallsGatePin.callsPureA_of_gateKids_pin,
   ``Tools.ShippingCallsGatePinned.closeInstsM_runP,
   ``Tools.ShippingCallsGatePinned.machineClosesAtA_of_pure_pin,
   ``Tools.ShippingCallsGatePinned.machineClosesAtA_of_gateKids',
   ``Tools.ShippingMachineOutcomeA.core_reads_linkA,
   ``Tools.ShippingMachineOutcomeA.synthesizeMachineCertified_noneSplitA,
   ``Tools.ShippingMachineOutcomeA.synthesizeFromConst_machine_split2A,
   ``Tools.ShippingMachineOutcomeA.core_machine_outcomeA',
   ``Tools.ShippingMachineOutcomeA3.RunsTo.try_finally',
   ``Tools.ShippingMachineOutcomeA3.core_reads_link3A,
   ``Tools.ShippingMachineOutcomeA3.core_machine_outcomeA'',
   ``Tools.ShippingMachineOutcomeA4.coreFinally_split,
   ``Tools.ShippingMachineOutcomeA4.core_reads_link4A,
   ``Tools.ShippingMachineOutcomeA4.core_machine_outcomeA''',
   ``Tools.ShippingLetsCloseRoute.letsClose_of_noLets,
   ``Tools.ShippingLetsCloseRoute.closeLets_some_of_machine_some,
   ``Tools.ShippingLetsCloseRoute.not_letsClose_of_refusal,
   ``Tools.ShippingLetsCloseRoute.letsClose_iff_no_refusal,
   ``Tools.ShippingLetsAliasInv.machBindLet_noAlias,
   ``Tools.ShippingLetsAliasInv.machBindLetNamed_noAlias,
   ``Tools.ShippingLetsAliasInv.machLetIndex_noAlias,
   ``Tools.ShippingLetsAliasInv.machBindLetAlias_noAlias,
   ``Tools.ShippingLetsAliasInv.machClose_bvar,
   ``Tools.ShippingLetsReaderInv.letOk_mono,
   ``Tools.ShippingLetsReaderInv.machBindLetNamed_range,
   ``Tools.ShippingLetsReaderInv.machBindLet_range,
   ``Tools.ShippingLetsReaderInv.machBindLetAlias_range,
   ``Tools.ShippingLetsReaderInv.alias_premise,
   ``Tools.ShippingLetsReaderInv.convBvar_ok,
   ``Tools.ShippingLetsReaderInv.instArg_sat,
   ``Tools.ShippingLetsReaderInv.instSArg_sat,
   ``Tools.ShippingLetsReaderInv.nestedProbe_sat,
   ``Tools.ShippingLetsReaderInv.loopProbe_sat,
   ``Tools.ShippingLetsReaderInv.loopLet_facts,
   ``Tools.ShippingLetsReaderInv.conv_sat,
   ``Tools.ShippingLetsReaderInv.nested_sat,
   ``Tools.ShippingLetsReaderInv.inst_sat,
   ``Tools.ShippingLetsReaderInv.instS_sat,
   ``Tools.ShippingLetsReaderInv.chain_sat,
   ``Tools.ShippingLetsReaderInv.loopBody_sat,
   ``Tools.ShippingLetsReaderInv.loopRoot_sat,
   ``Tools.ShippingLetsReaderInv.step_good,
   ``Tools.ShippingLetsReaderInv.readF_good,
   ``Tools.ShippingLetsReaderInv.letTail_ok,
   ``Tools.ShippingLetsReaderInv.loopRegs_ok,
   ``Tools.ShippingLetsReaderInv.loopView_ok,
   ``Tools.ShippingLetsReaderInv.runApp_ok,
   ``Tools.ShippingLetsReaderInv.instCall_ok,
   ``Tools.ShippingLetsReaderInv.instCallS_ok,
   ``Tools.ShippingLetsReaderInv.memCall_ok,
   ``Tools.ShippingLetsReaderInv.projIota_ok,
   ``Tools.ShippingLetsReaderInv.regView_ok,
   ``Tools.ShippingLetsReaderInv.pureFacts_of,
   ``Tools.ShippingLetsReaderInv.machConvF_post,
   ``Tools.ShippingLetsReaderInv.machNestedF_post,
   ``Tools.ShippingLetsReaderInv.machChainF_post,
   ``Tools.ShippingLetsReaderInv.machLoopBodyF_post,
   ``Tools.ShippingLetsReaderInv.machLoopRootF_post,
   ``Tools.ShippingLetsReaderInv.alias_premise_of_conv,
   ``Tools.ShippingLetsReaderInv.machConvF_init,
   ``Tools.ShippingLetsReaderInv.machChainF_init,
   ``Tools.ShippingLetsReaderInv.real_conv_post,
   ``Tools.ShippingLetsReaderInv.instSignatureS_type,
   ``Tools.ShippingLetsReaderInv.sigTyRange_structEnv,
   ``Tools.ShippingLetsReaderInv.letOk_declValue,
   ``Tools.ShippingLetsReaderInv.bundleIota_key1,
   ``Tools.ShippingLetsReaderInv.bundleIota_key2,
   ``Tools.ShippingLetsReaderInv.bundleIota_key3,
   ``Tools.ShippingLetsReaderInv.bundleIotaRange,
   ``Tools.ShippingLetsReaderInv.machConvF_post',
   ``Tools.ShippingLetsReaderInv.machNestedF_post',
   ``Tools.ShippingLetsReaderInv.machChainF_post',
   ``Tools.ShippingLetsReaderInv.machLoopBodyF_post',
   ``Tools.ShippingLetsReaderInv.machLoopRootF_post',
   ``Tools.ShippingLetsReaderInv.alias_premise_of_conv',
   ``Tools.ShippingLetsReaderInv.machConvF_init',
   ``Tools.ShippingLetsReaderInv.machChainF_init',
   ``Tools.ShippingLetsReaderInv.real_conv_post',
   ``Tools.ShippingLetsReaderInv.liftSpec_ok,
   ``Tools.ShippingLetsReaderInv.inst1Spec_ok,
   ``Tools.ShippingLetsReaderInv.liftRange_of_agrees,
   ``Tools.ShippingLetsReaderInv.inst1Range_of_agrees,
   ``Tools.ShippingLetsReaderInv.rootFloatS_ok,
   ``Tools.ShippingLetsReaderInv.rootFloatRange_of_agrees,
   ``Tools.ShippingLetsReaderInv.machConvF_post'',
   ``Tools.ShippingLetsReaderInv.machChainF_post'',
   ``Tools.ShippingLetsReaderInv.machConvF_init'',
   ``Tools.ShippingLetsReaderInv.machChainF_init'',
   ``Tools.ShippingLetsReaderInv.real_conv_post'',
   ``Tools.ShippingCallsMemA.callsPureA_of_memKids,
   ``Tools.ShippingCallsMemA.machineClosesAtA_of_memKids,
   ``Tools.ShippingCallsMemA.machineClosesAtA_memOnly_names,
   ``Tools.ShippingCallsMemA.machineClosesAtA_of_memOnlyData_names,
   ``Tests.Compiler.CallsMemAMemWideTest.memWide_closesA,
   ``Tests.Compiler.CallerTwiceATest.callerRep_closesA,
   ``Tests.Compiler.CallerTwiceATest.callerTwice_closesA,
   ``Tools.ShippingCallsMemPinned.closeInstsGM_runP,
   ``Tools.ShippingCallsMemPinned.machineClosesAtA_of_pure_pinG,
   ``Tools.ShippingCallsMemPinned.callsPureGP_of_memKids',
   ``Tools.ShippingSeqChildIfaceA.seqChild_ifaceA,
   ``Tools.ShippingSeqChildIfaceA.seqChild_of_realA,
   ``Tools.ShippingSeqChildIfaceDeepA.deepChild_ifaceA,
   ``Tools.ShippingSeqChildIfaceDeepA.deepChild_kidsSelfA,
   ``Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids,
   ``Tools.ShippingSeqChildDeepConsumerA.deepChild_ifaceA',
   ``Tools.ShippingSeqChildDeepConsumerA.deepChild_kidsMaskedA,
   ``Tools.ShippingSeqChildDeepMaskedA.core_calls_portsG_ranA,
   ``Tools.ShippingSeqChildDeepMaskedA.core_conn_refsG_ranA,
   ``Tools.ShippingSeqChildDeepMaskedA.deepChild_outsMaskedA,
   ``Tools.ShippingSeqChildDeepFactsA.deepChild_ranA,
   ``Tools.ShippingSeqChildDeepFactsA.deepChild_runFactsA,
   ``Tools.ShippingSeqChildDeepFactsA.deepChild_outsCheckA,
   ``Tools.ShippingSeqChildDeepFactsA.deepChild_designCheckA,
   ``Tools.ShippingSeqChildDeepKidCheckA.kids_designCheck_inA,
   ``Tools.ShippingSeqChildDeepKidCheckA.deepChild_kidCheckA,
   ``Tools.ShippingSeqChildDeepKidFactsA.core_outsIn_ranA,
   ``Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidCheckA_loc,
   ``Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidCheckA_of_all,
   ``Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA,
   ``Tools.ShippingSeqParentKidFactsA.kidsA_runFacts,
   ``Tools.ShippingSeqParentKidFactsA.kidsA_outsCheck,
   ``Tools.ShippingSeqParentKidFactsA.kidsA_maskedN,
   ``Tools.ShippingSeqParentKidFactsA.kidsA_designCheck,
   ``Tools.ShippingSeqChildDeepIfacePA.core_inPorts_ranA,
   ``Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP,
   ``Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA,
   ``Tools.ShippingParentRanA.machineRanA_main,
   ``Tools.ShippingParentTailsA.core_kids_facts_ranA,
   ``Tools.ShippingParentTailsA.core_linkedWF_ranA,
   ``Tools.ShippingParentTailsA.core_instOuts_not_assigned_ranA,
   ``Tools.ShippingParentTailsA.core_closed_typedIn_ranA,
   ``Tools.ShippingParentDesignA.core_hierGate_anyA,
   ``Tools.ShippingParentDesignA.core_kidsPass_anyA,
   ``Tools.ShippingParentDesignA.core_closeInstsA,
   ``Tools.ShippingParentDesignA.core_runFactsHA,
   ``Tools.ShippingParentDesignA.core_designCheckHA,
   ``Tools.ShippingParentRunFactsA.leaf_run_outsAssignedA, ``Tools.ShippingParentRunFactsA.leaf_real_outsAssignedA,
   ``Tools.ShippingParentRunFactsA.leaf_real_kidAA, ``Tools.ShippingParentRunFactsA.leaf_real_kidRA,
   ``Tools.ShippingParentRunFactsA.hkidW_of_dataA, ``Tools.ShippingParentRunFactsA.core_raw_facts_ranA,
   ``Tools.ShippingParentRunFactsA.core_outsExtracted_ranA, ``Tools.ShippingParentRunFactsA.core_callPorts_ranA,
   ``Tools.ShippingParentRunFactsA.core_instOutWidthsOk_ranA, ``Tools.ShippingParentRunFactsA.core_runFacts_ranA,
   ``Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA,
   ``Tools.ShippingParentPortsA.core_calls_ports₁A,
   ``Tools.ShippingParentPortsA.core_callConns₁A,
   ``Tools.ShippingParentPortsA.core_portsMatch_raw₁A,
   ``Tools.ShippingParentPortsA.core_hierTyped₁A,
   ``Tools.ShippingParentGateA.gate_real_portsA,
   ``Tools.ShippingParentGateA.gate_real_kidKA,
   ``Tools.ShippingRanABridge.machineRanA_of_runJQC,
   ``Tools.ShippingKidsSelfA.core_callConns_ranA,
   ``Tools.ShippingKidsSelfA.core_kids_self_ranA,
   ``Tools.ShippingKidsSelfA.core_kidsPass_deep_ranA,
   ``Tools.ShippingKidsSelfA.core_kidsMaskedN_top_ranA,
   ``Tools.ShippingKidsSelfA.core_kids_selfA,
   ``Tools.ShippingKidsSelfA.core_kidsPass_deepA,
   ``Tools.ShippingKidsSelfA.core_kidsMaskedN_topA,
   ``Tools.ShippingEntryDefinesRun.gate_core_factsL, ``Tools.ShippingEntryDefinesRun.gate_child_fullL,
   ``Tools.ShippingEntryDefinesRun.gate_child_combL, ``Tools.ShippingEntryDefinesRun.gate_child_fullFactsL,
   ``Tools.ShippingEntryDefinesRun.childFull_of_realAL, ``Tools.ShippingEntryDefinesRun.childFn_of_gateRunL,
   ``Tools.ShippingEntryDefinesRun.EntryDefinesRun.of_envRun,
   ``Tools.ShippingEntryDefinesRun.EntryDefinesRun.at_reads,
   ``Tools.ShippingEntryReadsLinked.core_split, ``Tools.ShippingEntryReadsLinked.core_chain,
   ``Tools.ShippingEntryReadsLinked.EntryDefinesRunG.at_core, ``Tools.ShippingEntryReadsLinked.EntryDefinesRunG.of_entry,
   ``Tools.ShippingEntryReadsLinked.getEnv_value, ``Tools.ShippingEntryReadsLinked.getConstInfo_value,
   ``Tools.ShippingEntryReadsLinked.ci_in_envR, ``Tools.ShippingEntryReadsLinked.gate_child_fullFactsG,
   ``Tools.ShippingEntryReadsLinked.childFull_of_realAG,
   ``Tools.ShippingLeafBodyCi.leaf_body_triple, ``Tools.ShippingLeafBodyCi.core_tripleKL,
   ``Tools.ShippingLeafBodyCi.core_tripleK0L, ``Tools.ShippingLeafBodyCi.hkeep_nestedL,
   ``Tools.ShippingLeafBodyCi.hkeep_zeroL, ``Tools.ShippingLeafBodyCi.synthesizeChild_leafMiss_nestedL,
   ``Tools.ShippingLeafBodyCi.synthesizeChild_leafMiss_zeroL,
   ``Tools.ShippingLeafTermKeeps.term_fuel_keeps, ``Tools.ShippingLeafTermKeeps.leafTranslatorKeeps_of_quote,
   ``Tools.ShippingLeafTermKeeps.leafTranslatorKeeps_of_machineData,
   ``Tools.ShippingLeafTermKeeps.synthesizeChild_leafMiss_nested_final,
   ``Tools.ShippingLeafTermKeeps.synthesizeChild_leafMiss_zero_final,
   ``Tools.ShippingSharedLeafHit.synthesizeChild_hit,
   ``Tools.ShippingSharedLeafHit.synthesizeChild_leafMiss_nested_ins,
   ``Tools.ShippingSharedLeafHit.sharedLeaf_nested,
   ``Tools.ShippingSharedLeafHit.sharedLeaf_nested_ext,
   ``Tools.ShippingSharedLeafExt.cacheExtends_of_synthesizeChild,
   ``Tools.ShippingSharedLeafExt.cacheExtends_of_two_runs,
   ``Tools.ShippingSharedLeafExt.sharedLeaf_nested_ext_run,
   ``Tools.ShippingSharedLeafExt.mem_designWith,
   ``Tools.ShippingSharedLeafExt.cacheClosed_insert_kids,
   ``Tools.ShippingSharedLeafNL.leafKid_step, ``Tools.ShippingSharedLeafNL.closeLoop_leaf,
   ``Tools.ShippingSharedLeafNL.closeInstsGM_leafRun, ``Tools.ShippingSharedLeafNL.machineSynth_leafKids,
   ``Tools.ShippingSharedLeafNL.core_run_tracked, ``Tools.ShippingSharedLeafNL.full_run_tracked,
   ``Tools.ShippingSharedLeafNL.designWith_hasName,
   ``Tools.ShippingSharedLeafNL.synthesizeChild_nonleaf_miss, ``Tools.ShippingSharedLeafNL.topshare_pair,
   ``Tools.ShippingSharedLeafNL.topshare_closing,
   ``Tools.ShippingTopShareRun.core_run_tracked0', ``Tools.ShippingTopShareRun.core_run_tracked0,
   ``Tools.ShippingTopShareRun.machineSynth_closing_split, ``Tools.ShippingTopShareRun.topshare_entry_run,
   ``Tools.ShippingTopShareRun.topshare_quad, ``Tools.ShippingTopShareRun.topshare_closing4,
   ``Tools.ShippingTopShareRun.topshare_entry_run4, ``Tools.ShippingTopShareRun.machineSynth_ne_none4,
   ``Tools.ShippingTopShareRun.topshare_entry_run4', ``Tools.ShippingTopShareRet.topshare_entry_run4_ret,
   ``Tools.ShippingTopShareRan.machineRanA_start0, ``Tools.ShippingSeqParentAt.machine_design_noShips_noBd_dc_at,
   ``Tools.ShippingSeqParentAt.moduleByName_post_other,
   ``Tools.ShippingTopShareNoParent.closeInstsG_name_design, ``Tools.ShippingTopShareNoParent.noParent_of_cache,
   ``Tools.ShippingTopShareNoParent.topshare_quad_keys, ``Tools.ShippingTopShareNoParent.topshare_closing4_keys,
   ``Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np, ``Tools.ShippingTopShareNoParent.returned_design_eq,
   ``Tools.ShippingQuadLeafGeneric.origin_child_none, ``Tools.ShippingQuadLeafGeneric.leafOK_of_data,
   ``Tools.ShippingQuadLeafGeneric.leafCallee_closesA, ``Tools.ShippingQuadLeafGeneric.leafCallee_hsep,
   ``Tools.ShippingQuadLeafGeneric.leafCallee_hgk, ``Tools.ShippingQuadLeafGeneric.leafCallee_ifaceP,
   ``Tools.ShippingQuadLeafGeneric.leafCallee_calleeOK, ``Tools.ShippingQuadLeafGeneric.quad_shape,
   ``Tools.ShippingQuadLeafGeneric.quad_closes0, ``Tools.ShippingQuadLeafGeneric.quad_machineRun,
   ``Tools.ShippingQuadLeafGeneric.quad_entry_run_ret_np,
   ``Tools.ShippingQuadReturned.quad_returned, ``Tools.ShippingQuadReturned.quad_wired,
   ``Tools.ShippingQuadComposed.genTrace, ``Tools.ShippingQuadComposed.leaf_kidFactsA, ``Tools.ShippingQuadComposed.leafCallee_kidFactsA, ``Tools.ShippingQuadComposed.leafCallee_traceXA, ``Tools.ShippingQuadComposed.leafCallee_composedA, ``Tools.ShippingQuadComposed.leafCallee_seqChildRunN2, ``Tools.ShippingQuadComposed.leafCallee_runNCA, ``Tools.ShippingQuadComposed.quad_ranA, ``Tools.ShippingQuadComposed.quad_hkid, ``Tools.ShippingQuadComposed.quad_runFacts, ``Tools.ShippingQuadComposed.quad_outsCheck, ``Tools.ShippingQuadComposed.quad_kidsMasked, ``Tools.ShippingQuadComposed.quad_designCheck, ``Tools.ShippingQuadComposed.quad_traceXA, ``Tools.ShippingQuadComposed.quad_soundLA, ``Tools.ShippingQuadComposed.quad_composed,
   ``Tools.ShippingQuadCalls.call_inRange, ``Tools.ShippingQuadCalls.quadGroupFacts_of_RF, ``Tools.ShippingQuadCalls.quad_inRange, ``Tools.ShippingQuadCalls.leafCallee_hcalls,
   ``Tools.ShippingQuadCalls.quad_composed_split,
   ``Tools.ShippingQuadCallFacts.callFactF_of_fam, ``Tools.ShippingQuadCallFacts.quadSrcF_eq, ``Tools.ShippingQuadCallFacts.leafSrcC_eq,
   ``Tools.ShippingQuadCallFacts.extendBits_of_ne, ``Tools.ShippingQuadCallFacts.extendBools_of_ne, ``Tools.ShippingQuadHPoint.callFactF_of_hPointAt,
   -- (unit SR21, ledger L8ba) the K-ary generalisation: a LIST of K callees that share one leaf
   ``Tools.ShippingKaryRun.dup_getElem?, ``Tools.ShippingKaryRun.dup_length', ``Tools.ShippingKaryRun.kary_group, ``Tools.ShippingKaryRun.kary_loop,
   ``Tools.ShippingKaryRun.kary_closing, ``Tools.ShippingKaryRun.kary_insts_names, ``Tools.ShippingKaryRun.kary_insts_length,
   ``Tools.ShippingKaryEntry.kary_idx_of_name, ``Tools.ShippingKaryEntry.kary_machineSynth_ne_none, ``Tools.ShippingKaryEntry.kary_entry_run_ret_np,
   ``Tools.ShippingKaryLeafGeneric.kary_calleeOK, ``Tools.ShippingKaryLeafGeneric.kary_nc, ``Tools.ShippingKaryLeafGeneric.kary_call_callee,
   ``Tools.ShippingKaryLeafGeneric.kary_closes0, ``Tools.ShippingKaryLeafGeneric.kary_machineRun, ``Tools.ShippingKaryLeafGeneric.kary_entry_run,
   ``Tools.ShippingKaryComposed.kFind_of_mem, ``Tools.ShippingKaryComposed.kandk_forall, ``Tools.ShippingKaryComposed.forall_kandk,
   ``Tools.ShippingKaryComposed.kary_callee_at, ``Tools.ShippingKaryComposed.kary_name_mem, ``Tools.ShippingKaryComposed.kary_ranA,
   ``Tools.ShippingKaryComposed.kary_hkid, ``Tools.ShippingKaryComposed.kary_runFacts, ``Tools.ShippingKaryComposed.kary_outsCheck,
   ``Tools.ShippingKaryComposed.kary_kidsMasked, ``Tools.ShippingKaryComposed.kary_designCheck, ``Tools.ShippingKaryComposed.kary_traceXA,
   ``Tools.ShippingKaryComposed.kary_soundLA, ``Tools.ShippingKaryComposed.kary_inRange,
   ``Tools.ShippingKaryCalls.kary_composed_split, ``Tools.ShippingKaryFacts.kSrcF_eq,
   ``Tools.ShippingKaryBridge.KaryParentData.ofQuad, ``Tools.ShippingKaryBridge.KaryAll.ofQuad, ``Tools.ShippingKaryBridge.KaryBnd.ofQuad,
   ``Tools.ShippingKaryReturned.kary_returned, ``Tools.ShippingKaryReturned.kary_wired,
   -- SRM1: shared leaf / callee with a memory child (cache clauses CacheClosedNM + MemDet, memory-aware real runs)
   ``Tools.ShippingMemLeafCache.cacheCoh_of_nm, ``Tools.ShippingMemLeafCache.cacheClosedNM_insert_kids, ``Tools.ShippingMemLeafCache.memDet_insert_kids,
   ``Tools.ShippingMemLeafCache.cacheClosedNM_insert_leaf, ``Tools.ShippingMemLeafCache.memDet_insert_leaf,
   ``Tools.ShippingMemLeafRun.closeLoop_gen, ``Tools.ShippingMemLeafRun.closeInstsGM_gen, ``Tools.ShippingMemLeafRun.machineSynth_gen,
   ``Tools.ShippingMemLeafRun.synthesizeChild_miss_nm, ``Tools.ShippingMemLeafRun.stepNM_of_data, ``Tools.ShippingMemLeafRun.memTags_of_data,
   ``Tools.ShippingMemLeafRun.leafKid_step_nm, ``Tools.ShippingMemLeafRun.hcalls_of_names, ``Tools.ShippingMemLeafRun.memLeaf_stepNM,
   ``Tools.ShippingMemLeafRun.calleeOverLeaf_stepNM, ``Tools.ShippingMemLeafRun.closing_nm,
   -- SRM2: memory-aware miss-then-hit tracking and the parent's entry / machineRun / closes0
   ``Tools.ShippingNmGroup.memMod_eq_kid, ``Tools.ShippingNmGroup.nm_group, ``Tools.ShippingNmGroup.nm_loop, ``Tools.ShippingNmGroup.nm_insts_names,
   ``Tools.ShippingNmGroup.nm_insts_length, ``Tools.ShippingNmGroup.nm_closing,
   ``Tools.ShippingNmEntry.nm_idx_of_name, ``Tools.ShippingNmEntry.noParent_nm, ``Tools.ShippingNmEntry.nm_idx_lt, ``Tools.ShippingNmEntry.nm_call_callee,
   ``Tools.ShippingNmEntry.nm_machineSynth_ne_none, ``Tools.ShippingNmEntry.nm_entry_run_ret_np, ``Tools.ShippingNmEntry.nm_closes0,
   ``Tools.ShippingNmEntry.nm_machineRun, ``Tools.ShippingNmEntry.nm_entry_run,
   -- SRM3: the A-form memory-aware interface of a callee with a memory child (no `hnomem`) and its `MachineClosesAtA`
   ``Tools.ShippingSrm3Iface.origin_mem_of_child, ``Tools.ShippingSrm3Iface.core_kids_facts_ranAM, ``Tools.ShippingSrm3Iface.core_outsIn_ranAM,
   ``Tools.ShippingSrm3Iface.core_calls_portsG_ranAM, ``Tools.ShippingSrm3Iface.core_inPorts_ranAM, ``Tools.ShippingSrm3Iface.deepChild_ifaceP_M,
   ``Tools.ShippingSrm3Callee.memT_of, ``Tools.ShippingSrm3Callee.memCallee_closesA, ``Tools.ShippingSrm3Callee.adm_of_realChildA,
   ``Tools.ShippingSrm3Callee.gk_of_iface, ``Tools.ShippingSrm3Callee.sep_of_iface, ``Tools.ShippingSrm3Callee.memCallee_ifaceP,
   ``Tools.ShippingSrm3Callee.leafKid_ifaceP,
   -- SRM4: run theorem of a memory-bearing register machine, the hnomem-free A-form copies, KidFactsNC, the obstruction, callee over a memory leaf, parent consumers
   ``Tools.ShippingSrm4Run.MemCalls.child_ne_none, ``Tools.ShippingSrm4Run.memCallee_composedNW, ``Tools.ShippingSrm4Run.memCallee_seqChildRunN,
   ``Tools.ShippingSrm4Core1.kidTA_ofO, ``Tools.ShippingSrm4Core1.core_linkedWF_ranAM, ``Tools.ShippingSrm4Core1.core_instOuts_not_assigned_ranAM,
   ``Tools.ShippingSrm4Core1.core_closed_typedIn_ranAM,
   ``Tools.ShippingSrm4Core2.core_hierGate_anyAM, ``Tools.ShippingSrm4Core2.core_kids_self_ranAM, ``Tools.ShippingSrm4Core2.core_raw_facts_ranAM,
   ``Tools.ShippingSrm4Core2.core_outsExtracted_ranAM, ``Tools.ShippingSrm4Core2.core_callPorts_ranAM, ``Tools.ShippingSrm4Core2.core_instOutWidthsOk_ranAM,
   ``Tools.ShippingSrm4Core2.core_runFacts_ranAM,
   ``Tools.ShippingSrm4Core3.core_callConns_ranAM, ``Tools.ShippingSrm4Core3.core_conn_refsG_ranAM,
   ``Tools.ShippingSrm4Core4.core_callConns_ranAM, ``Tools.ShippingSrm4Core4.core_portsMatch_raw_ranAM, ``Tools.ShippingSrm4Core4.core_clk_ranAM,
   ``Tools.ShippingSrm4Core5.deepChild_ifaceA'M, ``Tools.ShippingSrm4Core5.deepChild_ranAM, ``Tools.ShippingSrm4Core5.deepChild_outsMaskedAM,
   ``Tools.ShippingSrm4Core6.KidTA.real', ``Tools.ShippingSrm4Core6.KidTA.mem', ``Tools.ShippingSrm4Core6.KidFactsNC.toT, ``Tools.ShippingSrm4Core6.memKidTNC_facts,
   ``Tools.ShippingSrm4Core6.hkidW_of_dataAM, ``Tools.ShippingSrm4Core6.deepChild_kidFactsNC,
   ``Tools.ShippingSrm4Check.textCheckI_memModule, ``Tools.ShippingSrm4Check.designCheck_memModule, ``Tools.ShippingSrm4Check.kidCheck_memModule_succ,
   ``Tools.ShippingSrm4Check.kidFactsA_check_false,
   ``Tools.ShippingSrm4Kid.memCallee_hsep, ``Tools.ShippingSrm4Kid.memCallee_kidFactsNC, ``Tools.ShippingSrm4Kid.memModule_inj, ``Tools.ShippingSrm4Kid.KidFactsA.toNC,
   ``Tools.ShippingSrm4Callee.memLeafCallee_hcalls, ``Tools.ShippingSrm4Callee.memLeafCallee_composedNW, ``Tools.ShippingSrm4Callee.memLeafCallee_seqChildRunN2,
   ``Tools.ShippingSrm4Parent.kidsNC_runFacts, ``Tools.ShippingSrm4Parent.kidsNC_outsCheck, ``Tools.ShippingSrm4Parent.kidsNC_maskedN,
   ``Tools.ShippingSrm4Parent.kidsNC_designCheck_of_kidsPass,
   ``Tools.ShippingSrm4Mixed.call_inRange_at, ``Tools.ShippingSrm4Mixed.ordCallee_hcalls, ``Tools.ShippingSrm4Mixed.callee_composedNW,
   ``Tools.ShippingSrm4Mixed.callee_seqChildRunN2,
   ``Tools.ShippingSrm5Height.hcheck_memKids, ``Tools.ShippingSrm5Height.hcheck_memModule, ``Tools.ShippingSrm5Height.hcheck_ord, ``Tools.ShippingSrm5Height.hcheck_edge,
   ``Tools.ShippingSrm5Height.hcheck_unresolved, ``Tools.ShippingSrm5Height.hcheck_norank, ``Tools.ShippingSrm5Height.hcheck_notBelow, ``Tools.ShippingSrm5Height.hcheck_selfInst,
   ``Tools.ShippingSrm5Height.hcheck_misnamed, ``Tools.ShippingSrm5Height.hcheck_eq_designCheck,
   ``Tools.ShippingSrm5Ident.inst_target_ranA, ``Tools.ShippingSrm5Ident.inst_target_ord_ranA,
   ``Tools.ShippingSrm5Transfer.kids_textCheck_inA, ``Tools.ShippingSrm5Transfer.kidsH_body_ranA, ``Tools.ShippingSrm5Transfer.kids_hcheck_inA,
   ``Tools.ShippingSrm5Transfer.kidsH_pass_ranA, ``Tools.ShippingSrm5Transfer.textCheckI_shipped, ``Tools.ShippingSrm5Transfer.kidsNC_hcheck,
   ``Tools.ShippingSrm5TransferM.kids_textCheck_inAM, ``Tools.ShippingSrm5TransferM.kidsH_body_ranAM, ``Tools.ShippingSrm5TransferM.kids_hcheck_inAM,
   ``Tools.ShippingSrm5Deep.deepChild_kidHeightAM, ``Tools.ShippingSrm5Deep.memCallee_kidHeight,
   ``Tools.ShippingSrm7Rank.kidsMax_le, ``Tools.ShippingSrm7Rank.kidsMax_mono, ``Tools.ShippingSrm7Rank.kidsMax_lt, ``Tools.ShippingSrm7Rank.declRank_mono,
   ``Tools.ShippingSrm7Rank.declRank_le, ``Tools.ShippingSrm7Rank.rkOf_mem, ``Tools.ShippingSrm7Rank.rkOf_decl, ``Tools.ShippingSrm7Rank.rkOf_edge,
   ``Tools.ShippingSrm7Rank.rank_pos, ``Tools.ShippingSrm7Rank.declRank_self, ``Tools.ShippingSrm7Rank.rkChecked_dup, ``Tools.ShippingSrm7Rank.rkChecked_wf,
   ``Tools.ShippingSrm7Rank.inClass_rank,
   ``Tools.ShippingSrm10Outs.outsLeaf_of_outsAssigned, ``Tools.ShippingSrm10Outs.houtsMod_rank0, ``Tools.ShippingSrm10Outs.houtsMod_succ_iff, ``Tools.ShippingSrm10Outs.houtsMod_pos, ``Tools.ShippingSrm10Outs.houtsMod_outs, ``Tools.ShippingSrm10Outs.houtsCheck_at, ``Tools.ShippingSrm10Outs.kidsPass_of_resolved, ``Tools.ShippingSrm10Outs.outsCheck_succ_at, ``Tools.ShippingSrm10Outs.outsCheck_of_houtsCheck_uni, ``Tools.ShippingSrm10Outs.houtsMod_of_outsCheck_hcheck, ``Tools.ShippingSrm10Outs.houtsCheck_of_outsCheck_hcheck, ``Tools.ShippingSrm10Outs.houtsMod_norank, ``Tools.ShippingSrm10Outs.houtsCheck_unresolved, ``Tools.ShippingSrm10Outs.houtsCheck_notBelow, ``Tools.ShippingSrm10Outs.houtsMod_rank0_refused,
   ``Tools.ShippingSrm11Bounds.leafStepTG_bound, ``Tools.ShippingSrm11Bounds.moduleStepBoundH, ``Tools.ShippingSrm11Bounds.KSn_stepBoundH, ``Tools.ShippingSrm11Bounds.runModuleTG_envBoundH,
   ``Tools.ShippingSrm11Bounds.svBoundsH_of_checks, ``Tools.ShippingSrm11Bounds.bodyInstOuts_instFree, ``Tools.ShippingSrm11Bounds.leafBounds_of_parentBounds, ``Tools.ShippingSrm11Bounds.svBoundsH_of_svBounds,
   ``Tools.ShippingSrm12Corr.decode_ofMem, ``Tools.ShippingSrm12Corr.decode_ofDecl, ``Tools.ShippingSrm12Corr.kidModName_mem_iff, ``Tools.ShippingSrm12Corr.decode_kidModName,
   ``Tools.ShippingSrm12Corr.kidTA_name, ``Tools.ShippingSrm12Corr.instTagged_mem_idx, ``Tools.ShippingSrm12Corr.instTagged_exists_idx, ``Tools.ShippingSrm12Corr.memModule_modCorr,
   ``Tools.ShippingSrm12Corr.memModule_design_modules, ``Tools.ShippingSrm12Corr.ran_instFwd, ``Tools.ShippingSrm12Corr.ran_instBwd, ``Tools.ShippingSrm12Corr.modCorr_of_run,
   ``Tools.ShippingSrm12Corr.ran_designCorr, ``Tools.ShippingSrm12Corr.memCallee_childCorr, ``Tools.ShippingSrm12Corr.childCorr_noInst, ``Tools.ShippingSrm12Corr.callees_mem_names,
   ``Tools.ShippingSrm12Corr.inst_rank]

end Tests.Compiler.ChildVertAuditTest

open Tests.Compiler.ChildVertAuditTest

#print axioms Tools.ShippingChildVertA.core_tripleA
#print axioms Tools.ShippingChildVertA.certified_keepsA

/-! ## Controls (b) and (c): the old boundary hidden behind a wrapper -/

namespace Tests.Compiler.ChildVertAuditTest.Hidden

/-- A wrapper whose VALUE (not its type) mentions the old bundle. -/
def hiddenWrap : Prop :=
  ∀ (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State),
    Nonempty (Tools.ShippingChildBndCore.RefLawsCore mref cref)

theorem usesWrap : hiddenWrap → True := fun _ => trivial

/-- An `opaque` constant whose stored value mentions the old bundle. -/
opaque hiddenOpaque : Prop :=
  ∀ (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State),
    Nonempty (Tools.ShippingChildBndCore.RefLawsCore mref cref)

theorem usesOpaque : True := (fun (_ : hiddenOpaque → True) => trivial) (fun _ => trivial)

end Tests.Compiler.ChildVertAuditTest.Hidden

open Lean Elab Command in
run_cmd liftTermElabM do
  -- (a) the walker sees the old bundle where it IS used
  let ctl ← depClosure ``Tools.ShippingChildInvA.RefLawsCore.toAOps
  unless ctl.contains ``Tools.ShippingChildBndCore.RefLawsCore do
    throwError "VERT AUDIT FAILED: walker broken (toAOps closure lacks RefLawsCore)"
  -- (b) through a wrapper's value
  let cb ← depClosure ``Tests.Compiler.ChildVertAuditTest.Hidden.usesWrap
  if (hits cb).isEmpty then
    throwError "VERT AUDIT FAILED: control (b) not flagged (wrapper value not followed)"
  -- (c) through an opaque body
  let cc ← depClosure ``Tests.Compiler.ChildVertAuditTest.Hidden.usesOpaque
  if (hits cc).isEmpty then
    throwError "VERT AUDIT FAILED: control (c) not flagged (opaque body not read)"
  let ccOld ← depClosureWith false ``Tests.Compiler.ChildVertAuditTest.Hidden.usesOpaque
  logInfo m!"VERT AUDIT CONTROLS: (a) ok; (b) flagged {hits cb}; (c) flagged {hits cc}; (c) with opaque bodies skipped (the first version's walk) flags {hits ccOld}"
  for n in audited do
    stdAxioms n
    let s ← depClosure n
    let hs := hits s
    unless hs.isEmpty do
      throwError "VERT AUDIT FAILED: {n} depends on the old boundary: {hs}"
    let (axs, ops, exts, impls) ← boundary s
    let proj := ops.filter fun c => (`Sparkle).isPrefixOf c || (`Tools).isPrefixOf c
    logInfo m!"{n}: PROJECT OPAQUE {proj.length} (`partial def`s and `initialize` refs: kernel body not the code): {proj}"
    logInfo m!"{n}: closure {s.size} constants (opaque bodies read), no RefLaws / RefLawsCore / toAOps / toA. BOUNDARY (not readable as kernel behaviour): axioms {axs}; opaque {ops.length}: {ops}; extern {exts.length}: {exts}; implemented_by {impls.length}: {impls}"
