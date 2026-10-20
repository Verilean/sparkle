import Tests.Compiler.MixDeepOutermostRanTest
import Tools.ShippingOutermostCommand
import Tools.ShippingOutermostCoverage

/-! # `mixDeep.machine_design_noPortsNR2_outermost`: the check-free depth-2 endpoint of `mixDeep` at OUTERMOST starts (round par/g-1)

WRITTEN, NOT BUILT. TARGET-ONLY; not in `Tests.AllTests`. ASSERTING: every
audit below is an error of the file when it fails.

## What this is, and what it is NOT

`mixDeep` (`Tests/Compiler/ShippingChildBoundaryTest.lean`: callees `mid2`,
`midH`, `cnt`; `midH` is also a callee of `mid2`) is the one declaration the
census leaves OPEN: its built endpoint `mixDeep.machine_design_noPortsNR2`
asks `MachineClosesAt mixDeep` — the machine synthesis does not fall back
from ANY invariant world of positive depth — and that is not derived for
callees sharing a descendant.

This file adds a SECOND endpoint, at outermost starts:

    mixDeep.machine_design_noPortsNR2_outermost :
      ∀ {mctx mref cctx cref w w' b design}
        (hr  : RunsTo (synthesizeCombinational mixDeep) mctx mref cctx cref w (b, design) w')
        (the reflections of mixDeep, mid2, midH, rcH, cnt at the run's contexts)
        (h0  : Start0 mref cref w),
        ∃ raw D, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
          ∃ ids, … DesignSV (childMap D.modules) 2 (checkedOptimize b) …

with the SAME conclusion after the boundary as the built endpoint (asserted
below by `isDefEq` on the two statements), no `MachineClosesAt`, no checker
constant, no antecedent under the existentials.

**It does not close `mixDeep`.** The built endpoint, its premise
`MachineClosesAt mixDeep` and the census are unchanged (asserted below), and
`mixDeep` stays OPEN there: at NESTED starts (a start world of positive
depth with an invariant cache, which `ChildBnd` also allows) nothing is
proved here. The new premise `Start0 mref cref w` — for one law witness, the
synthesis depth reads 0 at the start world — is NOT ALLOWED by
`Tools.ShippingFinalGoalCommand.allowed` and is NOT added to it: this
endpoint is counted in the separate table of `#outermost_coverage`, never in
`#design_coverage`'s COVERED total. That a public command's run starts at
depth 0 is argued by READING in `docs/parallel/G-mixdeep-outermost.md` §5; it
is a runtime premise of the same kind as `ChildBnd`, not a theorem.

## How it is built (nothing about the compiler is proved here)

The head `Tools.ShippingNoPorts.machine_design_noPorts` at `C := True` and
the boundary `Bnd₀ ∧ RanAt` (`Tools/ShippingOutermostCommand.lean`), its
hypotheses from the `_ran` forms of the split lemmas:

1. `mixDeep_runFacts_ran`, `mixDeep_outsG2_ran`, `mixDeep_maskedG_ran`,
   `mixDeep_designP2_ran`: the four run theorems of
   `Tests/Compiler/NoPortsMixDeepTest.lean` with `hcore entry closes hB`
   replaced by `ran` (`Tools.ShippingKidFacts.kids_*_ran`); the children's
   facts are that file's `mixDeep_kids` (reflections only).
2. `mixDeep.machine_composedNR2_ofTrace` (`composedOfTrace`): the generated
   composed theorem with its one use of the closing (the wired head) turned
   into a hypothesis.
3. `mixDeep.outermost_open_noPortsNR2` (`openTerm`).
4. `mixDeep_ranAt_outermost`: `RanAt` from `Start0`, by the BUILT
   `mixDeep_closes_prov` (`Tests/Compiler/MixDeepOutermostTest.lean`) and
   `machineRan_outermost`.
5. `mixDeep.machine_design_noPortsNR2_outermost` (`closeOutermost`): the
   boundary derived from the reflections and `Start0.childBnd`.

## SCOPE (binding for any report)

ONE declaration, `mixDeep`, at depth 2, OUTERMOST STARTS ONLY. Data
conditions decided per declaration by the kernel are conditions, not
reductions. The result depends on the compiler's guards with fallback. The
conclusion is about `DesignSV (childMap D.modules) 2 (checkedOptimize b)` —
the module list (children UNOPTIMISED), not the SV string, not `#sim`. -/

namespace Tests.Compiler.MixDeepOutermostEndpointTest
open Tools.ShippingMachineRan (Start0 MachineRan)
open Tools.ShippingOutermost (RanAt)
open Tests.Compiler.NoPortsMixDeepTest (outsT insT mixDeep_kids mixDeep_callWidths
  mixDeep_callArgs mixDeep_outChars)
open Tests.Compiler.MixDeepOutermostTest (mixDeep_closes_prov)

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `mixDeep`'s full-entry module**, from `MachineRan`
(`kids_runFacts_ran`). -/
theorem mixDeep_runFacts_ran {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineRan mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape raw D)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingKidFacts.kids_runFacts_ran (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    outsT insT 2 (mixDeep_kids hRm2 hRm hRr hRc) mixDeep_callWidths
    hpost ran

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 2 under the statement-kind gate**, from
`MachineRan` (`kids_outsCheck_ran`). -/
theorem mixDeep_outsG2_ran {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineRan mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape raw D)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck_ran (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    outsT insT 2 (mixDeep_kids hRm2 hRm hRr hRc)
    hpost ran hg

set_option maxHeartbeats 4000000 in
/-- **The children's masked outputs**, from `MachineRan` (`kids_maskedN_ran`). -/
theorem mixDeep_maskedG_ran {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineRan mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape raw D)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFacts.kids_maskedN_ran (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    outsT insT 2 (mixDeep_kids hRm2 hRm hRr hRc)
    hpost ran

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 2 of the shipped module, with no check premise**,
from `MachineRan` (`kids_designCheck_ran`). -/
theorem mixDeep_designP2_ran {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineRan mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape raw D)
    (hRm2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 2
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_designCheck_ran (nDecl := 1)
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_ok
    Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    outsT insT 2 (mixDeep_kids hRm2 hRm hRr hRc) mixDeep_callWidths mixDeep_callArgs
    hpost ran
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mixDeep_outChars o ho))
    (by decide)

/-- **`RanAt` of `mixDeep` at an outermost start**: every core run of
`mixDeep` from a `Start0` world performed a machine synthesis that returned
its result — from the five reflections, by the BUILT provenance chain
(`mixDeep_closes_prov`: the machine synthesis of `mixDeep` does not fall back
from a `Prov` world). No `MachineClosesAt`. The explicit arguments are in the
order `Tools.ShippingOutermostCommand.closeOutermost` applies them. -/
theorem mixDeep_ranAt_outermost {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w : Void IO.RealWorld}
    (hRg : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape)
    (hR2 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
      (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).shape)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
      (Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.machineData).shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
      Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape)
    (h0 : Start0 mref cref w)
    (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) :
    RanAt mctx mref cctx cref ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
      (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).shape w M D :=
  Tools.ShippingOutermost.ranAt_outermost hRg h0
    (fun L bb w9 r w10 hw9 hd9 hp9 hrun =>
      mixDeep_closes_prov L hR2 hRm hRr hRc bb w9 r w10 hw9 hd9 hp9 hrun) M D

end Tests.Compiler.MixDeepOutermostEndpointTest

/-! ## The generated steps -/

-- the built endpoint must be there BEFORE anything is added, and nothing of
-- this file's names may exist yet
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let env ← Lean.getEnv
  for n in [g ++ `machine_design_noPortsNR2, g ++ `machine_ships_hierNR2, g ++ `machine_composedNR2,
      g ++ `machine_sound] do
    unless env.contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [g ++ `machine_composedNR2_ofTrace, g ++ `outermost_open_noPortsNR2,
      g ++ `machine_design_noPortsNR2_outermost] do
    if env.contains n then throwError "{n}: exists already"
  let oldN := g ++ `machine_design_noPortsNR2
  let ci ← Lean.getConstInfo oldN
  let hashText : String := toString ci.type.hash
  Lean.logInfo m!"OUTERMOST ENDPOINT BEFORE: {oldN} present, type hash {hashText} (logged; logged again by the audit at the end of this file)"

-- 2. the composed theorem with the wired endpoint as a hypothesis
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let composedN := g ++ `machine_composedNR2
  let traceN := g ++ `machine_composedNR2_ofTrace
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingOutermostCommand.composedOfTrace g 2 traceN
  Lean.logInfo m!"OUTERMOST STEP composedOfTrace: {traceN} — the proof term of {composedN} with its application of the wired head replaced by a hypothesis; the closing binder no longer occurs (checked by the builder); kernel-checked, standard axioms"

-- 3. the head at C := True and the boundary Bnd₀ ∧ RanAt
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let name := g ++ `outermost_open_noPortsNR2
  let traceN := g ++ `machine_composedNR2_ofTrace
  let (type, value) ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingOutermostCommand.openTerm g 2 [] [rc] traceN
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_runFacts_ran
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_outsG2_ran
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_maskedG_ran
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_designP2_ran
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingMachineLinkedCommand.addTheorem name type value
  Lean.logInfo m!"OUTERMOST STEP openTerm: {name} — the head machine_design_noPorts at C := True and the boundary (built boundary ∧ RanAt), its wired endpoint from the _ran head, its composed theorem from {traceN}, its four run hypotheses from the kids_*_ran theorems; kernel-checked, standard axioms"

-- 5. the endpoint: the boundary from the reflections and Start0
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let m2 := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let name := g ++ `machine_design_noPortsNR2_outermost
  let lines ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingOutermostCommand.closeOutermost (g ++ `outermost_open_noPortsNR2) name
      [(`hR2, m2, false), (`hRm, m, false), (`hRr, rc, true), (`hRc, c, false)]
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_ranAt_outermost
  Lean.logInfo m!"OUTERMOST STEP closeOutermost {name}:\n{String.intercalate "\n" lines.toList}"

#check @Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_noPortsNR2_outermost
#print axioms Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_design_noPortsNR2_outermost
#print axioms Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machine_composedNR2_ofTrace
#print axioms Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_ranAt_outermost
#print axioms Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_designP2_ran

/-! ## The audit (an error on any failure) -/

namespace Tests.Compiler.MixDeepOutermostEndpointTest
open Lean Meta

/-- Under the same witnesses: the old body `∃ w…, P ∧ (A → C)` and the new
body `∃ w…, P' ∧ C'` have `P ≡ P'` and `C ≡ C'`. -/
partial def sameConclusion (old new : Lean.Expr) : MetaM Bool := do
  if old.isAppOfArity ``Exists 2 && new.isAppOfArity ``Exists 2 then
    let α := old.getArg! 0
    unless ← isDefEq α (new.getArg! 0) do return false
    let p := old.getArg! 1
    let q := new.getArg! 1
    let nm := if p.isLambda then p.bindingName! else `w
    withLocalDeclD nm α fun w =>
      sameConclusion (mkApp p w).headBeta (mkApp q w).headBeta
  else if old.isAppOfArity ``And 2 && new.isAppOfArity ``And 2 then
    unless ← isDefEq (old.getArg! 0) (new.getArg! 0) do return false
    let R := old.getArg! 1
    unless ← Tools.ShippingFinalGoalCommand.isPropArrow R do return false
    isDefEq R.bindingBody! (new.getArg! 1)
  else
    return false

end Tests.Compiler.MixDeepOutermostEndpointTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep
  let oldN := g ++ `machine_design_noPortsNR2
  let newN := g ++ `machine_design_noPortsNR2_outermost
  let closedN := g ++ `machine_design_noPortsNR2_closed
  -- (a) standard axioms
  for n in [newN, g ++ `machine_composedNR2_ofTrace, g ++ `outermost_open_noPortsNR2,
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_runFacts_ran,
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_outsG2_ran,
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_maskedG_ran,
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_designP2_ran,
      ``Tests.Compiler.MixDeepOutermostEndpointTest.mixDeep_ranAt_outermost,
      ``Tools.ShippingOutermost.ranAt_outermost, ``Tools.ShippingOutermost.ranAt_of_closes,
      ``Tools.ShippingKidFacts.kids_runFacts_ran, ``Tools.ShippingKidFacts.kids_outsCheck_ran,
      ``Tools.ShippingKidFacts.kids_maskedN_ran, ``Tools.ShippingKidFacts.kids_designCheck_ran] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  let newT := (← Lean.getConstInfo newN).type
  let oldT := (← Lean.getConstInfo oldN).type
  -- (b) the new statement: no checker, no closing, no ChildRanIn, no RanAt; DesignSV; Start0
  for k in Tests.Compiler.NoPortsTest.checkers ++
      [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingMachineEntry.MachineCloses,
       ``Tools.ShippingChildInv.ChildRanIn, ``Tools.ShippingOutermost.RanAt,
       ``Tools.ShippingMachineRan.MachineRan] do
    if (newT.find? (·.isConstOf k)).isSome then
      throwError "{newN}: the statement mentions {k}"
  unless (newT.find? (·.isConstOf ``Tools.ShippingDesignSV.DesignSV)).isSome do
    throwError "{newN}: the statement does not mention DesignSV"
  -- (c) the EXISTING endpoint is unchanged: present, still asking MachineClosesAt of mixDeep
  -- as a binder, and still without a closed form
  let closesBinder ← Lean.Meta.forallTelescope oldT fun xs _ => do
    let mut found : Bool := false
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if t.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && t.getArg! 4 == Lean.toExpr g then
        found := true
    pure found
  unless closesBinder do
    throwError "{oldN}: MachineClosesAt of {g} is no longer among its binders — the built endpoint changed"
  if (← Lean.getEnv).contains closedN then
    throwError "{closedN}: exists — this file adds no closed form of the built endpoint"
  -- (d) the binders of the new statement, in order: 8 data binders, the run, the five
  -- reflections (mixDeep, mid2, midH, rcH, cnt), Start0 — and nothing else
  let m2 := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let shapeOk ← Lean.Meta.forallTelescope newT fun xs _ => do
    let mut props : Array Lean.Expr := #[]
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp t then props := props.push t
    unless props.size == 7 do
      throwError "{newN}: {props.size} proposition binders, expected 7 (the run, five reflections, Start0)"
    let isM (t : Lean.Expr) (k : Lean.Name) : Bool :=
      t.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 && t.getArg! 4 == Lean.toExpr k
    let isG (t : Lean.Expr) (k : Lean.Name) : Bool :=
      t.isAppOfArity ``Tools.ShippingInlineSoundness.EntryDefines 6 && t.getArg! 4 == Lean.toExpr k
    let runOk : Bool := props[0]!.isAppOf ``Tools.ShippingEntrySoundness.RunsTo &&
      (props[0]!.find? (·.isConstOf ``Sparkle.Compiler.Elab.synthesizeCombinational)).isSome
    pure (runOk && isM props[1]! g && isM props[2]! m2 && isM props[3]! m && isG props[4]! rc &&
      isM props[5]! c && props[6]!.isAppOfArity ``Tools.ShippingMachineRan.Start0 3)
  unless shapeOk do
    throwError "{newN}: its proposition binders are not, in order, the run of synthesizeCombinational, the reflections of {g}, {m2}, {m}, {rc}, {c}, and Start0"
  -- (e) the conclusion is the built endpoint's: the same `P`, and the same statement after the
  -- boundary, at the same binders
  let same ← Lean.Meta.forallBoundedTelescope oldT (some 10) fun xs restOld => do
    let restNew ← Lean.Meta.instantiateForall newT xs
    Lean.Meta.forallTelescope restOld fun _ bodyOld =>
      Lean.Meta.forallTelescope restNew fun _ bodyNew =>
        Tests.Compiler.MixDeepOutermostEndpointTest.sameConclusion bodyOld bodyNew
  unless same do
    throwError "{newN}: its conclusion is not the conclusion of {oldN} after the boundary"
  -- (f) under the existentials of the new statement: no antecedent
  let inner ← Lean.Meta.forallTelescope newT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  unless inner.size == 0 do
    throwError "{newN}: {inner.size} antecedent(s) under the existentials, expected none"
  -- (g) the classifier's label of every premise: exactly ONE not allowed, and it is Start0
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines newN
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.size == 1 do
    throwError "{newN}: {bad.size} premise(s) NOT ALLOWED by the classifier, expected exactly 1 (Start0):\n{String.intercalate "\n" bad.toList}"
  let start0Label ← Lean.Meta.forallTelescope newT fun xs _ => do
    let mut label : String := "absent"
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if t.isAppOf ``Tools.ShippingMachineRan.Start0 then
        let ok := Tools.ShippingFinalGoalCommand.allowed t
        label := if ok then "ALLOWED" else "NOT ALLOWED"
    pure label
  unless start0Label == "NOT ALLOWED" do
    throwError "{newN}: its Start0 premise is labelled {start0Label} by the existing classifier — the classifier or the statement changed"
  -- (h) the census's own re-check does NOT pass on it; the outermost re-check does
  let census ← Tools.ShippingDesignCoverage.recheck newN
  if census.ok then
    throwError "{newN}: the census's re-check PASSES on it — it would be counted COVERED (a defect to report, not a result)"
  let outer ← Tools.ShippingOutermostCoverage.recheck newN
  unless outer.ok do
    throwError "{newN}: the outermost re-check fails: Start0 binders {outer.start0}, other NOT ALLOWED {outer.badOther}, NOT ALLOWED antecedents {outer.badAntes}, checker / closing constants {outer.checkers}, DesignSV {outer.hasDesign}"
  let oldHash : String := toString oldT.hash
  let censusBad : Nat := census.bad
  Lean.logInfo m!"OUTERMOST ENDPOINT AUDIT {g}: {newN} on standard axioms. OUTERMOST SCOPE — not counted in the census population: the census's re-check fails on it ({censusBad} NOT ALLOWED premise: Start0, labelled {start0Label} by the existing classifier Tools.ShippingFinalGoalCommand.allowed, which was not changed), and #outermost_coverage lists it in its own table. Proposition binders, in order: the run of synthesizeCombinational {g}; the reflections of {g}, {m2}, {m}, {rc}, {c} at the run's contexts; Start0 at the start world. No MachineClosesAt, no MachineCloses, no ChildRanIn, no checker constant, no antecedent under the existentials. Its conclusion is the conclusion of {oldN} after the boundary (isDefEq at the same binders). The built endpoint {oldN} is UNCHANGED: present (type hash {oldHash}), MachineClosesAt of {g} still among its binders, no closed form; {g} stays OPEN in the census. NOT proved here: anything at a nested start (positive depth). SCOPE: one declaration at depth 2, outermost starts only; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list with the children UNOPTIMISED — not the SV string, not #sim."

-- the separate tally (its own table; `#design_coverage` is not run here and not changed)
set_option maxHeartbeats 0 in
#outermost_coverage
