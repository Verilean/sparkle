import Tests.Compiler.OneOutMidHTest
import Tests.Compiler.NoPortsTwoTest
import Tests.Compiler.ShippingCallsCloseDeepTest
import Tools.ShippingOneOutKid

/-! # `grandH` by hand: the depth endpoint without the four check premises, over a child WITH calls (G1, unit U2, round par/a-13)

`grandH → midH → rcH` (`Tests/Compiler/ShippingMachineDepthHTest.lean`):

    @[hardware_module] def rcH {dom} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := …   -- a gate
    @[hardware_module] def midH {dom} (en : Signal dom Bool) : CntOut dom :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal dom (BitVec 8))
        let y := rcH rs
        r <~ Signal.mux en y rs
        return { n := rs, hit := rs === 7#8 }
    def grandH (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal defaultDomain (BitVec 8))
        let m := midH en
        r <~ Signal.mux m.hit (rs + m.n) rs
        return rs

`#machine_no_ports grandH 1` REFUSES (BUILT log, `verification-a12.md`):
"the callee …midH is not a leaf register machine: it has calls of its own
(LeafKid.leaf asks shape.insts = []; depth 1 only)". This file reaches the
same endpoint BY HAND, with the general lemmas of this round:

    Tools/ShippingChildMapCongr.lean    the checks read the child map at the instances' names
    Tools/ShippingKidsSelf.lean         core_kids_self, core_kidsPass_deep, core_kidsMaskedN_top
    Tools/ShippingCallsChildPorts.lean  core_calls_ports₁ (ports of a machine with one-output calls)
    Tools/ShippingKidFacts.lean         KidFacts; kids_runFacts / _outsCheck / _maskedN / _designCheck
    Tools/ShippingOneOutKid.lean        OneOutKid (no `leaf`), the bridge, OneOutKid.facts

## What is proved here (one declaration)

* `midH_kid`: `OneOutKid mref cref midH midH.machineData 2 midHNames` from
  `midH`'s reflection and `rcH`'s reflection (in any contexts) — the data
  fields are the BUILT `midH.oneout_*` (`OneOutMidHTest`) and six `decide`s
  (the argument split, as `midH.iface_deep` decides them); the
  grandchildren's fields are `rcH.gate_full` / `rcH.gate_kidK` (BUILT);
  `portsRaw` is the BUILT `midH.machine_portsRawH` at the child's run;
  `closes` is the BUILT `midH.closes_deep`.
* `grandH_kids`: `KidFacts … 1` of every call entry's callee.
* `grandH_runFacts`, `grandH_outsG1`, `grandH_maskedG`, `grandH_designP1`:
  the four run hypotheses of `Tools.ShippingNoPorts.machine_design_noPorts`
  at `grandH`'s data (`Tools.ShippingKidFacts.kids_*`), each with the
  binders `hcore hpost entry closes (hg) hB hRm hRr`.
* `grandH.machine_design_noPortsNR1`: the head applied to the arguments of
  `grandH.machine_ships_hierNR1` (read off its proof term, as
  `Tools.ShippingNoPortsCommand.generate` does — that function is copied
  here with ONE change, below), and
  `grandH.machine_design_noPortsNR1_closed` (its `MachineClosesAt grandH`
  replaced by the premises of the BUILT `grandH.closes_deep`).

## The one premise ADDED against `grandH.machine_design_svNR1` (binding)

The open endpoint has one binder the base endpoint does not have:

    hRr : EntryDefines mctx mref cctx cref `rcH rcH.gateValue

— the grandchild's reflection AT THE RUN'S CONTEXTS. The base endpoint's
boundary states `rcH`'s reflection only inside `midH`'s own boundary (for
the contexts `midH` is synthesised in, under `ChildRanIn`); the hand
theorems need it for every real child of `midH`, and take it once, in the
run's contexts, moving it by `EntryDefines.ctx`. It is a REFLECTION (the
class the goal-gap classifier allows), and it is already a binder of the
BUILT closed form `grandH.machine_design_svNR1_closed` (a premise of
`grandH.closes_deep`), so the CLOSED endpoint of this file has no binder
the closed base endpoint lacks. Deriving it from the boundary instead
(`ChildRanIn.of_run` + the child's boundary conjunct) is NOT done.

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `grandH.machine_design_svNR1` | predicted state |
|---|---|---|
| `grandH.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN (hand lemmas + new Tools theorems, none built) — predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 1 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 1 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt grandH` (open form) | predicted absent in `_closed` (`grandH.closes_deep`, BUILT), pending build |
| | the boundary `Bnd` (`ChildBnd`, `MachineDefines midH`, and `midH`'s own boundary in the contexts it is synthesised in) | STAYS, unchanged: the one antecedent under the existentials |
| | `hr`, `MachineDefines grandH` | stay |
| | — | ADDED: `EntryDefines rcH` at the run's contexts (see above) |

The boundary's conjunct about `midH`'s own boundary is a `∀` over contexts;
`Tools.ShippingFinalGoalCommand.allowed` (run / reflection / `ChildBnd` /
conjunctions) does not classify it as allowed. That is a property of the
BASE endpoint `grandH.machine_design_svNR1` (BUILT) and is inherited here:
the audit prints the premise list with the classifier's verdicts and does
NOT claim "no NOT ALLOWED premise"; it asserts that the antecedents under
the existentials are exactly ONE and that no statement mentions a checker.
No goal-gap theorem is generated.

## SCOPE (binding for any report)

ONE declaration, `grandH`: a parent WITH a register, the general closing,
one callee `midH` — a machine with a register and ONE one-output call of a
GATE child — depth 1. (i) Data conditions decided per declaration by the
kernel (for `grandH`: `callsOk 1`, slot lengths, no late domain binder,
`insts ≠ []`, `slots ≠ []`, `instFields ≠ []`, output width / name / scalar
conditions, no memory callee, `callWidthsOk` against `midH`'s layout,
`callArgsOk` against `argWidths midH.machineData 2`; for `midH`: the BUILT
`midH.oneout_*` and the argument split; the name separation of `midH` from
`rcH` by `Tools.ShippingNameSep`) are conditions, not reductions. (ii) The
result depends on the compiler's guards with fallback, including the two
closings' own check that the merged design resolves every child module by
name to itself (`core_kids_self` reads it off a successful closing).
(iii) The conclusion is about `DesignSV (childMap D.modules) 1
(checkedOptimize b)` — the module list (the children as their entries
returned them, UNOPTIMISED), not the SV string, not `#sim`. (iv) The run,
the reflections and the boundary stay premises (no runtime model).
NOT covered: `mixD1` (`midH` + the leaf `cnt`: needs `KidFacts` of a leaf,
`LeafKid → KidFacts`, not written), depth 2 (`topD2`, `mixDeep`), a child
under the general closing (`grand → mid`), a generator (`scopeP` still
refuses), "all successful inputs".

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The shapes this file relies on, asserted on the reader's data first -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let rg ← Tools.ShippingMachineCommand.readMachine g
  let rm ← Tools.ShippingMachineCommand.readMachine m
  unless rg.nDecl == 1 do throwError "{g}: nDecl = {rg.nDecl}, the hand theorems are written for 1"
  unless rm.nDecl == 2 do throwError "{m}: nDecl = {rm.nDecl}, the hand theorems are written for 2"
  unless (rg.shape.insts.map (·.1)).eraseDups == [m] do
    throwError "{g}: the call entries are {rg.shape.insts.map (·.1)}, expected [{m}]"
  unless (rm.shape.insts.map (·.1)).eraseDups == [rc] do
    throwError "{m}: the call entries are {rm.shape.insts.map (·.1)}, expected [{rc}]"
  if rg.shape.instFields.isEmpty then throwError "{g}: instFields = [] — not the general closing"
  unless rm.shape.instFields.isEmpty do throwError "{m}: instFields ≠ [] — not the one-output closing"
  if rg.shape.layout.slots.isEmpty || rm.shape.layout.slots.isEmpty then
    throwError "{g} / {m}: no register"
  for n in [m ++ `machine_portsRawH, m ++ `oneout_callsOk, m ++ `closes_deep, g ++ `closes_deep,
      rc ++ `gate_full, rc ++ `gate_kidK, g ++ `machine_ships_hierNR1,
      g ++ `machine_design_svNR1] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [g ++ `machine_design_noPortsNR1, g ++ `machine_design_noPortsNR1_closed] do
    if (← Lean.getEnv).contains n then throwError "{n}: exists already"

namespace Tests.Compiler.NoPortsGrandHTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Tools.ShippingOneOutKid (OneOutKid)
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingCallsChildPorts (argWidths)

/-- The printed names of the descendants of `midH`'s callees: none (its one
callee is a gate). -/
def midHNames : Nat → List String := fun _ => ([] : List Lean.Name).map fun n => Sparkle.IR.ModuleName.ofDecl n

/-- Every call entry of `midH` is of `rcH` (decided on the reflected data). -/
theorem midH_entry : ∀ (k : Nat) (hk : k < midH.machineData.shape.insts.length),
    (midH.machineData.shape.insts[k]).1 = ``rcH := by decide

/-- Every call entry of `grandH` is of `midH`. -/
theorem grandH_entry : ∀ (k : Nat) (hk : k < grandH.machineData.shape.insts.length),
    (grandH.machineData.shape.insts[k]).1 = ``midH := by decide

set_option maxHeartbeats 4000000 in
/-- **`midH` as a child**: the interface without `leaf`, from its reflection
and its gate callee's. -/
theorem midH_kid {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    OneOutKid mref cref ``midH midH.machineData 2 midHNames :=
  { ok := midH.machine_ok
    body := midH.machine_body
    calls := midH.oneout_callsOk
    ss := midH.oneout_slotLen
    dom := midH.oneout_domB
    insts := midH.oneout_insts
    oneOut := midH.oneout_instFields
    slots := midH.oneout_slots
    outTy := by first | exact midH.oneout_outTy | decide
    outName := fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (midH.oneout_outChars o ho)
    outScalar := by first | exact midH.oneout_outScalar | decide
    nomem := midH.oneout_nomem
    hkD := by decide
    hIlen := by decide
    hSL := by decide
    hSlen := by decide
    hLlen := by decide
    hNIn := by decide
    kid := by
      intro k hk y hy
      rw [midH_entry k hk] at hy ⊢
      exact Tools.ShippingKidsChildIface.kid_of_iface
        (Tools.ShippingCallsGate.ChildFull.iface (rcH.gate_full hRr hy))
    self := by
      have h : Tools.ShippingKidsChildIface.namesOf midH.machineData midHNames =
          (Tools.ShippingKidsChildIface.declsOf midH.machineData
            (fun _ => ([] : List Lean.Name))).map fun n => Sparkle.IR.ModuleName.ofDecl n :=
        Tools.ShippingKidsChildIface.namesOf_map midH.machineData
          (fun _ => ([] : List Lean.Name))
      rw [h]
      exact Tools.ShippingNameSep.Enc.not_mem_map_of _ _ (by decide)
    kidA := by
      intro k hk y hy
      rw [midH_entry k hk] at hy
      exact Tools.ShippingChecksGate.gate_kidA (rcH.gate_full hRr hy)
    kidR := by
      intro k hk y hy
      rw [midH_entry k hk] at hy
      exact Tools.ShippingChecksGate.gate_kidR (rcH.gate_full hRr hy)
    kidK := by
      intro k hk y hy
      rw [midH_entry k hk] at hy
      exact rcH.gate_kidK hRr hy
    portsRaw := fun _ _ _ _ _ _ _ hB hcore hpost =>
      midH.machine_portsRawH hcore hpost (Tools.ShippingReflectCtx.MachineDefines.ctx hRm)
        (midH.closes_deep (Tools.ShippingReflectCtx.EntryDefines.ctx hRr)) hB
        (Tools.ShippingReflectCtx.EntryDefines.ctx hRr)
    entry := fun _ _ => Tools.ShippingReflectCtx.MachineDefines.ctx hRm
    closes := fun _ _ => midH.closes_deep (Tools.ShippingReflectCtx.EntryDefines.ctx hRr) }

/-- **`KidFacts` of every call entry's callee of `grandH`**, one level down. -/
theorem grandH_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    ∀ (k : Nat) (hk : k < grandH.machineData.shape.insts.length),
      KidFacts mref cref (grandH.machineData.shape.insts[k]).1
        midH.machineData.shape.layout.outs (argWidths midH.machineData 2) 1 := by
  intro k hk
  rw [grandH_entry k hk]
  exact (midH_kid hRm hRr).facts

/-- The two width conditions of `grandH` against `midH`'s data. -/
theorem grandH_callWidths : Tools.ShippingCallWidths.callWidthsOk grandH.machineData 1
    (fun _ => midH.machineData.shape.layout.outs) = true := by
  first | decide | decide +kernel

theorem grandH_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk grandH.machineData 1
    (fun _ => argWidths midH.machineData 2) = true := by
  first | decide | decide +kernel

theorem grandH_outChars : ∀ o ∈ grandH.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `grandH`'s full-entry module** (`kids_runFacts`). -/
theorem grandH_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grandH [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grandH
      grandH.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``grandH
      grandH.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingKidFacts.kids_runFacts (nDecl := 1) grandH.machineData
    grandH.machine_ok grandH.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => midH.machineData.shape.layout.outs) (fun _ => argWidths midH.machineData 2) 1
    (grandH_kids hRm hRr) grandH_callWidths
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 1 under the statement-kind gate**
(`kids_outsCheck`). -/
theorem grandH_outsG1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grandH [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grandH
      grandH.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``grandH
      grandH.machineData.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck (nDecl := 1) grandH.machineData
    grandH.machine_ok grandH.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => midH.machineData.shape.layout.outs) (fun _ => argWidths midH.machineData 2) 1
    (grandH_kids hRm hRr)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **The children's masked outputs** (`kids_maskedN`). -/
theorem grandH_maskedG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grandH [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grandH
      grandH.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``grandH
      grandH.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFacts.kids_maskedN (nDecl := 1) grandH.machineData
    grandH.machine_ok grandH.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => midH.machineData.shape.layout.outs) (fun _ => argWidths midH.machineData 2) 1
    (grandH_kids hRm hRr)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 1 of the shipped module, with no check premise**
(`kids_designCheck`). -/
theorem grandH_designP1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``grandH [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``grandH
      grandH.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``grandH
      grandH.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_designCheck (nDecl := 1) grandH.machineData
    grandH.machine_ok grandH.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun _ => midH.machineData.shape.layout.outs) (fun _ => argWidths midH.machineData 2) 1
    (grandH_kids hRm hRr) grandH_callWidths grandH_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (grandH_outChars o ho))
    (by decide)

open Lean Meta Elab Command

/-- `Tools.ShippingShipsFreeCommand.discharge` with extra hypotheses besides
the conjuncts of the boundary (here: the grandchild's reflection at the
run's contexts). -/
def dischargeWith (thm : Name) (p0 hBnd goal : Lean.Expr) (extra : Array Lean.Expr) :
    MetaM Lean.Expr := do
  let parts := (← Tools.ShippingShipsNoOutsCommand.andParts hBnd) ++ extra
  let mut p := p0
  repeat
    let t ← whnfR (← instantiateMVars (← inferType p))
    let .forallE _ dom _ _ := t | break
    let mut found := false
    for q in parts do
      if ← isDefEq (← inferType q) dom then
        p := mkApp p q
        found := true
        break
    unless found do
      throwError "{thm}: asks{indentExpr dom}\nwhich is neither a conjunct of the endpoint's boundary{indentExpr (← inferType hBnd)}\nnor the extra reflection"
  unless ← isDefEq (← inferType p) goal do
    throwError "{thm}: proves{indentExpr (← inferType p)}\nbut the head asks{indentExpr goal}"
  instantiateMVars p

/-- `Tools.ShippingNoPortsCommand.generate`, copied, with ONE change: after
the binders of `f.machine_ships_hierNR{n}` the endpoint takes the reflection
of the gate grandchild `rc` at the run's contexts, which the four run
theorems ask besides the boundary's conjuncts. -/
def generateH (f rc : Name) (n : Nat) (facts outs masked design : Name) : MetaM Name := do
  let ships := f ++ Name.mkSimple s!"machine_ships_hierNR{n}"
  let name := f ++ Name.mkSimple s!"machine_design_noPortsNR{n}"
  if (← getEnv).contains name then throwError "{name}: exists already"
  let some (.thmInfo ti) := (← getEnv).find? ships
    | throwError "{ships}: not a theorem (run #machine_design_svNR first)"
  let v := ti.value
  unless v.isAppOf ``Tools.ShippingMachineShipsHier.machine_ships_hierC do
    throwError "{ships}: not built from machine_ships_hierC"
  let a := v.getAppArgs
  unless a.size == 25 do throwError "{ships}: {a.size} arguments of machine_ships_hierC, expected 25"
  let value ← forallTelescope (← inferType (mkConst ships)) fun xs _ => do
    unless xs.size == 11 do throwError "{ships}: {xs.size} binders, expected 11"
    let rT ← mkAppM ``Tools.ShippingInlineSoundness.EntryDefines
      #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, toExpr rc, mkConst (rc ++ `gateValue)]
    withLocalDeclD `hRr rT fun hRr => do
    let args : Array (Option Lean.Expr) :=
      #[some (mkNatLit n), some a[3]!, some a[4]!, some a[5]!, some a[6]!, some a[7]!,
        some a[8]!, some a[9]!, some a[10]!, some a[11]!,
        some a[12]!, some a[13]!, some a[14]!, some a[15]!, some a[16]!, some a[17]!,
        some a[18]!, some a[19]!, some a[20]!, some a[21]!,
        some a[22]!, some a[23]!, some a[24]!] ++ xs.map some
    let pre ← instantiateMVars
      (← mkAppOptM ``Tools.ShippingNoPorts.machine_design_noPorts args)
    if pre.hasMVar then throwError "{f}: the head's arguments were not all inferred"
    -- the run's facts: zs = raw D w1 hcore hpost hBnd ; xs[9] = entry, xs[10] = closes
    let .forallE _ TF _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's run-facts hypothesis is not where it is expected"
    let hFacts ← forallTelescope TF fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the run-facts hypothesis has {zs.size} binders"
      let p ← mkAppM facts #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith facts p zs[5]! goal #[hRr])
    let pre := mkApp pre hFacts
    -- the output check under the gate: zs = raw D w1 hcore hpost hg hBnd
    let .forallE _ TO _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's output-check hypothesis is not where it is expected"
    let hOuts ← forallTelescope TO fun zs goal => do
      unless zs.size == 7 do throwError "{f}: the output-check hypothesis has {zs.size} binders"
      let p ← mkAppM outs #[zs[3]!, zs[4]!, xs[9]!, xs[10]!, zs[5]!]
      mkLambdaFVars zs (← dischargeWith outs p zs[6]! goal #[hRr])
    let pre := mkApp pre hOuts
    -- the children's bound: zs = raw D w1 hcore hpost hBnd (cut at 6 binders)
    let .forallE _ TM _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's children-bound hypothesis is not where it is expected"
    let hMasked ← forallBoundedTelescope TM (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the children-bound hypothesis has {zs.size} binders"
      let p ← mkAppM masked #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith masked p zs[5]! goal #[hRr])
    let pre := mkApp pre hMasked
    -- `designCheck` with no check premise: zs = raw D w1 hcore hpost hBnd (cut at 6)
    let .forallE _ TD _ _ ← whnfR (← inferType pre)
      | throwError "{f}: the head's design-check hypothesis is not where it is expected"
    let hDesign ← forallBoundedTelescope TD (some 6) fun zs goal => do
      unless zs.size == 6 do throwError "{f}: the design-check hypothesis has {zs.size} binders"
      let p ← mkAppM design #[zs[3]!, zs[4]!, xs[9]!, xs[10]!]
      mkLambdaFVars zs (← dischargeWith design p zs[5]! goal #[hRr])
    mkLambdaFVars (xs ++ #[hRr]) (mkApp pre hDesign)
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{name}: REFUSED, the statement still mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem name type value
  return name

/-- The closed form: the endpoint's `MachineClosesAt f` (its last binder but
one) replaced by the premises of `cl` (`f.closes_deep`); a premise of `cl`
that is the endpoint's last binder (the grandchild's reflection) is NOT
repeated. -/
def closeDeep (f openN cl closedN : Name) : MetaM Unit := do
  if (← getEnv).contains closedN then throwError "{closedN}: exists already"
  let info ← getConstInfo openN
  let clT := (← getConstInfo cl).type
  let value ← forallTelescope info.type fun xs _ => do
    let m := xs.size
    unless m ≥ 2 do throwError "{openN}: {m} binders"
    let closes := xs[m - 2]!
    let hRr := xs[m - 1]!
    let ct ← instantiateMVars (← inferType closes)
    unless ct.isAppOfArity ``Tools.ShippingChildInv.MachineClosesAt 6 && ct.getArg! 4 == toExpr f do
      throwError "{openN}: its last binder but one is not MachineClosesAt of {f}:{indentExpr ct}"
    let ctx := ct.getAppArgs.extract 0 4
    let hRrT ← instantiateMVars (← inferType hRr)
    forallTelescope (← instantiateForall clT ctx) fun hs goal => do
      unless ← isDefEq goal ct do
        throwError "{cl}: proves{indentExpr goal}\nnot{indentExpr ct}"
      let mut keep : Array Lean.Expr := #[]
      let mut args : Array Lean.Expr := #[]
      for h in hs do
        if ← isDefEq (← inferType h) hRrT then
          args := args.push hRr
        else
          keep := keep.push h
          args := args.push h
      let body := mkAppN (mkConst openN)
        (xs.extract 0 (m - 2) ++ #[mkAppN (mkConst cl) (ctx ++ args), hRr])
      mkLambdaFVars (xs.extract 0 (m - 2) ++ keep ++ #[hRr]) body
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if (type.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closedN}: the closed statement still asks MachineClosesAt"
  for c in Tools.ShippingNoPortsCommand.forbidden do
    if (type.find? (·.isConstOf c)).isSome then
      throwError "{closedN}: REFUSED, the statement mentions {c}"
  Tools.ShippingMachineLinkedCommand.addTheorem closedN type value

end Tests.Compiler.NoPortsGrandHTest

/-! ## The endpoint and its closed form -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsGrandHTest.generateH g rc 1
      ``Tests.Compiler.NoPortsGrandHTest.grandH_runFacts
      ``Tests.Compiler.NoPortsGrandHTest.grandH_outsG1
      ``Tests.Compiler.NoPortsGrandHTest.grandH_maskedG
      ``Tests.Compiler.NoPortsGrandHTest.grandH_designP1
  let closed := Tools.ShippingMachineClosesGen.closedName name
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsGrandHTest.closeDeep g name (g ++ `closes_deep) closed
  Lean.logInfo m!"NOPORTS GRANDH [{name}, {closed}]: the depth endpoint of a parent whose child has calls of its own, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (grandH_runFacts, grandH_outsG1, grandH_maskedG, grandH_designP1: Tools.ShippingKidFacts.kids_* over OneOutKid midH); one binder ADDED against the base endpoint: the reflection of {rc} at the run's contexts"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let old := g ++ `machine_design_svNR1
  let openN := g ++ `machine_design_noPortsNR1
  let closed := g ++ `machine_design_noPortsNR1_closed
  -- (a) standard axioms: the general theorems of this round, the hand lemmas, the endpoints
  for n in [``Tools.ShippingChildMapCongr.linkedWF_congr,
      ``Tools.ShippingChildMapCongr.noSelfRead_congr,
      ``Tools.ShippingChildMapCongr.portsMatchB_congr,
      ``Tools.ShippingChildMapCongr.outMaskedB_perm_insts,
      ``Tools.ShippingChildMapCongr.outsMaskedN_of_typed,
      ``Tools.ShippingKidsSelf.core_kids_self,
      ``Tools.ShippingKidsSelf.core_kidsPass_deep,
      ``Tools.ShippingKidsSelf.core_kidsMaskedN_top,
      ``Tools.ShippingCallsChildPorts.core_calls_ports₁,
      ``Tools.ShippingCallsChildPorts.CallsPorts.inWidths,
      ``Tools.ShippingCallsChildPorts.core_conn_wires₁,
      ``Tools.ShippingKidFacts.kids_runFacts,
      ``Tools.ShippingKidFacts.kids_outsCheck,
      ``Tools.ShippingKidFacts.kids_maskedN,
      ``Tools.ShippingKidFacts.kids_designCheck,
      ``Tools.ShippingOneOutKid.core_designCheck_in₁,
      ``Tools.ShippingOneOutKid.OneOutKid.core,
      ``Tools.ShippingOneOutKid.OneOutKid.check,
      ``Tools.ShippingOneOutKid.OneOutKid.facts,
      ``Tests.Compiler.NoPortsGrandHTest.midH_kid,
      ``Tests.Compiler.NoPortsGrandHTest.grandH_kids,
      ``Tests.Compiler.NoPortsGrandHTest.grandH_runFacts,
      ``Tests.Compiler.NoPortsGrandHTest.grandH_outsG1,
      ``Tests.Compiler.NoPortsGrandHTest.grandH_maskedG,
      ``Tests.Compiler.NoPortsGrandHTest.grandH_designP1, openN, closed] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) no endpoint statement mentions a checker constant
  for n in [openN, closed] do
    let ci ← Lean.getConstInfo n
    for c in Tests.Compiler.NoPortsTest.checkers do
      if (ci.type.find? (·.isConstOf c)).isSome then
        throwError "{n}: the statement mentions {c}"
  -- (c) the inventory: the base endpoint of this build asks the four check premises
  let oldT := (← Lean.getConstInfo old).type
  for c in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf c)).isSome do
      throwError "{old}: does not mention {c} (the inventory is wrong)"
  -- (d) the closing: asked by the open form, not by the closed one
  let openT := (← Lean.getConstInfo openN).type
  let closedT := (← Lean.getConstInfo closed).type
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt"
  if (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closed}: still asks MachineClosesAt"
  -- (e) the binders of the closed form: the run, and reflections only; one
  -- reflection of grandH, of midH and of rcH each
  let (nBinders, refl) ← Lean.Meta.forallTelescope closedT fun xs _ => do
    let mut props : Nat := 0
    let mut refl : List Lean.Name := []
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp t then
        props := props + 1
        if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then pure ()
        else if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
            t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines then
          for c in [g, m, rc] do
            if (t.find? fun e => e == Lean.toExpr c).isSome then refl := refl ++ [c]
        else
          throwError "{closed}: a binder that is neither the run nor a reflection:{Lean.indentExpr t}"
    return (props, refl)
  unless nBinders == 4 && refl.length == 3 && refl.contains g && refl.contains m &&
      refl.contains rc do
    throwError "{closed}: {nBinders} proposition binders, reflections of {refl}; expected the run and one reflection each of {g}, {m}, {rc}"
  -- (f) the antecedents under the existentials: exactly one (the boundary),
  -- and it is an antecedent of the base endpoint too
  let inner ← Lean.Meta.forallTelescope closedT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let innerOld ← Lean.Meta.forallTelescope oldT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  unless inner.size == 1 do
    throwError "{closed}: {inner.size} antecedents under the existentials, expected 1 (the boundary)"
  let same := innerOld.any fun a => a.1 == inner[0]!.1
  -- (g) the complete premise list, with the goal-gap classifier's verdicts (LOGGED)
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.size ≤ 1 do
    throwError "{closed}: {bad.size} premises the classifier does not allow, expected at most the inherited boundary:\n{String.intercalate "\n" bad.toList}"
  Lean.logInfo m!"NOPORTS GRANDH AUDIT {g}: {openN} and {closed} on standard axioms, with the general theorems of Tools.ShippingChildMapCongr / KidsSelf / CallsChildPorts / KidFacts / OneOutKid and the hand lemmas midH_kid, grandH_kids, grandH_runFacts, grandH_outsG1, grandH_maskedG, grandH_designP1. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: {nBinders} proposition binders — the run and the reflections of {refl}; MachineClosesAt asked by the open form only. Under the existentials: 1 antecedent, the boundary; printed the same as an antecedent of {old}: {same}. The goal-gap classifier lists {bad.size} premise(s) NOT ALLOWED — the boundary's conjunct about {m}'s own boundary in the contexts it is synthesised in is a ∀ over contexts, INHERITED from {old}, not removed and not claimed removed. ADDED against the open base endpoint: the reflection of {rc} at the run's contexts (a binder of the base CLOSED endpoint already). SCOPE: one declaration, a parent WITH a register under the general closing, one callee with a register and a one-output call of a gate child, depth 1; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback (including the closings' own design-consistency check); DesignSV of the module list with the children UNOPTIMISED — not the SV string, not #sim. NOT covered: mixD1, topD2, mixDeep, grand, a generator."
