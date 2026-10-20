import Tests.Compiler.NoPortsGrandHTest
import Tools.ShippingLeafKidFacts

/-! # `mixD1` by hand: the depth endpoint without the four check premises, over TWO DIFFERENT kinds of children (G1, unit U2, round par/a-14)

`mixD1 → {midH → rcH, cnt}` (`Tests/Compiler/ShippingDesignSVTest.lean` 43–50, READ):

    def mixD1 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal defaultDomain (BitVec 8))
        let a := midH en          -- a register AND a one-output call of the gate child rcH
        let b := cnt en           -- a leaf register machine
        r <~ Signal.mux a.hit (rs + b.n) rs
        return rs

`#machine_no_ports mixD1 1` REFUSES (BUILT log, `verification-a12.md` 81:
"the callee …midH is not a leaf register machine"). This file reaches the
same endpoint BY HAND:

    Tools/ShippingLeafKidFacts.lean   leafKid_facts : LeafKid … c dk → KidFacts … c dk.outs (declWidths dk) n   (NEW)
    Tools/ShippingOneOutKid.lean      OneOutKid.facts                                                            (BUILT)
    Tools/ShippingKidFacts.lean       kids_runFacts / _outsCheck / _maskedN / _designCheck                       (BUILT)
    Tests/Compiler/NoPortsGrandHTest  midH_kid, generateH, closeDeep                                             (BUILT)

## READ vs INFERRED about `mixD1`'s data (nothing was run)

READ (source): the two callees and the projected fields — `a.hit` (of
`midH`) and `b.n` (of `cnt`); one declared binder `en`; one register.
READ (BUILT logs): `mixD1.machine_ships_hierNR1`, `mixD1.machine_design_svNR1`
(`ShippingChildBoundaryTest` 156) and `mixD1.closes_deep` with 3 reflection
premises (`ShippingCallsCloseDeepTest`, "DEEP CLOSINGS … (2, 2, 3, 3)") exist;
`cnt.machine_leafKid` exists (`NoPortsTest`); the reader's `insts` has one
entry per PROJECTED FIELD (`verification-a13.md`).
MEASURED (integrator's build of the first version of this file): the call
entries are `[midH, midH, cnt, cnt]` — one entry per projected field, FOUR
entries. Asserted by the first `run_cmd` on the reader's data: that list,
`nDecl = 1`, `instFields ≠ []` (general closing), a slot. The three
premises of `mixD1.closes_deep` are ASSUMED to be the reflections of `midH`,
`cnt` and `rcH` (the audit checks the closed form's binders).

## What is proved here (one declaration)

* `mixD1_tables`: there are per-entry tables `kidOuts`, `kidIns` with
  `KidFacts … (insts[k]).1 (kidOuts k) (kidIns k) 1` for every entry,
  `callWidthsOk mixD1.machineData 1 kidOuts` and
  `callArgsOk mixD1.machineData 1 kidIns` — from the reflections of `midH`,
  `rcH`, `cnt`. `midH`'s entry: `(midH_kid hRm hRr).facts` (argument widths
  `argWidths midH.machineData 2`); `cnt`'s entry:
  `leafKid_facts (cnt.machine_leafKid hRc) 1` (argument widths
  `declWidths cnt.machineData`).
* `mixD1_runFacts`, `mixD1_outsG1`, `mixD1_maskedG`, `mixD1_designP1`: the
  four run hypotheses of the head, each with the binders
  `hcore hpost entry closes (hg) hB hRm hRr hRc`.
* `mixD1.machine_design_noPortsNR1` (`generateH`, as for `grandH`) and
  `mixD1.machine_design_noPortsNR1_closed` (`closeDeep` over the BUILT
  `mixD1.closes_deep`).

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `mixD1.machine_design_svNR1` | predicted state |
|---|---|---|
| `mixD1.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 1 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`) | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 1 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt mixD1` (open form) | predicted absent in `_closed` (`mixD1.closes_deep`, BUILT), pending build |
| | the boundary (`ChildBnd`, `MachineDefines midH`, `midH`'s own boundary in the contexts it is synthesised in, `MachineDefines cnt`) | STAYS in this file, unchanged (reduced in `NoPortsMixD1BTest`) |
| | `hr`, `MachineDefines mixD1` | stay |
| | — | ADDED to the open form: `EntryDefines rcH` at the run's contexts (a binder of the base CLOSED endpoint already) |

## SCOPE (binding for any report)

ONE declaration, `mixD1`: a parent WITH a register, the general closing, two
callees — `midH` (a register and ONE one-output call of a GATE child) and
`cnt` (a leaf register machine) — depth 1. Data conditions decided per
declaration by the kernel (conditions, not reductions). The result depends
on the compiler's guards with fallback. The conclusion is about `DesignSV
(childMap D.modules) 1 (checkedOptimize b)` — the module list (children
UNOPTIMISED), not the SV string, not `#sim`. The run, the reflections and
the boundary stay premises (no runtime model). NOT covered: depth 2
(`topD2`, `mixDeep`), a child under the general closing (`grand → mid`), a
generator, "all successful inputs".

UNVERIFIED at the time of writing: this file was not built. -/

/-! ## The shapes this file relies on, asserted on the reader's data first -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let rg ← Tools.ShippingMachineCommand.readMachine g
  let rcnt ← Tools.ShippingMachineCommand.readMachine c
  let entries := rg.shape.insts.map (·.1)
  unless rg.nDecl == 1 do throwError "{g}: nDecl = {rg.nDecl}, the hand theorems are written for 1"
  -- distinct callees (the reader has one entry per projected field)
  let kids := entries.eraseDups
  unless kids.length == 2 && kids.contains m && kids.contains c do
    throwError "{g}: the distinct callees are {kids}, expected {m} and {c}"
  unless entries == [m, m, c, c] do
    throwError "{g}: the call entries are {entries}; mixD1_entry / outsT / insT are written for the MEASURED [{m}, {m}, {c}, {c}]"
  if rg.shape.instFields.isEmpty then throwError "{g}: instFields = [] — not the general closing"
  if rg.shape.layout.slots.isEmpty then throwError "{g}: no register"
  unless rcnt.shape.insts.isEmpty do throwError "{c}: has calls — not a leaf"
  for n in [g ++ `closes_deep, g ++ `machine_ships_hierNR1, g ++ `machine_design_svNR1,
      c ++ `machine_leafKid, c ++ `machine_closes, m ++ `closes_deep, rc ++ `gate_full,
      ``Tests.Compiler.NoPortsGrandHTest.midH_kid] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [g ++ `machine_design_noPortsNR1, g ++ `machine_design_noPortsNR1_closed] do
    if (← Lean.getEnv).contains n then throwError "{n}: exists already"
  Lean.logInfo m!"NOPORTS MIXD1 DATA {g}: nDecl={rg.nDecl}, call entries {entries}, instFields={rg.shape.instFields}, slots={rg.shape.layout.slots.length}"

namespace Tests.Compiler.NoPortsMixD1Test
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingCallsChildPorts (argWidths)
open Tests.Compiler.NoPortsGrandHTest (midH_kid)

/-- The per-entry layouts. MEASURED (integrator's build log): the call
entries are `[midH, midH, cnt, cnt]` — one entry per projected field. -/
noncomputable def outsT (k : Nat) : List Sparkle.IR.Machine.OutField :=
  if k < 2 then midH.machineData.shape.layout.outs else (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs

/-- The per-entry argument widths. -/
noncomputable def insT (k : Nat) : List Nat :=
  if k < 2 then argWidths midH.machineData 2
  else Tools.ShippingPortWidthsPure.declWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData

/-- Every call entry's callee: `midH` for the entries 0 and 1, `cnt` for the
others (ONE statement, decided on the reflected data). -/
theorem mixD1_entry : ∀ (k : Nat) (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData).shape.insts[k]).1 =
      if k < 2 then ``midH else ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by
  decide

set_option maxHeartbeats 4000000 in
/-- **The per-entry tables of `mixD1`**: `KidFacts` of every call entry's
callee at depth 1 and the two width conditions. -/
theorem mixD1_tables {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape) :
    ∃ (kidOuts : Nat → List Sparkle.IR.Machine.OutField) (kidIns : Nat → List Nat),
      (∀ (k : Nat) (hk : k < (Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData).shape.insts.length),
        KidFacts mref cref ((Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData).shape.insts[k]).1 (kidOuts k) (kidIns k) 1) ∧
      Tools.ShippingCallWidths.callWidthsOk Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData 1 kidOuts = true ∧
      Tools.ShippingPortsMatchRaw.callArgsOk Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData 1 kidIns = true := by
  have hM : KidFacts mref cref ``midH midH.machineData.shape.layout.outs
      (argWidths midH.machineData 2) 1 := (midH_kid hRm hRr).facts
  have hC : KidFacts mref cref ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs (Tools.ShippingPortWidthsPure.declWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData) 1 :=
    Tools.ShippingLeafKidFacts.leafKid_facts
      (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_leafKid hRc) 1
  refine ⟨outsT, insT, ?_, (by first | decide | decide +kernel),
    (by first | decide | decide +kernel)⟩
  intro k hk
  rw [mixD1_entry k hk]
  by_cases h : k < 2
  · have e1 : outsT k = midH.machineData.shape.layout.outs := if_pos h
    have e2 : insT k = argWidths midH.machineData 2 := if_pos h
    have e3 : (if k < 2 then ``midH
        else ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt) = ``midH := if_pos h
    rw [e1, e2, e3]
    exact hM
  · have e1 : outsT k = (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData).shape.layout.outs := if_neg h
    have e2 : insT k = Tools.ShippingPortWidthsPure.declWidths Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData := if_neg h
    have e3 : (if k < 2 then ``midH
        else ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt) =
        ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := if_neg h
    rw [e1, e2, e3]
    exact hC

theorem mixD1_outChars : ∀ o ∈ Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `mixD1`'s full-entry module** (`kids_runFacts`). -/
theorem mixD1_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b := by
  obtain ⟨kidOuts, kidIns, hkid, hcw, -⟩ := mixD1_tables hRm hRr hRc
  exact Tools.ShippingKidFacts.kids_runFacts (nDecl := 1) Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOuts kidIns 1 hkid hcw
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 1 under the statement-kind gate**
(`kids_outsCheck`). -/
theorem mixD1_outsG1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true := by
  obtain ⟨kidOuts, kidIns, hkid, -, -⟩ := mixD1_tables hRm hRr hRc
  exact Tools.ShippingKidFacts.kids_outsCheck (nDecl := 1) Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOuts kidIns 1 hkid
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **The children's masked outputs** (`kids_maskedN`). -/
theorem mixD1_maskedG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true := by
  obtain ⟨kidOuts, kidIns, hkid, -, -⟩ := mixD1_tables hRm hRr hRc
  exact Tools.ShippingKidFacts.kids_maskedN (nDecl := 1) Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOuts kidIns 1 hkid
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 1 of the shipped module, with no check premise**
(`kids_designCheck`). -/
theorem mixD1_designP1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1 Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRm : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``midH
      midH.machineData.shape)
    (hRr : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
    (hRc : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true := by
  obtain ⟨kidOuts, kidIns, hkid, hcw, hargs⟩ := mixD1_tables hRm hRr hRc
  exact Tools.ShippingKidFacts.kids_designCheck (nDecl := 1) Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machineData
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_ok
    Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1.machine_body
    (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    kidOuts kidIns 1 hkid hcw hargs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mixD1_outChars o ho))
    (by decide)

end Tests.Compiler.NoPortsMixD1Test

/-! ## The endpoint and its closed form -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsGrandHTest.generateH g rc 1
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_runFacts
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_outsG1
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_maskedG
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_designP1
  let closed := Tools.ShippingMachineClosesGen.closedName name
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsGrandHTest.closeDeep g name (g ++ `closes_deep) closed
  Lean.logInfo m!"NOPORTS MIXD1 [{name}, {closed}]: the depth endpoint of a parent with a child with calls of its own AND a leaf register machine child, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — by hand (mixD1_tables: OneOutKid.facts of midH, leafKid_facts of cnt; mixD1_runFacts, mixD1_outsG1, mixD1_maskedG, mixD1_designP1: Tools.ShippingKidFacts.kids_*); one binder ADDED against the open base endpoint: the reflection of {rc} at the run's contexts"

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1
  let m := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let rc := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
  let old := g ++ `machine_design_svNR1
  let openN := g ++ `machine_design_noPortsNR1
  let closed := g ++ `machine_design_noPortsNR1_closed
  -- (a) standard axioms
  for n in [``Tools.ShippingLeafKidFacts.leafKid_facts,
      ``Tools.ShippingOneOutKid.OneOutKid.facts,
      ``Tools.ShippingKidFacts.kids_runFacts,
      ``Tools.ShippingKidFacts.kids_outsCheck,
      ``Tools.ShippingKidFacts.kids_maskedN,
      ``Tools.ShippingKidFacts.kids_designCheck,
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_tables,
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_runFacts,
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_outsG1,
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_maskedG,
      ``Tests.Compiler.NoPortsMixD1Test.mixD1_designP1, openN, closed] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) no endpoint statement mentions a checker constant
  for n in [openN, closed] do
    let ci ← Lean.getConstInfo n
    for k in Tests.Compiler.NoPortsTest.checkers do
      if (ci.type.find? (·.isConstOf k)).isSome then
        throwError "{n}: the statement mentions {k}"
  -- (c) the inventory: the base endpoint of this build asks the four check premises
  let oldT := (← Lean.getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsDepth.kidsMaskedN, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck] do
    unless (oldT.find? (·.isConstOf k)).isSome do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (d) the closing: asked by the open form, not by the closed one
  let openT := (← Lean.getConstInfo openN).type
  let closedT := (← Lean.getConstInfo closed).type
  unless (openT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome do
    throwError "{openN}: does not ask MachineClosesAt"
  if (closedT.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
    throwError "{closed}: still asks MachineClosesAt"
  -- (e) the binders of the closed form: the run, and reflections only — of
  -- mixD1, midH, cnt (MachineDefines) and rcH (EntryDefines)
  let (nProps, refl) ← Lean.Meta.forallTelescope closedT fun xs _ => do
    let mut props : Nat := 0
    let mut refl : List Lean.Name := []
    for x in xs do
      let t ← Lean.instantiateMVars (← Lean.Meta.inferType x)
      if ← Lean.Meta.isProp t then
        props := props + 1
        if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then pure ()
        else if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines ||
            t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines then
          for k in [g, m, c, rc] do
            if (t.find? fun e => e == Lean.toExpr k).isSome then refl := refl ++ [k]
        else
          throwError "{closed}: a binder that is neither the run nor a reflection:{Lean.indentExpr t}"
    return (props, refl)
  unless nProps == 5 && refl.length == 4 && refl.contains g && refl.contains m &&
      refl.contains c && refl.contains rc do
    throwError "{closed}: {nProps} proposition binders, reflections of {refl}; expected the run and one reflection each of {g}, {m}, {c}, {rc}"
  -- (f) the antecedents under the existentials: exactly one (the boundary),
  -- an antecedent of the base endpoint too
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
  Lean.logInfo m!"NOPORTS MIXD1 AUDIT {g}: {openN} and {closed} on standard axioms, with Tools.ShippingLeafKidFacts.leafKid_facts, OneOutKid.facts, the kids_* theorems and the hand lemmas mixD1_tables, mixD1_runFacts, mixD1_outsG1, mixD1_maskedG, mixD1_designP1. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. Closed form: {nProps} proposition binders — the run and the reflections of {refl}; MachineClosesAt asked by the open form only. Under the existentials: 1 antecedent, the boundary; printed the same as an antecedent of {old}: {same}. The goal-gap classifier lists {bad.size} premise(s) NOT ALLOWED in THIS closed form (the inherited boundary; its reduction is NoPortsMixD1BTest, not claimed here). ADDED against the open base endpoint: the reflection of {rc} at the run's contexts. SCOPE: one declaration, a parent WITH a register under the general closing, two callees (a register machine with a one-output call of a gate child; a leaf register machine), depth 1; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list with the children UNOPTIMISED — not the SV string, not #sim. NOT covered: topD2, mixDeep, grand, a generator."
