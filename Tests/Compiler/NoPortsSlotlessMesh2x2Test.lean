import Tests.Compiler.NoPortsSlotlessLib

/-! # `mesh2x2`: a parent WITHOUT a register, four calls with DIFFERENT arguments of one sequential child, chained through their fields — the depth-1 SV endpoint with no compiler-check premise (G1, unit U5a, round par/a-21)

`Sparkle.Tests.Compiler.MultiInstance.mesh2x2`
(`Tests/Compiler/MultiInstanceTest.lean:46`):

    def mesh2x2 {dom : DomainConfig} (a0 a1 w00 w01 w10 w11 : Signal dom (BitVec 32)) :
        Signal dom (BitVec 32) :=
      let zero : Signal dom (BitVec 32) := Signal.pure (0#32)
      let pe00 := pe a0        zero      w00
      let pe01 := pe pe00.aOut zero      w01
      let pe10 := pe a1        pe00.pOut w10
      let pe11 := pe pe10.aOut pe01.pOut w11
      let _ := pe11.aOut
      pe11.pOut

Callee: the LEAF REGISTER machine `pe` (as `engineOnce`). MEASURED at
23a6f28c (`docs/parallel/verification-a20.md`): `nDecl = 7`, slots `0`,
lets `11`, every call entry of `pe`; `#machine_design_svNR mesh2x2 1` and
`#machine_closes_at mesh2x2` go through (log-only try, nothing kept). The
number of call entries and their argument `let`s were NOT in the excerpt
(the log line is cut): step 1 logs them one line per entry.

This file is `Tests/Compiler/NoPortsSlotlessEngineOnceTest.lean` (BUILT) at
`mesh2x2`'s data, step for step; the shared meta code (data log, audit) is
`Tests/Compiler/NoPortsSlotlessLib.lean`. `pe.machine_closes`,
`pe.seq_child_runN`, `pe.machine_leafKid` are IMPORTED from the engineOnce
test, not recreated.

## Many entries of one callee: ONE decided statement

The per-entry facts do not split over the entries: `mesh_entry` is one
decided `∀ k hk, (insts[k]).1 = pe` (independent of the entry count), and
`KidFacts` of entry `k` is `leafKid_facts (pe.machine_leafKid hRp) 1` after
rewriting by it; the tables `kidOuts`, `kidIns` are CONSTANT functions
(`pe`'s outputs, `pe`'s declared widths). `callWidthsOk` / `callArgsOk`
range over the entries by themselves (`List.range insts.length`).

## The hypothesis that reads the argument `let`s

None of the four run theorems has one. `callArgsOk` reads every entry's
argument `let`s, but only their WIDTHS against `declWidths pe` — true
whether or not two entries share arguments. `SeqKid` is entry 0 alone.

The one hypothesis on the path whose TRUTH depends on the entries'
arguments being distinct is `hfieldsNd` of
`Tools.ShippingCallsSeqKids.machineClosesAt_of_seqKids` (inside
`mesh2x2.machine_closes_at`, decided by the built generator):

    callee equal → argument lets equal → field equal → k = k'

Here the callee is always `pe`, and several entries read the SAME field of
different instances (INFERRED from the source: `pOut` of `pe00`, `pe01`,
`pe11`; `aOut` of `pe00`, `pe10` and, if the dead `let _` is read,
`pe11`). Such entries are told apart by their argument `let`s ONLY: the
hypothesis is true exactly because the four calls have four different
argument lists (`(a0, zero, w00)`, `(pe00.aOut, zero, w01)`,
`(a1, pe00.pOut, w10)`, `(pe10.aOut, pe01.pOut, w11)` — they differ already
in the weight). It would be FALSE for a reading with two entries of one
instance and one field. Evaluation: (a) BUILT — `#machine_closes_at mesh2x2`
went through at 23a6f28c, i.e. the kernel decided it true; (b) here it is
restated verbatim and decided as `mesh_fieldsNd` (not used by a proof);
(c) the `FIELDSND` log line of step 1 lists the entry pairs separated by
arguments only — the measurement to read after the build.

## EXPECTED (stated before the build)

`mesh2x2.machine_design_noPortsNR1_closed`: binders — the run,
`MachineDefines mesh2x2`, `MachineDefines pe`; under the existentials one
antecedent, `ChildBnd ∧ MachineDefines pe` (ALLOWED). Against
`mesh2x2.machine_design_svNR1`: `shipsHierCheck`, `kidsMaskedN`,
`designCheck`, `outsCheck` absent, nothing added.

## SCOPE

As the engineOnce test: one declaration, depth 1, data conditions decided
per declaration (conditions, not reductions), compiler guards with
fallback, `DesignSV` of the module list — not the SV string, not `#sim`;
the run, the reflections and `ChildBnd` stay premises.

The decided statements are under `maxHeartbeats 0` (the conditions under
which the base commands were measured on this declaration).

WRITTEN, NOT BUILT. -/

/-! ## 1. The reader data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let pe := ``Sparkle.Tests.Compiler.MultiInstance.pe
  let f := ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
  let rp ← Tests.Compiler.NoPortsSlotlessLib.logData "NOPORTS SLOTLESS MESH" pe
  let r ← Tests.Compiler.NoPortsSlotlessLib.logData "NOPORTS SLOTLESS MESH" f
  unless r.nDecl == 7 do throwError "{f}: nDecl = {r.nDecl}, the hand theorems are written for 7"
  unless r.shape.layout.slots.isEmpty do
    throwError "{f}: {r.shape.layout.slots.length} slots — not a parent without a register"
  if r.shape.insts.isEmpty then throwError "{f}: no call"
  if r.shape.instFields.isEmpty then throwError "{f}: instFields = [] — not the general closing"
  unless (r.shape.insts.map (·.1)).eraseDups == [pe] do
    throwError "{f}: the call entries are {r.shape.insts.map (·.1)}, expected every entry to be {pe}"
  unless rp.shape.insts.isEmpty do throwError "{pe}: has calls — not a leaf"
  if rp.shape.layout.slots.isEmpty then throwError "{pe}: no register — not a sequential child"
  for n in [f ++ `machineData, f ++ `machine_ok, f ++ `machine_body,
      pe ++ `machineData, pe ++ `machine_ok, pe ++ `machine_body,
      pe ++ `machine_closes, pe ++ `machine_leafKid] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1, f ++ `machine_closes_at,
      f ++ `machine_design_noPortsNR1, f ++ `machine_design_noPortsNR1_closed] do
    if (← Lean.getEnv).contains n then throwError "{n}: exists already"

/-! ## 2. The base endpoint and the closing, by the built commands -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.MultiInstance.mesh2x2 1

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.MultiInstance.mesh2x2

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
  for n in [f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1, f ++ `machine_closes_at] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
  let (lines, _) ← Tests.Compiler.NoPortsTest.premiseLines (f ++ `machine_design_svNR1)
  let clInfo ← Lean.getConstInfo (f ++ `machine_closes_at)
  let clT := clInfo.type
  Lean.logInfo m!"NOPORTS SLOTLESS MESH BASE {f}: machine_ships_hierNR1, machine_design_svNR1 and machine_closes_at generated by the built commands, standard axioms; the base endpoint's premises:\n{String.intercalate "\n" lines.toList}\nthe closing theorem: {clT}"

/-! ## 3. The four run hypotheses, by hand -/

namespace Tests.Compiler.NoPortsSlotlessMesh2x2Test
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingSlotlessClk (SeqKid)

set_option maxHeartbeats 0 in
/-- Every call entry of `mesh2x2` is of `pe` (ONE decided statement over
the entries of the reflected data, whatever their count). -/
theorem mesh_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts[k]).1 =
      ``Sparkle.Tests.Compiler.MultiInstance.pe := by decide

set_option maxHeartbeats 0 in
theorem mesh_insts :
    (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

set_option maxHeartbeats 0 in
theorem mesh_general :
    (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.instFields ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

set_option maxHeartbeats 0 in
/-- `mesh2x2` has NO register (the reflected data). -/
theorem mesh_noSlots :
    (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.layout.slots = [] :=
  List.length_eq_zero_iff.mp (by decide)

set_option maxHeartbeats 0 in
/-- `hfieldsNd` of `machineClosesAt_of_seqKids` at `mesh2x2`'s data,
restated verbatim and decided: two entries of one callee with the same
argument `let`s and the same field are one entry. Not used by a proof below
(the built `mesh2x2.machine_closes_at` decides its own copy). -/
theorem mesh_fieldsNd : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts[k]).1 =
      ((Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts[k']).1 →
    ((Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts[k]).2.1 =
      ((Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts[k']).2.1 →
    (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.instFields.getD k "" =
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.instFields.getD k' "" →
    k = k' := by decide

/-- **`KidFacts` of every call entry's callee of `mesh2x2`** (`pe`, by
`mesh_entry` and the built `leafKid_facts`). -/
theorem mesh_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    ∀ (k : Nat)
      (hk : k < (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts.length),
      KidFacts mref cref
        ((Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts[k]).1
        (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs
        (Tools.ShippingPortWidthsPure.declWidths
          Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1 := by
  intro k hk
  rw [mesh_entry k hk]
  exact Tools.ShippingLeafKidFacts.leafKid_facts
    (Sparkle.Tests.Compiler.MultiInstance.pe.machine_leafKid hRp) 1

/-- **The first call entry of `mesh2x2` is a sequential child**
(`seqKid_of_leafAt` at entry 0, callee `pe`). -/
theorem mesh_seqKid {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    SeqKid mref cref Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData := by
  have h0 : 0 < (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.insts.length :=
    List.length_pos_iff.mpr mesh_insts
  refine Tools.ShippingSlotlessClk.seqKid_of_leafAt (mctx := mctx) (cctx := cctx) 0 h0
    (dk := Sparkle.Tests.Compiler.MultiInstance.pe.machineData) ?_
  rw [mesh_entry 0 h0]
  exact Sparkle.Tests.Compiler.MultiInstance.pe.machine_leafKid hRp

set_option maxHeartbeats 0 in
/-- The two width conditions of `mesh2x2` against `pe`'s data. -/
theorem mesh_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData 7
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs) =
      true := by
  first | decide | decide +kernel

set_option maxHeartbeats 0 in
theorem mesh_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData 7
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 0 in
theorem mesh_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 0 in
/-- **The run's facts of `mesh2x2`'s full-entry module** (`kids_runFactsS`,
second disjunct). -/
theorem mesh_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingSlotlessKidFacts.kids_runFactsS (nDecl := 7)
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_body
    (by decide) (by decide) (by decide)
    mesh_insts (Or.inr (mesh_seqKid hRp)) mesh_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (mesh_kids hRp) mesh_callWidths
    hB hcore hpost entry closes

set_option maxHeartbeats 0 in
/-- **The output check at depth 1 under the statement-kind gate** (the built
`kids_outsCheck`: no hypothesis on the slots). -/
theorem mesh_outsG1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck (nDecl := 7)
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_body
    (by decide) (by decide) (by decide)
    mesh_insts
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (mesh_kids hRp)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 0 in
/-- **The children's masked outputs** (the built `kids_maskedN`: no
hypothesis on the slots). -/
theorem mesh_maskedG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFacts.kids_maskedN (nDecl := 7)
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_body
    (by decide) (by decide) (by decide)
    mesh_insts mesh_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (mesh_kids hRp)
    hB hcore hpost entry closes

set_option maxHeartbeats 0 in
/-- **`designCheck` at depth 1 of the shipped module, with no check premise**
(`kids_designCheckS`, second disjunct). -/
theorem mesh_designP1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2 [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
      (Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingSlotlessKidFacts.kids_designCheckS (nDecl := 7)
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machineData
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_body
    (by decide) (by decide) (by decide)
    mesh_insts (Or.inr (mesh_seqKid hRp)) mesh_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (mesh_kids hRp) mesh_callWidths mesh_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (mesh_outChars o ho))
    (by decide)

end Tests.Compiler.NoPortsSlotlessMesh2x2Test

/-! ## 4. The endpoint, its closed form, the gap theorem -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingNoPortsCommand.generate f 1
      ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_runFacts
      ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_outsG1
      ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_maskedG
      ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_designP1
  let closed := Tools.ShippingMachineClosesGen.closedName name
  let ok ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingMachineClosesAtGen.closeEndpointAt f (f ++ `machine_closes_at) name closed
  unless ok do throwError "{name}: no MachineClosesAt premise of {f} to close"
  unless (← Lean.getEnv).contains closed do throwError "{closed}: not added"
  Lean.logInfo m!"NOPORTS SLOTLESS MESH [{name}, {closed}]: the depth-1 endpoint of a parent WITHOUT a register with four calls of DIFFERENT arguments of one leaf register machine, chained through their fields, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — the head and the generator are the built ones (machine_design_noPorts, ShippingNoPortsCommand.generate); the run facts and designCheck by hand from kids_runFactsS / kids_designCheckS at the second disjunct (SeqKid), the output check and the children's bound by the built kids_outsCheck / kids_maskedN"

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.MultiInstance.mesh2x2.machine_design_noPortsNR1_closed

/-! ## 5. The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsSlotlessLib.audit "NOPORTS SLOTLESS MESH"
    ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2
    ``Sparkle.Tests.Compiler.MultiInstance.pe
    [``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_entry,
     ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_fieldsNd,
     ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_kids,
     ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_seqKid,
     ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_runFacts,
     ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_outsG1,
     ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_maskedG,
     ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_designP1]
    ``Tests.Compiler.NoPortsSlotlessMesh2x2Test.mesh_noSlots
