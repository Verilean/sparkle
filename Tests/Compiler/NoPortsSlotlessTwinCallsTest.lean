import Tests.Compiler.NoPortsSlotlessLib

/-! # `twinCalls`: a parent WITHOUT a register, two `let`-bound calls with IDENTICAL arguments of a sequential child — the depth-1 SV endpoint with no compiler-check premise (G1, unit U5a, round par/a-21)

`Sparkle.Tests.Compiler.MultiInstance.twinCalls`
(`Tests/Compiler/MultiInstanceTest.lean:65`):

    def twinCalls {dom : DomainConfig} (x y w : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
      let e1 := pe x y w
      let e2 := pe x y w
      e1.aOut + e2.pOut

Callee: the LEAF REGISTER machine `pe` (as `engineOnce`). MEASURED at
23a6f28c (`docs/parallel/verification-a20.md`): `nDecl = 4`, slots `0`,
lets `3`, every call entry of `pe`; `#machine_design_svNR twinCalls 1` and
`#machine_closes_at twinCalls` go through (log-only try, nothing kept).

This file is `Tests/Compiler/NoPortsSlotlessEngineOnceTest.lean` (BUILT) at
`twinCalls`'s data, step for step; the shared meta code (data log, audit)
is `Tests/Compiler/NoPortsSlotlessLib.lean`. `pe.machine_closes`,
`pe.seq_child_runN`, `pe.machine_leafKid` are IMPORTED from the engineOnce
test, not recreated.

## The steps (each THROWS where it fails)

1. the reader data of `pe` and `twinCalls`: LOGGED (one line per call
   entry, and the `FIELDSND` evaluation), then asserted;
2. the BASE endpoint by the BUILT commands: `#machine_design_svNR twinCalls 1`
   and `#machine_closes_at twinCalls`;
3. by hand, the four run hypotheses of
   `Tools.ShippingNoPorts.machine_design_noPorts`: `tw_runFacts`
   (`kids_runFactsS`), `tw_outsG1` (`kids_outsCheck`), `tw_maskedG`
   (`kids_maskedN`), `tw_designP1` (`kids_designCheckS`) — `KidFacts` of
   every entry through ONE decided statement (`tw_entry`: every entry's
   callee is `pe`) and the built `leafKid_facts`; `SeqKid` by
   `seqKid_of_leafAt` at entry 0;
4. the endpoint `twinCalls.machine_design_noPortsNR1` by the BUILT
   `Tools.ShippingNoPortsCommand.generate`, its `_closed` form by the BUILT
   `closeEndpointAt`, the gap theorem by `#machine_goal_gap_of`;
5. the audit (`NoPortsSlotlessLib.audit`).

## The hypothesis that reads the argument `let`s

None of the four run theorems has one: `callWidthsOk` / `callArgsOk` are
stated per entry against the constant tables of `pe` and are indifferent to
two entries sharing their arguments. The one hypothesis on the path whose
truth depends on the entries' arguments is `hfieldsNd` of
`machineClosesAt_of_seqKids` (inside `twinCalls.machine_closes_at`, decided
by the built generator). It is restated and decided here as `tw_fieldsNd`
(not used by a proof: the kernel's evaluation, recorded). INFERRED from the
source and `lets = 3` (the three argument `let`s are shared, issue #107's
dedup): the entries are `(pe, same args, aOut)` and `(pe, same args, pOut)`
— `hfieldsNd` holds by the FIELD clause, the arguments do not separate
them. The `FIELDSND` log line of step 1 is the measurement.

## EXPECTED (stated before the build)

`twinCalls.machine_design_noPortsNR1_closed`: binders — the run,
`MachineDefines twinCalls`, `MachineDefines pe`; under the existentials one
antecedent, `ChildBnd ∧ MachineDefines pe` (ALLOWED). Against
`twinCalls.machine_design_svNR1`: `shipsHierCheck`, `kidsMaskedN`,
`designCheck`, `outsCheck` absent, nothing added.

## SCOPE

As the engineOnce test: one declaration, depth 1, data conditions decided
per declaration (conditions, not reductions), compiler guards with
fallback, `DesignSV` of the module list — not the SV string, not `#sim`;
the run, the reflections and `ChildBnd` stay premises.

WRITTEN, NOT BUILT. -/

/-! ## 1. The reader data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let pe := ``Sparkle.Tests.Compiler.MultiInstance.pe
  let f := ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
  let rp ← Tests.Compiler.NoPortsSlotlessLib.logData "NOPORTS SLOTLESS TWIN" pe
  let r ← Tests.Compiler.NoPortsSlotlessLib.logData "NOPORTS SLOTLESS TWIN" f
  unless r.nDecl == 4 do throwError "{f}: nDecl = {r.nDecl}, the hand theorems are written for 4"
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
#machine_design_svNR Sparkle.Tests.Compiler.MultiInstance.twinCalls 1

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.MultiInstance.twinCalls

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
  for n in [f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1, f ++ `machine_closes_at] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
  let (lines, _) ← Tests.Compiler.NoPortsTest.premiseLines (f ++ `machine_design_svNR1)
  let clInfo ← Lean.getConstInfo (f ++ `machine_closes_at)
  let clT := clInfo.type
  Lean.logInfo m!"NOPORTS SLOTLESS TWIN BASE {f}: machine_ships_hierNR1, machine_design_svNR1 and machine_closes_at generated by the built commands, standard axioms; the base endpoint's premises:\n{String.intercalate "\n" lines.toList}\nthe closing theorem: {clT}"

/-! ## 3. The four run hypotheses, by hand -/

namespace Tests.Compiler.NoPortsSlotlessTwinCallsTest
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingSlotlessClk (SeqKid)

/-- Every call entry of `twinCalls` is of `pe` (ONE decided statement over
the entries of the reflected data, whatever their count). -/
theorem tw_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts[k]).1 =
      ``Sparkle.Tests.Compiler.MultiInstance.pe := by decide

theorem tw_insts :
    (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

theorem tw_general :
    (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.instFields ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

/-- `twinCalls` has NO register (the reflected data). -/
theorem tw_noSlots :
    (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.layout.slots = [] :=
  List.length_eq_zero_iff.mp (by decide)

/-- `hfieldsNd` of `machineClosesAt_of_seqKids` at `twinCalls`'s data,
restated verbatim and decided: two entries of one callee with the same
argument `let`s and the same field are one entry. Not used by a proof below
(the built `twinCalls.machine_closes_at` decides its own copy). -/
theorem tw_fieldsNd : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts[k]).1 =
      ((Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts[k']).1 →
    ((Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts[k]).2.1 =
      ((Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts[k']).2.1 →
    (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.instFields.getD k "" =
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.instFields.getD k' "" →
    k = k' := by decide

/-- **`KidFacts` of every call entry's callee of `twinCalls`** (`pe`, by
`tw_entry` and the built `leafKid_facts`). -/
theorem tw_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    ∀ (k : Nat)
      (hk : k < (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts.length),
      KidFacts mref cref
        ((Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts[k]).1
        (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs
        (Tools.ShippingPortWidthsPure.declWidths
          Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1 := by
  intro k hk
  rw [tw_entry k hk]
  exact Tools.ShippingLeafKidFacts.leafKid_facts
    (Sparkle.Tests.Compiler.MultiInstance.pe.machine_leafKid hRp) 1

/-- **The first call entry of `twinCalls` is a sequential child**
(`seqKid_of_leafAt` at entry 0, callee `pe`). -/
theorem tw_seqKid {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    SeqKid mref cref Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData := by
  have h0 : 0 < (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.insts.length :=
    List.length_pos_iff.mpr tw_insts
  refine Tools.ShippingSlotlessClk.seqKid_of_leafAt (mctx := mctx) (cctx := cctx) 0 h0
    (dk := Sparkle.Tests.Compiler.MultiInstance.pe.machineData) ?_
  rw [tw_entry 0 h0]
  exact Sparkle.Tests.Compiler.MultiInstance.pe.machine_leafKid hRp

/-- The two width conditions of `twinCalls` against `pe`'s data. -/
theorem tw_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData 4
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs) =
      true := by
  first | decide | decide +kernel

theorem tw_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData 4
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) = true := by
  first | decide | decide +kernel

theorem tw_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `twinCalls`'s full-entry module** (`kids_runFactsS`,
second disjunct). -/
theorem tw_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.twinCalls [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingSlotlessKidFacts.kids_runFactsS (nDecl := 4)
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_body
    (by decide) (by decide) (by decide)
    tw_insts (Or.inr (tw_seqKid hRp)) tw_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (tw_kids hRp) tw_callWidths
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 1 under the statement-kind gate** (the built
`kids_outsCheck`: no hypothesis on the slots). -/
theorem tw_outsG1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.twinCalls [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck (nDecl := 4)
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_body
    (by decide) (by decide) (by decide)
    tw_insts
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (tw_kids hRp)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **The children's masked outputs** (the built `kids_maskedN`: no
hypothesis on the slots). -/
theorem tw_maskedG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.twinCalls [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFacts.kids_maskedN (nDecl := 4)
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_body
    (by decide) (by decide) (by decide)
    tw_insts tw_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (tw_kids hRp)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 1 of the shipped module, with no check premise**
(`kids_designCheckS`, second disjunct). -/
theorem tw_designP1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.twinCalls [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
      (Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingSlotlessKidFacts.kids_designCheckS (nDecl := 4)
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machineData
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_body
    (by decide) (by decide) (by decide)
    tw_insts (Or.inr (tw_seqKid hRp)) tw_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (tw_kids hRp) tw_callWidths tw_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (tw_outChars o ho))
    (by decide)

end Tests.Compiler.NoPortsSlotlessTwinCallsTest

/-! ## 4. The endpoint, its closed form, the gap theorem -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingNoPortsCommand.generate f 1
      ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_runFacts
      ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_outsG1
      ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_maskedG
      ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_designP1
  let closed := Tools.ShippingMachineClosesGen.closedName name
  let ok ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingMachineClosesAtGen.closeEndpointAt f (f ++ `machine_closes_at) name closed
  unless ok do throwError "{name}: no MachineClosesAt premise of {f} to close"
  unless (← Lean.getEnv).contains closed do throwError "{closed}: not added"
  Lean.logInfo m!"NOPORTS SLOTLESS TWIN [{name}, {closed}]: the depth-1 endpoint of a parent WITHOUT a register with two let-bound calls of identical arguments of a leaf register machine, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — the head and the generator are the built ones (machine_design_noPorts, ShippingNoPortsCommand.generate); the run facts and designCheck by hand from kids_runFactsS / kids_designCheckS at the second disjunct (SeqKid), the output check and the children's bound by the built kids_outsCheck / kids_maskedN"

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.MultiInstance.twinCalls.machine_design_noPortsNR1_closed

/-! ## 5. The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsSlotlessLib.audit "NOPORTS SLOTLESS TWIN"
    ``Sparkle.Tests.Compiler.MultiInstance.twinCalls
    ``Sparkle.Tests.Compiler.MultiInstance.pe
    [``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_entry,
     ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_fieldsNd,
     ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_kids,
     ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_seqKid,
     ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_runFacts,
     ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_outsG1,
     ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_maskedG,
     ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_designP1]
    ``Tests.Compiler.NoPortsSlotlessTwinCallsTest.tw_noSlots
