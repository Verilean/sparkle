import Tests.Compiler.NoPortsTest
import Tests.Compiler.ShippingMachineSeqLinkedTest
import Tools.ShippingSlotlessKidFacts
import Tools.ShippingLeafKidFacts
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingFinalGoalCommand
import Tools.ShippingNoPortsCommand

/-! # `engineOnce`: a parent WITHOUT a register, of a sequential child — the depth-1 SV endpoint with no compiler-check premise (G1, unit U5a, round par/a-20)

`Sparkle.Tests.Compiler.MultiInstance.engineOnce`
(`Tests/Compiler/MultiInstanceTest.lean:58`):

    def engineOnce {dom : DomainConfig} (x y w : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
      let e := pe x y w
      e.aOut + e.pOut

Its callee `pe` (`MultiInstanceTest.lean:35`) is a LEAF REGISTER machine
(two `Signal.reg`, no call, two outputs `aOut`, `pOut`). `engineOnce` has
no `Signal.reg`: its module's `clk` and `rst` inputs are the ones
`withClockFor` appends for the sequential child.

Until this file `engineOnce` had ONE shipping endpoint,
`engineOnce.machine_ships_hier` (`Tests/Compiler/ShippingMachineSeqLinkedTest.lean:48`;
premises `shipsHierCheck`, `Bd`), and no design-level endpoint: no
generator REFUSES it at the base (read: `#machine_design_svNR`,
`#machine_design_svR0`, `#machine_design_sv0` have no test on the slots);
they were never run on it. `#machine_no_ports` refuses it (`scopeP`:
"parent without a register").

## The steps (each THROWS where it fails)

1. the reader data of `pe`, `engineOnce`, `twinCalls`, `mesh2x2`: LOGGED,
   then the shapes the hand theorems rely on are asserted;
2. the BASE endpoint by the BUILT commands, run on `engineOnce` for the
   first time: `#machine_design_svNR engineOnce 1`
   (`engineOnce.machine_ships_hierNR1`, `engineOnce.machine_design_svNR1`)
   and `#machine_closes_at engineOnce` (`machineClosesAt_of_seqKids`: it has
   no hypothesis on the slots);
3. `pe.machine_leafKid` by the BUILT `leafKidTheorem`;
4. by hand, the four run hypotheses of
   `Tools.ShippingNoPorts.machine_design_noPorts`: `engine_runFacts`
   (`kids_runFactsS`), `engine_outsG1` (`kids_outsCheck`, built),
   `engine_maskedG` (`kids_maskedN`, built), `engine_designP1`
   (`kids_designCheckS`) — `KidFacts` of `pe` by the built `leafKid_facts`,
   and `SeqKid` (the second disjunct of `hck`) by `seqKid_of_leafAt`;
5. the endpoint `engineOnce.machine_design_noPortsNR1` by the BUILT
   `Tools.ShippingNoPortsCommand.generate`, its `_closed` form by the BUILT
   `closeEndpointAt`, the gap theorem by `#machine_goal_gap_of`;
6. the audit, as `NoPortsTest`: standard axioms; no checker constant in an
   endpoint statement while the base endpoint mentions the four; no gap
   hypothesis; every premise of the closed form ALLOWED (the complete list
   LOGGED as `NOPORTS PREMISE` lines);
7. LOG ONLY, nothing kept: whether the two base commands go through on
   `twinCalls` and `mesh2x2`.

## EXPECTED (stated before the build)

`engineOnce.machine_design_noPortsNR1_closed`: binders — the run,
`MachineDefines engineOnce`, `MachineDefines pe`; under the existentials one
antecedent, `ChildBnd ∧ MachineDefines pe` (ALLOWED). Against
`engineOnce.machine_design_svNR1`: `shipsHierCheck`, `kidsMaskedN`,
`designCheck`, `outsCheck` absent, nothing added.

## SCOPE (binding for any claim from this file)

One declaration, depth 1; a parent WITHOUT a register under the general
closing whose callees are all one leaf register machine. Data conditions
decided per declaration by the kernel (`callsOk 4`, slot lengths, no late
domain binder, `insts ≠ []`, `instFields ≠ []`, output width / name /
scalar, no memory callee, `callWidthsOk` / `callArgsOk` against `pe`'s data,
every entry's callee is `pe`, `pe.machine_leafKid`'s own, the closing's):
conditions, not reductions — a declaration where one fails is not covered.
The compiler's guards with fallback. The conclusion is about
`DesignSV (childMap D.modules) 1 (checkedOptimize b)` — the module list,
not the SV string, not `#sim`. The run, the reflections and `ChildBnd` stay
premises (no runtime model). NOT covered: `twinCalls`, `mesh2x2` (step 7
only logs their base commands), a generator, a parent without a register of
combinational children.

WRITTEN, NOT BUILT. -/

/-! ## 1. The reader data: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let pe := ``Sparkle.Tests.Compiler.MultiInstance.pe
  let f := ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
  let rp ← Tools.ShippingMachineCommand.readMachine pe
  Lean.logInfo m!"NOPORTS SLOTLESS DATA {pe}: nDecl={rp.nDecl}, slots={rp.shape.layout.slots.length}, lets={rp.shape.layout.lets}, call entries {rp.shape.insts.map (·.1)}, instFields={rp.shape.instFields}, outputs {rp.shape.layout.outs.map (·.name)}"
  for g in [f, ``Sparkle.Tests.Compiler.MultiInstance.twinCalls,
      ``Sparkle.Tests.Compiler.MultiInstance.mesh2x2] do
    let r ← Tools.ShippingMachineCommand.readMachine g
    Lean.logInfo m!"NOPORTS SLOTLESS DATA {g}: nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, lets={r.shape.layout.lets}, call entries {r.shape.insts.map (·.1)}, argument lets {r.shape.insts.map (·.2.1)}, instFields={r.shape.instFields}, outputs {r.shape.layout.outs.map (·.name)}"
  let r ← Tools.ShippingMachineCommand.readMachine f
  unless r.nDecl == 4 do throwError "{f}: nDecl = {r.nDecl}, the hand theorems are written for 4"
  unless r.shape.layout.slots.isEmpty do
    throwError "{f}: {r.shape.layout.slots.length} slots — not a parent without a register"
  if r.shape.insts.isEmpty then throwError "{f}: no call"
  if r.shape.instFields.isEmpty then throwError "{f}: instFields = [] — not the general closing"
  unless (r.shape.insts.map (·.1)).eraseDups == [pe] do
    throwError "{f}: the call entries are {r.shape.insts.map (·.1)}, expected every entry to be {pe}"
  unless rp.shape.insts.isEmpty do throwError "{pe}: has calls — not a leaf"
  if rp.shape.layout.slots.isEmpty then throwError "{pe}: no register — not a sequential child"
  for n in [f ++ `machineData, f ++ `machine_ok, f ++ `machine_body, f ++ `machine_ships_hier,
      pe ++ `machineData, pe ++ `machine_ok, pe ++ `machine_body] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not in the imports (this file builds on it)"
  for n in [f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1, f ++ `machine_closes_at,
      f ++ `machine_design_noPortsNR1, f ++ `machine_design_noPortsNR1_closed,
      pe ++ `machine_leafKid] do
    if (← Lean.getEnv).contains n then throwError "{n}: exists already"

/-! ## 2. The base endpoint and the closing, by the built commands -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.MultiInstance.engineOnce 1

set_option maxHeartbeats 0 in
#machine_closes_at Sparkle.Tests.Compiler.MultiInstance.engineOnce

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let pe := ``Sparkle.Tests.Compiler.MultiInstance.pe
  let f := ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
  for n in [f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1, f ++ `machine_closes_at,
      pe ++ `machine_closes] do
    unless (← Lean.getEnv).contains n do throwError "{n}: not generated"
    Tests.Compiler.NoPortsTest.stdAxioms n
  let (lines, _) ← Tests.Compiler.NoPortsTest.premiseLines (f ++ `machine_design_svNR1)
  let clInfo ← Lean.getConstInfo (f ++ `machine_closes_at)
  let clT := clInfo.type
  Lean.logInfo m!"NOPORTS SLOTLESS BASE {f}: machine_ships_hierNR1, machine_design_svNR1 and machine_closes_at generated by the built commands (first run on a parent without a register), standard axioms; the base endpoint's premises:\n{String.intercalate "\n" lines.toList}\nthe closing theorem: {clT}"

/-! ## 3. The leaf child's premises (`LeafKid`) -/

set_option maxHeartbeats 0 in
run_cmd do
  let n ← Lean.Elab.Command.withScope
    (fun s => { s with opts := Lean.Elab.async.set s.opts false })
    (Tools.ShippingNoPortsCommand.leafKidTheorem ``Sparkle.Tests.Compiler.MultiInstance.pe)
  Lean.logInfo m!"NOPORTS SLOTLESS LEAFKID {n}: generated by the built leafKidTheorem"

/-! ## 4. The four run hypotheses, by hand -/

namespace Tests.Compiler.NoPortsSlotlessEngineOnceTest
open Tools.ShippingKidFacts (KidFacts)
open Tools.ShippingSlotlessClk (SeqKid)

/-- Every call entry of `engineOnce` is of `pe` (decided on the reflected data). -/
theorem engine_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.insts[k]).1 =
      ``Sparkle.Tests.Compiler.MultiInstance.pe := by decide

theorem engine_insts :
    (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.insts ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

theorem engine_general :
    (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.instFields ≠ [] :=
  fun h0 => absurd (congrArg List.length h0) (by decide)

/-- `engineOnce` has NO register (the reflected data). -/
theorem engine_noSlots :
    (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.layout.slots = [] :=
  List.length_eq_zero_iff.mp (by decide)

/-- **`KidFacts` of every call entry's callee of `engineOnce`** (the leaf
register machine `pe`, by the built `leafKid_facts`). -/
theorem engine_kids {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    ∀ (k : Nat)
      (hk : k < (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.insts.length),
      KidFacts mref cref
        ((Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.insts[k]).1
        (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs
        (Tools.ShippingPortWidthsPure.declWidths
          Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1 := by
  intro k hk
  rw [engine_entry k hk]
  exact Tools.ShippingLeafKidFacts.leafKid_facts
    (Sparkle.Tests.Compiler.MultiInstance.pe.machine_leafKid hRp) 1

/-- **The first call entry of `engineOnce` is a sequential child**: the second
disjunct of `hck` (`seqKid_of_leafAt` at entry 0, callee `pe`). -/
theorem engine_seqKid {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    SeqKid mref cref Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData := by
  have h0 : 0 < (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.insts.length :=
    List.length_pos_iff.mpr engine_insts
  refine Tools.ShippingSlotlessClk.seqKid_of_leafAt (mctx := mctx) (cctx := cctx) 0 h0
    (dk := Sparkle.Tests.Compiler.MultiInstance.pe.machineData) ?_
  rw [engine_entry 0 h0]
  exact Sparkle.Tests.Compiler.MultiInstance.pe.machine_leafKid hRp

/-- The two width conditions of `engineOnce` against `pe`'s data. -/
theorem engine_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData 4
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs) =
      true := by
  first | decide | decide +kernel

theorem engine_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData 4
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) = true := by
  first | decide | decide +kernel

theorem engine_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxHeartbeats 4000000 in
/-- **The run's facts of `engineOnce`'s full-entry module** (`kids_runFactsS`,
second disjunct: `"rst"` is an input because the child is sequential). -/
theorem engine_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.engineOnce [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
      (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
      (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingSlotlessKidFacts.kids_runFactsS (nDecl := 4)
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_body
    (by decide) (by decide) (by decide)
    engine_insts (Or.inr (engine_seqKid hRp)) engine_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (engine_kids hRp) engine_callWidths
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **The output check at depth 1 under the statement-kind gate** (the built
`kids_outsCheck`: no hypothesis on the slots). -/
theorem engine_outsG1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.engineOnce [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
      (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
      (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingKidFacts.kids_outsCheck (nDecl := 4)
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_body
    (by decide) (by decide) (by decide)
    engine_insts
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (engine_kids hRp)
    hB hcore hpost entry closes hg

set_option maxHeartbeats 4000000 in
/-- **The children's masked outputs** (the built `kids_maskedN`: no
hypothesis on the slots). -/
theorem engine_maskedG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.engineOnce [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
      (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
      (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidFacts.kids_maskedN (nDecl := 4)
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_body
    (by decide) (by decide) (by decide)
    engine_insts engine_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (engine_kids hRp)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth 1 of the shipped module, with no check premise**
(`kids_designCheckS`, second disjunct: the parent's `clk` / `rst` are one
bit in the emitter's width map because the child is sequential). -/
theorem engine_designP1 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.MultiInstance.engineOnce [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
      (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
      (Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hRp : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.MultiInstance.pe
      (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 1
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingSlotlessKidFacts.kids_designCheckS (nDecl := 4)
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machineData
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_ok
    Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_body
    (by decide) (by decide) (by decide)
    engine_insts (Or.inr (engine_seqKid hRp)) engine_general
    (by decide) (by decide)
    (fun _ => (Sparkle.Tests.Compiler.MultiInstance.pe.machineData).shape.layout.outs)
    (fun _ => Tools.ShippingPortWidthsPure.declWidths
      Sparkle.Tests.Compiler.MultiInstance.pe.machineData) 1
    (engine_kids hRp) engine_callWidths engine_callArgs
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (engine_outChars o ho))
    (by decide)

open Lean Meta Elab Command in
/-- `#slotless_try "tag" in cmd`: elaborate `cmd`, LOG whether it went
through, and put the environment and the message log back in BOTH cases —
nothing is kept. -/
elab "#slotless_try " tag:str " in " c:command : command => do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let before := savedMsgs.toList.length
  let thrown ← try
      elabCommand c
      pure none
    catch ex => pure (some (← ex.toMessageData.toString))
  let msgs := (← get).messages.toList.drop before
  let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
  let failure : Option String := match thrown with
    | some msg => some msg
    | none => if errs.isEmpty then none else some (String.intercalate " | " (errs.take 2))
  setEnv savedEnv
  modify fun s => { s with messages := savedMsgs }
  match failure with
  | some msg => logInfo m!"NOPORTS SLOTLESS TRY {tag.getString}: FAILED — {msg}"
  | none => logInfo m!"NOPORTS SLOTLESS TRY {tag.getString}: OK (nothing kept)"

end Tests.Compiler.NoPortsSlotlessEngineOnceTest

/-! ## 5. The endpoint, its closed form, the gap theorem -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingNoPortsCommand.generate f 1
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_runFacts
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_outsG1
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_maskedG
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_designP1
  let closed := Tools.ShippingMachineClosesGen.closedName name
  let ok ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingMachineClosesAtGen.closeEndpointAt f (f ++ `machine_closes_at) name closed
  unless ok do throwError "{name}: no MachineClosesAt premise of {f} to close"
  unless (← Lean.getEnv).contains closed do throwError "{closed}: not added"
  Lean.logInfo m!"NOPORTS SLOTLESS [{name}, {closed}]: the depth-1 endpoint of a parent WITHOUT a register whose callee is a leaf register machine, without the portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck and kidsMaskedN antecedents — the head and the generator are the built ones (machine_design_noPorts, ShippingNoPortsCommand.generate); the run facts and designCheck by hand from kids_runFactsS / kids_designCheckS at the second disjunct (SeqKid: the child is sequential), the output check and the children's bound by the built kids_outsCheck / kids_maskedN"

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.MultiInstance.engineOnce.machine_design_noPortsNR1_closed

/-! ## 6. The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.MultiInstance.engineOnce
  let pe := ``Sparkle.Tests.Compiler.MultiInstance.pe
  let old := f ++ `machine_design_svNR1
  let openN := f ++ `machine_design_noPortsNR1
  let closed := f ++ `machine_design_noPortsNR1_closed
  let gap := f ++ `machine_design_noPortsNR1_closed_gap
  -- (a) standard axioms: the new general theorems, the built ones they
  -- apply, the hand lemmas, the endpoints
  for n in [``Tools.ShippingSlotlessClk.inputs_tail_shape,
      ``Tools.ShippingSlotlessClk.weS_clk_rst_tail,
      ``Tools.ShippingSlotlessClk.seqKid_of_leafAt,
      ``Tools.ShippingSlotlessClk.core_seqKid_inputs,
      ``Tools.ShippingSlotlessClk.core_slotless_seq,
      ``Tools.ShippingSlotlessClk.core_raw_factsS,
      ``Tools.ShippingSlotlessClk.core_clkS,
      ``Tools.ShippingSlotlessKidFacts.core_runFactsS,
      ``Tools.ShippingSlotlessKidFacts.core_designCheck_runS,
      ``Tools.ShippingSlotlessKidFacts.kids_runFactsS,
      ``Tools.ShippingSlotlessKidFacts.kids_designCheckS,
      ``Tools.ShippingSlotlessKidFacts.kids_runFacts_again,
      ``Tools.ShippingSlotlessKidFacts.kids_designCheck_again,
      ``Tools.ShippingKidFacts.kids_outsCheck,
      ``Tools.ShippingKidFacts.kids_maskedN,
      ``Tools.ShippingLeafKidFacts.leafKid_facts,
      ``Tools.ShippingNoPorts.machine_design_noPorts,
      pe ++ `machine_leafKid,
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_kids,
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_seqKid,
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_noSlots,
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_runFacts,
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_outsG1,
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_maskedG,
      ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_designP1,
      old, openN, closed, gap] do
    unless (← Lean.getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- (b) no endpoint statement mentions a checker constant
  for n in [openN, closed, gap] do
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
  -- (e) the data: the parent has NO register (a theorem about the reflected
  -- data, not the reader's word)
  let nsInfo ← Lean.getConstInfo ``Tests.Compiler.NoPortsSlotlessEngineOnceTest.engine_noSlots
  let nsT := nsInfo.type
  -- (f) no gap hypothesis
  let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames gap
  unless gaps.isEmpty do
    throwError "{f}: the gap hypotheses are {gaps}, expected none"
  -- (g) the complete premise list of the closed endpoint (LOGGED), every one ALLOWED
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty do
    throwError "{closed}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  Lean.logInfo m!"NOPORTS SLOTLESS AUDIT {f}: {openN}, {closed} and {gap} on standard axioms, with the new general theorems of Tools.ShippingSlotlessClk (core_seqKid_inputs, core_slotless_seq, core_raw_factsS, core_clkS, seqKid_of_leafAt) and Tools.ShippingSlotlessKidFacts (core_runFactsS, core_designCheck_runS, kids_runFactsS, kids_designCheckS), the built kids_outsCheck / kids_maskedN / leafKid_facts / machine_design_noPorts and the hand lemmas engine_kids, engine_seqKid, engine_runFacts, engine_outsG1, engine_maskedG, engine_designP1. The parent has no register: {nsT}. No endpoint statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN or hierCheck, while {old} mentions shipsHierCheck, kidsMaskedN, designCheck and outsCheck. MachineClosesAt asked by the open form only. NO gap hypothesis; {lines.size} binders and antecedents of the closed form listed, 0 NOT ALLOWED. SCOPE: one declaration, depth 1, a parent WITHOUT a register under the general closing whose callees are all the leaf register machine {pe}; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim; the run, the reflections and ChildBnd remain premises. NOT covered: twinCalls, mesh2x2, a generator, a parent without a register of combinational children."

/-! ## 7. LOG ONLY: the base commands on the other two parents of `pe` (nothing kept) -/

set_option maxHeartbeats 0 in
#slotless_try "twinCalls: #machine_design_svNR 1" in
  #machine_design_svNR Sparkle.Tests.Compiler.MultiInstance.twinCalls 1

set_option maxHeartbeats 0 in
#slotless_try "twinCalls: #machine_closes_at" in
  #machine_closes_at Sparkle.Tests.Compiler.MultiInstance.twinCalls

set_option maxHeartbeats 0 in
#slotless_try "mesh2x2: #machine_design_svNR 1" in
  #machine_design_svNR Sparkle.Tests.Compiler.MultiInstance.mesh2x2 1

set_option maxHeartbeats 0 in
#slotless_try "mesh2x2: #machine_closes_at" in
  #machine_closes_at Sparkle.Tests.Compiler.MultiInstance.mesh2x2
