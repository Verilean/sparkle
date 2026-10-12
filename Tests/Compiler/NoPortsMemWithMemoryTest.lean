import Tests.Compiler.NoPortsMemWithMemoryLib
import Tests.Compiler.ShippingMachineSeqLoopTest
import Tools.ShippingMemOnlyCloses
import Tools.ShippingNameSep

/-! # `withMemory`: the depth-0 design endpoint of a memory-only parent with a TRANSPORTED endpoint, open and closed (round par/b-17)

`withMemory` (`Tests/Compiler/ShippingMachineFuseTest.lean` 42–51, READ):

    def withMemory (we : Signal defaultDomain Bool) (wd : Signal defaultDomain (BitVec 8)) :
        Signal defaultDomain (BitVec 8) :=
      let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
        let addr := Signal.fst st
        let rd := Signal.memoryComboRead addr wd we addr
        let _dead := Signal.memoryComboRead addr wd we (Signal.pure 0#4)
        let c := innerCnt (rd === (Signal.pure 0#8 : …))
        bundle2 (Signal.register 0#4 (addr + …)) (Signal.register 0#8 (rd + c))
      Signal.snd st

`innerCnt` (17–20) is a helper with its own `Signal.loop` and NO
`@[hardware_module]`: it is inlined, so the compiler reads ONE machine with
the outer loop's registers and the inner loop's, and two memory calls (the
dead one included: "an unused memory is still an instance", file header 12).

## Its endpoints (READ)

| constant | made by | shape |
|---|---|---|
| `withMemory.machine_sound` | `ShippingMachineCommand.generate … (checkCloses := false)` (`ShippingMachineFuseTest` 60) | `loops.length > 1` → `fuseInst` (`ShippingMachineCommand` 2503–2516), then `loopProof` → head `machine_trace_of_loop_causal` (2150) on the FUSED value; then `Eq.mpr (congrArg motive heq)` with `heq : withMemory.machineSourceDecl = withMemory.machineSource` (2560–2576) |
| `withMemory.machine_composedT` | `#machine_composedT` (`ShippingMachineMemLinkedTest` 56) and `#machine_composedTS` (`ShippingMachineSeqLoopTest` 43; `generateAny` routes a memory-only parent to the same generator) | `Eq.mpr (congrArg motive heq) (fun [11 binders] => machine_linkedT_mem [wired twin on the untransported arguments] …)` (`ShippingMachineMemCommand` 59–98) |
| `withMemory.machine_ships_hier` | `#machine_ships_hier` (`ShippingMachineSeqLoopTest` 44) | `machine_ships_hier` on 24 arguments, route `.mem`: `soundL` = the wired twin of the UNTRANSPORTED head (source `srcL` = the fused one), `composed` = the transported `machine_composedT` (source `src` = the declaration's) (`ShippingMachineShipsHierCommand` 50–54, 68–75) |

Against `memCounter`'s: the SAME heads, argument counts and binders; the
only differences are the `Eq.mpr` around `machine_sound` and
`machine_composedT`, and `src ≠ srcL` in `machine_ships_hier` (for
`memCounter` both are `memCounter.machineSource`). INFERRED, LOGGED by the
first command below.

## The memory-only chain on `withMemory`'s data — evaluated BY READING (nothing was run)

PREDICTED data (the first command LOGS the real ones and THROWS on a
difference that makes a hypothesis false): nDecl=2 (`we`, `wd`), slots=3
(`addr`, the result register, `innerCnt`'s), loops=2, call entries
`[SparkleMem.combo.4.8, SparkleMem.combo.4.8]`, instFields=`[out, out]`,
argument lets two lists of 4 that differ in the last (`addr` against the
constant `0#4`), lets=4, binders=11, one output.

| hypothesis | where | status on `withMemory` |
|---|---|---|
| `ok`, `body` | `MemOnlyData` | BUILT constants `withMemory.machine_ok`, `.machine_body` (`ShippingMachineCommand` 2190, 2534–2545) |
| `calls : callsOk 2` | `MemOnlyData` | DECIDED here (`withMemory_calls`); predicted true — NOT MEASURED |
| `slots`, `domB`, `outTy`, `outNames`, `outScalar` | `MemOnlyData` | DECIDED here; predicted true |
| `ins`, `sl`, `fne` (`≠ []`) | `MemOnlyData` | DECIDED here (lengths); the first command throws on `[]` |
| `mem` (every entry a placeholder of widths 4 / 8) | `MemOnlyData` | `withMemory_entry` DECIDED + the BUILT `mem_isMem` |
| `cw : callWidthsOk`, `args : callArgsOk` | `MemOnlyData` | DECIDED here against `memOuts 8` / `memIns 4 8`; predicted true (the operands are `addr` 4, `wd` 8, `we` 1, `addr` or `0#4` 4) |
| the four run hypotheses | `memOnly_runFacts / _outsCheck / _kidsMem / _designCheck` | apply AS IS: they take the core run, the reflection, `MachineClosesAt`, `ChildBnd` and `MemOnlyData` — none mentions the source, so the transport does not reach them |
| `halias` | `machineClosesAt_memOnly` | DECIDED here; predicted true (every `let` is an input, a slot projection or a constant) — NOT MEASURED |
| `hargsN`, `hfield` | 〃 | DECIDED here; the first command checks them on the reader's data |
| `hargsNd` | 〃 | DECIDED here; the two entries have one callee and one field; their argument lists are predicted to differ in the read address. If the compiler bound `addr` and `0#4` to ONE `let` this is FALSE: the first command throws ("hargsNd is FALSE: STOP") |
| `hsep` | 〃 | all entries of ONE placeholder: `sep_of_one` |
| `hparent` | 〃 | `parent_of_one` + `withMemory_notin` (a five-component name does not print as `SparkleMem_combo_4_8`; DECIDED over `Tools.ShippingNameSep.cands`) |
| `hout` | 〃 | DECIDED here; the first command checks the output's first character |

So the chain applies to `withMemory` with NO new general theorem about
memories; what a transported endpoint needs is in the GENERATOR
(`Tests.Compiler.NoPortsMemWithMemory.generateT0`) and one lemma
(`Tools.ShippingMemTransport.composedG_src`).

## What the new statements are relative to

`withMemory` has NO design-level base endpoint. The new statements are NOT
`withMemory.machine_ships_hier` with premises removed. Against it:

1. CONCLUSION: `DesignSV (childMap D.modules) 0 (checkedOptimize b) …` — a
   closed run of the module list exists AND every closed run shows the
   source — under three more use conditions of the emitted widths (inputs,
   start registers, instance states); `machine_ships_hier` concludes
   `runModuleTG flatKS …`, the stateful linked run of the shipped IR module.
2. ANTECEDENTS under the existentials: `machine_ships_hier` has
   `shipsHierCheck (childMap D.modules) b`, its boundary `True`, and
   `kidsMem (childMap D.modules) b.body`; the new statement has ONE,
   `ChildBnd mref cref w` (ADDED). `designCheck` / `outsCheck` are premises
   of neither (they would be of a `machine_design_sv0`, which does not exist).
3. CLOSING: all-worlds `MachineCloses withMemory` (a binder of
   `machine_ships_hier`; undischargeable, `Tools/ShippingMemOnlyAtAll.lean`)
   → `MachineClosesAt withMemory` in the open form → nothing in the closed form.
4. The run and `MachineDefines withMemory` stay.
5. Both are about the declaration's source `withMemory.machineSourceDecl`.

## EXPECTED (stated before the build; the audits THROW otherwise)

| endpoint | premise | predicted state |
|---|---|---|
| `withMemory.machine_design_noPortsR0` (NEW) | `shipsHierCheck (childMap D.modules) b` (of `machine_ships_hier`) | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `kidsMem (childMap D.modules) b.body` (of `machine_ships_hier`) | predicted absent, pending build |
| | boundary `True` (of `machine_ships_hier`) | REPLACED by `ChildBnd mref cref w` — ADDED antecedent (allowed) |
| | `MachineCloses withMemory` (of `machine_ships_hier`) | REPLACED by `MachineClosesAt withMemory` — STILL A PREMISE, the one NOT ALLOWED |
| | `hr`, `MachineDefines withMemory` | stay |
| `withMemory.machine_design_noPortsR0_closed` (NEW) | `MachineClosesAt withMemory` | predicted ABSENT, pending build; nothing added (`withMemory_closes` has no premise) |
| | `hr`, `MachineDefines withMemory`, antecedent `ChildBnd` | stay; all ALLOWED |
| `…_closed_gap` | gap hypotheses | predicted NONE |

SCOPE: one declaration, depth 0, a register parent whose children are
memories only (the inner loop is inlined, not a child), data conditions
decided per declaration (conditions, not reductions), compiler guards with
fallback, `DesignSV` of the module list — not the SV string, not `#sim`.
The run, the reflection of `withMemory` and `ChildBnd` at the start world
remain premises.

WRITTEN, NOT BUILT (par/b-17). -/

/-! ## The reader's data and the endpoints' shapes: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemWithMemory.logData
    ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory 2
    [Sparkle.Compiler.MachMemory.memChildName true 4 8]

namespace Tests.Compiler.NoPortsMemWithMemoryTest
open Tools.ShippingMemKid (memOuts memIns)

/-! ## The data conditions (decided on the reflected data) -/

/-- Every call entry of `withMemory` is of the memory placeholder. -/
theorem withMemory_entry : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts[k]).1 =
      Sparkle.Compiler.MachMemory.memChildName true 4 8 := by
  first | decide | decide +kernel

theorem withMemory_calls :
    (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).callsOk 2 =
      true := by
  first | decide | decide +kernel

theorem withMemory_slots :
    (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).ss.length =
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.layout.slots.length := by
  first | decide | decide +kernel

theorem withMemory_domB :
    ∀ b ∈ (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.binders.drop 2,
      b.2 ≠ .domain := by
  first | decide | decide +kernel

theorem withMemory_outTy :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.layout.outs,
      o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem withMemory_callWidths : Tools.ShippingCallWidths.callWidthsOk
    Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData 2
    (fun _ => memOuts 8) = true := by
  first | decide | decide +kernel

theorem withMemory_callArgs : Tools.ShippingPortsMatchRaw.callArgsOk
    Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData 2
    (fun _ => memIns 4 8) = true := by
  first | decide | decide +kernel

theorem withMemory_outChars :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.layout.outs,
      ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

theorem withMemory_outScalar :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.layout.outs,
      Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

/-- **The data conditions of `withMemory`** (every field decided above or a
generated constant of the declaration). -/
theorem withMemory_data : Tools.ShippingMemOnly.MemOnlyData
    Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData 2 4 8 :=
  Tools.ShippingMemOnly.MemOnlyData.mk
    Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_ok
    Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_body
    withMemory_calls withMemory_slots withMemory_domB
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    withMemory_outTy
    (fun k hk => Exists.intro true
      ((congrArg Sparkle.Compiler.MachMemory.memChild? (withMemory_entry k hk)).trans
        Tests.Compiler.NoPortsMemOnlyCounterTest.mem_isMem))
    withMemory_callWidths withMemory_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (withMemory_outChars o ho))
    withMemory_outScalar

/-! ## The four run hypotheses of the head (`memOnly_*` at `withMemory`'s data) -/

/-- **The run's facts of `withMemory`'s full-entry module** (`memOnly_runFacts`). -/
theorem withMemory_runFacts {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingGuardsSound.RunFacts (Tools.ShippingMachineLinked.childMap D.modules) b :=
  Tools.ShippingMemOnly.memOnly_runFacts withMemory_data hB hcore hpost entry closes

/-- **The output check at depth 0 under the statement-kind gate**
(`memOnly_outsCheck`). -/
theorem withMemory_outsG0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_outsCheck withMemory_data hB hcore hpost entry closes hg

/-- **The children's bound of the memory route, `kidsMem`** (`memOnly_kidsMem`). -/
theorem withMemory_kidsMemG {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingMachineShipsHier.kidsMem (Tools.ShippingMachineLinked.childMap D.modules)
      b.body = true :=
  Tools.ShippingMemOnly.memOnly_kidsMem withMemory_data hB hcore hpost entry closes

/-- **`designCheck` at depth 0 of the shipped module, with no check premise**
(`memOnly_designCheck`). -/
theorem withMemory_designP0 {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w1 : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore
        ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingMemOnly.memOnly_designCheck withMemory_data hB hcore hpost entry closes

/-! ## The data conditions of the closing (decided on the reflected data) -/

theorem withMemory_alias :
    (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).letsAliasOk = true := by
  first | decide | decide +kernel

theorem withMemory_argsN : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts[k]).2.1.length = 4 := by
  first | decide | decide +kernel

theorem withMemory_field : ∀ (k : Nat),
    k < (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts.length →
    (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.instFields.getD k "" = "out" := by
  first | decide | decide +kernel

theorem withMemory_argsNd : ∀ (k : Nat)
    (hk : k < (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts.length)
    (k' : Nat)
    (hk' : k' < (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts.length),
    ((Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts[k]).1 =
      ((Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts[k']).1 →
    ((Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts[k]).2.1 =
      ((Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.insts[k']).2.1 →
    k = k' := by
  first | decide | decide +kernel

theorem withMemory_outHead :
    ∀ o ∈ (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape.layout.outs,
      o.name.toList.head? ≠ some 'i' := by
  first | decide | decide +kernel

/-- **The data conditions of the closing of `withMemory`**. -/
theorem withMemory_closeData : Tools.ShippingMemOnlyCloses.MemOnlyCloseData
    Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData :=
  Tools.ShippingMemOnlyCloses.MemOnlyCloseData.mk withMemory_alias withMemory_argsN
    withMemory_field withMemory_argsNd withMemory_outHead

/-- `withMemory` does not print as the memory module's name. -/
theorem withMemory_notin :
    (``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory : Lean.Name).toString ∉
      [(Sparkle.Compiler.MachMemory.memModule true 4 8).1.name] :=
  Tools.ShippingNameSep.not_mem_of _ _ (by first | decide | decide +kernel)

set_option maxHeartbeats 4000000 in
/-- **`MachineClosesAt withMemory`** — a memory-only parent, from decided
reader data only: NO premise (the transport does not reach the closing: it
is a statement about the reader's shape). -/
theorem withMemory_closes {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State} :
    Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref
      ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
      (Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machineData).shape :=
  Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData
    withMemory_data withMemory_closeData
    (Tools.ShippingMemOnlyCloses.sep_of_one withMemory_entry)
    (Tools.ShippingMemOnlyCloses.parent_of_one withMemory_entry
      Tests.Compiler.NoPortsMemOnlyCounterTest.mem_isMem withMemory_notin)

end Tests.Compiler.NoPortsMemWithMemoryTest

/-! ## The open endpoint (`MachineClosesAt` still a binder) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
  let name ← Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tests.Compiler.NoPortsMemWithMemory.generateT0 f
      ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_runFacts
      ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_outsG0
      ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_kidsMemG
      ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_designP0
  Lean.logInfo m!"WITHMEMORY [{name}]: the depth-0 design endpoint of a memory-only parent with a TRANSPORTED endpoint, under MachineClosesAt and ChildBnd — a NEW statement ({f} has no design-level base endpoint); the composed theorem is read under the transport and moved to the declaration's source by composedG_src; MachineClosesAt is STILL a binder"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemWithMemory.auditOpen
    ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
    [``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_entry,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_data,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_runFacts,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_outsG0,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_kidsMemG,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_designP0]

/-! ## The closed endpoint -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
  let closed ← Tests.Compiler.NoPortsMemOnlyClosed.closeIt f
    ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_closes
  Lean.logInfo m!"WITHMEMORY CLOSED [{closed}]: {f}.machine_design_noPortsR0 with its binder MachineClosesAt {f} discharged by withMemory_closes (NO premise), by Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly"

/-! ## The goal gap -/

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory.machine_design_noPortsR0_closed

/-! ## The audit of the closed endpoint (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.NoPortsMemWithMemory.auditClosed
    ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory
    ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_closes
    [``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_entry,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_data,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_alias,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_argsN,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_field,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_argsNd,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_outHead,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_closeData,
     ``Tests.Compiler.NoPortsMemWithMemoryTest.withMemory_notin]
