import Tests.Compiler.ShippingCallsCloseTest
import Tests.Compiler.NoPortsTest
import Tools.ShippingOneOutCommand
import Tools.ShippingOneOutSameRun
import Tools.ShippingChecksCoreGate
import Tools.ShippingChecksGate
import Tools.ShippingCombKidText

/-! # ONE endpoint: `caller` (child `pick`), the combinational head with two of its four check premises gone and the other two narrowed to two independent conditions (G1, rounds par/a-6, par/a-7)

Declaration: `Sparkle.Tests.Compiler.ShippingMachineInstTest.caller` — a
`circuit do` with TWO registers (`sel`, `acc`) and ONE call entry, of the
combinational declaration `pick` (compiled by the certified GATE; one output
`Signal (BitVec 8)`), tied by the ONE-OUTPUT closing `closeInsts`
(`instFields = []`).

Its deepest endpoint so far is `caller.machine_design_svHR` (and
`caller.machine_design_svHR_closed`), whose statement is
`∃ raw D, … ∧ (A₁ → Bnd → A₂ → A₃ → A₄ → …)` with the FOUR check premises

    A₁  shipsHierHCheck D.modules b = true
    A₂  kidsComb D.modules (checkedOptimize b).body = true
    A₃  designCheck (childMap D.modules) 0 (checkedOptimize b) = true
    A₄  outsCheck (childMap D.modules) 0 (checkedOptimize b) = true

This file adds `caller.machine_design_svH_free` (and its `_closed` form):
the same conclusion, from the same generator arguments, with

    A₂  GONE — derived from the run by `core_runFactsH` (`RunFactsH.comb`:
        `closeInsts_kidsComb`) and moved to the shipped module in the head;
    A₄  GONE — derived from the run by `core_outsCheck_all_gate` with
        `gate_kidA` / `gate_kidR` at `pick` (`caller_outsH`);
    A₃  NARROWED to its one conjunct
          portsMatchB (childMap D.modules) (checkedOptimize b) = true
        — the other seven conjuncts of `textCheckI` and the children's check
        are derived (`core_designCheckH`, `gate_real_kidK`; `caller_designH`);
    A₁  NARROWED to its one conjunct
          hierTyped (childMap D.modules) b = true
        — `hierCheck` (all seven conjuncts; `hierBinds b` is no longer asked
        at all: the head splits on the compiler's branches) and `kidsLocal`
        are derived (`caller_factsH`; the head `machine_design_svH_free`).

So the endpoint is NOT check-free: TWO INDEPENDENT check conditions remain
(`hierTyped …` of the full entry's module; `portsMatchB …` of the shipped
module). They are written as ONE antecedent (a conjunction) only because the
head takes one residual parameter; that is a matter of form, not "one item
left". What is missing for each is in
`docs/parallel/A-oneout.md` §4 (the gate child's port widths in the
emitter's and in the IR's width tables). No "goal gap empty" claim is made
for `caller`.

## Scope, exactly

* AXES. The parent `caller` HAS a register (two slots): `core_runFactsH` and
  `core_designCheckH` take `d.shape.layout.slots ≠ []`, decided here, and the
  head's `RunFactsH.rst` (`"rst" ∈ b.inputs`) comes from it. Nothing here
  covers a parent WITHOUT a register. The child is a GATE declaration, one
  output, combinational (no clock/reset input: `CallStmt` of the closing
  itself). These two axes are independent in the statements: "the parent has
  a register" is the hypothesis `hsl`; "the child is combinational" is
  `instFields = []` plus the closing's own check.
* DATA CONDITIONS decided per declaration in this file (kernel `decide` /
  `rfl` on the reflected `caller.machineData`; where one fails the theorem
  does not exist — nothing false is proved): `callsOk 1`;
  `ss.length = shape.layout.slots.length`; no domain binder after the first;
  `shape.insts ≠ []`; `shape.instFields = []`; `shape.layout.slots ≠ []`;
  every output's `ty.bitWidth = width`; no memory callee; the output names
  character-wise `charOk`; the output types `scalarTy`; the one entry's
  callee is `pick`; and for `pick` what `#gate_child` left
  (`pick.gate_old`, `pick.gate_peel`, `pick.gate_wf`, the binder positions).
  Plus those of the generators run before (`caller.machine_ships_hierHR`'s
  output-width premise, `caller.machine_closes_at`'s name conditions).
* COMPILER GUARDS the result depends on: `checkedOptimize` ships the input
  module where its hierarchical check does not bind, and keeps a candidate
  only under the guards of `deinline` (distinct instance names, linked
  order, `printOk`, …). The theorem is about the guarded compiler.
* RUNTIME BOUNDARY (premises, with no runtime model): the run of the entry
  `RunsTo (synthesizeCombinational caller) …`, `MachineDefines` of `caller`,
  `ChildBnd mref cref w` at the run's start world, `EntryDefines` of `pick`.
* WHAT THE CONCLUSION IS ABOUT: `DesignSV (childMap D.modules) 0
  (checkedOptimize b) …` — the emitted-text semantics of the shipped module
  over the modules of the core run's design `D` (existence of a closed run
  showing the source, and every closed run). NOT the printed string, not a
  parser, not `#sim`.

The test throws unless: the four hand theorems and the endpoints are on
standard axioms; the new endpoint's statement mentions none of
`shipsHierHCheck`, `hierCheck`, `kidsLocal`, `kidsComb`, `designCheck`,
`outsCheck`; the old one mentions the four; among the premises of the new
endpoint that are not a run / a reflection / `ChildBnd` there is exactly one
antecedent carrying checker constants, the residual, and it holds BOTH
independent conditions `hierTyped …` and `portsMatchB …` (the unclosed
endpoint also has the closing premise `MachineClosesAt`, which its `_closed`
form replaces by the premises of `caller.machine_closes_at`); and both
conditions hold on the real modules of `caller` (they are not vacuous
there). The complete premise lists are logged (`NOPORTS PREMISE` lines).

## On which objects the residual is evaluated (review of 7fa6a19f, point 3)

The endpoint's residual is about `(b, D)`: `b` the module the full entry
`synthesizeCombinational caller` returns, `D` the design of the CORE run
inside that same run (`∃ raw D` of the statement). The test runs the full
entry ONCE, gets `(b, design)`, evaluates `design.modules.all (·.name !=
b.name)` and, under it, evaluates the residual with `design.modules` in the
place of `D.modules`. These are the same list:
`Tools.ShippingOneOutSameRun.fullEntry_sameDesign` — from the full run and
that very condition on `(b, design)`, `design.modules = D.modules` for the
core run inside it. (The run the test performs is a run of the meta
program in this process; the theorem is about `RunsTo`; that a real run is
a `RunsTo` is the runtime boundary, as everywhere.) Logged as
`ONEOUT RESIDUAL caller: hierTyped=<T/F> portsMatchB=<T/F> (same run)`.

A SECOND, separate run of the core entry is kept only as a labelled
cross-check (`ONEOUT CROSS-CHECK`): its design's modules must equal the
first run's (`==`), its module must post-process to the first run's `b`,
and the residual must evaluate the same; any disagreement is an error. It
is not what the claim rests on.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.OneOutCallerTest
open Sparkle.Tests.Compiler.ShippingMachineInstTest

/-- The gate child `pick`'s full-entry facts, from a real-child witness and
its reflection in the run's contexts. -/
theorem pick_full {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``pick pick.gateValue)
    {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildInv.RealChild mref cref ``pick y) :
    Tools.ShippingGateChildComb.ChildFull ``pick pick.gateBinders y.1 y.2 :=
  Tools.ShippingCallsGate.childFull_of_real hR0 pick.gate_old pick.gate_peel pick.gate_wf
    (Tools.ShippingGateChild.bool_positions (by decide))
    (Tools.ShippingGateChild.bits_positions (by decide)) hy

set_option maxHeartbeats 0 in
/-- **The run's facts of `caller`'s full-entry module** (`core_runFactsH` at
`caller`'s data): the gate, distinct instance names, the self-read test, the
extraction of the instance-driven wires, the reset input, the children's
combinational check. Premises: the core run, the post-processing fact,
`caller`'s reflection and closing, `ChildBnd`. -/
theorem caller_factsH {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``caller [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``caller
      caller.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``caller
      caller.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.ShippingOneOutFacts.RunFactsH D.modules b :=
  Tools.ShippingOneOutFacts.core_runFactsH (nDecl := 1) caller.machineData
    caller.machine_ok caller.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    rfl
    (by decide) (by decide)
    hB hcore hpost entry closes
    (fun h0 => absurd (congrArg List.length h0) (by decide))

/-- The typing premise is the residual's first conjunct: NOT derived. -/
theorem caller_typedH {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (_hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``caller [] false)
      mctx mref cctx cref w (raw, D) w1)
    (_hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (_entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``caller
      caller.machineData.shape)
    (_closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``caller
      caller.machineData.shape)
    (hty : Tools.ShippingHierTyped.hierTyped
      (Tools.ShippingMachineLinked.childMap D.modules) b = true) :
    Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b = true :=
  hty

set_option maxHeartbeats 0 in
/-- **`designCheck` of `caller`'s shipped module at depth 0, from the run and
the connection widths** (`core_designCheckH` at `caller`'s data; the
children's check by `gate_real_kidK` at `pick`). The one check premise left:
`portsMatchB`. -/
theorem caller_designH {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``caller [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``caller
      caller.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``caller
      caller.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``pick pick.gateValue)
    (hports : Tools.ShippingDesignSV.portsMatchB
      (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b) = true) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingOneOutFacts.core_designCheckH (nDecl := 1) caller.machineData
    caller.machine_ok caller.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    rfl
    (by decide) (by decide)
    hB hcore hpost entry closes
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      ((show ∀ o ∈ caller.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
          Sparkle.IR.NameHints.charOk c = true from by
        first | decide | decide +kernel) o ho))
    (by decide)
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero =>
        exact Tools.ShippingCombKidText.gate_real_kidK hR0 pick.gate_old pick.gate_peel
          pick.gate_wf (Tools.ShippingGateChild.bool_positions (by decide))
          (Tools.ShippingGateChild.bits_positions (by decide)) hy
      | succ k => exact absurd hk' (by omega))
    0 hports

set_option maxHeartbeats 0 in
/-- **`outsCheck` of `caller`'s shipped module at depth 0, from the run**
(`core_outsCheck_all_gate` at `caller`'s data, `gate_kidA` / `gate_kidR` at
`pick`), under the statement-kind gate. No check premise. -/
theorem caller_outsH {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``caller [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``caller
      caller.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``caller
      caller.machineData.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (hR0 : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``pick pick.gateValue) :
    Tools.ShippingDesignSVBack.outsCheck (Tools.ShippingMachineLinked.childMap D.modules) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingChecksCoreGate.core_outsCheck_all_gate (nDecl := 1) caller.machineData
    caller.machine_ok caller.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide)) (by decide) (by decide)
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact Tools.ShippingChecksGate.gate_kidA (pick_full hR0 hy)
      | succ k => exact absurd hk' (by omega))
    (by
      intro k hk y hy
      have hk' : k < 1 := hk
      cases k with
      | zero => exact Tools.ShippingChecksGate.gate_kidR (pick_full hR0 hy)
      | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes hg 0

/-! ## The endpoint -/

set_option maxHeartbeats 0 in
#machine_design_svH_free Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
  (fun b D =>
    Tools.ShippingHierTyped.hierTyped (Tools.ShippingMachineLinked.childMap D.modules) b = true ∧
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b) = true)
  [caller_factsH, caller_typedH, caller_designH, caller_outsH]

#check @Sparkle.Tests.Compiler.ShippingMachineInstTest.caller.machine_design_svH_free

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.ShippingMachineInstTest.caller
  let old := f ++ `machine_design_svHR
  let new := f ++ `machine_design_svH_free
  let std (n : Name) : MetaM Unit := do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  -- the general theorems and the hand instances
  for n in [``Tools.ShippingOneOutHead.machine_design_svH_free,
      ``Tools.ShippingOneOutFacts.core_runFactsH, ``Tools.ShippingOneOutFacts.core_designCheckH,
      ``Tools.ShippingOneOutFacts.core_kidsComb₁, ``Tools.ShippingOneOutFacts.core_instNames₁,
      ``Tools.ShippingOneOutFacts.core_noSelfRead₁,
      ``Tools.ShippingOneOutFacts.core_outsExtracted₁, ``Tools.ShippingOneOutFacts.core_rst_any,
      ``Tools.ShippingOneOutClose.closeInsts_instNames,
      ``Tools.ShippingOneOutClose.noSelfRead_of_calls,
      ``Tools.ShippingOneOutSameRun.fullEntry_sameDesign,
      ``caller_factsH, ``caller_typedH, ``caller_designH, ``caller_outsH, new] do
    std n
  let checks := [``Tools.ShippingHierPremises.shipsHierHCheck,
    ``Tools.ShippingMachineDepthH.kidsComb, ``Tools.ShippingDesignSV.designCheck,
    ``Tools.ShippingDesignSVBack.outsCheck]
  -- the old endpoint asks the four check premises
  let oldT := (← getConstInfo old).type
  for c in checks do
    unless (oldT.find? (·.isConstOf c)).isSome do
      throwError "{old}: does not mention {c} (the inventory of this round is wrong)"
  -- the new one, and its closed form where there is one, asks none of them,
  -- nor `hierCheck` / `kidsLocal`
  let mut ends := [new]
  let closed := Tools.ShippingMachineClosesGen.closedName new
  if (← getEnv).contains closed then ends := ends ++ [closed]
  for n in ends do
    std n
    let t := (← getConstInfo n).type
    for c in checks ++ [``Tools.ShippingHierPremisesBase.hierCheck,
        ``Tools.ShippingHierOptRunH.kidsLocal] do
      if (t.find? (·.isConstOf c)).isSome then throwError "{n}: the statement mentions {c}"
    -- the declared residual is there
    for c in [``Tools.ShippingHierTyped.hierTyped, ``Tools.ShippingDesignSV.portsMatchB] do
      unless (t.find? (·.isConstOf c)).isSome do
        throwError "{n}: the residual premise {c} is not in the statement"
    -- the complete premise list (`NOPORTS PREMISE` lines: the helper of
    -- `NoPortsTest`). The premises that are not a run, a reflection or
    -- `ChildBnd`: exactly ONE residual antecedent; besides it, on the
    -- unclosed endpoint, only the closing premise `MachineClosesAt`
    -- (the closed form replaces it by `caller.machine_closes_at`'s premises,
    -- which are listed, not judged, here)
    let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines n
    logInfo m!"{String.intercalate "\n" lines.toList}"
    let has (l s : String) : Bool := (l.splitOn s).length > 1
    let residual := bad.filter fun l => has l "hierTyped" || has l "portsMatchB"
    unless residual.size == 1 && residual.all (fun l => has l "hierTyped" && has l "portsMatchB") do
      throwError "{n}: expected one residual antecedent holding the two conditions hierTyped and portsMatchB, found {residual.size}:\n{String.intercalate "\n" bad.toList}"
    if n == new then
      for l in bad do
        unless has l "hierTyped" || has l "MachineClosesAt" do
          throwError "{n}: a premise that is neither the residual nor the closing premise:\n{l}"
    logInfo m!"ONEOUT PREMISES {n}: {lines.size} binders and antecedents listed; not a run / reflection / ChildBnd: {bad.size}; of them the residual antecedent: 1, holding 2 INDEPENDENT check conditions (hierTyped; portsMatchB)"
  let tf (x : Bool) : String := if x then "T" else "F"
  -- (1) the residual on (b, D) of ONE run of the full entry. `design.modules`
  -- is `D.modules` of the core run inside that run when no module of
  -- `design` is named as `b` (`fullEntry_sameDesign`); that condition is
  -- evaluated first, on the same pair
  let (b, design) ← Sparkle.Compiler.Elab.synthesizeCombinational f
  let hno := design.modules.all fun x => !(x.name == b.name)
  unless hno do
    throwError "{f}: a module of the full entry's design is named as its module {b.name}: design.modules is not known to be the core design's modules, the residual is not evaluated"
  let o := Sparkle.IR.OptCheck.checkedOptimize b
  let C := Tools.ShippingMachineLinked.childMap design.modules
  let hty := Tools.ShippingHierTyped.hierTyped C b
  let hpm := Tools.ShippingDesignSV.portsMatchB C o
  logInfo m!"ONEOUT RESIDUAL caller: hierTyped={tf hty} portsMatchB={tf hpm} (same run)"
  unless hty && hpm do
    throwError "{f}: a residual condition fails on the modules of one full run (hierTyped={tf hty}, portsMatchB={tf hpm})"
  -- (2) CROSS-CHECK only: a second, separate run of the core entry
  let (raw2, D2) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore f [] false
  let dz2 := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw2
  let sameMods := D2.modules == design.modules
  let sameTop := b == dz2 || b == Sparkle.IR.RefineCheck.mergeChecked dz2
  let C2 := Tools.ShippingMachineLinked.childMap D2.modules
  let hty2 := Tools.ShippingHierTyped.hierTyped C2 b
  let hpm2 := Tools.ShippingDesignSV.portsMatchB C2 o
  logInfo m!"ONEOUT CROSS-CHECK caller (a second, separate core run; not what the claim rests on): modules equal to the first run's={tf sameMods}, its module post-processes to the first run's b={tf sameTop}, hierTyped={tf hty2} portsMatchB={tf hpm2}"
  unless sameMods && sameTop && hty2 == hty && hpm2 == hpm do
    throwError "{f}: the separate core run DISAGREES with the full run (modules equal={tf sameMods}, top agrees={tf sameTop}, hierTyped {tf hty2} vs {tf hty}, portsMatchB {tf hpm2} vs {tf hpm})"
  logInfo m!"ONEOUT caller: endpoint {ends} (WRITTEN; a reduction only once built) — of the four check premises of {old} (shipsHierHCheck, kidsComb, designCheck, outsCheck): kidsComb and outsCheck derived from the run; designCheck narrowed to portsMatchB of the shipped module; shipsHierHCheck narrowed to hierTyped of the full entry's module (hierBinds no longer asked). TWO INDEPENDENT residual conditions remain as premises: hierTyped={tf hty}, portsMatchB={tf hpm} on (b, D) of one full run. Scope: caller has a register (slots ≠ []); one call entry of the gate child pick, one-output closing; slotless parents and other declarations not covered. Standard axioms."

end Tests.Compiler.OneOutCallerTest
