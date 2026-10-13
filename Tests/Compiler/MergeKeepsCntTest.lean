import Lean.Elab.Command
import Tests.Compiler.PortsMatchRawLeafTest
import Tests.Compiler.LeafEntryCexProbe
import Tools.ShippingMergeKeepsLeaf
import Tools.ShippingMergeKeepsCheck
import Tools.ShippingFinalGoalCommand

/-! # `cnt` AS AN ENTRY with `hmergeReg` discharged (G1, round par/a-30)

`cnt.machine_ships_leafB` (`Tests/Compiler/LeafEntryCntBndTest.lean`, built)
has TWO NOT ALLOWED binders: `hmergeReg` and `hoptPrint`. This file adds
`cnt.machine_ships_leafR`: the same conclusion WITHOUT `hmergeReg`
(`Tools.ShippingMergeKeepsLeaf.leaf_entry_textChecks_bndR`).

## What the statement is — and is NOT

`hmergeReg` is not assumed and not weakened: it is PROVED for the run's
module, from `Tools.ShippingMergeKeeps.mergeChecked_keeps` (the merge keeps a
non-assignment statement of a body with `LastNonAssign`) and
`Tools.ShippingMergeKeepsLeaf.leaf_run_lastNonAssign` (the leaf's cleaned
closed machine has `LastNonAssign`: its first register is followed by
registers and output assignments only). No compiler file is changed: the
guard "Diff 2" of `docs/parallel/B-optprint.md` is not needed for a leaf
register machine.

ONE binder stays NOT ALLOWED: `hoptPrint` (false for the optimizer, by the
built probe `optCex`; a guard in the compiler — user decision). So this is
NOT a check-free endpoint and is not to be counted as one.

## The probe module, against the hypothesis (section 4)

`mergeCex` (`Tests/Compiler/LeafEntryCexProbe.lean`): `a = 5; register n;
n = 5`. EVALUATED here (compiled evaluation in `run_cmd`, an error on any
other value — not a kernel `decide`; the kernel-level statements are in
`Tests/Compiler/MergeKeepsCexTest.lean`):

* `lastNonAssignB mergeCex.body = false` — by
  `Tools.ShippingMergeKeeps.not_lastNonAssign` the module is OUTSIDE the
  hypothesis (its only non-assignment, `register n`, is followed by
  `n = 5`);
* `(mergeChecked mergeCex).body.all isAssign = true` — the register is lost;
* a module INSIDE the hypothesis on which the merge does rewrite something:
  `dupReg` — `a = 5; register n1 <= a; register n2 <= a`. By hand: round 1
  gives classes `a ↦ 0, n1 ↦ 1, n2 ↦ 1`; round 2 the same, 2 classes ≠ 3
  nodes; `rep = {0 ↦ a, 1 ↦ n1}`, `subst = {n2 ↦ n1}`; body
  `a = 5; register n1 <= a; n2 = n1` — `n1`, the representative, is still a
  register. Asserted: `lastNonAssignB dupReg.body = true`, and the raw and
  the checked merge are not assignments only. LOGGED only (a hand
  prediction, not a consequence of a theorem): that the raw merge did turn
  one register into an alias.

## SCOPE (binding for any report)

ONE declaration, `cnt`, as an entry; ONE module (`MachineShips` at the
emitter's own width map) — not `DesignSV`, not the SV string, not `#sim`;
data conditions decided for `cnt` (`cnt_leafKid`); the run, the reflection
and the runtime boundary stay premises; `hoptPrint` stays a premise and is
NOT ALLOWED.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.MergeKeepsCntTest
open Sparkle.IR.AST

/-! ## 1. The constants: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let r ← Tools.ShippingMachineCommand.readMachine c
  let env ← Lean.getEnv
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for n in [c ++ `machineData, c ++ `machine_closes, c ++ `machine_ships_wired,
      c ++ `machine_ships_leafR,
      ``Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid,
      ``Tools.ShippingMergeKeeps.partsRec_keeps,
      ``Tools.ShippingMergeKeeps.parts_eq_model,
      ``Tools.ShippingMergeKeeps.mergeChecked_keeps,
      ``Tools.ShippingMergeKeepsLeaf.leaf_run_lastNonAssign,
      ``Tools.ShippingMergeKeepsLeaf.leaf_entry_textChecks_bndR] do
    if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
  Lean.logInfo m!"MERGEKEEPS CNT DATA {c}: nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, call entries {r.shape.insts.map (·.1)}, outputs {r.shape.layout.outs.map (·.name)}. In the environment: {have_}; not: {lack}"
  unless r.shape.insts.isEmpty do throwError "{c}: it has calls — not a leaf"
  if r.shape.layout.slots.isEmpty then throwError "{c}: no register slot"
  for n in [c ++ `machineData, c ++ `machine_closes, c ++ `machine_ships_wired,
      ``Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid,
      ``Tools.ShippingMergeKeepsLeaf.leaf_entry_textChecks_bndR] do
    unless env.contains n do
      throwError "{n}: not in the environment — this file needs it"
  let leafR : Lean.Name := c ++ `machine_ships_leafR
  if env.contains leafR then
    throwError "{leafR}: already in the environment"

/-! ## 2. `cnt.machine_ships_leafR` -/

set_option maxHeartbeats 0 in
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let stx ← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hbnd : Tools.ShippingChildInv.ChildBnd mref cref w)
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational
          ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
        ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
        Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape)
      (hoptPrint : Sparkle.IR.OptCheck.checkedOptimize b = b ∨
        Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true) =>
      Tools.ShippingLeafEntry.leaf_entry_ships_of
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_wired hr entry
          (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_closes mctx mref cctx cref))
        (Tools.ShippingMergeKeepsLeaf.leaf_entry_textChecks_bndR
          (Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid entry) hbnd hr hoptPrint))
  let e0 ← Lean.Elab.Term.elabTermAndSynthesize stx none
  let e ← Lean.instantiateMVars e0
  if e.hasMVar then
    throwError "{c}: the proof term of machine_ships_leafR has an unassigned metavariable"
  let ty0 ← Lean.Meta.inferType e
  let ty ← Lean.instantiateMVars ty0
  let leaf := c ++ `machine_ships_leafR
  Tools.ShippingMachineLinkedCommand.addTheorem leaf ty e
  Lean.logInfo m!"MERGEKEEPS CNT ADDED {leaf} (standard axioms): {ty}"

/-! ## 3. The premise listing and the assertions -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let leaf := c ++ `machine_ships_leafR
  let base := c ++ `machine_ships_wired
  let info ← Lean.getConstInfo leaf
  let binfo ← Lean.getConstInfo base
  let mentions (t : Lean.Expr) (n : Lean.Name) : Bool := (t.find? (·.isConstOf n)).isSome
  -- every proposition binder, classified
  let report ← Lean.Meta.forallTelescope info.type fun xs body => do
    let mut lines : Array String := #[]
    let mut bad : Nat := 0
    let mut bnd : Nat := 0
    let mut asg : Nat := 0
    for x in xs do
      let t0 ← Lean.Meta.inferType x
      let t ← Lean.instantiateMVars t0
      let isP ← Lean.Meta.isProp t
      if isP then
        let pp ← Lean.Meta.ppExpr t
        let nm ← x.fvarId!.getUserName
        if t.isAppOf ``Tools.ShippingChildInv.ChildBnd then bnd := bnd + 1
        if mentions t ``Sparkle.IR.RegDedup.isAssign then asg := asg + 1
        if Tools.ShippingFinalGoalCommand.allowed t then
          lines := lines.push s!"MERGEKEEPS PREMISE {leaf}: ALLOWED     binder {nm} : {pp}"
        else
          bad := bad + 1
          lines := lines.push s!"MERGEKEEPS PREMISE {leaf}: NOT ALLOWED binder {nm} : {pp}"
    let ppBody ← Lean.Meta.ppExpr body
    lines := lines.push s!"MERGEKEEPS CONCLUSION {leaf}: {ppBody}"
    return (lines, bad, bnd, asg)
  for l in report.1 do Lean.logInfo l
  let checks : List Lean.Name :=
    [``Sparkle.IR.OptCheck.simpleBody, ``Tools.SVParser.EmitSem.seqCheck,
      ``Tools.ShippingSeqSVSoundness.seqNames]
  let inBase := checks.filter (mentions binfo.type)
  let inLeaf := checks.filter (mentions info.type)
  let closing := mentions info.type ``Tools.ShippingMachineEntry.MachineCloses
  let invW := mentions info.type ``Tools.ShippingChildInv.InvW
  Lean.logInfo m!"MERGEKEEPS CNT CHECKS: of {checks} — in {base}: {inBase}; in {leaf}: {inLeaf}. MachineCloses in {leaf}: {closing}. InvW in {leaf}: {invW}. ChildBnd binders: {report.2.2.1}. Binders mentioning isAssign (hmergeReg): {report.2.2.2}. NOT ALLOWED binders of {leaf}: {report.2.1}"
  unless inBase.length == 3 do
    throwError "{base}: expected to mention the three check constants, mentions {inBase}"
  unless inLeaf.isEmpty do
    throwError "{leaf}: still mentions {inLeaf}"
  if closing then throwError "{leaf}: still mentions MachineCloses"
  if invW then throwError "{leaf}: still mentions InvW"
  unless report.2.2.1 == 1 do
    throwError "{leaf}: {report.2.2.1} ChildBnd binders, expected 1"
  unless report.2.2.2 == 0 do
    throwError "{leaf}: {report.2.2.2} binders mention isAssign, expected 0 (hmergeReg is gone)"
  unless report.2.1 == 1 do
    throwError "{leaf}: {report.2.1} NOT ALLOWED binders, expected 1 (hoptPrint)"
  -- the general theorems: standard axioms
  for n in [``Tools.ShippingMergeKeeps.isA_sig,
      ``Tools.ShippingMergeKeeps.partsRec_keeps,
      ``Tools.ShippingMergeKeeps.lastNonAssign_of_nodup,
      ``Tools.ShippingMergeKeeps.parts_eq_model,
      ``Tools.ShippingMergeKeeps.model_eq_rec,
      ``Tools.ShippingMergeKeeps.mergeRaw_keeps_nonAssign,
      ``Tools.ShippingMergeKeeps.mergeChecked_keeps,
      ``Tools.ShippingMergeKeeps.not_lastNonAssign,
      ``Tools.ShippingMergeKeepsLeaf.closeMachine_lastNonAssign,
      ``Tools.ShippingMergeKeepsLeaf.leaf_run_lastNonAssign,
      ``Tools.ShippingMergeKeepsLeaf.leaf_mergeReg,
      ``Tools.ShippingMergeKeepsLeaf.leaf_entry_textChecks_bndR,
      ``Tools.ShippingMergeKeepsLeaf.leaf_entry_shipped_seq_bndR,
      ``Tools.ShippingMergeKeepsLeaf.leaf_entry_ships_bndR, leaf] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  let old : Lean.Name := c ++ `machine_ships_leafB
  Lean.logInfo m!"MERGEKEEPS CNT: {leaf} — against {old}: hmergeReg is gone (proved for the run's module: the merge keeps a non-assignment statement of a body with LastNonAssign, and the leaf's cleaned closed machine has it); no simpleBody, seqCheck, seqNames, MachineCloses, InvW; standard axioms. NOT a check-free endpoint and NOT counted: ONE binder stays NOT ALLOWED — hoptPrint (false for the optimizer by the probe optCex; a guard in the compiler, user decision). SCOPE: one declaration, one module (MachineShips), data conditions decided for cnt; not DesignSV, not the SV string, not #sim"

/-! ## 4. The probe module against the hypothesis: evaluated -/

/-- Two registers with the same next value: the merge turns the second into
an alias of the first. -/
def dupReg : Module :=
  { name := "dupReg"
    inputs := [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
    outputs := []
    wires := [{ name := "a", ty := .bitVector 8 }, { name := "n1", ty := .bitVector 8 },
      { name := "n2", ty := .bitVector 8 }]
    body :=
      [ .assign "a" (.const 5 8)
      , .register "n1" "clk" ("rst", .synchronous) (.ref "a") 0
      , .register "n2" "clk" ("rst", .synchronous) (.ref "a") 0 ] }

run_cmd do
  let m := Tests.Compiler.LeafEntryCexProbe.mergeCex
  let hyp : Bool := Tools.ShippingMergeKeeps.lastNonAssignB m.body
  let a0 : Bool := m.body.all Sparkle.IR.RegDedup.isAssign
  let k := Sparkle.IR.RefineCheck.mergeChecked m
  let a1 : Bool := k.body.all Sparkle.IR.RegDedup.isAssign
  Lean.logInfo s!"MERGEKEEPS CEX mergeCex: lastNonAssignB = {hyp}; isAssign-all of m = {a0}; mergeChecked body = {repr k.body}; isAssign-all of mergeChecked m = {a1}"
  if hyp then
    throwError "mergeCex: lastNonAssignB is true — the module is INSIDE the hypothesis, so either the checker or the theorem's hypothesis is not what the note says"
  if a0 then throwError "mergeCex: its body is assignments only"
  -- Version note (integrator, 2026-10-13): since the compiler's merge guard (poc 50ffea04) the CHECKED
  -- merge keeps a non-assignment statement on every module, so the counterexample is evaluated on the RAW
  -- merge, the function `mergeRaw_keeps_nonAssign` is about; the checked merge must now keep the statement.
  let rawCex := Sparkle.IR.RegDedup.mergeDuplicatesRaw m
  let rawCexA : Bool := rawCex.body.all Sparkle.IR.RegDedup.isAssign
  Lean.logInfo s!"MERGEKEEPS CEX mergeCex (raw merge): isAssign-all of mergeDuplicatesRaw m = {rawCexA}"
  unless rawCexA do
    throwError "mergeCex: the RAW merge kept a non-assignment — the counterexample of docs/parallel/A-leaf-entry-2.md §1 no longer evaluates as built"
  if a1 then
    throwError "mergeCex: the CHECKED merge is assignments only — the compiler's non-assignment guard did not fire"
  let g := dupReg
  let hypG : Bool := Tools.ShippingMergeKeeps.lastNonAssignB g.body
  let rG := Sparkle.IR.RegDedup.mergeDuplicatesRaw g
  let kG := Sparkle.IR.RefineCheck.mergeChecked g
  let rawA : Bool := rG.body.all Sparkle.IR.RegDedup.isAssign
  let chkA : Bool := kG.body.all Sparkle.IR.RegDedup.isAssign
  let changed : Bool := rG.body.any Sparkle.IR.RegDedup.isAssign &&
    (rG.body.filter Sparkle.IR.RegDedup.isAssign).length == 2
  Lean.logInfo s!"MERGEKEEPS POS dupReg: lastNonAssignB = {hypG}; raw merge body = {repr rG.body}; isAssign-all of the raw merge = {rawA}; mergeChecked body = {repr kG.body}; isAssign-all of mergeChecked = {chkA}; the raw merge made the second register an alias: {changed}"
  unless hypG do throwError "dupReg: lastNonAssignB is false"
  if rawA then
    throwError "dupReg: the raw merge is assignments only — mergeRaw_keeps_nonAssign would be FALSE on a module with the hypothesis"
  if chkA then
    throwError "dupReg: the checked merge is assignments only — mergeChecked_keeps would be FALSE on a module with the hypothesis"
  -- a prediction made by hand about the merge, not a consequence of a theorem: LOGGED only
  let verdict : String :=
    if changed then "PREDICTION CONFIRMED — the raw merge is a = 5; register n1; n2 = n1 (one register became an alias, the representative stayed a register)"
    else "PREDICTION REFUTED — the raw merge did not turn exactly one register into an alias; the positive example then does not exercise the rewrite (the two assertions above still hold)"
  Lean.logInfo s!"MERGEKEEPS POS VERDICT: {verdict}"

end Tests.Compiler.MergeKeepsCntTest
