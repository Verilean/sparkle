import Tests.Compiler.PortsMatchRawLeafTest
import Tools.ShippingGuardsLeaf
import Tools.ShippingFinalGoalCommand

/-! # `cnt` AS AN ENTRY with no NOT-ALLOWED binder (candidate branch `fix/opt-print-guard`)

`cnt.machine_ships_leafB` (`Tests/Compiler/LeafEntryCntBndTest.lean`, built
on poc) has two NOT ALLOWED binders, `hmergeReg` and `hoptPrint`; neither is
a theorem of the poc compiler. On this branch the compiler has the two
guards of `docs/parallel/G-opt-print-guard-candidate.md`, and the binders
are theorems (`Tools/ShippingGuardsLeaf.lean`):

* `hmergeReg` := `Tools.ShippingGuardsLeaf.mergeReg_closed b`
  (from `mergeChecked_keeps_nonAssign`);
* `hoptPrint` := `Tools.ShippingGuardsLeaf.leaf_entry_optPrint … hbnd hr`
  (from `checkedOptimize_instFree_print` and `leaf_entry_raw_bnd`).

This file adds `cnt.machine_ships_leafC`: the conclusion of
`cnt.machine_ships_leafB` with premises exactly the run, `MachineDefines cnt`
and `ChildBnd`.

## Order

1. the constants this file needs: LOGGED, then asserted;
2. `cnt.machine_ships_leafC`: added, standard axioms (an error otherwise);
3. its statement and every proposition binder (ALLOWED / NOT ALLOWED by
   `Tools.ShippingFinalGoalCommand.allowed`): LOGGED; then asserted — exactly
   three proposition binders (one `RunsTo`, one `MachineDefines`, one
   `ChildBnd`), 0 NOT ALLOWED; no occurrence of `InvW`, `simpleBody`,
   `seqCheck`, `seqNames`, `MachineCloses`, `printOk`, `isAssign`.

## SCOPE (binding for any report)

ONE declaration, `cnt`, as an entry; ONE module (`MachineShips` at the
emitter's own width map) — not `DesignSV`, not the SV string, not `#sim`;
data conditions decided for `cnt` (`cnt_leafKid`); the run, the reflection
and the runtime boundary stay premises. It holds for the compiler OF THIS
BRANCH (two guards added to `Sparkle/IR/RefineCheck.lean`), not for poc.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.LeafEntryCntClosedTest

/-! ## 1. The constants: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let r ← Tools.ShippingMachineCommand.readMachine c
  let env ← Lean.getEnv
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for n in [c ++ `machineData, c ++ `machine_closes, c ++ `machine_ships_wired,
      c ++ `machine_ships_leafB, c ++ `machine_ships_leafC,
      ``Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid,
      ``Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd,
      ``Tools.ShippingGuardsLeaf.checkedOptimize_instFree_print,
      ``Tools.ShippingGuardsLeaf.mergeChecked_keeps_nonAssign,
      ``Tools.ShippingGuardsLeaf.mergeReg_closed,
      ``Tools.ShippingGuardsLeaf.leaf_entry_optPrint] do
    if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
  Lean.logInfo m!"LEAFENTRYC CNT DATA {c}: nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, call entries {r.shape.insts.map (·.1)}, outputs {r.shape.layout.outs.map (·.name)}. In the environment: {have_}; not: {lack}"
  unless r.shape.insts.isEmpty do throwError "{c}: it has calls — not a leaf"
  if r.shape.layout.slots.isEmpty then throwError "{c}: no register slot"
  for n in [c ++ `machineData, c ++ `machine_closes, c ++ `machine_ships_wired,
      ``Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid] do
    unless env.contains n do
      throwError "{n}: not in the environment — this file needs it"
  let leafC : Lean.Name := c ++ `machine_ships_leafC
  if env.contains leafC then
    throwError "{leafC}: already in the environment"

/-! ## 2. `cnt.machine_ships_leafC` -/

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
        Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape) =>
      Tools.ShippingLeafEntry.leaf_entry_ships_of
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_wired hr entry
          (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_closes mctx mref cctx cref))
        (Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd
          (Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid entry) hbnd hr
          (Tools.ShippingGuardsLeaf.mergeReg_closed b)
          (Tools.ShippingGuardsLeaf.leaf_entry_optPrint
            (Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid entry) hbnd hr)))
  let e0 ← Lean.Elab.Term.elabTermAndSynthesize stx none
  let e ← Lean.instantiateMVars e0
  if e.hasMVar then
    throwError "{c}: the proof term of machine_ships_leafC has an unassigned metavariable"
  let ty0 ← Lean.Meta.inferType e
  let ty ← Lean.instantiateMVars ty0
  let leaf := c ++ `machine_ships_leafC
  Tools.ShippingMachineLinkedCommand.addTheorem leaf ty e
  Lean.logInfo m!"LEAFENTRYC CNT ADDED {leaf} (standard axioms): {ty}"

/-! ## 3. The premise listing and the assertions -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let leaf := c ++ `machine_ships_leafC
  let base := c ++ `machine_ships_wired
  let info ← Lean.getConstInfo leaf
  let binfo ← Lean.getConstInfo base
  -- every proposition binder, classified
  let report ← Lean.Meta.forallTelescope info.type fun xs body => do
    let mut lines : Array String := #[]
    let mut bad : Nat := 0
    let mut bnd : Nat := 0
    let mut runs : Nat := 0
    let mut defs : Nat := 0
    for x in xs do
      let t0 ← Lean.Meta.inferType x
      let t ← Lean.instantiateMVars t0
      let isP ← Lean.Meta.isProp t
      if isP then
        let pp ← Lean.Meta.ppExpr t
        let nm ← x.fvarId!.getUserName
        if t.isAppOf ``Tools.ShippingChildInv.ChildBnd then bnd := bnd + 1
        if t.isAppOf ``Tools.ShippingEntrySoundness.RunsTo then runs := runs + 1
        if t.isAppOf ``Tools.ShippingMachineEntry.MachineDefines then defs := defs + 1
        if Tools.ShippingFinalGoalCommand.allowed t then
          lines := lines.push s!"LEAFENTRYC PREMISE {leaf}: ALLOWED     binder {nm} : {pp}"
        else
          bad := bad + 1
          lines := lines.push s!"LEAFENTRYC PREMISE {leaf}: NOT ALLOWED binder {nm} : {pp}"
    let ppBody ← Lean.Meta.ppExpr body
    lines := lines.push s!"LEAFENTRYC CONCLUSION {leaf}: {ppBody}"
    let counts : List Nat := [bad, bnd, runs, defs, lines.size - 1]
    return (lines, counts)
  for l in report.1 do Lean.logInfo l
  let bad : Nat := report.2.getD 0 0
  let bnd : Nat := report.2.getD 1 0
  let runs : Nat := report.2.getD 2 0
  let defs : Nat := report.2.getD 3 0
  let props : Nat := report.2.getD 4 0
  let mentions (t : Lean.Expr) (n : Lean.Name) : Bool := (t.find? (·.isConstOf n)).isSome
  let checks : List Lean.Name :=
    [``Sparkle.IR.OptCheck.simpleBody, ``Tools.SVParser.EmitSem.seqCheck,
      ``Tools.ShippingSeqSVSoundness.seqNames]
  let guards : List Lean.Name :=
    [``Sparkle.IR.PrintGuard.printOk, ``Sparkle.IR.RegDedup.isAssign]
  let inBase := checks.filter (mentions binfo.type)
  let inLeaf := checks.filter (mentions info.type)
  let guardsInLeaf := guards.filter (mentions info.type)
  let closing := mentions info.type ``Tools.ShippingMachineEntry.MachineCloses
  let invW := mentions info.type ``Tools.ShippingChildInv.InvW
  Lean.logInfo m!"LEAFENTRYC CNT CHECKS: of {checks} — in {base}: {inBase}; in {leaf}: {inLeaf}. Of {guards} in {leaf}: {guardsInLeaf}. MachineCloses in {leaf}: {closing}. InvW in {leaf}: {invW}. Proposition binders: {props} (RunsTo {runs}, MachineDefines {defs}, ChildBnd {bnd}). NOT ALLOWED binders of {leaf}: {bad}"
  unless inBase.length == 3 do
    throwError "{base}: expected to mention the three check constants, mentions {inBase}"
  unless inLeaf.isEmpty do
    throwError "{leaf}: still mentions {inLeaf}"
  unless guardsInLeaf.isEmpty do
    throwError "{leaf}: still mentions {guardsInLeaf}"
  if closing then throwError "{leaf}: still mentions MachineCloses"
  if invW then throwError "{leaf}: still mentions InvW"
  unless bad == 0 do
    throwError "{leaf}: {bad} NOT ALLOWED binders, expected 0"
  unless props == 3 && runs == 1 && defs == 1 && bnd == 1 do
    throwError "{leaf}: {props} proposition binders (RunsTo {runs}, MachineDefines {defs}, ChildBnd {bnd}), expected exactly one of each"
  -- the general theorems: standard axioms
  for n in [``Tools.ShippingGuardsLeaf.checkedOptimize_instFree_print,
      ``Tools.ShippingGuardsLeaf.mergeChecked_keeps_nonAssign,
      ``Tools.ShippingGuardsLeaf.mergeReg_closed,
      ``Tools.ShippingGuardsLeaf.leaf_entry_seqBranch,
      ``Tools.ShippingGuardsLeaf.leaf_entry_optPrint,
      ``Tools.ShippingGuardsLeaf.leaf_entry_textChecks_closed,
      ``Tools.ShippingGuardsLeaf.leaf_entry_shipped_seq_closed,
      ``Tools.ShippingGuardsLeaf.leaf_entry_ships_closed, leaf] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  let old : Lean.Name := c ++ `machine_ships_leafB
  Lean.logInfo m!"LEAFENTRYC CNT: {leaf} — against {old}: hmergeReg and hoptPrint are gone (discharged by mergeChecked_keeps_nonAssign and checkedOptimize_instFree_print, theorems of THIS BRANCH's compiler: two guards in Sparkle/IR/RefineCheck.lean, each falling back to the input module); premises exactly the run, MachineDefines cnt, ChildBnd; 0 NOT ALLOWED; no simpleBody, seqCheck, seqNames, MachineCloses, InvW; standard axioms. SCOPE: one declaration, one module (MachineShips at the emitter's own width map), data conditions decided for cnt; not DesignSV, not the SV string, not #sim; an ISOLATED CANDIDATE — not a statement about poc"

end Tests.Compiler.LeafEntryCntClosedTest
