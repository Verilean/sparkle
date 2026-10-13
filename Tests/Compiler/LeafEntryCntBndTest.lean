import Tests.Compiler.PortsMatchRawLeafTest
import Tools.ShippingLeafEntryBnd
import Tools.ShippingFinalGoalCommand

/-! # `cnt` AS AN ENTRY, from `ChildBnd` at the start world (G1, round par/a-24)

`cnt.machine_ships_leaf` (`Tests/Compiler/LeafEntryCntTest.lean`, built) has
three NOT ALLOWED binders: `InvW` at the start world, `hmergeReg`,
`hoptPrint`. This file adds `cnt.machine_ships_leafB`: the same conclusion
with `ChildBnd mref cref w` in place of `InvW mref cref w`
(`Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd`).

## What the statement is — and is NOT

ONE premise changes class: the start-world premise is the ALLOWED `ChildBnd`.
TWO binders stay NOT ALLOWED, and this round did NOT remove them:

* `hmergeReg` — as a statement about `mergeChecked` on ALL modules it is
  FALSE by reading (`docs/parallel/A-leaf-entry-2.md` §1: a module in which a
  register and an assignment share a name); the true statement needs a
  hypothesis on the module and a proof about `mergeDuplicatesParts`, or a
  guard in the compiler (user decision);
* `hoptPrint` — FALSE for the optimizer by reading (§3: a single-use wire
  holding a literal-amount left shift, inlined into an addition); a guard in
  the compiler (user decision).

So this is NOT a check-free endpoint and is not to be counted as one.

## Order

1. the constants this file needs: LOGGED, then asserted;
2. `cnt.machine_ships_leafB`: added, standard axioms (an error otherwise);
3. its statement and every proposition binder (ALLOWED / NOT ALLOWED by
   `Tools.ShippingFinalGoalCommand.allowed`): LOGGED; then asserted — no
   occurrence of `InvW`, `simpleBody`, `seqCheck`, `seqNames`,
   `MachineCloses`; a `ChildBnd` binder; exactly TWO binders NOT ALLOWED.

## SCOPE (binding for any report)

ONE declaration, `cnt`, as an entry; ONE module (`MachineShips` at the
emitter's own width map) — not `DesignSV`, not the SV string, not `#sim`;
data conditions decided for `cnt` (`cnt_leafKid`); the run, the reflection
and the runtime boundary stay premises; `hmergeReg` and `hoptPrint` stay
premises and are NOT ALLOWED.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.LeafEntryCntBndTest

/-! ## 1. The constants: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let r ← Tools.ShippingMachineCommand.readMachine c
  let env ← Lean.getEnv
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for n in [c ++ `machineData, c ++ `machine_closes, c ++ `machine_ships_wired,
      c ++ `machine_ships_leaf, c ++ `machine_ships_leafB,
      ``Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid,
      ``Tools.ShippingLeafEntryBnd.leaf_run_typedIn_bnd,
      ``Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd] do
    if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
  Lean.logInfo m!"LEAFENTRYB CNT DATA {c}: nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, call entries {r.shape.insts.map (·.1)}, outputs {r.shape.layout.outs.map (·.name)}. In the environment: {have_}; not: {lack}"
  unless r.shape.insts.isEmpty do throwError "{c}: it has calls — not a leaf"
  if r.shape.layout.slots.isEmpty then throwError "{c}: no register slot"
  for n in [c ++ `machineData, c ++ `machine_closes, c ++ `machine_ships_wired,
      ``Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid] do
    unless env.contains n do
      throwError "{n}: not in the environment — this file needs it"
  let leafB : Lean.Name := c ++ `machine_ships_leafB
  if env.contains leafB then
    throwError "{leafB}: already in the environment"

/-! ## 2. `cnt.machine_ships_leafB` -/

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
      (hmergeReg : ∀ m0 : Sparkle.IR.AST.Module,
        b = Sparkle.IR.RefineCheck.mergeChecked m0 →
        m0.body.all Sparkle.IR.RegDedup.isAssign = false →
        b.body.all Sparkle.IR.RegDedup.isAssign = false)
      (hoptPrint : Sparkle.IR.OptCheck.checkedOptimize b = b ∨
        Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true) =>
      Tools.ShippingLeafEntry.leaf_entry_ships_of
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_wired hr entry
          (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_closes mctx mref cctx cref))
        (Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd
          (Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid entry) hbnd hr hmergeReg hoptPrint))
  let e0 ← Lean.Elab.Term.elabTermAndSynthesize stx none
  let e ← Lean.instantiateMVars e0
  if e.hasMVar then
    throwError "{c}: the proof term of machine_ships_leafB has an unassigned metavariable"
  let ty0 ← Lean.Meta.inferType e
  let ty ← Lean.instantiateMVars ty0
  let leaf := c ++ `machine_ships_leafB
  Tools.ShippingMachineLinkedCommand.addTheorem leaf ty e
  Lean.logInfo m!"LEAFENTRYB CNT ADDED {leaf} (standard axioms): {ty}"

/-! ## 3. The premise listing and the assertions -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let leaf := c ++ `machine_ships_leafB
  let base := c ++ `machine_ships_wired
  let info ← Lean.getConstInfo leaf
  let binfo ← Lean.getConstInfo base
  -- every proposition binder, classified
  let report ← Lean.Meta.forallTelescope info.type fun xs body => do
    let mut lines : Array String := #[]
    let mut bad : Nat := 0
    let mut bnd : Nat := 0
    for x in xs do
      let t0 ← Lean.Meta.inferType x
      let t ← Lean.instantiateMVars t0
      let isP ← Lean.Meta.isProp t
      if isP then
        let pp ← Lean.Meta.ppExpr t
        let nm ← x.fvarId!.getUserName
        if t.isAppOf ``Tools.ShippingChildInv.ChildBnd then bnd := bnd + 1
        if Tools.ShippingFinalGoalCommand.allowed t then
          lines := lines.push s!"LEAFENTRYB PREMISE {leaf}: ALLOWED     binder {nm} : {pp}"
        else
          bad := bad + 1
          lines := lines.push s!"LEAFENTRYB PREMISE {leaf}: NOT ALLOWED binder {nm} : {pp}"
    let ppBody ← Lean.Meta.ppExpr body
    lines := lines.push s!"LEAFENTRYB CONCLUSION {leaf}: {ppBody}"
    return (lines, bad, bnd)
  for l in report.1 do Lean.logInfo l
  let mentions (t : Lean.Expr) (n : Lean.Name) : Bool := (t.find? (·.isConstOf n)).isSome
  let checks : List Lean.Name :=
    [``Sparkle.IR.OptCheck.simpleBody, ``Tools.SVParser.EmitSem.seqCheck,
      ``Tools.ShippingSeqSVSoundness.seqNames]
  let inBase := checks.filter (mentions binfo.type)
  let inLeaf := checks.filter (mentions info.type)
  let closing := mentions info.type ``Tools.ShippingMachineEntry.MachineCloses
  let invW := mentions info.type ``Tools.ShippingChildInv.InvW
  Lean.logInfo m!"LEAFENTRYB CNT CHECKS: of {checks} — in {base}: {inBase}; in {leaf}: {inLeaf}. MachineCloses in {leaf}: {closing}. InvW in {leaf}: {invW}. ChildBnd binders: {report.2.2}. NOT ALLOWED binders of {leaf}: {report.2.1}"
  unless inBase.length == 3 do
    throwError "{base}: expected to mention the three check constants, mentions {inBase}"
  unless inLeaf.isEmpty do
    throwError "{leaf}: still mentions {inLeaf}"
  if closing then throwError "{leaf}: still mentions MachineCloses"
  if invW then throwError "{leaf}: still mentions InvW"
  unless report.2.2 == 1 do
    throwError "{leaf}: {report.2.2} ChildBnd binders, expected 1"
  unless report.2.1 == 2 do
    throwError "{leaf}: {report.2.1} NOT ALLOWED binders, expected 2 (hmergeReg, hoptPrint)"
  -- the general theorems: standard axioms
  for n in [``Tools.ShippingLeafEntryBnd.leaf_run_typedIn_bnd,
      ``Tools.ShippingLeafEntryBnd.leaf_run_typedIn_again,
      ``Tools.ShippingLeafEntryBnd.leaf_entry_raw_bnd,
      ``Tools.ShippingLeafEntryBnd.leaf_entry_raw_again,
      ``Tools.ShippingLeafEntryBnd.leaf_entry_textChecks_bnd,
      ``Tools.ShippingLeafEntryBnd.leaf_entry_shipped_seq_bnd,
      ``Tools.ShippingLeafEntryBnd.leaf_entry_ships_bnd, leaf] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  let old : Lean.Name := c ++ `machine_ships_leaf
  Lean.logInfo m!"LEAFENTRYB CNT: {leaf} — against {old}: the start-world premise InvW is gone, ChildBnd (ALLOWED) is in its place; no simpleBody, seqCheck, seqNames, MachineCloses; standard axioms. NOT a check-free endpoint and NOT counted: two binders stay NOT ALLOWED — hmergeReg (as a statement about mergeChecked on all modules it is false by reading: a register and an assignment sharing a name) and hoptPrint (false for the optimizer by reading: a single-use literal-amount shift wire inlined into an addition). Both need a guard in the compiler (user decision) or, for hmergeReg, a proof about mergeDuplicatesParts under a distinct-names hypothesis. SCOPE: one declaration, one module (MachineShips), data conditions decided for cnt; not DesignSV, not the SV string, not #sim"

end Tests.Compiler.LeafEntryCntBndTest
