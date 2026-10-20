import Lean.Elab.Command
import Tests.Compiler.LeafEntryCntClosedTest
import Tests.Compiler.NoPortsTest
import Tools.ShippingLeafDesignCommand

/-! # `cnt` AS AN ENTRY, at the design level (round par/b-27)

`cnt.machine_ships_leafC` (`Tests/Compiler/LeafEntryCntClosedTest.lean`)
ends in `MachineShips` at the emitter's own width map: ONE module. This file
adds `cnt.machine_design_leaf0`: the design-level endpoint of `cnt` as an
entry, in the shape of the parents' depth-0 endpoints —

    ∀ {mctx mref cctx cref w w' b design}
      (hr : RunsTo (synthesizeCombinational cnt) mctx mref cctx cref w (b, design) w')
      (entry : MachineDefines mctx mref cctx cref cnt cnt.machineData.shape),
      ∃ raw, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
        (ChildBnd mref cref w → ∃ ids, … ∀ i bools bits T ins st0 mems kids, … →
          (∃ envsO, DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
              ⟨st0, mems, kids⟩ envsO ∧ envsO.length = T ∧ …)
          ∧ ∀ envs', DesignSV (childMap design.modules) 0 (checkedOptimize b) (seedIn b ins) T
              ⟨st0, mems, kids⟩ envs' → envs'.length = T ∧ …)

— over the general bridge `Tools.ShippingLeafDesign.leaf_entry_design0_of_wired`
(`Tools/ShippingLeafDesign.lean`).

## Order

1. the constants this file needs: LOGGED, then asserted;
2. `cnt.machine_design_leaf0` BY HAND: the bridge applied to
   `cnt.machine_ships_wired`, `cnt.machine_closes` and the hand-built
   `Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid`; added, standard
   axioms (an error otherwise);
3. the COMPARE path: `#machine_leaf_design_try cnt "REBUILT"` — the command
   rebuilds the theorem from `cnt.machine_leafKid` (the generated one), adds
   `cnt.machine_design_leaf0_regen` and requires the statements `isDefEq`;
   the comparison is repeated and LOGGED here;
4. the audit BY THE PARENTS' TOOLS: `#machine_goal_gap_of` on the endpoint
   (the `GOALGAP` lines; the gap theorem must have NO `gap_…` hypothesis);
   the complete premise listing by `Tests.Compiler.NoPortsTest.premiseLines`
   (the `NOPORTS PREMISE` lines; 0 NOT ALLOWED); no checker constant of
   `Tests.Compiler.NoPortsTest.checkers`; standard axioms; then the command's
   own audit (`Tools.ShippingLeafDesignCommand.audit`).

## What the empty gap means, and what it does NOT

(i) DATA CONDITIONS decided for `cnt` (`cnt.machine_leafKid` /
`cnt_leafKid`, kernel `decide` on the reflected `machineData`): `ok`, the
body equation, `callsOk nIn`, no domain binder after `nIn`, `shape.insts =
[]`, `shape.layout.slots ≠ []`, `ss.length = slots.length`, the outputs'
`ty.bitWidth = width`, names `sanitizeName`-stable, types `scalarTy`; and
`cnt.machine_closes`, `cnt.machine_ships_wired` (the four structural
premises of `machine_ships_wired`). Conditions, not reductions.

(ii) COMPILER GUARDS: the two guards of `Sparkle/IR/RefineCheck.lean` on the
instance-free branch (`checkedOptimize`: `refineCheck m o && printOk o`,
else the input module; `mergeChecked`: the merge is kept only if it keeps a
non-assignment statement). The theorem is about the guarded compiler and
says nothing about how often a guard falls back.

(iii) WHAT THE CONCLUSION IS ABOUT: the module LIST — `DesignSV (childMap
design.modules) 0 (checkedOptimize b) …`, the emitted-text semantics of the
shipped module. For an instance-free module this is the run of its own
emitted text (`designSV0_of_leaf`, `designSV0_leaf_text`): the child map is
never consulted. NOT the printed SystemVerilog string, not a parser reading
it back, not a simulator, not `#sim`.

(iv) SCOPE: ONE declaration, `cnt`, as an entry; depth 0; no call.

(v) STANDING RUNTIME ASSUMPTIONS: the run (`RunsTo`), the reflection
(`MachineDefines cnt`) and `ChildBnd mref cref w` stay PREMISES.

WRITTEN, NOT BUILT. -/
namespace Tests.Compiler.LeafDesignCntTest

/-! ## 1. The constants: LOGGED first, then asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let r ← Tools.ShippingMachineCommand.readMachine c
  let env ← Lean.getEnv
  let mut have_ : List Lean.Name := []
  let mut lack : List Lean.Name := []
  for n in [c ++ `machineData, c ++ `machine_closes, c ++ `machine_ships_wired,
      c ++ `machine_leafKid, c ++ `machine_ships_leafC, c ++ `machine_design_leaf0,
      c ++ `machine_design_leaf0_regen, c ++ `machine_design_leaf0_gap,
      ``Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid,
      ``Tools.ShippingLeafDesign.leaf_entry_design0_of_wired,
      ``Tools.ShippingLeafDesign.leaf_entry_design,
      ``Tools.ShippingLeafDesign.leaf_entry_design_all,
      ``Tools.ShippingLeafDesign.leaf_design_of_ships] do
    if env.contains n then have_ := have_ ++ [n] else lack := lack ++ [n]
  Lean.logInfo m!"LEAFDESIGN CNT DATA {c}: nDecl={r.nDecl}, slots={r.shape.layout.slots.length}, call entries {r.shape.insts.map (·.1)}, outputs {r.shape.layout.outs.map (·.name)}. In the environment: {have_}; not: {lack}"
  unless r.shape.insts.isEmpty do throwError "{c}: it has calls — not a leaf"
  if r.shape.layout.slots.isEmpty then throwError "{c}: no register slot"
  for n in [c ++ `machineData, c ++ `machine_closes, c ++ `machine_ships_wired,
      c ++ `machine_leafKid,
      ``Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid] do
    unless env.contains n do
      throwError "{n}: not in the environment — this file needs it"
  for s in [`machine_design_leaf0, `machine_design_leaf0_regen, `machine_design_leaf0_gap] do
    if env.contains (c ++ s) then
      throwError "{c ++ s}: already in the environment (NAME CLASH)"

/-! ## 2. `cnt.machine_design_leaf0`, by hand over the bridge -/

set_option maxHeartbeats 0 in
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let stx ← `(fun {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
      (hr : Tools.ShippingEntrySoundness.RunsTo
        (Sparkle.Compiler.Elab.synthesizeCombinational
          ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt)
        mctx mref cctx cref w (b, design) w')
      (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref
        ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
        Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machineData.shape) =>
      Tools.ShippingLeafDesign.leaf_entry_design0_of_wired
        (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_ships_wired hr entry
          (Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_closes mctx mref cctx cref))
        (Tests.Compiler.PortsMatchRawLeafTest.cnt_leafKid entry) hr)
  let e0 ← Lean.Elab.Term.elabTermAndSynthesize stx none
  let e ← Lean.instantiateMVars e0
  if e.hasMVar then
    throwError "{c}: the proof term of machine_design_leaf0 has an unassigned metavariable"
  let ty0 ← Lean.Meta.inferType e
  let ty ← Lean.instantiateMVars ty0
  let leaf := c ++ `machine_design_leaf0
  Tools.ShippingMachineLinkedCommand.addTheorem leaf ty e
  Lean.logInfo m!"LEAFDESIGN CNT ADDED {leaf} (by hand over leaf_entry_design0_of_wired, standard axioms): {ty}"

#check @Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_design_leaf0

/-! ## 3. The compare path: the command against the hand-built theorem -/

set_option maxHeartbeats 0 in
#machine_leaf_design_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt "REBUILT"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let old := c ++ `machine_design_leaf0
  let regen := c ++ `machine_design_leaf0_regen
  let env ← Lean.getEnv
  unless env.contains regen do
    throwError "{regen}: not added by the compare path"
  let tOld := (← Lean.getConstInfo old).type
  let tNew := (← Lean.getConstInfo regen).type
  let same ← Lean.Meta.isDefEq tOld tNew
  let syntactic : Bool := tOld == tNew
  Lean.logInfo m!"LEAFDESIGN CNT COMPARE {c}: {regen} (the generator's term, over cnt.machine_leafKid) against {old} (the hand-built term, over cnt_leafKid): isDefEq {same}; syntactically equal {syntactic}"
  unless same do
    throwError "{regen}: its statement is not isDefEq that of {old}"
  -- both statements pass the generator's own checks
  discard <| Tools.ShippingLeafDesignCommand.checkStatement c regen tNew
  discard <| Tools.ShippingLeafDesignCommand.checkStatement c old tOld
  for ax in ← Lean.collectAxioms regen do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "{regen} uses a non-standard axiom: {ax}"

/-! ## 4. The audit, by the parents' tools -/

set_option maxHeartbeats 0 in
#machine_goal_gap_of Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.machine_design_leaf0

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let c := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let leaf := c ++ `machine_design_leaf0
  let gap := c ++ `machine_design_leaf0_gap
  let env ← Lean.getEnv
  unless env.contains gap do
    throwError "{gap}: not added by #machine_goal_gap_of"
  -- the general theorems: standard axioms
  for n in [``Tools.ShippingLeafDesign.post_ports,
      ``Tools.ShippingLeafDesign.declWidth_of_wires,
      ``Tools.ShippingLeafDesign.textRun_unique,
      ``Tools.ShippingLeafDesign.designSV0_leaf_text,
      ``Tools.ShippingLeafDesign.designSV0_leaf_unique,
      ``Tools.ShippingLeafDesign.leaf_design_of_ships,
      ``Tools.ShippingLeafDesign.leaf_design0_of_checks,
      ``Tools.ShippingLeafDesign.leaf_entry_design0_of_wired,
      ``Tools.ShippingLeafDesign.leaf_entry_design,
      ``Tools.ShippingLeafDesign.leaf_entry_design_all,
      leaf, gap] do
    Tests.Compiler.NoPortsTest.stdAxioms n
  -- no checker constant, in the endpoint and in its gap theorem
  for n in [leaf, gap] do
    let ci ← Lean.getConstInfo n
    for k in Tests.Compiler.NoPortsTest.checkers do
      if (ci.type.find? (·.isConstOf k)).isSome then
        throwError "{n}: the statement mentions {k}"
  -- no gap hypothesis
  let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames gap
  unless gaps.isEmpty do
    throwError "{c}: the gap hypotheses are {gaps}, expected none"
  -- the complete premise list, by the parents' classifier
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines leaf
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  unless bad.isEmpty do
    throwError "{leaf}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  -- the command's own audit (exactly: the run, MachineDefines cnt, ChildBnd)
  Tools.ShippingLeafDesignCommand.audit c
  let old : Lean.Name := c ++ `machine_ships_leafC
  Lean.logInfo m!"LEAFDESIGN CNT: {leaf} — against {old} (MachineShips of ONE module at the emitter's own width map): the conclusion is DesignSV (childMap design.modules) 0 (checkedOptimize b), a closed run showing the source exists AND every closed run from the same seeding and states shows it; seeded by seedIn b; MachineShips' input condition at declWidth raw discharged from the one at declWidth b (nine use conditions against ten; the start registers of the module before the merge stay a use condition). Audited by the parents' tools: #machine_goal_gap_of — NO gap hypothesis; NoPortsTest.premiseLines — {lines.size} binders and antecedents listed, 0 NOT ALLOWED (the run, MachineDefines cnt, ChildBnd under ∃ raw); no checker constant (portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN, hierCheck); standard axioms (also the ten theorems of Tools/ShippingLeafDesign.lean and the gap theorem); the generator's statement isDefEq the hand-built one. NOT in the conclusion: the IR run of the shipped module (leaf_entry_design_all keeps it). SCOPE: one declaration as an entry, depth 0, no call; data conditions decided for cnt; the run, the reflection and ChildBnd stay premises; a compiler with the two guards of Sparkle/IR/RefineCheck.lean; DesignSV of the module list — not the SV string, not #sim"

end Tests.Compiler.LeafDesignCntTest
