import Tests.Compiler.LeafDesignClosedTest
import Tests.Compiler.ChildVertAuditTest
import Tools.ShippingLeafInputWidthsA
-- BUILT (unit LX, par/u-lx): lx1 exit 0 (663 jobs; generation + audit + axioms standard). See REPORT-LX.md.

/-! # Unit LX: `dead7.machine_design_closedA` — one concrete leaf on the NEW boundary

`Sparkle.Tests.Compiler.LeafDeadInitTest.dead7.machine_design_closed` (generated in
`LeafDesignClosedTest` by `#machine_leaf_design_closed`) is the kernel-checked application of
`leaf_sat_design_closed5` to the data of `dead7.machine_ships_wired`, the two decided data
conditions, `dead7.machine_closes` and `dead7.machine_leafKid`. Here the SAME application is made to
`Tools.ShippingLeafInputWidthsA.leaf_sat_design_closed5A` (the generator below is a local copy of
`Tools.ShippingLeafDesignClosedCommand.generate`, nothing in the existing command is changed), so the
old premise `hbnd : ChildBnd mref cref w` is replaced by

    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) (hw : JQ O.quiet 0 w).

## Remaining premises of `dead7.machine_design_closedA` (outer binders)

* the run `hr : RunsTo (synthesizeCombinational dead7) … (b, design) w'` — PREMISE (a run hypothesis).
* `entry : MachineDefines … dead7 dead7.machineData.shape` — PREMISE (as in the old theorem).
* `O : RefLawsAOps MkRefd mref cref` — PREMISE (law family; that the real runtime satisfies it is OPEN,
  runtime fit not claimed; logical inconsistency NOT PROVEN).
* `hA : AdmCtx O.quiet mctx cctx` — PREMISE; that the real command context is admissible is OPEN (R13/R14).
* `hw : JQ O.quiet 0 w` — PREMISE; that the entry's start world satisfies it is OPEN (L9).
No `cv w = {}`, no `RefLawsATele`, no `ChildBnd`/`StartV`/`RefLaws`.

PROVED for dead7 (discharged inside, as in the old theorem): `soundL` (generic `machine_ships_wired` data),
`dead7.machine_closes` (`MachineCloses`), `dead7.machine_leafKid` (`LeafKid`), the data conditions
`hlen`, `hinitW` (decided), `hnoI`, `hsl`, `hSS`, `houtTy`, and — inside `leaf_sat_design_closed5A` — the
input-width / text-check antecedents (`leaf_input_widthsA`, `leaf_entry_*_closedA`).

Scope: design-level statement for one leaf state machine; no runtime-fit claim; `O`, `hA`, `hw` are
hypotheses, not facts about a real `#eval` of the compiler. -/

namespace Sparkle.Tests.Compiler.LeafDesignClosedATest
open Lean Elab Command Meta Term

/-- Local copy of `Tools.ShippingLeafDesignClosedCommand.generate` with `leaf_sat_design_closed5A`:
binders after the data are `{mctx mref cctx cref w w' b design} hr entry closes K O hA hw`. -/
def generateA (f : Name) : TermElabM Name := do
  let wiredN := f ++ `machine_ships_wired
  let ci ← getConstInfo wiredN
  let some v := ci.value? (allowOpaque := true) | throwError "{wiredN}: no value"
  let some app := v.find? (·.isAppOf ``Tools.ShippingMachineShipsW.machine_ships_wired)
    | throwError "{wiredN}: no machine_ships_wired application in its value"
  let args := app.getAppArgs
  if args.size < 11 then throwError "{wiredN}: only {args.size} arguments"
  let pre := args.extract 0 11
  if pre.any (·.hasLooseBVars) then throwError "{wiredN}: open arguments"
  let e0 := mkAppN (mkConst ``Tools.ShippingLeafInputWidthsA.leaf_sat_design_closed5A
    app.getAppFn.constLevels!) pre
  let t0 ← whnf (← inferType e0)
  let .forallE _ tLen _ _ := t0 | throwError "closed5A: hlen binder expected"
  let e1 := mkApp e0 (← mkDecideProof tLen)
  let t1 ← whnf (← inferType e1)
  let .forallE _ tInit _ _ := t1 | throwError "closed5A: hinitW binder expected"
  let e2 := mkApp e1 (← mkDecideProof tInit)
  let closesN := f ++ `machine_closes
  let kidN := f ++ `machine_leafKid
  unless (← getEnv).contains closesN do throwError "{closesN} absent"
  unless (← getEnv).contains kidN do throwError "{kidN} absent"
  let ty2 ← inferType e2
  let val ← forallTelescopeReducing ty2 fun xs _ => do
    if xs.size < 15 then throwError "closed5A: {xs.size} binders, 15 expected"
    let mctx := xs[0]!; let mref := xs[1]!; let cctx := xs[2]!; let cref := xs[3]!
    let hr := xs[8]!; let entry := xs[9]!
    let O := xs[12]!; let hA := xs[13]!; let hw := xs[14]!
    let closes ← mkAppOptM closesN #[mctx, mref, cctx, cref]
    let kid ← mkAppOptM kidN #[none, none, none, none, entry]
    let body := mkAppN e2 #[xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[5]!, xs[6]!, xs[7]!,
      hr, entry, closes, kid, O, hA, hw]
    mkLambdaFVars (xs.extract 0 8 ++ #[hr, entry, O, hA, hw]) body
  let val ← instantiateMVars val
  let ty ← instantiateMVars (← inferType val)
  let n := f ++ `machine_design_closedA
  addDecl (.thmDecl { name := n, levelParams := ci.levelParams, type := ty, value := val })
  return n

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let n ← generateA ``Sparkle.Tests.Compiler.LeafDeadInitTest.dead7
  logInfo m!"{n} added"

open Tests.Compiler.ChildVertAuditTest in
/-- Audit of `dead7.machine_design_closedA` (THROWS): standard axioms; the outer Prop premises are
exactly `RunsTo`, `MachineDefines`, `AdmCtx`, `JQ`; the closure (type, value, opaque bodies,
constructors) contains no old-boundary constant (`RefLaws`, `RefLawsCore`, `toAOps`, `toA`, `ChildBnd`,
`StartV`). The opaque/extern/implemented_by counts are structural, not a runtime-fit proof. -/
def auditDesignClosedA (n : Name) : TermElabM Unit := do
  stdAxioms n
  let ty := (← getConstInfo n).type
  let outer ← forallTelescope ty fun xs _ => do
    let mut ps : Array Lean.Expr := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then ps := ps.push t
    return ps
  unless outer.size == 4 do throwError "{n}: {outer.size} outer premises, 4 expected"
  let heads := outer.map (·.getAppFn.constName?)
  unless heads.contains (some ``Tools.ShippingEntrySoundness.RunsTo) &&
      heads.contains (some ``Tools.ShippingMachineEntry.MachineDefines) &&
      heads.contains (some ``Tools.ShippingChildInvA.AdmCtx) &&
      heads.contains (some ``Tools.ShippingChildVCA.JQ) do
    throwError "{n}: outer premises are not run / MachineDefines / AdmCtx / JQ: {heads}"
  -- `O` is data (a Type), not a Prop: exactly one binder of type `RefLawsAOps _ _ _`, and no binder
  -- of type `RefLawsATele` (dead7 is a leaf: no T needed).
  let (nO, nTele) : Nat × Nat ← forallTelescope ty fun xs _ => do
    let mut a : Nat := 0; let mut b : Nat := 0
    for x in xs do
      let t ← inferType x
      if t.getAppFn.constName? == some ``Tools.ShippingChildInvA.RefLawsAOps then
        -- the Fresh argument must be exactly `MkRefd` (not another freshness predicate)
        unless (t.getAppArgs[0]?.bind (·.constName?)) == some ``Tools.ShippingChildFresh.MkRefd do
          throwError "{n}: RefLawsAOps binder with Fresh ≠ MkRefd: {t}"
        a := a + 1
      if t.getAppFn.constName? == some ``Tools.ShippingChildInvA.RefLawsATele then b := b + 1
    return (a, b)
  unless nO == 1 && nTele == 0 do
    throwError "{n}: {nO} RefLawsAOps binders (1 expected), {nTele} RefLawsATele binders (0 expected)"
  let cl ← depClosure n
  let bad := hits cl ++ cl.toList.filter fun c =>
    [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV,
     `Tools.ShippingChildInvA.RefLawsATele].any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "{n}: old boundary in closure: {bad}"
  let (axs, ops, exts, impls) ← boundary cl
  logInfo m!"LEAFDESIGN-A AUDIT OK: {n}: standard axioms; outer premises exactly run / MachineDefines / AdmCtx / JQ (+ exactly one data binder O : RefLawsAOps MkRefd _ _, no RefLawsATele binder); closure {cl.size} constants, no RefLaws/RefLawsCore/toAOps/toA/ChildBnd/StartV/RefLawsATele; boundary (structural): {axs.length} axioms, {ops.length} opaque, {exts.length} extern, {impls.length} implemented_by"

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  auditDesignClosedA ``Sparkle.Tests.Compiler.LeafDeadInitTest.dead7.machine_design_closedA

#print axioms Sparkle.Tests.Compiler.LeafDeadInitTest.dead7.machine_design_closedA

/-- Old vs new head: after the 8 implicit data arguments, `hr`, `entry` (shared, aligned positions),
the final conclusions (`MachineDesignClosed`-style statement of the old `hbnd`-head and of the new
`(O, hA, hw)`-head) are `isDefEq` (THROWS otherwise). The extra binders (`hbnd` vs `O hA hw`) must
not occur in the conclusions. -/
def checkSameConclusion (old new : Name) : TermElabM Unit := do
  let tn := (← getConstInfo new).type
  let to := (← getConstInfo old).type
  forallTelescope tn fun xs cn => do
    unless xs.size == 13 do throwError "new head: {xs.size} binders, 13 expected"
    -- shared prefix: 8 implicits + hr + entry
    let mut t := to
    for x in xs.extract 0 10 do
      let .forallE _ d b _ := t.headBeta | throwError "old head: fewer binders than expected"
      unless ← isDefEq d (← inferType x) do
        throwError "shared binder type mismatch:\n  old {d}\n  new {← inferType x}"
      t := b.instantiate1 x
    forallTelescope t fun ys co => do
      unless ys.size == 1 do throwError "old head: {ys.size} extra binders (hbnd), 1 expected"
      unless !cn.containsFVar xs[10]!.fvarId! && !cn.containsFVar xs[11]!.fvarId! &&
          !cn.containsFVar xs[12]!.fvarId! && !co.containsFVar ys[0]!.fvarId! do
        throwError "a conclusion depends on hbnd / O / hA / hw"
      unless ← isDefEq co cn do
        throwError "conclusions differ:\n  old {co}\n  new {cn}"
      logInfo m!"CONCLUSION CHECK OK: {old} and {new} have isDefEq conclusions (shared 10 binders, then hbnd vs O hA hw)"

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  checkSameConclusion ``Sparkle.Tests.Compiler.LeafDeadInitTest.dead7.machine_design_closed
    ``Sparkle.Tests.Compiler.LeafDeadInitTest.dead7.machine_design_closedA

end Sparkle.Tests.Compiler.LeafDesignClosedATest
