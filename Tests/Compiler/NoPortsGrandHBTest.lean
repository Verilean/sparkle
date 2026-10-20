import Tests.Compiler.NoPortsGrandHTest
import Tools.ShippingBoundaryClose

/-! # `grandH`: the boundary of the closed check-free endpoint, reduced to `ChildBnd` (G1, round par/a-14)

The BUILT `grandH.machine_design_noPortsNR1_closed` has ONE antecedent under
its existentials (real log, `docs/parallel/verification-a13.md` 94–105):

    ChildBnd mref cref w ∧
      MachineDefines mctx mref cctx cref `midH midH.machineData.shape ∧
        True ∧
          ∀ mctx' cctx', ChildRanIn mref cref `midH mctx' cctx' →
            ∀ wc raw D, ChildBnd mref cref wc →
              ChildBnd mref cref wc ∧ EntryDefines mctx' mref cctx' cref `rcH rcH.gateValue

and the binders (same log, 88–93)

    entry : MachineDefines mctx mref cctx cref `grandH …
    hR_…midH : MachineDefines mctx mref cctx cref `midH midH.machineData.shape
    hRr : EntryDefines mctx mref cctx cref `rcH rcH.gateValue

BY READING: conjunct 2 IS the binder `hR_…midH`; conjunct 3 is `True`;
conjunct 4 follows from `hRr` alone — given `mctx' cctx'`, the (unused)
`ChildRanIn`, `wc raw D` and `hb : ChildBnd mref cref wc`, the pair is
`⟨hb, Tools.ShippingReflectCtx.EntryDefines.ctx hRr⟩` (a reflection does
not depend on the contexts; BUILT). `ChildRanIn` gives nothing that is
needed. So the antecedent is equivalent, under the binders, to
`ChildBnd mref cref w`.

`#machine_boundary_close` (`Tools/ShippingBoundaryClose.lean`) adds

    grandH.machine_design_noPortsNR1_closedB

— the same binders, the antecedent under the existentials `ChildBnd mref
cref w` only — proved by applying the BUILT `_closed` to the reassembled
antecedent; `#machine_goal_gap_of` then adds `…_closedB_gap`.

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise of `grandH.machine_design_noPortsNR1_closed` | predicted state |
|---|---|---|
| `grandH.machine_design_noPortsNR1_closedB` | antecedent conjunct `MachineDefines midH` (a binder too) | WRITTEN, NOT BUILT — predicted absent from the antecedent (stays a binder), pending build |
| | antecedent conjunct `True` | predicted absent, pending build |
| | antecedent conjunct `∀ mctx' cctx', ChildRanIn … midH … → ∀ wc raw D, ChildBnd wc → ChildBnd wc ∧ EntryDefines mctx' … rcH` (NOT ALLOWED) | predicted absent, pending build |
| | antecedent conjunct `ChildBnd mref cref w` | STAYS (allowed) |
| | binders: the run, `MachineDefines grandH`, `MachineDefines midH`, `EntryDefines rcH` | STAY, unchanged; none added |
| `…_closedB_gap` | gap hypotheses | predicted NONE; premise listing 0 NOT ALLOWED |

SCOPE: one declaration; nothing about the compiler is proved here (the new
theorem is the built one applied); every scope clause of
`NoPortsGrandHTest` stands. The OPEN form `grandH.machine_design_noPortsNR1`
is not touched (it has no reflection binder of `midH` to derive from: its
`MachineDefines midH` is only in the boundary — it could be reduced by the
same command to `ChildBnd ∧ MachineDefines midH`; not done).

UNVERIFIED at the time of writing: this file was not built. -/

set_option maxHeartbeats 0 in
#machine_boundary_close
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closed

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH.machine_design_noPortsNR1_closedB

namespace Tests.Compiler.NoPortsGrandHBTest
open Lean Meta

/-- Under the existentials of `∃ w…, P ∧ (A → C)`: is `A` an application of
`ChildBnd` (three arguments)? -/
partial def onlyBnd (ty : Lean.Expr) : MetaM Bool := do
  if ty.isAppOfArity ``Exists 2 then
    let p := ty.getArg! 1
    withLocalDeclD `w (ty.getArg! 0) fun w => onlyBnd (mkApp p w).headBeta
  else if ty.isAppOfArity ``And 2 then
    let R := ty.getArg! 1
    return R.isForall && R.bindingDomain!.isAppOfArity ``Tools.ShippingChildInv.ChildBnd 3
  else return false

/-- The audit of a reduced closed form `closedB` of `closed`: standard
axioms, no checker constant, the same binders, exactly one antecedent under
the existentials and it is `ChildBnd`, 0 NOT ALLOWED in the premise listing,
no gap hypothesis in `closedB_gap`. Returns the premise lines. -/
def auditB (closed closedB gap : Name) : MetaM (Array String) := do
  for n in [``Tools.ShippingReflectCtx.MachineDefines.ctx,
      ``Tools.ShippingReflectCtx.EntryDefines.ctx, closed, closedB, gap] do
    unless (← getEnv).contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  let cT := (← getConstInfo closed).type
  let bT := (← getConstInfo closedB).type
  let gT := (← getConstInfo gap).type
  for (n, t) in [(closedB, bT), (gap, gT)] do
    for c in Tests.Compiler.NoPortsTest.checkers do
      if (t.find? (·.isConstOf c)).isSome then throwError "{n}: the statement mentions {c}"
    if (t.find? (·.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
      throwError "{n}: asks MachineClosesAt"
    if (t.find? (·.isConstOf ``Tools.ShippingChildInv.ChildRanIn)).isSome then
      throwError "{n}: still mentions ChildRanIn (a child's boundary over contexts)"
  -- the same binders, in the same order, with the same types
  let same ← forallTelescope cT fun xs _ => pure xs.size
  let nB ← forallTelescope bT fun xs _ => pure xs.size
  unless same == nB do
    throwError "{closedB}: {nB} binders, {closed} has {same}"
  let pc ← forallTelescope cT fun xs _ => do
    let mut out : Array String := #[]
    for x in xs do
      out := out.push (toString (← ppExpr (← instantiateMVars (← inferType x))))
    return out
  let pb ← forallTelescope bT fun xs _ => do
    let mut out : Array String := #[]
    for x in xs do
      out := out.push (toString (← ppExpr (← instantiateMVars (← inferType x))))
    return out
  unless pc == pb do
    throwError "{closedB}: its binders are not those of {closed}:\n{pb}\nvs\n{pc}"
  -- the antecedents under the existentials
  let innerOld ← forallTelescope cT fun _ body => Tests.Compiler.NoPortsTest.innerAntecedents body
  let inner ← forallTelescope bT fun _ body => Tests.Compiler.NoPortsTest.innerAntecedents body
  unless innerOld.size == 1 && !innerOld[0]!.2 do
    throwError "{closed}: expected ONE antecedent, not allowed (the inventory is wrong): {innerOld.map (·.1)}"
  unless inner.size == 1 && inner[0]!.2 do
    throwError "{closedB}: expected ONE allowed antecedent under the existentials: {inner.map (·.1)}"
  let isBnd ← forallTelescope bT fun _ body => onlyBnd body
  unless isBnd do throwError "{closedB}: the antecedent is not ChildBnd mref cref w alone"
  -- the premise listing and the gap theorem
  let (lines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closedB
  unless bad.isEmpty do
    throwError "{closedB}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
  let gaps ← Tests.Compiler.ShipsFreeMaskedTest.gapNames gap
  unless gaps.isEmpty do throwError "{gap}: the gap hypotheses are {gaps}, expected none"
  return lines

end Tests.Compiler.NoPortsGrandHBTest

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let g := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH
  let closed := g ++ `machine_design_noPortsNR1_closed
  let closedB := g ++ `machine_design_noPortsNR1_closedB
  let gap := g ++ `machine_design_noPortsNR1_closedB_gap
  let lines ← Tests.Compiler.NoPortsGrandHBTest.auditB closed closedB gap
  Lean.logInfo m!"{String.intercalate "\n" lines.toList}"
  Lean.logInfo m!"NOPORTS GRANDH BOUNDARY {g}: {closedB} (from the built {closed} by Tools.ShippingBoundaryClose: the boundary's conjuncts MachineDefines midH, True and the ∀-contexts conjunct about midH's own boundary are DERIVED from the binders by EntryDefines.ctx — nothing assumed, the binders are those of {closed}) and {gap} on standard axioms; under the existentials ONE antecedent, ChildBnd mref cref w; {lines.size} binders and antecedents listed, 0 NOT ALLOWED; NO gap hypothesis; no checker constant, no MachineClosesAt, no ChildRanIn in either statement. SCOPE: as NoPortsGrandHTest (one declaration, depth 1, per-declaration decided data conditions, compiler guards with fallback, DesignSV of the module list, not the SV string, not #sim); the run, the reflections of grandH / midH / rcH at the run's contexts and ChildBnd at the start world remain premises."
