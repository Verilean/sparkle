import Tests.Compiler.OneOutFamilyTest

/-! # `#machine_oneout` on parents with TWO called declarations: `callerMix`, `callerABA` (G1, round par/a-10)

Both are register parents (`sel`, `acc`) of GATE children in the one-output
closing; the callees are two DECLARATIONS, `pick` and `pickD`:

| | declaration | call entries | what is new against `callerRep` |
|---|---|---|---|
| (i) | `callerMix` | `pick`, `pickD` | two distinct callees: the generator's per-entry DISJUNCTION (`f.oneout_entries` is `∀ k hk, (entry k is pick ∧ …) ∨ (entry k is pickD ∧ …)`, the proofs split it with `rcases`), two `EntryDefines` binders in every generated lemma |
| (ii) | `callerABA` | `pick`, `pickD`, `pick` | the same with three entries, the first callee twice |

## What was read before writing this file (the expectations below rest on it)

* `Tools/ShippingMachineClosesAtGen.lean` (`closesAtCore`): with several
  called declarations the name premises `hnames` / `hparent` are binders of
  `f.machine_closes_at` ONLY when `Tools.ShippingNameSep.sepB` fails on a
  pair; otherwise they are discharged inside the proof by
  `Tools.ShippingNameSep.Enc.hnames_of _ (by decide)` /
  `hparent_of _ _ (by decide)`. `hfresh` is discharged when no output name
  starts with `i`.
  ROUND par/b-30 (WRITTEN, NOT BUILT): `hnames` is now ALWAYS discharged
  (`Tools.ShippingNameDischarge.names_inj _`, no condition) and `hparent` by
  `parent_ne _ _ (by decide)` on the declaration NAMES; a `hparent` binder
  only where a call entry is a call of the parent itself. The statements of
  `f.machine_closes_at` for the two declarations here are unchanged (they
  had no name binder); the assertion below now names the new lemmas.
* `Tests/Compiler/ShippingCallsCloseTest.lean` (BUILT, in `Tests.AllTests`):
  `auditClosed callerMix 2` and `auditClosed callerABA 2` — each
  `machine_closes_at` has EXACTLY TWO proposition binders, and the first is
  a reflection. With two distinct callees the generator pushes two
  reflection binders (`hR0`, `hR1`) before any name binder; so two binders
  in all means NO name-separation binder: `sepB` held and the three name
  conditions were discharged.
* `Tools/ShippingOneOutGenCommand.lean`, the several-callee branch
  (`perEntry` at `n ≥ 2`, `alt`, the `binders` / `hRs` loops): read against
  the single-callee branch that built. No defect found by reading; no
  corrected generator was written. It was never elaborated before this file.

## EXPECTED outcome (stated before the build, asserted below)

For both declarations: `GENERATED`; the premises of `f.machine_closes_at`
are exactly `EntryDefines … pick pick.gateValue` and
`EntryDefines … pickD pickD.gateValue` (class `reflection`), none mentions
`Lean.Name.toString`, and the proof uses `names_inj` and `parent_ne`
(par/b-30; before: `Enc.hnames_of` and `Enc.hparent_of`);
therefore the closed form `f.machine_design_svH_full_closed` has NO premise
of class `other` — the previous round's guess ("name-separation premises
expected in the closed form") is expected to be WRONG for these two. The
closed form's proposition binders: the run, `MachineDefines f`, the two
`EntryDefines`; under `∃ raw D`: `ChildBnd`, the two `EntryDefines`.

If instead a name premise is a binder of `machine_closes_at`, the family
audit throws at "contributes premises that are not a run / a reflection /
ChildBnd", printing it: that outcome is an error of this file, not silently
accepted — the expectation above would have to be restated.

## What a GENERATED line means here (binding)

The scope sentence of `Tests/Compiler/OneOutFamilyTest.lean` applies
unchanged, one declaration at a time: per-declaration data conditions
decided by the kernel (`f.oneout_*`, `pick.gate_width`, `pickD.gate_width`,
what `#gate_child` left; for `machine_closes_at` also "no call entry is a
call of the parent", decided on the declaration names) are conditions, not
reductions; the run, `MachineDefines f`,
`EntryDefines pick`, `EntryDefines pickD`, `ChildBnd` stay premises; the
result depends on the compiler's guards; the conclusion is about
`DesignSV (childMap D.modules) 0 (checkedOptimize b)`. A parent WITH a
register, GATE children, the one-output closing. NOT slotless parents, NOT
machine-route children, NOT several outputs, NOT "all successful inputs".

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.OneOutTwoCalleeTest
open Lean Meta Elab Command

/-- The assertions specific to two called declarations: what
`f.machine_closes_at` asks, and that both reflections are binders of the
closed endpoint. Skipped (with a log line) where no endpoint was generated. -/
def twoCallee (f : Name) (kids : List Name) : MetaM Unit := do
  let full := f ++ `machine_design_svH_full
  let closed := Tools.ShippingMachineClosesGen.closedName full
  let cl := f ++ `machine_closes_at
  unless (← getEnv).contains closed do
    logInfo m!"ONEOUT TWO-CALLEE {f}: no closed endpoint — the name-separation question is NOT answered for {f}"
    return
  -- the proposition binders of `f.machine_closes_at`
  let clT := (← getConstInfo cl).type
  let props ← forallTelescope clT fun xs _ => do
    let mut acc : Array Lean.Expr := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then acc := acc.push t
    return acc
  let printed ← props.mapM fun t => do return toString (← ppExpr t)
  unless props.size == kids.length do
    throwError "{cl}: {props.size} proposition binders, expected {kids.length} (one EntryDefines per called declaration):\n{String.intercalate "\n" printed.toList}"
  for t in props do
    unless t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines do
      throwError "{cl}: a binder that is not an EntryDefines: {← ppExpr t}"
    if (t.find? (fun e => e.isConstOf ``Lean.Name.toString || e.isConstOf ``Sparkle.IR.ModuleName.ofDecl)).isSome then
      throwError "{cl}: a binder states a name condition (Name.toString): {← ppExpr t}"
  for c in kids do
    unless props.any (fun t => (t.find? (·.isConstOf (c ++ `gateValue))).isSome) do
      throwError "{cl}: no EntryDefines binder of {c}"
  -- the name conditions: discharged inside the proof from the DECLARATION
  -- names (par/b-30) — the proof term of `machine_closes_at` applies
  -- `names_inj` (callee against callee: no condition, `ofDecl` is injective)
  -- and `parent_ne` (callee against parent: `decide` on `Lean.Name`s), and
  -- does NOT apply the candidate-rendering lemmas of `Tools.ShippingNameSep`
  let used : Array Name := match (← getEnv).find? cl with
    | some (.thmInfo ti) => ti.value.getUsedConstants
    | _ => #[]
  let hn := used.contains ``Tools.ShippingNameDischarge.names_inj
  let hp := used.contains ``Tools.ShippingNameDischarge.parent_ne
  unless hn && hp do
    throwError "{cl}: the proof does not go through Tools.ShippingNameDischarge (names_inj used: {hn}, parent_ne used: {hp}) although no name premise is a binder"
  for old in [``Tools.ShippingNameSep.Enc.hnames_of, ``Tools.ShippingNameSep.Enc.hparent_of] do
    if used.contains old then
      throwError "{cl}: the proof still applies {old} (the candidate renderings)"
  -- the closed endpoint: no name condition written, every callee's reflection a binder
  let closedT := (← getConstInfo closed).type
  if (closedT.find? (fun e => e.isConstOf ``Lean.Name.toString || e.isConstOf ``Sparkle.IR.ModuleName.ofDecl)).isSome then
    throwError "{closed}: the statement writes a name condition (Name.toString)"
  let cprops ← forallTelescope closedT fun xs _ => do
    let mut acc : Array Lean.Expr := #[]
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if ← isProp t then acc := acc.push t
    return acc
  for c in kids do
    unless cprops.any (fun t => t.isAppOf ``Tools.ShippingInlineSoundness.EntryDefines &&
        (t.find? (·.isConstOf (c ++ `gateValue))).isSome) do
      throwError "{closed}: no EntryDefines binder of {c}"
  logInfo m!"ONEOUT TWO-CALLEE {f}: {cl} has {props.size} proposition binders, all EntryDefines ({kids}), none a name condition; the name separation (callee against callee, callee against parent) is discharged inside its proof by Tools.ShippingNameDischarge.names_inj / parent_ne — callee against callee with no condition (ofDecl is injective), callee against parent decided by the kernel on the declaration NAMES (a per-declaration condition, not a reduction); {closed} writes no Name.toString and has the reflection of each of {kids} as a binder. The expectation of the previous round (name-separation premises in the closed form) does NOT hold for {f}."

end Tests.Compiler.OneOutTwoCalleeTest

/-! ## (i) `callerMix` (`pick`, `pickD`) — expected GENERATED, closed form without a premise of class `other` -/

set_option maxHeartbeats 0 in
#machine_oneout_try Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick,
     ``Sparkle.Tests.Compiler.ShippingMachineInstTest.pickD] false
  Tests.Compiler.OneOutTwoCalleeTest.twoCallee
    ``Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick,
     ``Sparkle.Tests.Compiler.ShippingMachineInstTest.pickD]

/-! ## (ii) `callerABA` (`pick`, `pickD`, `pick`) — expected GENERATED, closed form without a premise of class `other` -/

set_option maxHeartbeats 0 in
#machine_oneout_try callerABA "GENERATED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Tests.Compiler.OneOutFamilyTest.audit ``callerABA
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick,
     ``Sparkle.Tests.Compiler.ShippingMachineInstTest.pickD] false
  Tests.Compiler.OneOutTwoCalleeTest.twoCallee ``callerABA
    [``Sparkle.Tests.Compiler.ShippingMachineInstTest.pick,
     ``Sparkle.Tests.Compiler.ShippingMachineInstTest.pickD]
