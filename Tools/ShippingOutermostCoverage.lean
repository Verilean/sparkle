import Lean.Elab.Command
import Tools.ShippingDesignCoverage
import Tools.ShippingMachineRan

/-! # `#outermost_coverage`: design-level endpoints at OUTERMOST starts — a SEPARATE tally (round par/g-1)

WRITTEN, NOT BUILT. A MEASUREMENT of the environment of the file it is run
in: it adds nothing and proves nothing. `Tools/ShippingDesignCoverage.lean`
(`#design_coverage`, the census) is NOT edited and its counts are not
touched.

## Why a separate table

The census counts a declaration as COVERED when one of its
`machine_design_…` constants has every proposition binder and every
antecedent ALLOWED by `Tools.ShippingFinalGoalCommand.allowed` (the run, a
reflection, `ChildBnd`, conjunctions of those). An endpoint at outermost
starts has one more premise,

    Start0 mref cref w    -- for ONE law witness: the synthesis ref is set,
                          -- the synthesis depth reads 0, the world is quiet

which that classifier does NOT allow and which is NOT added to it (ruling of
2026-10-14). Such an endpoint holds from depth-0 starts only; the census's
endpoints hold from every world of `ChildBnd` (depth 0, or nested with an
invariant cache). The two are different scopes and are counted apart.

## What this command lists

Every constant `f.s` whose last component `s` is a design-level name of the
census (`Tools.ShippingDesignCoverage.isDesign`) AND ends with `_outermost`.
It is an OUTERMOST START of `f` when, on its stored statement,

1. exactly ONE proposition binder is `Start0 …`, and every OTHER proposition
   binder is ALLOWED by the census's classifier;
2. every antecedent under the leading existentials is ALLOWED;
3. it mentions none of the census's checker / closing constants
   (`Tools.ShippingDesignCoverage.checkerConsts`: the seven checkers,
   `MachineCloses`, `MachineClosesAt`, `ChildRanIn`);
4. it mentions `Tools.ShippingDesignSV.DesignSV`.

For each constant the row also gives what the CENSUS's own re-check
(`Tools.ShippingDesignCoverage.recheck`, unchanged) says of it. By READING
of that function such a constant FAILS it (its `Start0` binder is counted
NOT ALLOWED), so the census lists it among the declaration's design-level
constants that are not check-free and does not count it. If the census's
re-check PASSES on one, the row says so in capitals: that would be a defect
of the census, to be reported, not a result.

A constant under a prefix that is not itself a constant of the environment
(a test namespace) is listed with the note that the census gives such a
prefix no row. -/
namespace Tools.ShippingOutermostCoverage
open Lean Meta Elab Command

/-- A design-level constant name of the census that ends with `_outermost`. -/
def isOutermost (s : String) : Bool :=
  Tools.ShippingDesignCoverage.isDesign s && s.endsWith "_outermost"

/-- The re-check of one `…_outermost` constant. -/
structure Check where
  ok : Bool
  props : Nat
  start0 : Nat
  /-- `Start0` binders the census's classifier allows (expected 0) -/
  start0Allowed : Nat
  badOther : Nat
  antes : Nat
  badAntes : Nat
  checkers : List Name
  hasDesign : Bool
  err : Option String := none

def recheck (c : Name) : MetaM Check := do
  try
    let ci ← getConstInfo c
    let ty := ci.type
    let checkers := Tools.ShippingDesignCoverage.checkerConsts.filter fun k =>
      (ty.find? (·.isConstOf k)).isSome
    let hasDesign := (ty.find? (·.isConstOf ``Tools.ShippingDesignSV.DesignSV)).isSome
    let (props, start0, start0Allowed, badOther, antes, badAntes) ←
      forallTelescope ty fun xs body => do
        let mut props : Nat := 0
        let mut start0 : Nat := 0
        let mut start0Allowed : Nat := 0
        let mut badOther : Nat := 0
        for x in xs do
          let t ← instantiateMVars (← inferType x)
          if ← isProp t then
            props := props + 1
            let ok := Tools.ShippingFinalGoalCommand.allowed t
            if t.isAppOf ``Tools.ShippingMachineRan.Start0 then
              start0 := start0 + 1
              if ok then start0Allowed := start0Allowed + 1
            else
              unless ok do badOther := badOther + 1
        let (antes, badAntes) ← Tools.ShippingDesignCoverage.antecedents body
        pure (props, start0, start0Allowed, badOther, antes, badAntes)
    return { ok := start0 == 1 && badOther == 0 && badAntes == 0 && checkers.isEmpty && hasDesign,
             props, start0, start0Allowed, badOther, antes, badAntes, checkers, hasDesign }
  catch ex =>
    let msg ← ex.toMessageData.toString
    return { ok := false, props := 0, start0 := 0, start0Allowed := 0, badOther := 0, antes := 0,
             badAntes := 0, checkers := [], hasDesign := false, err := some msg }

/-- The `…_outermost` design-level constants of the environment:
(declaration prefix, constant). -/
def collect (env : Environment) : Array (Name × Name) :=
  env.constants.fold (fun (acc : Array (Name × Name)) (n : Name) (_ : ConstantInfo) =>
    match n with
    | .str p s => if isOutermost s then acc.push (p, n) else acc
    | _ => acc) #[]

/-- `#outermost_coverage`: see the file header. -/
elab "#outermost_coverage" : command => do
  logInfo m!"OUTERMOST COVERAGE START"
  let env ← getEnv
  let found := (collect env).qsort fun a b => a.2.toString < b.2.toString
  let mut rows : Array String := #[]
  let mut starts : Array Name := #[]
  let mut censusPass : Array Name := #[]
  for (p, c) in found do
    let (ch, census) ← liftTermElabM do
      let ch ← recheck c
      let census ← Tools.ShippingDesignCoverage.recheck c
      pure (ch, census.ok)
    let isDecl : Bool := env.contains p
    let declNote : String :=
      if isDecl then "its prefix is a declaration"
      else "its prefix is NOT a constant of the environment (the census gives it no row)"
    let censusNote : String :=
      if census then "THE CENSUS'S RE-CHECK PASSES ON IT — it would be counted COVERED: a defect of the census to report"
      else "the census's re-check fails on it (not counted COVERED)"
    if census then censusPass := censusPass.push c
    let detail : String := match ch.err with
      | some e => s!"error {e}"
      | none => s!"proposition binders {ch.props}: Start0 {ch.start0} (of which ALLOWED by the census's classifier: {ch.start0Allowed}), other NOT ALLOWED {ch.badOther}; antecedents under the existentials {ch.antes}, NOT ALLOWED {ch.badAntes}; checker / closing constants {ch.checkers}; DesignSV mentioned: {ch.hasDesign}"
    if ch.ok then
      starts := starts.push p
      rows := rows.push s!"OUTERMOST ROW {p}: OUTERMOST START by {c} — {detail}; {declNote}; {censusNote}"
    else
      rows := rows.push s!"OUTERMOST ROW {p}: NOT an outermost start: {c} — {detail}; {declNote}; {censusNote}"
  for r in rows do logInfo m!"{r}"
  let distinct := starts.toList.eraseDups
  logInfo m!"OUTERMOST COVERAGE TOTALS: {found.size} constant(s) named machine_design_…_outermost; outermost starts: {distinct.length} declaration(s) {distinct}. OUTERMOST SCOPE — a SEPARATE population: these are NOT counted in #design_coverage's COVERED total and do not change it. An outermost start means: every premise ALLOWED except exactly one Start0 (depth 0 for the law witness at the start world — a runtime premise of the same kind as ChildBnd, NOT ALLOWED by Tools.ShippingFinalGoalCommand.allowed and not added to it), no checker / closing constant, a DesignSV conclusion; it says nothing at nested starts. Constants of this list on which the census's own re-check passes (expected none): {censusPass.toList}"

end Tools.ShippingOutermostCoverage
