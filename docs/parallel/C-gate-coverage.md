# `#gate_coverage` — a separate tally of gate-route parents (worker C, par/gate-cov)

WRITTEN, NOT BUILT. Ruling (reviewer, 2026-10-15): gate-parent rows are a SEPARATE kind with separate columns
(existence-only / all-run / remaining conditions; target-only vs in-suite); never claim all-input coverage from
the machine-route population. `GateDefines` is a separate gate-only reflection class
(`docs/parallel/G-gatedefines-class.md`).

## Files
* `Tools/ShippingGateCoverage.lean` (new): `#gate_coverage p₁ … pₙ`. Reads the environment only; nothing added.
  `#design_coverage` / `#outermost_coverage` and the machine classifier `Tools.ShippingFinalGoalCommand.allowed`
  are unchanged (reused, not edited). Machine-route census numbers (134 / 133) cannot change: no file of that
  census is touched, and `GateCoverageTest` is target-only.
* `Tests/Compiler/GateCoverageTest.lean` (new, TARGET-ONLY): imports `GateConeDesignAllTest`,
  `GateConeWrapPickSourceTest`; runs the command on the eight parents.
* `lakefile.lean`: `lean_lib «Tools.ShippingGateCoverage» where roots := #[`Tools.ShippingGateCoverage]`
  (the test is a module of the existing `Tests` lib, no line needed).

## How a theorem is read (by TYPE, never by name)
* belongs to `P`: a leading binder `RunsTo (synthesizeCombinational ``P) …` (name literal decoded by `Expr.name?`).
* observation: mentions `evalAssignsH` and the constant `P`, directly or through a `… → Prop` definition up to two
  deep (`ParentMixObserves` → `ParentMixObservesC`). `WrapPickObservesT` (against `pickF`, only the literal
  ``wrapPick``) does not count.
* existence: a subterm `∃ e, DesignSV … e ∧ R`, `R` mentioning `P`; all-run: `∀ e, DesignSV … e → R`, `R`
  mentioning `P`.
* premises (binders + antecedents met under `∃`/`∧`/`∀` of the conclusion, stopping at the two clauses):
  `run` / `GATE` (`GateDefines`; capitals if the machine classifier ever allows it) / `ALLOWED` (classifier) /
  `INPUT` (the `Admissible` seeding antecedent) / `OTHER` (head constant, a remaining condition); plus the census's
  checker / closing constants mentioned.
* axioms: `Lean.collectAxioms`, OK iff ⊆ {propext, Classical.choice, Quot.sound}.
* in-suite: theorem's module in the import closure of `Tests.AllTests`, read from the source files under the
  current directory (else `UNKNOWN`).

## Build order (integrator, serial, cgrun)
1. `lake build Tools.ShippingGateCoverage`
2. `lake build Tests.Compiler.GateCoverageTest` (needs the gate test modules built; they are target-only).

## Predicted output (not measured)
SCAN: 8 parents; in-suite closure ≈ 1221 modules (python reading of the same import lines).

Rows (columns abbreviated; theorem lists are by last name component):

| parent | observation | existence-only | all-run | remaining (strongest form) | axioms | suite |
|---|---|---|---|---|---|---|
| parentUse | cone_runK', designA, designSV…, SVN…, SVall | designSV…, SVN, SVN2, SVN3 | `parentUse_gate_designSVall` | GATE [GateDefines]; OTHER [DesignSideR]; INPUT [Admissible]; ALLOWED [ChildBnd, EntryDefines] | OK | target-only |
| wrapAdd | same pattern | same | `wrapAdd_gate_designSVall` | same | OK | target-only |
| parentMix | + cone_runG / runG' / runK (OTHER: isHardwareModule-, get?-, fst-, modules- antecedents) | same | `parentMix_gate_designSVall` | same | OK | target-only |
| parentTwoCalls | same pattern | same | `…_designSVall` | same | OK | target-only |
| parentRepeat | same pattern | same | `…_designSVall` | same | OK | target-only |
| parentCmp | same pattern | same | `…_designSVall` | same | OK | target-only |
| parentNested | same pattern | same | `…_designSVall` | same | OK | target-only |
| wrapPick | `wrapPick_gate_cone_runK'` | NONE | NONE | (observation) GATE [GateDefines]; OTHER []; ALLOWED [ChildBnd, EntryDefines] | OK | target-only |

`wrapPick_gate_cone_runKT` and helper lemmas (`entryWN`, `coneKC`, …, when they carry the run binder) are counted
in "none of the three forms".

TOTALS (predicted): observation 8; existence-only 7; all-run 7; no form []; GATE CLASS 8; remaining OTHER of the
strongest forms [DesignSideR]; non-standard axioms []; in-suite 0, target-only 8, mixed 0; followed by the
SEPARATE-TALLY / no-all-input disclaimer.

## Risks
* Not built: API spellings (`Expr.name?`, `collectAxioms` in `MetaM`, `realizeGlobalConstNoOverloadWithInfo`,
  `String.splitOn`/`startsWith`, structural recursion of `isPredType` on `Expr`) checked against the v4.32.1
  sources but not compiled.
* In-suite depends on lean's working directory being the package root (lake's default); otherwise the column is
  `UNKNOWN`, not wrong.
* Import parsing is line-based (stops at the first `namespace` / `/-!` / `open` / … line).
* The observation test is syntactic plus two deltas; a source observation stated through a deeper chain of
  definitions would be missed (counted under "none of the three forms").
* "all-run" is the theorem's every-closed-run clause from its own seeding/states (`ships_design_svN_all` form), not
  all inputs; the row and TOTALS say so.

## Integration (integrator, 2026-10-15) — BUILT with fixes, MEASURED
Applied on poc b3248937 (+ lakefile lean_lib). Run `gcov` (cgrun, 3 GiB, swap 0, `-j 1`). As written
`Tools.ShippingGateCoverage` failed to parse: a multi-line structure instance in a `do` block (a field on a
continuation line) and `TSyntax` passed where `Syntax` is expected; integrator fixes: the record on one line
(values bound by `let` first), `id.raw`. Then `Tools.ShippingGateCoverage`, `Tests.Compiler.GateCoverageTest`:
exit 0. `#design_coverage` / `#outermost_coverage` / ALLOWED untouched.
MEASURED (Tests.Compiler.GateCoverageTest):
    GATE COVERAGE TOTALS of 8 gate-route parent(s): observation 8; existence-only 7; all-run 7; no theorem of any form []; strongest form carries GateDefines (GATE CLASS) for 8; remaining OTHER conditions of the strongest forms [DesignSideR]; non-standard axioms in []; in-suite 0, target-only 8, mixed 0. 1417 ms. A SEPARATE TALLY of the kind 'gate-route parent': NOT part of #design_coverage (its machine-route population and counts are unchanged and counted apart) nor of #outermost_coverage. GateDefines is the separate 
Per parent (seven): all-run `<p>_gate_designSVall`, remaining from it: GATE CLASS [GateDefines]; OTHER
[DesignSideR]; INPUT [Admissible]; ALLOWED [ChildBnd, EntryDefines]; axioms standard; target-only.
wrapPick: observation `wrapPick_gate_cone_runK'` only (no existence / all-run), GATE CLASS [GateDefines];
ALLOWED [ChildBnd, EntryDefines]; target-only.
