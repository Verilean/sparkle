import Tools.ShippingFGCircuitS2bRun
set_option autoImplicit false
-- FG circuit pilot S2b check (light, small run_cmd blocks). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §30.

/-! # FGCircuitPilotCheck25

1. AXIOMS: `ds_fun`, `circCVS_functional`, the table rules, `HftObCDS`, `HftFinalStmtS` use only the standard axioms.
2. LEVEL-CONTROLS: the evidence `lvlNat u = some 1` accepts `1` and `max 1 1`, and rejects `0`, `max 1 2`, `imax 1 0`, a parameter.
3. SMALL-DERIVE: the typed `DS` derivation of `default (Bool × Bool)` through `instInhabitedProd` (whose unfolding contains `Inhabited.mk.{max 1 1}`) is generated and kernel-checked
   (the S1w2 STOP-1: not derivable in `DW`); its numbers (nodes / ms / term size) are logged.
4. CONTROLS: an expression with another constructor (`Option.some`), and `Inhabited.default.{max 1 1}` (only `mk` was generalised), are NOT derivable.
5. FAIL-CLOSED: `hftObCDS_of_tables` is not a constant of this build (the root derivation is not supplied; `hcd` stays a hypothesis). -/
namespace Tests.Gen5.FGCircuitPilotCheck25
open Lean Meta Elab Command Term Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bShare Tools.ShippingFGCircuitS2bRun

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def axiomsOk (n : Name) : CoreM Unit := do
  let ax ← collectAxioms n
  unless ax.all (standardAxioms.contains ·) do throwError "{n}: non-standard axioms {ax}"

run_cmd liftTermElabM do
  for n in [``ds_fun, ``cds_fun, ``circCVS_functional, ``ds_inhMk_one, ``ds_default_of_mk, ``ds_unf_t, ``ds_beta_t, ``ds_projStep_t, ``ds_projCtor_t, ``ds_recIota_t, ``ds_projRec_t,
      ``ds_unitVal_t, ``ds_prodMk_t, ``ds_inhMk_t, ``ds_mapFst_t, ``ds_mapSnd_t, ``HftObCDS, ``HftFinalStmtS, ``circCVS_hft_run] do
    axiomsOk n
  logInfo "AXIOMS ok: DS functionality, the table rules, HftObCDS, HftFinalStmtS"

run_cmd do
  let one : Level := .succ .zero
  unless lvlNat one == some 1 && lvlNat (.max one one) == some 1 && lvlNat (.imax one one) == some 1 do throwError "accepts"
  unless lvlNat .zero != some 1 && lvlNat (.max one (.succ one)) != some 1 && lvlNat (.imax one .zero) != some 1 && lvlNat (.param `u) != some 1 && lvlNat (.mvar ⟨`m⟩) != some 1 do
    throwError "rejects"
  logInfo "LEVEL-CONTROLS ok: 1, max 1 1, imax 1 1 accepted; 0, max 1 2, imax 1 0, param, mvar rejected"

open Tools.ShippingFGCircuitS1mCD in
def boolBool : Lean.Expr := appN ``Prod [.zero, .zero] [.const ``Bool [], .const ``Bool []]
open Tools.ShippingFGCircuitS1mCD in
def smallRoot : Lean.Expr :=
  appN ``Inhabited.default [.succ .zero] [boolBool,
    appN ``instInhabitedProd [.zero, .zero] [.const ``Bool [], .const ``Bool [], .const ``instInhabitedBool [], .const ``instInhabitedBool []]]

run_cmd do
  let env ← getEnv
  let ok := (← getEnv).contains `Tests.Gen5.FGCircuitPilotCheck25.smallThm
  if ok then throwError "unexpected"
  deriveTerm `Tests.Gen5.FGCircuitPilotCheck25.smallThm smallRoot
  unless (← getEnv).contains `Tests.Gen5.FGCircuitPilotCheck25.smallThm do throwError "smallThm missing"
  logInfo "SMALL-DERIVE ok: smallThm kernel-checked (numbers above)"

run_cmd liftTermElabM do
  axiomsOk `Tests.Gen5.FGCircuitPilotCheck25.smallThm
  logInfo "SMALL-AXIOMS ok: smallThm uses only the standard axioms"

open Tools.ShippingFGCircuitS1mCD in
run_cmd do
  let bad1 := appN ``Option.some [.zero] [.const ``Bool [], .const ``Bool.true []]
  let r1 ← (try deriveTerm `Tests.Gen5.FGCircuitPilotCheck25.badCtor bad1; pure false catch _ => pure true)
  unless r1 do throwError "another constructor was derived"
  let bad2 := appN ``Inhabited.default [.max (.succ .zero) (.succ .zero)] [boolBool, .const ``instInhabitedBool []]
  let r2 ← (try deriveTerm `Tests.Gen5.FGCircuitPilotCheck25.badDefault bad2; pure false catch _ => pure true)
  unless r2 do throwError "Inhabited.default at max 1 1 was derived"
  logInfo "CONTROLS ok: Option.some and Inhabited.default.{max 1 1} are not derivable"


/-! ## SHARE-LADDER: the let-ladder `E_k = let x := E_{k-1}; Prod.mk x x` (a shared structure, like the `have ep := …; have emit := …` bodies of `hftPcieLoop`):
substitution by `instE` (the rule evaluators' own, structural) builds a tree of 2^k nodes, `Expr.instantiate1` keeps the DAG (k + 1 nodes). Same result (`==`), very different size. -/

open Tools.ShippingFGCircuitS1mCD in
def ladder : Nat → Lean.Expr
  | 0 => .const `c []
  | k + 1 => .letE `x (.const `Foo []) (ladder k) (appN ``Prod.mk [.zero, .zero] [.const `A [], .const `B [], .bvar 0, .bvar 0]) false

open Tools.ShippingFGCircuitS1mCD in
def zetaAllOld : Lean.Expr → Lean.Expr
  | .letE _ _ v b _ => instE (zetaAllOld b) (zetaAllOld v) 0
  | e => e

def zetaAllNew : Lean.Expr → Lean.Expr
  | .letE _ _ v b _ => (zetaAllNew b).instantiate1 (zetaAllNew v)
  | e => e

run_cmd do
  let k := 16
  let a := zetaAllOld (ladder k)
  let ta := a.sizeWithoutSharing
  let b := zetaAllNew (ladder k)
  let tb := b.sizeWithoutSharing
  unless a == b do throwError "the two substitutions disagree"
  let dag := (Tools.ShippingFGCircuitS2bGen.dagTree b).1
  logInfo m!"SHARE-LADDER ok (k={k}): same result (==); tree size {ta} (instE) / {tb} (instantiate1) nodes, but the instantiate1 result is a DAG of {dag} distinct nodes"

run_cmd do
  if (← getEnv).contains `Tools.ShippingFGCircuitS2bRun.hftObCDS_of_tables then throwError "hftObCDS_of_tables is present: update docs §30"
  logInfo "FAIL-CLOSED ok: hftObCDS_of_tables is not a constant (hcd is a hypothesis)"

end Tests.Gen5.FGCircuitPilotCheck25
