import Tools.ShippingFGCircuitS1wGen
set_option autoImplicit false
-- FG circuit pilot S1w2 check (light). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §23.6.

/-! # FGCircuitPilotCheck22

1. AXIOMS: the table evaluators' soundness and the table rules use only the standard axioms.
2. FAIL-CLOSED: `hftObCDW_of_tables` is NOT a constant of this build (the typed derivation is not supplied; `hcd` stays a hypothesis).
3. STOP-1: the unfolding of `instInhabitedProd` at levels `[0,0]` gives `Inhabited.mk.{max 1 1}`, which is not the level list `[1]` of the rule `DW.inhMk`. -/
namespace Tests.Gen5.FGCircuitPilotCheck22
open Lean Meta Elab Command Term Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def axiomsOk (n : Name) : CoreM Unit := do
  let ax ← collectAxioms n
  unless ax.all (standardAxioms.contains ·) do throwError "{n}: non-standard axioms {ax}"

run_cmd liftTermElabM do
  for n in [``envLk_of, ``unfoldL_sound, ``iotaL_sound, ``whStepL_sound, ``recMajorL_sound, ``recStepCoreL_sound, ``recStepL_sound, ``whStepRL_sound, ``headRedexRL_sound] do
    axiomsOk n
  logInfo "AXIOMS-A ok: envLk_of and the evaluator soundness theorems"

run_cmd liftTermElabM do
  for n in [``dw_unf_t, ``dw_beta_t, ``dw_projStep_t, ``dw_projCtor_t, ``dw_recIota_t, ``dw_projRec_t, ``dw_unitVal_t, ``dw_prodMk_t, ``dw_inhMk_t, ``dw_mapFst_t, ``dw_mapSnd_t,
      ``HftObCDW, ``HftFinalStmtW] do
    axiomsOk n
  logInfo "AXIOMS-B ok: the table versions of the rules, HftObCDW, HftFinalStmtW"

run_cmd liftTermElabM do
  let env ← getEnv
  let absent := (`Tools.ShippingFGCircuitS1wRun.hftObCDW_of_tables) 
  if env.contains absent then throwError "hftObCDW_of_tables is present: update docs §23.6"
  if env.contains `Tools.ShippingFGCircuitS1sCD.hftObCDW_of_tables then throwError "hftObCDW_of_tables is present: update docs §23.6"
  logInfo "FAIL-CLOSED ok: hftObCDW_of_tables is not a constant (hcd is a hypothesis)"

run_cmd liftTermElabM do
  let env ← getEnv
  let some (.defnInfo d) := env.find? ``instInhabitedProd | throwError "instInhabitedProd"
  let v := instLE d.levelParams [.zero, .zero] d.value
  let lvls : List Name := []
  let rec find : Lean.Expr → List (List Level)
    | .const c ls => if c == ``Inhabited.mk then [ls] else []
    | .app f a => find f ++ find a
    | .lam _ t b _ => find t ++ find b
    | .forallE _ t b _ => find t ++ find b
    | .letE _ t x b _ => find t ++ find x ++ find b
    | .proj _ _ x => find x
    | .mdata _ x => find x
    | _ => []
  let found := (find v).eraseDups
  unless found.length == 1 && found != [[.succ .zero]] do throwError "unexpected levels {found}"
  logInfo m!"STOP-1 ok: Inhabited.mk levels in the unfolding of instInhabitedProd: {found} (rule needs [1]); {lvls.length}"

end Tests.Gen5.FGCircuitPilotCheck22
