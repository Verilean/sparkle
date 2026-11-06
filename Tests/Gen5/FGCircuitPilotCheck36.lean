import Tools.ShippingFGCircuitS2iRun
import Tools.ShippingFGCircuitS2pValHead
set_option autoImplicit false
-- FG circuit pilot S2p check (light, small run_cmd blocks). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §41.

/-! # FGCircuitPilotCheck36

1. AXIOMS: `sh_fun`, `dt_fun`, `sh_var_val`, `bvarV_spine` use only the standard axioms.
2. POSITIVE (kernel-checked by the generator): a `let`-bound VALUE variable returned through a lambda (`Sh.bvarV` + `DT.viaVar`), twice in a pair, and under two nested value binders.
3. NEGATIVE CONTROLS (fail-closed, EXPECTED error text; a generator failure is NOT a non-derivability theorem): a value entry in head position WITH arguments (not added), `Signal.mk` (still no rule), an unbound variable.
The positive and the negative cases go through the same generator and are reported with the same text. -/
namespace Tests.Gen5.FGCircuitPilotCheck36
open Lean Meta Elab Command Term Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl
open Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT Tools.ShippingFGCircuitS2iTbl Tools.ShippingFGCircuitS2iRun

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def axiomsOk (n : Name) : CoreM Unit := do
  let ax ← collectAxioms n
  unless ax.all (standardAxioms.contains ·) do throwError "{n}: non-standard axioms {ax}"

run_cmd liftTermElabM do
  for n in [``sh_fun, ``dt_fun, ``cdt_fun, ``tdt_fun, ``cdt_eq, ``Tools.ShippingFGCircuitS2pValHead.sh_var_val, ``Tools.ShippingFGCircuitS2pValHead.bvarV_spine] do
    axiomsOk n
  logInfo "AXIOMS ok: Sh/DT functionality and the value-head lemmas use only the standard axioms"

def bl : Lean.Expr := .const ``Bool []
def bF : Lean.Expr := .const ``Bool.false []
def bT : Lean.Expr := .const ``Bool.true []
def mkP (x y : Lean.Expr) : Lean.Expr := appN ``Prod.mk [.zero, .zero] [bl, bl, x, y]
def idB : Lean.Expr := .lam `y bl (.bvar 0) .default
def letB (v b : Lean.Expr) : Lean.Expr := .letE `x bl v b false

def report (tag : String) (n : Name) : CommandElabM Unit := do
  unless (← getEnv).contains n do throwError "{tag}: {n} missing"
  liftTermElabM (axiomsOk n)
  logInfo m!"{tag} ok: {n} kernel-checked, standard axioms only"

-- VALHEAD: `let x := false; (fun y => y) x`  (the closure `x` evaluates to the value variable #0)
derive_expr_t valHead := (letB bF (.app idB (.bvar 0)) : Lean.Expr)
run_cmd report "VALHEAD" `Tests.Gen5.FGCircuitPilotCheck36.valHead
-- VALHEAD-PAIR: `let x := true; Prod.mk ((fun y => y) x) x`
derive_expr_t valHeadPair := (letB bT (mkP (.app idB (.bvar 0)) (.bvar 0)) : Lean.Expr)
run_cmd report "VALHEAD-PAIR" `Tests.Gen5.FGCircuitPilotCheck36.valHeadPair
-- VALHEAD-NEST: `let x := true; let x := false; Prod.mk ((fun y => y) #1) ((fun y => y) #0)` (two value binders, different entries)
derive_expr_t valHeadNest := (letB bT (letB bF (mkP (.app idB (.bvar 1)) (.app idB (.bvar 0)))) : Lean.Expr)
run_cmd report "VALHEAD-NEST" `Tests.Gen5.FGCircuitPilotCheck36.valHeadNest

def errOf (n : Name) (e : Lean.Expr) : CommandElabM (Option String) := do
  try
    deriveTerm n e
    pure none
  catch ex => pure (some (← (liftCoreM ex.toMessageData.toString)))

def expectErr (tag : String) (n : Name) (e : Lean.Expr) (needle : String) : CommandElabM Unit := do
  match ← errOf n e with
  | none => throwError "{tag}: the control was derived"
  | some msg =>
    unless (msg.splitOn needle).length > 1 do throwError "{tag}: unexpected error text: {msg}"
    if (← getEnv).contains n then throwError "{tag}: a theorem was added"
    logInfo m!"{tag} ok: not derived, with the expected generator error «{needle}» (a generator failure, not a non-derivability theorem)"

-- a value entry applied to an argument: `let x := false; x true` (ill-typed; the rule is only for the EMPTY spine)
run_cmd expectErr "CTRL-VALAPP" `Tests.Gen5.FGCircuitPilotCheck36.ctrlValApp (letB bF (.app (.bvar 0) bT)) "value entry applied"
-- Signal.mk is still a value head without a rule
run_cmd expectErr "CTRL-SIGNALMK" `Tests.Gen5.FGCircuitPilotCheck36.ctrlMk
          (appN ``Sparkle.Core.Signal.Signal.mk [.zero] [.const ``Sparkle.Core.Domain.defaultDomain [], bl, .lam `t (.const ``Nat []) bF .default]) "has no rule"
-- an unbound variable under the value head
run_cmd expectErr "CTRL-UNBOUND" `Tests.Gen5.FGCircuitPilotCheck36.ctrlUnbound (.app idB (.bvar 3)) "not bound"

end Tests.Gen5.FGCircuitPilotCheck36
