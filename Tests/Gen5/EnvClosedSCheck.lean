import Tools.ShippingGen5EnvClosedS
set_option autoImplicit false
/-! D.D-4 EnvCl: check of `Tools/ShippingGen5EnvClosedS.lean` (`EnvDeclClosed` stated on the structure of `Expr` alone). Structural match, negative controls, the API facts that fix what cannot be
proved, axioms, remaining obligations. No TRUSTED / axiom / sorry / native_decide. The corpus audit is the meta audit of `Tests/Gen5/EnvDeclClosedAudit*.lean` (draft §SoundS3, §EnvCl). -/
namespace Tests.Gen5.EnvClosedSCheck
open Lean Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueESL Tools.ShippingGen5EnvDeclClosed Tools.ShippingGen5EnvClosedS
open Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueES

/-! ## Structural match -/
example (e : Expr) (k : Nat) : closedAtB e k = true ↔ lbr e ≤ k := closedAtB_iff e k
example (env : Environment) : EnvDeclClosedS env ↔ EnvDeclClosed env := envDeclClosedS_iff env
example (env : Environment) : EnvDeclClosedS env ↔ EnvClosedL env := envDeclClosedS_iff_closedL env
example (env : Environment) (R : Name → Prop) : EnvDeclClosedSOn env R ↔ EnvDeclClosedOn env R := envDeclClosedSOn_iff env R
-- the definition has the intended shape (unfolds to the two stored-declaration clauses over `ClosedS`)
example (env : Environment) : EnvDeclClosedS env =
    ((∀ (c : Name) (ci : ConstantInfo), env.find? c = some ci → ClosedS ci.type) ∧
     (∀ (c : Name) (d : DefinitionVal), env.find? c = some (.defnInfo d) → ClosedS d.value)) := rfl
-- the final carrier, with `EnvDeclClosedS` the only environment hypothesis
example : ∀ (PT : PrimTableK) (env : Environment), EnvDeclClosedS env →
    (∀ ρ : Val, Tools.ShippingGen5ConstValueEVL.TDenV PT env ρ (.const `Nat []) Nat) →
    (∀ ρ : Val, Tools.ShippingGen5ConstValueEVL.TDenV PT env ρ (.const `String []) String) →
    Tools.ShippingGen5ConstValueEVL.OblDenTypedV PT env :=
  fun _ _ => denTypedVL_S
example : ∀ (PT : PrimTableK) (env : Environment), EnvDeclClosedS env →
    (∀ ρ : Val, TDenL PT env ρ (.const `Nat []) Nat) → (∀ ρ : Val, TDenL PT env ρ (.const `String []) String) →
    Tools.ShippingGen5ConstValueELProof.OblDenSubstL PT env → Tools.ShippingGen5ConstValueELProof.OblDenTypedL PT env :=
  fun _ _ => denTypedL_S
-- the route through the kernel invariant needs only the restricted bridge
example (env : Environment) (hz : OblLbrZeroOn env) (h : KernelClosedInvariant env) : EnvClosedL env :=
  (envDeclClosedS_iff_closedL env).1 (envDeclClosedS_of_kernel hz h)
example (env : Environment) (hz : OblLbrZero) : OblLbrZeroOn env := oblLbrZeroOn_of_global env hz

/-! ## Negative controls -/
-- `closedAtB` is not trivially true: a free `bvar` is rejected, a captured one is accepted, an escaping one under a binder is rejected
example : closedAtB (.bvar 0) 0 = false := by decide
example : closedAtB (.lam `x (.const `Nat []) (.bvar 0) .default) 0 = true := by decide
example : closedAtB (.lam `x (.const `Nat []) (.bvar 1) .default) 0 = false := by decide
example : closedAtB (.letE `x (.const `Nat []) (.bvar 0) (.bvar 0) false) 0 = false := by decide   -- the value `bvar 0` is not under the binder
example : closedAtB (.forallE `x (.bvar 0) (.bvar 0) .default) 0 = false := by decide                -- the domain `bvar 0` is not under the binder
example : closedAtB (.app (.const `f []) (.mdata {} (.proj `S 0 (.bvar 2)))) 2 = false ∧ closedAtB (.app (.const `f []) (.mdata {} (.proj `S 0 (.bvar 2)))) 3 = true := by decide
-- `ClosedS` agrees with `lbr = 0` on these, including the truncated subtraction case `lbr (lam _ (bvar 0)) = 0`
example : lbr (.lam `x (.const `Nat []) (.bvar 0) .default) = 0 ∧ ClosedS (.lam `x (.const `Nat []) (.bvar 0) .default) := by decide
-- `EnvDeclClosedS` is a real premise: one stored declaration with a loose bound variable refutes it
theorem not_closed_of_loose_type (env : Environment) (c : Name) (ci : ConstantInfo) (h : env.find? c = some ci) (ht : ci.type = .bvar 0) : ¬ EnvDeclClosedS env := by
  intro hc
  have := hc.1 c ci h
  rw [ht] at this
  exact absurd this (by decide)
theorem not_closed_of_loose_value (env : Environment) (c : Name) (d : DefinitionVal) (h : env.find? c = some (.defnInfo d)) (hv : d.value = .bvar 3) : ¬ EnvDeclClosedS env := by
  intro hc
  have := hc.2 c d h
  rw [hv] at this
  exact absurd this (by decide)
-- the localised form says nothing outside its set
example (env : Environment) : EnvDeclClosedSOn env (fun _ => False) := fun _ h => h.elim

/-! ## What the Lean API gives (and does not give) about `Expr.looseBVarRange` -/
-- `looseBVarRange` is `data.looseBVarRange.toNat` and `data` is built from `Expr.mkData` / `Expr.mkAppData`, both `opaque`: no computation, no equation
open Meta in
run_meta do
  let env ← getEnv
  -- (a) `mkData` / `mkAppData` / `hasLooseBVar` / `instantiate1` / `liftLooseBVars` are `opaque`: they carry no equation
  for n in [``Expr.mkData, ``Expr.mkAppData, ``Expr.hasLooseBVar, ``Expr.instantiate1, ``Expr.liftLooseBVars] do
    let some ci := env.find? n | throwError "{n} absent"
    unless (match ci with | .opaqueInfo _ => true | _ => false) do throwError "{n} is not opaque (the API changed: re-examine OblLbrZero)"
  -- (b) `looseBVarRange` is a plain def over `data`
  let some (.defnInfo _) := env.find? ``Expr.looseBVarRange | throwError "looseBVarRange is not a def"
  -- (c) no theorem outside this project (core / Std / Init) mentions `Expr.looseBVarRange` in its statement
  let mut ts : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if ci.isTheorem && !((`Tools).isPrefixOf n || (`Tests).isPrefixOf n) && (ci.type.find? (fun e => e.isConstOf ``Expr.looseBVarRange)).isSome then ts := ts.push n
  unless ts.isEmpty do throwError "theorems about looseBVarRange now exist: {ts}"
  -- (d) it does not compute, even at full transparency; positive control: `Nat.add 1 2 = 3` does
  let lhs := mkApp (mkConst ``Expr.looseBVarRange) (mkApp (mkConst ``Expr.bvar) (mkNatLit 3))
  let eq4 ← withTransparency .all (isDefEq lhs (mkNatLit 4))
  let eq0 ← withTransparency .all (isDefEq lhs (mkNatLit 0))
  let pos ← withTransparency .all (isDefEq (mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 2)) (mkNatLit 3))
  unless pos do throwError "positive control FAILED: the defeq checker did not reduce Nat.add"
  if eq4 || eq0 then throwError "looseBVarRange (bvar 3) now computes: re-examine OblLbrZero"
  logInfo m!"API facts ok: mkData/mkAppData/hasLooseBVar/instantiate1/liftLooseBVars opaque; 0 non-project theorems about looseBVarRange; (bvar 3).looseBVarRange stuck (≠4, ≠0 by defeq); positive control ok"

/-! ## `EnvDeclClosedS` does not pass through `looseBVarRange`; the old chain does -/
/-- constants reachable from `n` through definitions / theorem statements, restricted to the project's own namespaces -/
partial def reach (env : Environment) (seen : Std.HashSet Name) (n : Name) : Std.HashSet Name :=
  if seen.contains n then seen else
  let seen := seen.insert n
  match env.find? n with
  | none => seen
  | some ci =>
    let own := (`Tools).isPrefixOf n || (`Tests).isPrefixOf n
    let body : List Expr := match ci with
      | .defnInfo d => [d.type, d.value]
      | _ => [ci.type]
    let names := body.foldl (fun acc e => e.foldConsts acc fun c a => a.push c) #[]
    if !own then seen else names.foldl (fun s c => reach env s c) seen

run_meta do
  let env ← getEnv
  let uses (n : Name) : Bool := (reach env {} n).contains ``Expr.looseBVarRange
  -- positive control: the old chain does use it
  unless uses ``OblLbrZero && uses ``KernelClosedInvariant && uses ``OblLbrZeroOn do throwError "detector FAILED: the bridge props must mention looseBVarRange"
  let clean : List Name := [``EnvDeclClosedS, ``ClosedS, ``closedAtB, ``EnvDeclClosedSOn, ``EnvDeclClosed, ``EnvClosedL, ``denTypedVL_S, ``denTypedL_S, ``denTypedVL_of_rows_S]
  let bad := clean.filter uses
  unless bad.isEmpty do throwError "mention Expr.looseBVarRange: {bad}"
  logInfo m!"looseBVarRange-free (statement, through project definitions): {clean.length} names; detector flags OblLbrZero / KernelClosedInvariant / OblLbrZeroOn"

/-! ## Remaining obligations (Prop definitions, none assumed or proved here) -/
run_meta do
  let env ← getEnv
  let obls : List Name := [``EnvDeclClosedS, ``OblLbrZeroOn, ``KernelClosedInvariant, ``OblLbrZero]
  let mut lines : Array MessageData := #[]
  for n in obls do
    let some ci := env.find? n | throwError "{n} absent"
    if ci.isTheorem || (match ci with | .axiomInfo _ => true | _ => false) then throwError "{n} is a theorem/axiom, expected a Prop definition"
    lines := lines.push m!"  {n}"
  logInfo m!"named obligations ({lines.size}; Prop definitions, none assumed). Needed by the carrier: EnvDeclClosedS only. Routes to it: KernelClosedInvariant + OblLbrZeroOn (⇐ OblLbrZero):\n{MessageData.joinSep lines.toList "\n"}"

/-! ## Axioms -/
def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
run_meta do
  let proved : List Name :=
    [``closedAtB_iff, ``closedS_iff, ``envDeclClosedS_iff, ``envDeclClosedS_iff_closedL, ``envDeclClosedSOn_iff, ``envDeclClosedS_of_on,
     ``denTypedL_S, ``denTypedVL_S, ``denTypedVL_of_rows_S, ``oblLbrZeroOn_of_global, ``envDeclClosedS_of_kernel, ``kernelInvariant_of_declClosedS_and_range,
     ``not_closed_of_loose_type, ``not_closed_of_loose_value]
  let env ← getEnv
  let mut bad : Array Name := #[]
  for n in proved do
    unless env.contains n do throwError "{n} absent"
    let ax ← Lean.collectAxioms n
    if ax.any (fun a => !stdAx.contains a) then bad := bad.push n
  unless bad.isEmpty do throwError "non-standard axiom (or sorryAx) in: {bad}"
  logInfo m!"axiom check ok: {proved.length} proved declarations use only propext / Classical.choice / Quot.sound"
axiom negControlAxiom : False
theorem negControlUsesAxiom : (1 : Nat) = 2 := negControlAxiom.elim
run_meta do
  let ax ← Lean.collectAxioms ``negControlUsesAxiom
  unless ax.contains ``negControlAxiom do throwError "negative control FAILED: detector missed the axiom"
  logInfo m!"negative control ok: detector flags {ax.toList}"

end Tests.Gen5.EnvClosedSCheck

#print axioms Tools.ShippingGen5EnvClosedS.closedAtB_iff
#print axioms Tools.ShippingGen5EnvClosedS.envDeclClosedS_iff
#print axioms Tools.ShippingGen5EnvClosedS.denTypedVL_S
#print axioms Tools.ShippingGen5EnvClosedS.denTypedVL_of_rows_S
#print axioms Tools.ShippingGen5EnvClosedS.envDeclClosedS_of_kernel
