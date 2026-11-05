import Tools.ShippingGen5ConstValueEV
set_option autoImplicit false
-- D.D-4 Val: structural match of the proved statements about the valuation carrier `CVEKV`, negative controls (evidence-free conversion), `#print axioms`, remaining named obligations.
namespace Tests.Gen5.ValCheck
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES Tools.ShippingGen5ConstValueEV

/-! ## Structural match: the statements are exactly the intended ones -/
-- functionality: rules also determine the label; a converted derivation determines `(α, v)`
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEKVB PT env ρ e τ α v → ∀ (τ' : Expr) (β : Type) (w : β), CVEKVB PT env ρ e τ' β w → τ = τ' ∧ α = β ∧ HEq v w :=
  fun _ _ _ _ _ _ _ h _ _ _ h' => cvekvb_fun h h'
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ : Expr) (α : Type) (v : α),
    CVEKV PT env ρ e τ α v → ∀ (τ' : Expr) (β : Type) (w : β), CVEKV PT env ρ e τ' β w → α = β ∧ HEq v w :=
  fun _ _ _ _ _ _ _ h _ _ _ h' => cvekv_fun h h'
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (τ : Expr) (T : Type), TDenV PT env ρ τ T → ∀ T' : Type, TDenV PT env ρ τ T' → T = T' :=
  fun _ _ _ _ _ h _ h' => tdenv_fun h h'
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (ks : List Bool) (es : List Expr) (as : List Arg),
    ArgsDenV PT env ρ ks es as → ∀ as' : List Arg, ArgsDenV PT env ρ ks es as' → as = as' := fun _ _ _ _ _ _ h _ h' => argsdenv_fun h h'
example : ∀ (PT : PrimTableK) (env : Environment) (X : Name) (ls : List Level) (α β : Type) (v : α) (w : β),
    ConstValueEAtV PT env X ls α v → ConstValueEAtV PT env X ls β w → α = β ∧ HEq v w :=
  fun PT env X ls _ _ _ _ h h' => constValueEAtV_functional PT env X ls h h'
example : ∀ (PT : PrimTableK) (env : Environment) (X : Name) (α β : Type) (v : α) (w : β),
    CVLSKV PT env X α v → CVLSKV PT env X β w → α = β ∧ HEq v w := fun PT env X _ _ _ _ h h' => cvlskv_functional PT env X h h'
-- the conversion rule: evidence for BOTH labels (the structure of the constructor), and the derived `cvekv_conv`
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ0 τ : Expr) (α : Type) (v : α),
    CVEKVB PT env ρ e τ0 α v → TDenV PT env ρ τ0 α → TDenV PT env ρ τ α → CVEKV PT env ρ e τ α v := fun _ _ _ _ _ _ _ _ b h0 h1 => CVEKV.conv b h0 h1
example : ∀ (PT : PrimTableK) (env : Environment) (ρ : Val) (e τ τ' : Expr) (α : Type) (v : α),
    CVEKV PT env ρ e τ α v → TDenV PT env ρ τ α → TDenV PT env ρ τ' α → CVEKV PT env ρ e τ' α v := fun _ _ _ _ _ _ _ _ h h0 h1 => cvekv_conv h h0 h1
-- Q1: the rules `app` / `letE` / `tlet` have the intended shape (label = `letE` binding; the argument is evaluated, a valuation entry is pushed)
example {PT : PrimTableK} {env : Environment} {ρ : Val} {fe x A B : Expr} {n : Name} {bi : BinderInfo} {TA : Type} (TB : TA → Type)
    {fv : (a : TA) → TB a} {av : TA} (hA : TDenV PT env ρ A TA) (hB : ∀ a : TA, TDenV PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) B (TB a))
    (hf : CVEKVB PT env ρ fe (.forallE n A B bi) ((a : TA) → TB a) fv) (hx : CVEKV PT env ρ x A TA av)
    (hnh : ¬ ∃ (c : Name) (ls : List Level), fe.getAppFn = .const c ls) :
    CVEKVB PT env ρ (.app fe x) (.letE n A x B false) (TB av) (fv av) := CVEKVB.app TB hA hB hf hx hnh
example {PT : PrimTableK} {env : Environment} {ρ : Val} {n : Name} {A v b B : Expr} {nd : Bool} {TA TB : Type} {av : TA} {bv : TB}
    (hA : TDenV PT env ρ A TA) (hv : CVEKV PT env ρ v A TA av) (hb : CVEKVB PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) b B TB bv) :
    CVEKVB PT env ρ (.letE n A v b nd) (.letE n A v B nd) TB bv := .letE hA hv hb
example {PT : PrimTableK} {env : Environment} {ρ : Val} {n : Name} {A v B : Expr} {nd : Bool} {TA T : Type} {av : TA}
    (hA : TDenV PT env ρ A TA) (hv : CVEKV PT env ρ v A TA av) (hB : TDenV PT env (⟨A, ⟨TA, av⟩⟩ :: ρ) B T) :
    TDenV PT env ρ (.letE n A v B nd) T := .tlet hA hv hB
-- weakening of all four judgments
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env → ∀ (E : Entry) (s : Nat) (ρ ρ' : Val), InsV E s ρ ρ' →
    ∀ (e τ : Expr) (α : Type) (v : α), CVEKV PT env ρ e τ α v → CVEKV PT env ρ' (liftS e s 1) (liftS τ s 1) α v :=
  fun _ _ hcl _ _ _ _ hI _ _ _ _ h => cvekv_wk hcl hI h
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env → ∀ (E : Entry) (s : Nat) (ρ ρ' : Val), InsV E s ρ ρ' →
    ∀ (τ : Expr) (T : Type), TDenV PT env ρ τ T → TDenV PT env ρ' (liftS τ s 1) T :=
  fun _ _ hcl _ _ _ _ hI _ _ h => tdenv_wk hcl hI h
-- soundness: `OblDenTypedV` is closed with premises `EnvClosedS` and the two literal rows ONLY. The type has no `OblDenSubstS`, no `SafeArg`.
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env →
    (∀ ρ : Val, TDenV PT env ρ (.const `Nat []) Nat) → (∀ ρ : Val, TDenV PT env ρ (.const `String []) String) →
    ∀ (ρ : Val) (e τ : Expr) (α : Type) (v : α), WfValV PT env ρ → CVEKV PT env ρ e τ α v → TDenV PT env ρ τ α :=
  fun _ _ hcl hN hS => denTypedV hcl hN hS
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env → ∀ ρ : Val, WfValV PT env ρ → ∀ (A : Expr) (TA : Type) (hA : TDenV PT env ρ A TA) (a : TA),
    WfValV PT env (⟨A, ⟨TA, a⟩⟩ :: ρ) := fun _ _ hcl _ hρ _ _ hA a => wfValV_cons hcl hρ hA a
example : ∀ (PT : PrimTableK) (env : Environment), WfValV PT env [] := wfValV_nil
-- the range of `RowArgsAt` that the conversion supplies
example : ∀ (PT : PrimTableK) (env : Environment), EnvClosedS env →
    (∀ ρ : Val, TDenV PT env ρ (.const `Nat []) Nat) → (∀ ρ : Val, TDenV PT env ρ (.const `String []) String) →
    ∀ (ρ : Val), WfValV PT env ρ → ∀ (ks : List Bool) (es : List Expr) (as : List Arg), ArgsDenV PT env ρ ks es as →
    ∀ (T : Expr), TeleEv PT env ρ T ks es as → ArgsTeleV PT env ρ T ks es as (instForallS T es) :=
  fun _ _ hcl hN hS _ hρ _ _ _ hargs _ h => argsTeleV_of_ev hcl hN hS hρ hargs h
example (PT : PrimTableK) (env : Environment) (c : Name) (ls : List Level) (row : TmRow) (hrow : PT.tms c ls = some row) (hk : row.kinds = []) :
    RowTeleEvAt PT env c ls := rowTeleEvAt_nullary PT env c ls row hrow hk

/-! ## The substitution obligation does not occur (meta check over the proof term of `denTypedV`)

`OblDenSubstS`, its proof for safe arguments and the substitution lemma family are not among the constants reachable from `denTypedV` (type and value, through the `Tools.ShippingGen5ConstValueEV` / `...ES` declarations).
`substS` itself still occurs in the carrier in two places only, as labels computed by structural operations: `betaS` (unfold) and `instForallS` (prim). The rules `app` / `letE` / `tlet` do not mention it. -/
open Lean Meta in
def reachable (env : Environment) (roots : List Name) (pfx : List Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := roots
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      if !(pfx.any (fun p => p.isPrefixOf n)) then continue
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? then cs := cs ++ v.getUsedConstants
      for c in cs do
        if !seen.contains c then todo := c :: todo
  return seen

run_meta do
  let env ← getEnv
  let pfx : List Name := [`Tools.ShippingGen5ConstValueEV, `Tools.ShippingGen5ConstValueES]
  let seen := reachable env [``denTypedV, ``denTypedVB, ``wfValV_cons, ``tdenv_wk, ``cvekv_wk] pfx
  let banned : List Name := [``OblDenSubstS, ``oblDenSubstS_safe, ``tdens_subst, ``argsdens_subst, ``cveks_subst, ``SubV, ``SafeArg, ``substS_betaS, ``substS_instForallS]
  let hit := banned.filter seen.contains
  unless hit.isEmpty do throwError "denTypedV reaches banned substitution declarations: {hit}"
  -- control of the detector: the OLD soundness theorem does reach `OblDenSubstS`
  let seenS := reachable env [``denTypedS] pfx
  unless seenS.contains ``OblDenSubstS do throwError "detector control FAILED: denTypedS must reach OblDenSubstS"
  -- the new rules do not mention `substS` (labels are `letE`); the old `CVEKS.app` / `letE` do
  let mentions (n : Name) (tgt : Name) : MetaM Bool := do
    let some ci := env.find? n | throwError "{n} absent"
    return ci.type.getUsedConstants.contains tgt
  for r in [``CVEKVB.app, ``CVEKVB.letE, ``TDenV.tlet, ``CVEKV.conv] do
    if ← mentions r ``substS then throwError "{r} mentions substS"
  unless (← mentions ``CVEKS.app ``substS) && (← mentions ``CVEKS.letE ``substS) do throwError "detector control FAILED: CVEKS.app / letE must mention substS"
  logInfo m!"substitution check ok: denTypedV reaches {seen.size} declarations, none of {banned}; CVEKVB.app / CVEKVB.letE / TDenV.tlet / CVEKV.conv do not mention substS (old CVEKS.app / letE do)"

/-! ## A model table, for positive examples and negative controls (only here; `PT` stays arbitrary in the theorems) -/
def tyRowM (T : Type) : TyRow := ⟨[], fun _ => some T⟩
/-- `Nat ↦ Nat`, an alias `Tst.M ↦ Nat`, and a 1-element type `Tst.U ↦ Unit`. -/
def PTv : PrimTableK :=
  ⟨fun D Ls =>
     if D == `Nat && Ls.isEmpty then some (tyRowM Nat)
     else if D == `Tst.M && Ls.isEmpty then some (tyRowM Nat)
     else if D == `Tst.U && Ls.isEmpty then some (tyRowM Unit)
     else none,
   fun _ _ => none⟩

theorem tdenv_const_nullary {PT : PrimTableK} {env : Environment} {c : Name} {ls : List Level} {row : TyRow} {T : Type}
    (hrow : PT.tys c ls = some row) (hnd : ¬ IsDefn env c) (hk : row.kinds = []) (hT : row.den [] = some T) (ρ : Val) :
    TDenV PT env ρ (.const c ls) T :=
  .tcon (args := []) (as := []) hrow hnd (by rw [hk]; exact .nil) hT rfl

theorem tden_Nat (env : Environment) (hN : ¬ IsDefn env `Nat) (ρ : Val) : TDenV PTv env ρ (.const `Nat []) Nat :=
  tdenv_const_nullary (row := tyRowM Nat) (by simp [PTv]) hN rfl rfl ρ
theorem tden_M (env : Environment) (hM : ¬ IsDefn env `Tst.M) (ρ : Val) : TDenV PTv env ρ (.const `Tst.M []) Nat :=
  tdenv_const_nullary (row := tyRowM Nat) (by simp [PTv]) hM rfl rfl ρ

/-- Positive: a converted label. The literal `0` has label `Nat`; with evidence for both labels it also has the alias label `Tst.M` (the same Lean type). -/
example (env : Environment) (hN : ¬ IsDefn env `Nat) (hM : ¬ IsDefn env `Tst.M) :
    CVEKV PTv env [] (.lit (.natVal 0)) (.const `Tst.M []) Nat 0 := .conv .natLit (tden_Nat env hN []) (tden_M env hM [])

/-- Negative control 1: the type `Tst.U` (denoting `Unit`) does not denote `Nat`. So the evidence premise of `conv` cannot be supplied for a mismatched label. -/
theorem tden_U_not_Nat (env : Environment) (hU : env.find? `Tst.U = none) (ρ : Val) : ¬ TDenV PTv env ρ (.const `Tst.U []) Nat := by
  intro h
  cases h with
  | tcon hrow hnd hargs hT he =>
    obtain ⟨rfl, rfl, rfl⟩ := spine_inj (as := []) (he : mkAppN (.const `Tst.U []) ([] : List Expr).toArray = _)
    have h1 : PTv.tys `Tst.U [] = some (tyRowM Unit) := by simp [PTv]
    rw [h1] at hrow; cases hrow
    have hUN : (Unit : Type) = Nat := Option.some.inj hT
    have : ∀ a b : Nat, a = b := by rw [← hUN]; exact fun _ _ => rfl
    exact absurd (this 0 1) (by decide)
  | tunfold hd hb he =>
    obtain ⟨rfl, rfl, rfl⟩ := spine_inj (as := []) (he : mkAppN (.const `Tst.U []) ([] : List Expr).toArray = _)
    rw [hU] at hd; cases hd

/-- Negative control 2: an UNCONDITIONAL conversion (any label, no evidence) is unsound. Its conclusion `TDenV ρ τ Nat` for the arbitrary label `τ` is false: here `τ = Tst.U`.
So `OblDenTyped` would fail for a derivation `lit 0 : Tst.U`, which an evidence-free `conv` would admit. `CVEKV.conv` cannot build it (control 1 refutes its `h1`). -/
theorem uncond_conv_unsound (env : Environment) (hU : env.find? `Tst.U = none) : ¬ ∀ τ : Expr, TDenV PTv env [] τ Nat :=
  fun h => tden_U_not_Nat env hU [] (h (.const `Tst.U []))

/-- Negative control 3: the valuation well-formedness `WfValV` is a real premise: an entry whose label `Tst.U` is paired with a `Nat` value is not well-formed. -/
theorem not_wfValV_junk (env : Environment) (hU : env.find? `Tst.U = none) :
    ¬ WfValV PTv env [⟨.const `Tst.U [], ⟨Nat, 0⟩⟩] := by
  intro h
  have := h 0 ⟨.const `Tst.U [], ⟨Nat, 0⟩⟩ rfl
  simp only [liftS] at this
  exact tden_U_not_Nat env hU _ this

/-- Negative control 4: the telescope evidence is a real premise. A term argument of type `Nat` against a binder `Tst.U` (denoting `Unit`) has no `TeleEv`. -/
theorem teleEv_mismatch (env : Environment) (hU : env.find? `Tst.U = none) (ρ : Val) (R : Expr) :
    ¬ TeleEv PTv env ρ (.forallE `x (.const `Tst.U []) R .default) [true] [.lit (.natVal 0)] [.tm ⟨Nat, (0 : Nat)⟩] := by
  intro h
  cases h with
  | tm hA _ => exact tden_U_not_Nat env hU ρ hA

/-- Positive: the evidence exists for a matching binder and the typed argument list is built (the argument keeps the binder type `Nat` as its label). -/
example (env : Environment) (hcl : EnvClosedS env) (hN : ¬ IsDefn env `Nat) (hS : ∀ ρ : Val, TDenV PTv env ρ (.const `String []) String) (R : Expr) :
    ArgsTeleV PTv env [] (.forallE `x (.const `Nat []) R .default) [true] [.lit (.natVal 0)] [.tm ⟨Nat, (0 : Nat)⟩]
      (instForallS (.forallE `x (.const `Nat []) R .default) [.lit (.natVal 0)]) :=
  argsTeleV_of_ev hcl (fun ρ => tden_Nat env hN ρ) hS (wfValV_nil PTv env)
    (.tm (.core .natLit) .nil) (.tm (tden_Nat env hN []) .nil)

/-- Negative control 5: a type argument cannot be typed by `TyRKS` when it is a `forallE`: `TyRKS` has no `forallE` / `sort` rule. This is why type arguments are only given the kind check `TeleEv.ty`. -/
theorem tyRKS_no_forallE (PT : PrimTableK) (env : Environment) (Γ : List Expr) (n : Name) (A B : Expr) (bi : BinderInfo) (τ : Expr) :
    ¬ TyRKS PT env Γ (.forallE n A B bi) τ := by
  intro h
  generalize hE : Expr.forallE n A B bi = E at h
  cases h
  all_goals first | exact (spine_ne hE (by intros; simp [Expr.getAppFn])).elim | cases hE

/-- Control 6 (the reason the function position of `app` is label-determining): two different Π labels denote one Lean type, so a converted function label would have two decompositions. -/
example (env : Environment) (hN : ¬ IsDefn env `Nat) (hM : ¬ IsDefn env `Tst.M) (ρ : Val) :
    TDenV PTv env ρ (.forallE `x (.const `Nat []) (.const `Nat []) .default) (Nat → Nat) ∧
    TDenV PTv env ρ (.forallE `x (.const `Tst.M []) (.const `Nat []) .default) (Nat → Nat) ∧
    (Expr.forallE `x (.const `Nat []) (.const `Nat []) .default ≠ .forallE `x (.const `Tst.M []) (.const `Nat []) .default) :=
  ⟨.pi (tden_Nat env hN ρ) (fun _ => Nat) (fun _ => tden_Nat env hN _),
   .pi (tden_M env hM ρ) (fun _ => Nat) (fun _ => tden_Nat env hN _), by simp⟩

/-! ## Remaining named obligations (Prop definitions; none is assumed or proved as stated) and axioms -/
run_meta do
  let env ← getEnv
  let remaining : List Name := [``EnvClosedS, ``RowTeleEvAt, ``OblPrimArgsV, ``RowArgsAtV]
  let judgments : List Name := [``OblDenTypedV, ``WfValV, ``TeleEv, ``ArgsTeleV]
  let mut lines : Array MessageData := #[]
  for n in remaining ++ judgments do
    let some ci := env.find? n | throwError "{n} absent"
    if ci.isTheorem || (match ci with | .axiomInfo _ => true | _ => false) then throwError "{n} is a theorem/axiom, expected a Prop definition"
    lines := lines.push m!"  {n} : {ci.type}"
  logInfo m!"named obligations / judgments ({lines.size}; Prop definitions, none assumed):\n{MessageData.joinSep lines.toList "\n"}"
  logInfo m!"remaining (not in this file): the literal rows hN / hS (condition on PT), EnvClosedS (bridge on instantiateLevelParams; other issue), RowTeleEvAt per row (telescope evidence), OblRowTypedS (rows issue), the kernel's Ty (not statable in core)"

def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
run_meta do
  let proved : List Name :=
    [``cvekv_conv, ``tdenv_fun, ``argsdenv_fun, ``cvekv_fun, ``cvekvb_fun, ``constValueEAtV_functional, ``cvlskv_functional,
     ``tdenv_wk, ``argsdenv_wk, ``cvekv_wk, ``cvekvb_wk, ``wfValV_nil, ``wfValV_cons, ``denTypedVB, ``denTypedV,
     ``argsTeleV_of_ev, ``rowArgsAtV_of_ev, ``oblPrimArgsV_of_ev, ``rowTeleEvAt_of_none, ``argsdenv_length, ``rowTeleEvAt_nullary, ``rowArgsAtV_nullary,
     ``tden_Nat, ``tden_M, ``tden_U_not_Nat, ``uncond_conv_unsound, ``not_wfValV_junk, ``teleEv_mismatch, ``tyRKS_no_forallE]
  let mut bad : Array Name := #[]
  for n in proved do
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

end Tests.Gen5.ValCheck

#print axioms Tools.ShippingGen5ConstValueEV.cvekv_fun
#print axioms Tools.ShippingGen5ConstValueEV.cvekvb_fun
#print axioms Tools.ShippingGen5ConstValueEV.cvekv_wk
#print axioms Tools.ShippingGen5ConstValueEV.denTypedV
#print axioms Tools.ShippingGen5ConstValueEV.argsTeleV_of_ev
