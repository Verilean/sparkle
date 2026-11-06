import Tools.ShippingFGCircuit
set_option autoImplicit false
-- FG circuit pilot S1c, unit 1: functionality of `CD`/`TD`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `CD` / `TD` are functional

Two derivations of the same expression in the same valuation give the same Lean type and the same value (`HEq`, since the type is an index).
Every rule of `CD`/`TD` recognizes the head constant of the whole application (or the `bvar`/`lam`/`letE` constructor), so a clash of two rules on one
expression is refuted by constructor/constant disequality, and two uses of the same rule force equal sub-expressions, which the induction hypothesis
handles. This is the `ConstValueFunctional CircCV`-style fact for the rules the four roots use (`bvAbbrev` is functional because `bvAbbrevRow` is a
function of the name). -/
namespace Tools.ShippingFGCircuit
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG

theorem appN_1 (c : Name) (ls : List Level) (a : Expr) : appN c ls [a] = .app (.const c ls) a := rfl
theorem appN_2 (c : Name) (ls : List Level) (a b : Expr) : appN c ls [a, b] = .app (.app (.const c ls) a) b := rfl
theorem appN_3 (c : Name) (ls : List Level) (a b d : Expr) : appN c ls [a, b, d] = .app (.app (.app (.const c ls) a) b) d := rfl
theorem appN_4 (c : Name) (ls : List Level) (a b d f : Expr) :
    appN c ls [a, b, d, f] = .app (.app (.app (.app (.const c ls) a) b) d) f := rfl
theorem appN_5 (c : Name) (ls : List Level) (a b d f g : Expr) :
    appN c ls [a, b, d, f, g] = .app (.app (.app (.app (.app (.const c ls) a) b) d) f) g := rfl
theorem appN_6 (c : Name) (ls : List Level) (a b d f g h : Expr) :
    appN c ls [a, b, d, f, g, h] = .app (.app (.app (.app (.app (.app (.const c ls) a) b) d) f) g) h := rfl

theorem bvAbbrevRow_defaultDomain : bvAbbrevRow ``Sparkle.Core.Domain.defaultDomain = none := by decide
theorem bvAbbrevRow_instInhabitedBool : bvAbbrevRow ``instInhabitedBool = none := by decide

macro "clash" : tactic =>
  `(tactic| (try subst_vars) <;> (simp_all [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, bvAbbrevRow_defaultDomain, bvAbbrevRow_instInhabitedBool]))


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
mutual
theorem td_fun {ρ : Val} {e : Expr} {T T' : Type} (h : TD ρ e T) (h' : TD ρ e T') : T = T' := by
  cases h with
  | nat he => cases h' with
    | nat he' => rfl
    | _ => clash
  | bool he => cases h' with
    | bool he' => rfl
    | _ => clash
  | domainConfig he => cases h' with
    | domainConfig he' => rfl
    | _ => clash
  | bitvec he hw => cases h' with
    | bitvec he' hw' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have := eq_of_heq (cd_fun hw hw').2
      subst this; rfl
    | _ => clash
  | signal he hd ht => cases h' with
    | signal he' hd' ht' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h2 := td_fun ht ht'
      subst h2; rfl
    | _ => clash
termination_by sizeOf e
decreasing_by all_goals (simp_wf; first | (subst_vars; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.sizeOf_spec, Expr.lam.sizeOf_spec, Expr.letE.sizeOf_spec, Expr.const.sizeOf_spec]; omega) | (trace_state; fail))

theorem cd_fun {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'} (h : CD ρ e α v) (h' : CD ρ e α' v') : α = α' ∧ HEq v v' := by
  cases h with
  | bvar hb => cases h' with
    | bvar hb' =>
      have := Option.some.inj (hb.symm.trans hb')
      cases this
      exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | natLit he => cases h' with
    | natLit he' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      first | exact ⟨rfl, HEq.rfl⟩ | exact HEq.rfl
    | _ => clash
  | domDefault he => cases h' with
    | domDefault he' => exact ⟨rfl, HEq.rfl⟩
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr'; cases hr'
    | _ => clash
  | bvOfNat he hw hk => cases h' with
    | bvOfNat he' hw' hk' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hw hw').2
      subst h1
      have h2 := eq_of_heq (cd_fun hk hk').2
      subst h2; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | bvInhabited he hw => cases h' with
    | bvInhabited he' hw' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hw hw').2
      subst h1; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | boolInhabited he => cases h' with
    | boolInhabited he' => exact ⟨rfl, HEq.rfl⟩
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr'; cases hr'
    | _ => clash
  | sigPure he hd ht hx => cases h' with
    | sigPure he' hd' ht' hx' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h2 := td_fun ht ht'
      subst h2
      have h3 := eq_of_heq (cd_fun hx hx').2
      subst h3; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | sigRegister he hd ht hi hs => cases h' with
    | sigRegister he' hd' ht' hi' hs' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h2 := td_fun ht ht'
      subst h2
      have h3 := eq_of_heq (cd_fun hi hi').2
      subst h3
      have h4 := eq_of_heq (cd_fun hs hs').2
      subst h4; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | sigMux he hd ht hc ha hb => cases h' with
    | sigMux he' hd' ht' hc' ha' hb' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h2 := td_fun ht ht'
      subst h2
      have h3 := eq_of_heq (cd_fun hc hc').2
      subst h3
      have h4 := eq_of_heq (cd_fun ha ha').2
      subst h4
      have h5 := eq_of_heq (cd_fun hb hb').2
      subst h5; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | sigAddBV he hd hw ha hb => cases h' with
    | sigAddBV he' hd' hw' ha' hb' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h2 := eq_of_heq (cd_fun hw hw').2
      subst h2
      have h3 := eq_of_heq (cd_fun ha ha').2
      subst h3
      have h4 := eq_of_heq (cd_fun hb hb').2
      subst h4; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | sigLoop he hd ht hi hf => cases h' with
    | sigLoop he' hd' ht' hi' hf' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h2 := td_fun ht ht'
      subst h2
      have h3 := eq_of_heq (cd_fun hi hi').2
      subst h3
      have h4 := eq_of_heq (cd_fun hf hf').2
      subst h4; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | lam he hA hb => cases h' with
    | lam he' hA' hb' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := td_fun hA hA'
      subst h1
      have h2 : ∀ a, _ = _ := fun a => (cd_fun (hb a) (hb' a)).1
      have h2' := funext h2
      subst h2'
      have h3 : _ = _ := funext fun a => eq_of_heq (cd_fun (hb a) (hb' a)).2
      subst h3; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | letE he hA hv hb => cases h' with
    | letE he' hA' hv' hb' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := td_fun hA hA'
      subst h1
      have h2 := eq_of_heq (cd_fun hv hv').2
      subst h2
      exact cd_fun hb hb'
    | _ => clash
  | sigBeqBV he hd hw ha hb => cases h' with
    | sigBeqBV he' hd' hw' ha' hb' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h2 := eq_of_heq (cd_fun hw hw').2
      subst h2
      have h3 := eq_of_heq (cd_fun ha ha').2
      subst h3
      have h4 := eq_of_heq (cd_fun hb hb').2
      subst h4; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | sigAndBool he hd ha hb => cases h' with
    | sigAndBool he' hd' ha' hb' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h3 := eq_of_heq (cd_fun ha ha').2
      subst h3
      have h4 := eq_of_heq (cd_fun hb hb').2
      subst h4; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | sigOrBool he hd ha hb => cases h' with
    | sigOrBool he' hd' ha' hb' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h3 := eq_of_heq (cd_fun ha ha').2
      subst h3
      have h4 := eq_of_heq (cd_fun hb hb').2
      subst h4; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | sigNotBool he hd ha => cases h' with
    | sigNotBool he' hd' ha' =>
      have h := he.symm.trans he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars
      have h1 := eq_of_heq (cd_fun hd hd').2
      subst h1
      have h3 := eq_of_heq (cd_fun ha ha').2
      subst h3; exact ⟨rfl, HEq.rfl⟩
    | _ => clash
  | bvAbbrev he hr => cases h' with
    | bvAbbrev he' hr' =>
      have hc : _ := (Expr.const.inj (he.symm.trans he')).1
      subst hc
      rw [hr] at hr'
      cases hr'
      exact ⟨rfl, HEq.rfl⟩
    | domDefault he' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr; cases hr
    | boolInhabited he' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr; cases hr
    | _ => clash
termination_by sizeOf e
decreasing_by all_goals (simp_wf; first | (subst_vars; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.sizeOf_spec, Expr.lam.sizeOf_spec, Expr.letE.sizeOf_spec, Expr.const.sizeOf_spec]; omega) | (trace_state; fail))
end

/-- two derivations of the same expression in the same valuation at the SAME type give the same value -/
theorem cd_eq {ρ : Val} {e : Expr} {α : Type} {v v' : α} (h : CD ρ e α v) (h' : CD ρ e α v') : v = v' :=
  eq_of_heq (cd_fun h h').2

/-- `CircCV` (the concrete `ConstValueRel` the pilot uses) is functional: the `ConstValueFunctional` row for the circuit rules. -/
theorem circCV_functional : ConstValueFunctional CircCV := by
  intro env c α β v w ⟨d, hd, _, hv⟩ ⟨d', hd', _, hv'⟩
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  exact cd_fun hv hv'

/-- the source meaning of a declaration is unique: same shape, same meaning (up to the dependent type) -/
theorem sourceDenotes_unique {env : Environment} {X : Name} {params : List (String × Nat)} {sh sh' : SigShape} {m : sh.Ty} {m' : sh'.Ty}
    (h : SourceDenotes env X params sh m) (h' : SourceDenotes env X params sh' m') : sh = sh' ∧ HEq m m' := by
  obtain ⟨-, ci, hf, hs, hcv⟩ := h
  obtain ⟨-, ci', hf', hs', hcv'⟩ := h'
  rw [hf] at hf'
  have := Option.some.inj hf'
  subst this
  rw [hs] at hs'
  have := Option.some.inj hs'
  subst this
  exact ⟨rfl, (circCV_functional env X _ _ m m' hcv hcv').2⟩

theorem sourceDenotesMono_unique {env : Environment} {X : Name} {params : List (String × Nat)} {sh sh' : SigShape} {m : MonoTy sh} {m' : MonoTy sh'}
    (h : SourceDenotesMono env X params sh m) (h' : SourceDenotesMono env X params sh' m') : sh = sh' ∧ HEq m m' := by
  obtain ⟨-, d, hf, -, hs, hcv⟩ := h
  obtain ⟨-, d', hf', -, hs', hcv'⟩ := h'
  rw [hf] at hf'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hf')
  subst this
  rw [hs] at hs'
  have := Option.some.inj hs'
  subst this
  exact ⟨rfl, (cd_fun hcv hcv').2⟩

end Tools.ShippingFGCircuit

#print axioms Tools.ShippingFGCircuit.cd_fun
#print axioms Tools.ShippingFGCircuit.td_fun
#print axioms Tools.ShippingFGCircuit.circCV_functional
#print axioms Tools.ShippingFGCircuit.sourceDenotes_unique
#print axioms Tools.ShippingFGCircuit.sourceDenotesMono_unique
