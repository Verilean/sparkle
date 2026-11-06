import Tools.ShippingFGCircuitS2iDT
set_option autoImplicit false
-- FG circuit pilot S2i: functionality `dt_fun` of the bridge family `DT`, and the carrier / obligation over it. docs/FG-CIRCUIT-PILOT.md §35.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
namespace Tools.ShippingFGCircuitS2iDT
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1sCD
open Tools.ShippingFGCircuitS2iSh

theorem directHead_boolFalse : directHead ``Bool.false = true := by decide
theorem directHead_boolTrue : directHead ``Bool.true = true := by decide
theorem directHead_prodMk : directHead ``Prod.mk = true := by decide
theorem directHead_unit : directHead ``PUnit.unit = true := by decide
theorem directHead_inhMk : directHead ``Inhabited.mk = true := by decide
theorem stopD_of_stopC {c : Name} (h : stopC c = true) : stopD c = true := by simp [stopD, h]
theorem stopD_of_newStopC {c : Name} (h : newStopC c = true) : stopD c = true := by simp [stopD, h]
theorem stopD_of_tyStopC {c : Name} (h : tyStopC c = true) : stopD c = true := by simp [stopD, h]
theorem directHead_of_stopD {c : Name} (h : stopD c = true) : directHead c = true := by simp [directHead, h]

macro "clashT" : tactic =>
  `(tactic| (exfalso
             try subst_vars
             try simp_all [Res.kind, viaOK_appN, viaOK_bvar, viaOK_lam, directHead_of_stopD, stopD_of_stopC, stopD_of_newStopC, stopD_of_tyStopC,
               directHead_boolFalse, directHead_boolTrue, directHead_prodMk, directHead_unit, directHead_inhMk,
               newStopC_bundle2, newStopC_default, tyHeadStop, headStop, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, appFn, stopC_ofNat, stopC_defaultDomain, stopC_bvOfNat, stopC_bvInh,
               stopC_boolInh, stopC_pure, stopC_register, stopC_mux, stopC_hadd, stopC_loop, stopC_beq, stopC_hand, stopC_hor, stopC_compl, bvAbbrevRow_defaultDomain,
               bvAbbrevRow_instInhabitedBool, stopC_of_row, stopD_signalMap, tyStopC_nat, tyStopC_bool, tyStopC_dc, tyStopC_bitvec, tyStopC_signal, tyStopC_prod, tyStopC_punit]))

macro "injsT" he:ident he':ident : tactic =>
  `(tactic| (have h := Eq.trans (Eq.symm $he) $he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.proj.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **functionality** of `DT`: two derivations of the same expression in the same closure environment, of the same kind, have the same result. -/
theorem dt_fun {env : Environment} {ρ : Cx} {e : Expr} {r : Res} (h : DT env ρ e r) : ∀ {r' : Res}, DT env ρ e r' → r.kind = r'.kind → r = r' := by
  induction h with
  | nat he => intro r' h' hk; cases h' with
    | nat he' => rfl
    | _ => clashT
  | bool he => intro r' h' hk; cases h' with
    | bool he' => rfl
    | _ => clashT
  | domainConfig he => intro r' h' hk; cases h' with
    | domainConfig he' => rfl
    | _ => clashT
  | bitvec he hw ihw => intro r' h' hk; cases h' with
    | bitvec he' hw' =>
      injsT he he'
      have := val_eq (ihw hw' rfl)
      subst this; rfl
    | _ => clashT
  | signal he hd ht ihd iht => intro r' h' hk; cases h' with
    | signal he' hd' ht' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2; rfl
    | _ => clashT
  | bvar hb => intro r' h' hk; cases h' with
    | bvar hb' =>
      have := Option.some.inj (hb.symm.trans hb')
      cases this
      rfl
    | bvarClo hb' h'' => rw [hb] at hb'; cases hb'
    | _ => clashT
  | natLit he => intro r' h' hk; cases h' with
    | natLit he' =>
      injsT he he'
      rfl
    | _ => clashT
  | domDefault he => intro r' h' hk; cases h' with
    | domDefault he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr'; cases hr'
    | _ => clashT
  | bvOfNat he hw hk ihw ihk => intro r' h' hk; cases h' with
    | bvOfNat he' hw' hk' =>
      injsT he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1
      have h2 := val_eq (ihk hk' rfl)
      subst h2; rfl
    | _ => clashT
  | bvInhabited he hw ihw => intro r' h' hk; cases h' with
    | bvInhabited he' hw' =>
      injsT he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1; rfl
    | _ => clashT
  | boolInhabited he => intro r' h' hk; cases h' with
    | boolInhabited he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr'; cases hr'
    | _ => clashT
  | sigPure he hd ht hx ihd iht ihx => intro r' h' hk; cases h' with
    | sigPure he' hd' ht' hx' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3; rfl
    | _ => clashT
  | sigRegister he hd ht hi hs ihd iht ihi ihs => intro r' h' hk; cases h' with
    | sigRegister he' hd' ht' hi' hs' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | _ => clashT
  | sigMux he hd ht hc ha hb ihd iht ihc iha ihb => intro r' h' hk; cases h' with
    | sigMux he' hd' ht' hc' ha' hb' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihc hc' rfl)
      subst h3
      have h4 := val_eq (iha ha' rfl)
      subst h4
      have h5 := val_eq (ihb hb' rfl)
      subst h5; rfl
    | _ => clashT
  | sigAddBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigAddBV he' hd' hw' ha' hb' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashT
  | sigLoop he hd ht hi hf ihd iht ihi ihf => intro r' h' hk; cases h' with
    | sigLoop he' hd' ht' hi' hf' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihf hf' rfl)
      subst h4; rfl
    | _ => clashT
  | lam he hA hb ihA ihb => intro r' h' hk; cases h' with
    | lam he' hA' hb' =>
      injsT he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 : ∀ a, _ = _ := fun a => (val_inj (ihb a (hb' a) rfl)).1
      have h2' := funext h2
      subst h2'
      have h3 : _ = _ := funext fun a => eq_of_heq (val_inj (ihb a (hb' a) rfl)).2
      subst h3; rfl
    | _ => clashT
  | letE he hA hc hv hb ihA ihv ihb => intro r' h' hk; cases h' with
    | letE he' hA' hc' hv' hb' =>
      injsT he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 := val_eq (ihv hv' rfl)
      subst h2
      exact ihb hb' rfl
    | viaSh hv' hsh' hsp' hcan' h'' =>
      subst he
      cases hsh' with
      | letZ hA0 _ => rw [hc] at hA0; cases hA0
    | _ => clashT
  | sigBeqBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigBeqBV he' hd' hw' ha' hb' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashT
  | sigAndBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigAndBool he' hd' ha' hb' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashT
  | sigOrBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigOrBool he' hd' ha' hb' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashT
  | sigNotBool he hd ha ihd iha => intro r' h' hk; cases h' with
    | sigNotBool he' hd' ha' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3; rfl
    | _ => clashT
  | bvAbbrev he hr => intro r' h' hk; cases h' with
    | bvAbbrev he' hr' =>
      have hc : _ := (Expr.const.inj (he.symm.trans he')).1
      subst hc
      rw [hr] at hr'
      cases hr'
      rfl
    | domDefault he' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr; cases hr
    | boolInhabited he' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr; cases hr
    | viaSh hv' hsh' hsp' hcan' h'' =>
      subst he
      have h0 := stopC_of_row hr
      have hd : directHead _ = true := by simp [directHead, stopD, h0]
      simp [viaOK, appFn, hd] at hv'
    | _ => clashT
  | prodTy he ha hb iha ihb => intro r' h' hk; cases h' with
    | prodTy he' ha' hb' =>
      injsT he he'
      have h1 := ty_eq (iha ha' rfl)
      subst h1
      have h2 := ty_eq (ihb hb' rfl)
      subst h2; rfl
    | _ => clashT
  | punitTy he => intro r' h' hk; cases h' with
    | punitTy he' => rfl
    | _ => clashT
  | unitVal he hc => intro r' h' hk; cases h' with
    | unitVal he' hc' => rfl
    | _ => clashT
  | prodMk he hc ha hb hx hy iha ihb ihx ihy => intro r' h' hk; cases h' with
    | prodMk he' hc' ha' hb' hx' hy' =>
      injsT he he'
      have h1 := ty_eq (iha ha' rfl)
      subst h1
      have h2 := ty_eq (ihb hb' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3
      have h4 := val_eq (ihy hy' rfl)
      subst h4; rfl
    | _ => clashT
  | mapFst he hd hp ht ha hb hs ihd ihp iht iha ihb ihs => intro r' h' hk; cases h' with
    | mapFst he' hd' hp' ht' ha' hb' hs' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iha ha' rfl)
      subst h2
      have h3 := ty_eq (ihb hb' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | _ => clashT
  | mapSnd he hd hp ht ha hb hs ihd ihp iht iha ihb ihs => intro r' h' hk; cases h' with
    | mapSnd he' hd' hp' ht' ha' hb' hs' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iha ha' rfl)
      subst h2
      have h3 := ty_eq (ihb hb' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | _ => clashT
  | inhMk he hu0 hc ht hx iht ihx => intro r' h' hk; cases h' with
    | inhMk he' hu' hc' ht' hx' =>
      injsT he he'
      have h1 := ty_eq (iht ht' rfl)
      subst h1
      have h2 := val_eq (ihx hx' rfl)
      subst h2; rfl
    | _ => clashT
  | inhDefault he ht hi iht ihi => intro r' h' hk; cases h' with
    | inhDefault he' ht' hi' =>
      injsT he he'
      have h1 := ty_eq (iht ht' rfl)
      subst h1
      have h2 := val_eq (ihi hi' rfl)
      subst h2; rfl
    | _ => clashT
  | bundle2 he hd hta htb ha hb ihd ihta ihtb iha ihb => intro r' h' hk; cases h' with
    | bundle2 he' hd' hta' htb' ha' hb' =>
      injsT he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (ihta hta' rfl)
      subst h2
      have h3 := ty_eq (ihtb htb' rfl)
      subst h3
      have h4 := val_eq (iha ha' rfl)
      subst h4
      have h5 := val_eq (ihb hb' rfl)
      subst h5; rfl
    | _ => clashT
  | boolFalse he hc => intro r' h' hk; cases h' with
    | boolFalse he' hc' => rfl
    | _ => clashT
  | boolTrue he hc => intro r' h' hk; cases h' with
    | boolTrue he' hc' => rfl
    | _ => clashT
  | bvarClo hb h ih => intro r' h' hk; cases h' with
    | bvarClo hb' h' =>
      rw [hb] at hb'
      have := Option.some.inj hb'
      obtain ⟨e1, e2⟩ := Ent.clo_inj this
      subst e1; subst e2
      exact ih h' hk
    | bvar hb' => rw [hb] at hb'; cases hb'
    | _ => clashT
  | viaSh hv hsh hsp hcan h ih => intro r' h' hk; cases h' with
    | viaSh hv' hsh' hsp' hcan' h' =>
      have e1 := sh_fun hsh hsh'
      subst e1
      rcases map_clo_eq (hsp.symm.trans hsp') with ⟨h0, h0'⟩ | ⟨h1, h2⟩
      · have a1 := hcan h0
        have a2 := hcan' h0'
        subst a1; subst a2; subst h0; subst h0'
        exact ih h' hk
      · subst h1; subst h2
        exact ih h' hk
    | letE he' hA' hc' hv' hb' =>
      subst he'
      cases hsh with
      | letZ hA0 _ => rw [hc'] at hA0; cases hA0
    | bvAbbrev he' hr' =>
      subst he'
      have h0 := stopC_of_row hr'
      have hd : directHead _ = true := by simp [directHead, stopD, h0]
      simp [viaOK, appFn, hd] at hv
    | _ => clashT


theorem cdt_fun {env : Environment} {ρ : Cx} {e : Expr} {α α' : Type} {v : α} {v' : α'} (h : CDT env ρ e α v) (h' : CDT env ρ e α' v') :
    α = α' ∧ HEq v v' := val_inj (dt_fun h h' rfl)

theorem tdt_fun {env : Environment} {ρ : Cx} {e : Expr} {T T' : Type} (h : TDT env ρ e T) (h' : TDT env ρ e T') : T = T' := ty_eq (dt_fun h h' rfl)

theorem cdt_eq {env : Environment} {ρ : Cx} {e : Expr} {α : Type} {v v' : α} (h : CDT env ρ e α v) (h' : CDT env ρ e α v') : v = v' :=
  eq_of_heq (cdt_fun h h').2

end Tools.ShippingFGCircuitS2iDT

#print axioms Tools.ShippingFGCircuitS2iDT.dt_fun
