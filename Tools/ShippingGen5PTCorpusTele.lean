import Tools.ShippingGen5PTCorpusSpec
set_option autoImplicit false
/-! # `RowTeleEvAt PTcorpus` for the rows whose binder types mention the earlier type arguments (issue sparkle-ledger-dd4-deprows, Q-C 2nd step; draft: scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md §Tele)

No TRUSTED, axiom, `sorry`, `native_decide`. Existing files are unchanged. A row is counted only when a theorem `RowTeleEvAt PTcorpus env c ls` exists; its env facts stay hypotheses (`EnvForms`, `¬ IsDefn env D`, `EnvClosedL env`), evaluated in the real environment by `Tests/Gen5/PTCorpusTeleCheck.lean`.

* §1 `Form`: the binder types that occur (a type argument, a closed type constant, a one-argument type former, an arrow). `FE es i j F` is the expression that the binder `j` carries after the first `i` binders were replaced by `es`.
  `post_subst` is the computation of `substS` on a whole telescope (the step `TeleEv.tm` / `TeleEv.ty` take); `tdenF` derives `TDenV` of such a binder from the denotations of the substituted arguments (`tdenv_wk` under `EnvClosedL` for the lifts).
* §2 `teleEv_forms` / `rowTeleEvAt_of_forms`: `RowTeleEvAt` from the row's argument types (`FormsAre`, by construction of the telescope) and the env fact `EnvForms`. -/
namespace Tools.ShippingGen5PTCorpusTele
universe u
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
  Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueEVL Tools.ShippingGen5RowTypedV Tools.ShippingGen5PTCorpus

/-! ## §1 Binder forms -/

/-- The binder types of the open rows, over the earlier TYPE arguments (`var p` = the argument of binder `p`). -/
inductive Form : Type 1
  | var (p : Nat)
  | cst (c : Name) (ls : List Level) (T : Type)
  | app1 (c : Name) (ls : List Level) (G : Type → Type) (f : Form)
  | arrow (a b : Form)

def Form.vars : Form → List Nat
  | .var p => [p]
  | .cst .. => []
  | .app1 _ _ _ f => f.vars
  | .arrow a b => a.vars ++ b.vars

/-- The Lean type of a form, given the Lean types `ts` of the earlier (type) arguments. -/
def Form.ty : Form → List Type → Type
  | .var p, ts => ts.getD p PUnit
  | .cst _ _ T, _ => T
  | .app1 _ _ G f, ts => G (f.ty ts)
  | .arrow a b, ts => a.ty ts → b.ty ts

inductive Binder : Type 1
  | ty
  | tm (F : Form)

def Binder.kind : Binder → Bool
  | .ty => false
  | .tm _ => true

/-- The binder name of an arrow in a declared type (`a._@._internal._hyg.0`). -/
def argName : Name := .num (.str (.str (.str (.str .anonymous "a") "_@") "_internal") "_hyg") 0

/-- The expression of the form `F` at binder position `j`, after the first `i` binders were replaced by `es`: a replaced argument is lifted over the `j - i` binders in between; a not-yet-replaced one is its bound variable. -/
def FE (es : List Expr) (i : Nat) : Nat → Form → Expr
  | j, .var p => if p < i then liftS (es.getD p (.bvar 0)) 0 (j - i) else .bvar (j - 1 - p)
  | _, .cst c ls _ => .const c ls
  | j, .app1 c ls _ f => .app (.const c ls) (FE es i j f)
  | j, .arrow a b => .forallE argName (FE es i j a) (FE es i (j + 1) b) .default

/-- The telescope `T` whose leading binder is binder `j`, when the first `i` binders have been replaced by `es`: the binders are `bs` (a type binder is a `Sort`, a term binder has the type of its form). -/
def Post (es : List Expr) (i : Nat) : Nat → Expr → List Binder → Prop
  | _, _, [] => True
  | j, T, .ty :: bs => ∃ (x : Name) (u : Level) (B : Expr) (bi : BinderInfo), T = .forallE x (.sort u) B bi ∧ Post es i (j + 1) B bs
  | j, T, .tm F :: bs => ∃ (x : Name) (B : Expr) (bi : BinderInfo), T = .forallE x (FE es i j F) B bi ∧ Post es i (j + 1) B bs

/-- Every variable of a form at position `j` is an earlier binder. -/
def BoundB : Nat → List Binder → Prop
  | _, [] => True
  | j, .ty :: bs => BoundB (j + 1) bs
  | j, .tm F :: bs => (∀ p ∈ F.vars, p < j) ∧ BoundB (j + 1) bs

/-- The variables of a form refer to TYPE binders among the first `pre.length` (`pre` records which are type binders). -/
def wfB : List Binder → List Bool → Bool
  | [], _ => true
  | .ty :: bs, pre => wfB bs (pre ++ [true])
  | .tm F :: bs, pre => F.vars.all (fun p => pre.getD p false) && wfB bs (pre ++ [false])

theorem lt_of_getD_true : ∀ (pre : List Bool) (p : Nat), pre.getD p false = true → p < pre.length
  | [], p, h => by simp at h
  | b :: pre, 0, _ => by simp
  | b :: pre, p + 1, h => by
    have := lt_of_getD_true pre p (by simpa using h)
    simp; omega

theorem boundB_of_wfB : ∀ (rest : List Binder) (pre : List Bool), wfB rest pre = true → BoundB pre.length rest
  | [], _, _ => trivial
  | .ty :: bs, pre, h => by
    have := boundB_of_wfB bs (pre ++ [true]) h
    simpa [BoundB] using this
  | .tm F :: bs, pre, h => by
    simp only [wfB, Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun p hp => lt_of_getD_true pre p (by simpa using h.1 p hp), ?_⟩
    have := boundB_of_wfB bs (pre ++ [false]) h.2
    simpa using this

theorem FE_subst (es : List Expr) (i : Nat) (a : Expr) (hl : es.length = i) :
    ∀ (F : Form) (j : Nat), i + 1 ≤ j → (∀ p ∈ F.vars, p < j) → substS (FE es i j F) (j - i - 1) a = FE (es ++ [a]) (i + 1) j F
  | .var p, j, hj, hp => by
    have hpj : p < j := hp p (by simp [Form.vars])
    simp only [FE]
    by_cases h1 : p < i
    · have h2 : p < i + 1 := by omega
      simp only [h1, h2, if_true]
      rw [substS_liftS_in _ 0 (j - i) (j - i - 1) a (Nat.zero_le _) (by omega)]
      have : (es ++ [a]).getD p (.bvar 0) = es.getD p (.bvar 0) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show p < es.length by omega)]
      rw [this]
      congr 1
    · by_cases h3 : p = i
      · subst h3
        have h2 : p < p + 1 := by omega
        simp only [h1, h2, if_false, if_true]
        have : (es ++ [a]).getD p (.bvar 0) = a := by
          simp [List.getD_eq_getElem?_getD, hl]
        rw [this]
        have e1 : j - 1 - p = j - p - 1 := by omega
        rw [e1]
        simp [substS]
        congr 1
      · have h2 : ¬ p < i + 1 := by omega
        simp only [h1, h2, if_false]
        have e1 : j - 1 - p < j - i - 1 := by omega
        simp [substS, e1]
  | .cst c ls T, j, _, _ => by simp [FE, substS]
  | .app1 c ls G f, j, hj, hp => by
    simp only [FE, substS]
    rw [FE_subst es i a hl f j hj (fun p hq => hp p (by simpa [Form.vars] using hq))]
  | .arrow x y, j, hj, hp => by
    simp only [FE, substS]
    have hx := FE_subst es i a hl x j hj (fun p hq => hp p (by simp [Form.vars, hq]))
    have hy := FE_subst es i a hl y (j + 1) (by omega) (fun p hq => by have := hp p (by simp [Form.vars, hq]); omega)
    rw [show j - i - 1 + 1 = j + 1 - i - 1 by omega, hx, hy]


theorem post_subst (es : List Expr) (i : Nat) (a : Expr) (hl : es.length = i) :
    ∀ (bs : List Binder) (j : Nat) (T : Expr), i + 1 ≤ j → BoundB j bs → Post es i j T bs →
      Post (es ++ [a]) (i + 1) j (substS T (j - i - 1) a) bs
  | [], _, _, _, _, _ => trivial
  | .ty :: bs, j, T, hj, hb, ⟨x, u, B, bi, hT, hrest⟩ => by
    subst hT
    refine ⟨x, u, substS B (j - i - 1 + 1) a, bi, rfl, ?_⟩
    have := post_subst es i a hl bs (j + 1) B (by omega) hb hrest
    rwa [show j + 1 - i - 1 = j - i - 1 + 1 by omega] at this
  | .tm F :: bs, j, T, hj, hb, ⟨x, B, bi, hT, hrest⟩ => by
    subst hT
    refine ⟨x, substS B (j - i - 1 + 1) a, bi, ?_, ?_⟩
    · show Expr.forallE x (substS (FE es i j F) (j - i - 1) a) _ bi = _
      rw [FE_subst es i a hl F j hj hb.1]
    · have := post_subst es i a hl bs (j + 1) B (by omega) hb.2 hrest
      rwa [show j + 1 - i - 1 = j - i - 1 + 1 by omega] at this

/-! ## Denotation of a substituted binder -/

/-- The valuation `ρ'` is `ρ0` under `r` further binders. -/
def ExtV (r : Nat) (ρ0 ρ' : Val) : Prop := ∃ l : Val, l.length = r ∧ ρ' = l ++ ρ0

theorem tdenv_liftN {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {ρ0 : Val} {e : Expr} {T : Type}
    (h : TDenV PT env ρ0 e T) : ∀ l : Val, TDenV PT env (l ++ ρ0) (liftS e 0 l.length) T
  | [] => by simpa [liftS_zero] using h
  | E :: l => by
    have ih := tdenv_liftN hcl h l
    have := tdenv_wk hcl (InsV.here (l ++ ρ0) (E := E)) ih
    rw [liftS_liftS_add e 0 0 l.length 1 (Nat.le_refl _) (Nat.zero_le _)] at this
    simpa using this

/-- The leaves of a form denote: closed type constants at every valuation, a one-argument type former on a denoting argument. -/
def Form.Good (PT : PrimTableK) (env : Environment) : Form → Prop
  | .var _ => True
  | .cst c ls T => ∀ ρ : Val, TDenV PT env ρ (.const c ls) T
  | .app1 c ls G f => (∀ (ρ : Val) (e : Expr) (X : Type), TDenV PT env ρ e X → TDenV PT env ρ (.app (.const c ls) e) (G X)) ∧ f.Good PT env
  | .arrow a b => a.Good PT env ∧ b.Good PT env

theorem tdenF {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) (es : List Expr) (ts : List Type) (i : Nat) (ρ0 : Val) :
    ∀ (F : Form) (r : Nat) (ρ' : Val), ExtV r ρ0 ρ' → F.Good PT env →
      (∀ p ∈ F.vars, p < i ∧ TDenV PT env ρ0 (es.getD p (.bvar 0)) (ts.getD p PUnit)) → TDenV PT env ρ' (FE es i (i + r) F) (F.ty ts)
  | .var p, r, ρ', ⟨l, hl, hρ⟩, _, hv => by
    obtain ⟨hp, hd⟩ := hv p (by simp [Form.vars])
    subst hρ hl
    simp only [FE, hp, if_true, Nat.add_sub_cancel_left, Form.ty]
    exact tdenv_liftN hcl hd l
  | .cst c ls T, r, ρ', _, hg, _ => hg ρ'
  | .app1 c ls G f, r, ρ', hx, ⟨hg, hf⟩, hv =>
    hg ρ' _ _ (tdenF hcl es ts i ρ0 f r ρ' hx hf (fun p hp => hv p hp))
  | .arrow a b, r, ρ', hx, ⟨ha, hb⟩, hv =>
    .pi (tdenF hcl es ts i ρ0 a r ρ' hx ha (fun p hp => hv p (List.mem_append_left _ hp))) (fun _ => b.ty ts)
      (fun x => by
        obtain ⟨l, hl, hρ⟩ := hx
        exact tdenF hcl es ts i ρ0 b (r + 1) (⟨FE es i (i + r) a, ⟨a.ty ts, x⟩⟩ :: ρ')
          ⟨⟨FE es i (i + r) a, ⟨a.ty ts, x⟩⟩ :: l, by simp [hl], by simp [hρ]⟩ hb (fun p hp => hv p (List.mem_append_right _ hp)))

/-! ## The arguments of a row against the forms -/

def ArgsAreForms : List Binder → List Type → List Arg → Prop
  | [], _, [] => True
  | .ty :: bs, ts, .ty T :: xs0 => ArgsAreForms bs (ts ++ [T]) xs0
  | .tm F :: bs, ts, .tm d :: xs0 => d.ty = F.ty ts ∧ ArgsAreForms bs (ts ++ [PUnit]) xs0
  | _, _, _ => False

/-- By construction of the telescope: the type of each term binder is the type of the form, in the type arguments chosen so far. -/
def FormsAre : {ks : List Bool} → TmTele ks → List Binder → List Type → Prop
  | _, .done _ _, bs, _ => bs = []
  | _, .tm A k, bs, ts => ∃ (F : Form) (bs' : List Binder), bs = .tm F :: bs' ∧ A = F.ty ts ∧ ∀ a, FormsAre (k a) bs' (ts ++ [PUnit])
  | _, .ty k, bs, ts => ∃ bs' : List Binder, bs = .ty :: bs' ∧ ∀ T, FormsAre (k T) bs' (ts ++ [T])

theorem run_forms : ∀ {ks : List Bool} (t : TmTele ks) (bs : List Binder) (ts : List Type) (xs : List Arg) (d : Dyn),
    FormsAre t bs ts → t.run xs = some d → ArgsAreForms bs ts xs
  | _, .done R v, bs, ts, [], d, hF, hd => by
    simp only [FormsAre] at hF; subst hF; trivial
  | _, .done _ _, bs, ts, _ :: _, d, _, hd => by simp [TmTele.run] at hd
  | _, .tm A k, bs, ts, [], d, _, hd => by simp [TmTele.run] at hd
  | _, .tm A k, bs, ts, .ty _ :: xs, d, _, hd => by simp [TmTele.run] at hd
  | _, .tm A k, bs, ts, .tm ⟨α, a⟩ :: xs, d, hF, hd => by
    simp only [FormsAre] at hF
    obtain ⟨F, bs', hb, hA, hk⟩ := hF
    subst hb
    simp only [TmTele.run] at hd
    split at hd
    · rename_i h
      exact ⟨h.trans hA, run_forms (k _) bs' _ xs d (hk _) hd⟩
    · cases hd
  | _, .ty k, bs, ts, [], d, _, hd => by simp [TmTele.run] at hd
  | _, .ty k, bs, ts, .tm _ :: xs, d, _, hd => by simp [TmTele.run] at hd
  | _, .ty k, bs, ts, .ty X :: xs, d, hF, hd => by
    simp only [FormsAre] at hF
    obtain ⟨bs', hb, hk⟩ := hF
    subst hb
    simp only [TmTele.run] at hd
    exact run_forms (k X) bs' _ xs d (hk X) hd

/-! ## §2 The telescope evidence -/

def GoodB (PT : PrimTableK) (env : Environment) : List Binder → Prop
  | [] => True
  | .ty :: bs => GoodB PT env bs
  | .tm F :: bs => F.Good PT env ∧ GoodB PT env bs

theorem post_step (es : List Expr) (i : Nat) (a : Expr) (hl : es.length = i) (bs : List Binder) (B : Expr)
    (hb : BoundB (i + 1) bs) (h : Post es i (i + 1) B bs) : Post (es ++ [a]) (i + 1) (i + 1) (substS B 0 a) bs := by
  have := post_subst es i a hl bs (i + 1) B (Nat.le_refl _) hb h
  simpa using this

theorem getD_push {α : Type u} (l : List α) (x d : α) (p : Nat) :
    (l ++ [x]).getD p d = if p < l.length then l.getD p d else if p = l.length then x else d := by
  by_cases h : p < l.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · by_cases h2 : p = l.length
    · subst h2; simp [List.getD_eq_getElem?_getD]
    · have : l.length < p := by omega
      obtain ⟨k, hk⟩ : ∃ k, p - l.length = k + 1 := ⟨p - l.length - 1, by omega⟩
      simp [List.getD_eq_getElem?_getD, h, h2, List.getElem?_append_right (show l.length ≤ p by omega), hk]

theorem hev_push {PT : PrimTableK} {env : Environment} {ρ : Val} {pre : List Bool} {es : List Expr} {ts : List Type}
    (hes : es.length = pre.length) (hts : ts.length = pre.length)
    (hev : ∀ p, pre.getD p false = true → TDenV PT env ρ (es.getD p (.bvar 0)) (ts.getD p PUnit))
    (b : Bool) (e : Expr) (X : Type) (hX : b = true → TDenV PT env ρ e X) :
    ∀ p, (pre ++ [b]).getD p false = true → TDenV PT env ρ ((es ++ [e]).getD p (.bvar 0)) ((ts ++ [X]).getD p PUnit) := by
  intro p hp
  rw [getD_push] at hp
  rw [getD_push, getD_push, hes, hts]
  by_cases h1 : p < pre.length
  · simp only [h1, if_true] at hp ⊢
    exact hev p hp
  · by_cases h2 : p = pre.length
    · subst h2
      simp at hp ⊢
      exact hX hp
    · simp [h1, h2] at hp

theorem teleEv_forms {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {ρ : Val} :
    ∀ (rest : List Binder) (pre : List Bool) (es : List Expr) (ts : List Type) (T : Expr) (args : List Expr) (xs0 : List Arg),
      es.length = pre.length → ts.length = pre.length →
      (∀ p, pre.getD p false = true → TDenV PT env ρ (es.getD p (.bvar 0)) (ts.getD p PUnit)) →
      GoodB PT env rest → wfB rest pre = true → Post es pre.length pre.length T rest →
      ArgsDenV PT env ρ (rest.map Binder.kind) args xs0 → ArgsAreForms rest ts xs0 →
      TeleEv PT env ρ T (rest.map Binder.kind) args xs0
  | [], pre, es, ts, T, args, xs0, _, _, _, _, _, _, hargs, _ => by
    have hargs' : ArgsDenV PT env ρ [] args xs0 := hargs
    cases hargs'
    exact .nil
  | .ty :: rest, pre, es, ts, T, args, xs0, hes, hts, hev, hgood, hwf, ⟨x, u, B, bi, hT, hpost⟩, hargs, hforms => by
    have hargs' : ArgsDenV PT env ρ (false :: rest.map Binder.kind) args xs0 := hargs
    cases hargs' with
    | ty hX hs =>
      rename_i e es' as' X
      have hforms' : ArgsAreForms rest (ts ++ [X]) as' := hforms
      subst hT
      have hbd : BoundB pre.length (.ty :: rest) := boundB_of_wfB _ _ hwf
      have hpost' := post_step es pre.length e hes rest B hbd hpost
      have hlen : (pre ++ [true]).length = pre.length + 1 := by simp
      refine TeleEv.ty (T := X) (u := u) rfl ?_
      refine teleEv_forms hcl rest (pre ++ [true]) (es ++ [e]) (ts ++ [X]) (substS B 0 e) es' as' (by simp [hes]) (by simp [hts])
        (hev_push hes hts hev true e X (fun _ => hX)) hgood (by simpa [wfB] using hwf) (by rw [hlen]; exact hpost') hs hforms'
  | .tm F :: rest, pre, es, ts, T, args, xs0, hes, hts, hev, hgood, hwf, ⟨x, B, bi, hT, hpost⟩, hargs, hforms => by
    have hargs' : ArgsDenV PT env ρ (true :: rest.map Binder.kind) args xs0 := hargs
    cases hargs' with
    | tm hv hs =>
      rename_i e τ es' as' α v
      obtain ⟨hα, hforms'⟩ := hforms
      subst hT
      have hbd : BoundB pre.length (.tm F :: rest) := boundB_of_wfB _ _ hwf
      have hpost' := post_step es pre.length e hes rest B hbd.2 hpost
      have hlen : (pre ++ [false]).length = pre.length + 1 := by simp
      have hwf' : (F.vars.all (fun p => pre.getD p false) && wfB rest (pre ++ [false])) = true := hwf
      simp only [Bool.and_eq_true, List.all_eq_true] at hwf'
      have hA : TDenV PT env ρ (FE es pre.length pre.length F) α := by
        have := tdenF hcl es ts pre.length ρ F 0 ρ ⟨[], rfl, by simp⟩ hgood.1
          (fun p hp => ⟨lt_of_getD_true pre p (by simpa using hwf'.1 p hp), hev p (by simpa using hwf'.1 p hp)⟩)
        have hα' : α = F.ty ts := hα
        rw [hα']
        simpa using this
      refine TeleEv.tm hA ?_
      refine teleEv_forms hcl rest (pre ++ [false]) (es ++ [e]) (ts ++ [PUnit]) (substS B 0 e) es' as' (by simp [hes]) (by simp [hts])
        (hev_push hes hts hev false e PUnit (fun h => by cases h)) hgood.2 hwf'.2 (by rw [hlen]; exact hpost') hs hforms'

/-- The env fact: the instantiated declared type of `c` is the telescope of the binders `bs` (binder names and binder infos are free, everything else is literal). -/
def EnvForms (env : Environment) (c : Name) (ls : List Level) (bs : List Binder) : Prop :=
  ∀ ci : ConstantInfo, env.find? c = some ci → Post [] 0 0 (instantiateLevelParamsS ci.levelParams ls ci.type) bs

/-- `RowTeleEvAt` of a row whose binder types are forms over the earlier type arguments. -/
theorem rowTeleEvAt_of_forms {PT : PrimTableK} {env : Environment} (hcl : EnvClosedL env) {c : Name} {ls : List Level}
    (bs : List Binder) (t : TmTele (bs.map Binder.kind)) (hrow : PT.tms c ls = some t.row) (hF : FormsAre t bs [])
    (hwf : wfB bs [] = true) (hgood : GoodB PT env bs) (hT : EnvForms env c ls bs) : RowTeleEvAt PT env c ls := by
  intro ρ args ci row xs0 d hci hrow' hargs hd
  rw [hrow] at hrow'
  cases hrow'
  exact teleEv_forms hcl bs [] [] [] _ args xs0 rfl rfl (fun p hp => by simp at hp) hgood hwf (hT ci hci) hargs (run_forms t bs [] xs0 d hF hd)

end Tools.ShippingGen5PTCorpusTele
