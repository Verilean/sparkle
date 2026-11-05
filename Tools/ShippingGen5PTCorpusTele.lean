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
open Tools.ShippingGen5PTCorpusSpec Tools.ShippingGen5DepRows

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


/-! ## §3 The rows

The forms that occur: `T`, `T → T → T`, `T → T`, `T → T → Bool`, `Nat → T`, `T → Nat → T`, `List T`, `Nat`, `T₀ → T₁ → T₀` (over the type arguments `T`, `T₀`, `T₁`). -/

section forms
variable {env : Environment}

def v0 : Form := .var 0
def v1 : Form := .var 1
def fNat : Form := .cst `Nat [] Nat
def fBool : Form := .cst `Bool [] Bool
def fList : Form := .app1 `List [.zero] List v0
def fA2 : Form := .arrow v0 (.arrow v0 v0)
def fA1 : Form := .arrow v0 v0
def fBEq : Form := .arrow v0 (.arrow v0 fBool)
def fNatC : Form := .arrow fNat v0
def fNatP : Form := .arrow v0 (.arrow fNat v0)
def fPow : Form := .arrow v0 (.arrow v1 v0)

theorem goodNat (hN : ¬ IsDefn env `Nat) : fNat.Good PTcorpus env := fun _ => tdenv_const_nullary tys_Nat hN rfl rfl
theorem goodBool (hB : ¬ IsDefn env `Bool) : fBool.Good PTcorpus env := fun _ => tdenv_const_nullary tys_Bool hB rfl rfl
theorem goodList (hL : ¬ IsDefn env `List) : fList.Good PTcorpus env :=
  ⟨fun _ e X h => .tcon (c := `List) (ls := [.zero]) (args := [e]) («as» := [.ty X]) (row := ty_26.row) rfl hL (.ty h .nil) rfl (by simp [mkAppN, mkApp]), trivial⟩

macro "forms_tac" : tactic => `(tactic| (repeat (first | exact rfl | (refine ⟨_, rfl, fun _ => ?_⟩) | (refine ⟨_, _, rfl, rfl, fun _ => ?_⟩))))

end forms

def bs_A2 : List Binder := [.ty, .tm fA2]
def bs_A1 : List Binder := [.ty, .tm fA1]
def bs_BEq : List Binder := [.ty, .tm fBEq]
def bs_NatC : List Binder := [.ty, .tm fNatC]
def bs_NatP : List Binder := [.ty, .tm fNatP]
def bs_List : List Binder := [.ty, .tm fList]
def bs_V : List Binder := [.ty, .tm v0]
def bs_Wire : List Binder := [.ty, .tm fNat]
def bs_Nil : List Binder := [.ty]
def bs_Cons : List Binder := [.ty, .tm v0, .tm fList]
def bs_OfNat : List Binder := [.ty, .tm fNat, .tm v0]
def bs_Pow : List Binder := [.ty, .ty, .tm fPow]
def bs_Prod : List Binder := [.ty, .ty, .tm v0, .tm v1]

section goods
variable {env : Environment}
theorem good_A2 : GoodB PTcorpus env bs_A2 := by simp [bs_A2, GoodB, Form.Good, fA2, v0]
theorem good_A1 : GoodB PTcorpus env bs_A1 := by simp [bs_A1, GoodB, Form.Good, fA1, v0]
theorem good_V : GoodB PTcorpus env bs_V := by simp [bs_V, GoodB, Form.Good, v0]
theorem good_Nil : GoodB PTcorpus env bs_Nil := by simp [bs_Nil, GoodB]
theorem good_Pow : GoodB PTcorpus env bs_Pow := by simp [bs_Pow, GoodB, Form.Good, fPow, v0, v1]
theorem good_Prod : GoodB PTcorpus env bs_Prod := by simp [bs_Prod, GoodB, Form.Good, v0, v1]
theorem good_BEq (hB : ¬ IsDefn env `Bool) : GoodB PTcorpus env bs_BEq := by
  simp only [bs_BEq, GoodB, Form.Good, fBEq, v0]; exact ⟨⟨trivial, trivial, goodBool hB⟩, trivial⟩
theorem good_NatC (hN : ¬ IsDefn env `Nat) : GoodB PTcorpus env bs_NatC := by
  simp only [bs_NatC, GoodB, Form.Good, fNatC, v0]; exact ⟨⟨goodNat hN, trivial⟩, trivial⟩
theorem good_NatP (hN : ¬ IsDefn env `Nat) : GoodB PTcorpus env bs_NatP := by
  simp only [bs_NatP, GoodB, Form.Good, fNatP, v0]; exact ⟨⟨trivial, goodNat hN, trivial⟩, trivial⟩
theorem good_List (hL : ¬ IsDefn env `List) : GoodB PTcorpus env bs_List := by
  simp only [bs_List, GoodB, Form.Good, fList, v0]; exact ⟨goodList hL, trivial⟩
theorem good_Wire (hN : ¬ IsDefn env `Nat) : GoodB PTcorpus env bs_Wire := by
  simp only [bs_Wire, GoodB]; exact ⟨goodNat hN, trivial⟩
theorem good_Cons (hL : ¬ IsDefn env `List) : GoodB PTcorpus env bs_Cons := by
  simp only [bs_Cons, GoodB, Form.Good, v0]; exact ⟨trivial, goodList hL, trivial⟩
theorem good_OfNat (hN : ¬ IsDefn env `Nat) : GoodB PTcorpus env bs_OfNat := by
  simp only [bs_OfNat, GoodB, Form.Good, v0]; exact ⟨goodNat hN, trivial, trivial⟩
end goods

section rows
variable (env : Environment)
theorem ptc_tele_Add_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Add.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `Add.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_0 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_AndOp_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `AndOp.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `AndOp.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_1 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_Complement_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Complement.mk [.zero] bs_A1) : RowTeleEvAt PTcorpus env `Complement.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A1 tm_7 rfl (by forms_tac) (by decide) (good_A1) hT

theorem ptc_tele_Div_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Div.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `Div.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_8 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_Mod_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Mod.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `Mod.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_28 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_Mul_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Mul.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `Mul.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_29 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_OrOp_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `OrOp.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `OrOp.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_36 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_ShiftLeft_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `ShiftLeft.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `ShiftLeft.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_41 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_ShiftRight_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `ShiftRight.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `ShiftRight.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_42 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_Sub_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Sub.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `Sub.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_49 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_XorOp_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `XorOp.mk [.zero] bs_A2) : RowTeleEvAt PTcorpus env `XorOp.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A2 tm_50 rfl (by forms_tac) (by decide) (good_A2) hT

theorem ptc_tele_Neg_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Neg.mk [.zero] bs_A1) : RowTeleEvAt PTcorpus env `Neg.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_A1 tm_34 rfl (by forms_tac) (by decide) (good_A1) hT

theorem ptc_tele_BEq_mk (hcl : EnvClosedL env) (hB : ¬ IsDefn env `Bool)
    (hT : EnvForms env `BEq.mk [.zero] bs_BEq) : RowTeleEvAt PTcorpus env `BEq.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_BEq tm_3 rfl (by forms_tac) (by decide) (good_BEq hB) hT

theorem ptc_tele_NatCast_mk (hcl : EnvClosedL env) (hN : ¬ IsDefn env `Nat)
    (hT : EnvForms env `NatCast.mk [.zero] bs_NatC) : RowTeleEvAt PTcorpus env `NatCast.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_NatC tm_32 rfl (by forms_tac) (by decide) (good_NatC hN) hT

theorem ptc_tele_NatPow_mk (hcl : EnvClosedL env) (hN : ¬ IsDefn env `Nat)
    (hT : EnvForms env `NatPow.mk [.zero] bs_NatP) : RowTeleEvAt PTcorpus env `NatPow.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_NatP tm_33 rfl (by forms_tac) (by decide) (good_NatP hN) hT

theorem ptc_tele_Array_mk (hcl : EnvClosedL env) (hL : ¬ IsDefn env `List)
    (hT : EnvForms env `Array.mk [.zero] bs_List) : RowTeleEvAt PTcorpus env `Array.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_List tm_2 rfl (by forms_tac) (by decide) (good_List hL) hT

theorem ptc_tele_Inhabited_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Inhabited.mk [.succ .zero] bs_V) : RowTeleEvAt PTcorpus env `Inhabited.mk [.succ .zero] :=
  rowTeleEvAt_of_forms hcl bs_V tm_21 rfl (by forms_tac) (by decide) (good_V) hT

theorem ptc_tele_Sparkle_Core_Wireable_mk (hcl : EnvClosedL env) (hN : ¬ IsDefn env `Nat)
    (hT : EnvForms env `Sparkle.Core.Wireable.mk [] bs_Wire) : RowTeleEvAt PTcorpus env `Sparkle.Core.Wireable.mk [] :=
  rowTeleEvAt_of_forms hcl bs_Wire tm_47 rfl (by forms_tac) (by decide) (good_Wire hN) hT

theorem ptc_tele_List_nil (hcl : EnvClosedL env)
    (hT : EnvForms env `List.nil [.zero] bs_Nil) : RowTeleEvAt PTcorpus env `List.nil [.zero] :=
  rowTeleEvAt_of_forms hcl bs_Nil tm_27 rfl (by forms_tac) (by decide) (good_Nil) hT

theorem ptc_tele_List_cons (hcl : EnvClosedL env) (hL : ¬ IsDefn env `List)
    (hT : EnvForms env `List.cons [.zero] bs_Cons) : RowTeleEvAt PTcorpus env `List.cons [.zero] :=
  rowTeleEvAt_of_forms hcl bs_Cons tm_26 rfl (by forms_tac) (by decide) (good_Cons hL) hT

theorem ptc_tele_OfNat_mk (hcl : EnvClosedL env) (hN : ¬ IsDefn env `Nat)
    (hT : EnvForms env `OfNat.mk [.zero] bs_OfNat) : RowTeleEvAt PTcorpus env `OfNat.mk [.zero] :=
  rowTeleEvAt_of_forms hcl bs_OfNat tm_35 rfl (by forms_tac) (by decide) (good_OfNat hN) hT

theorem ptc_tele_Pow_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Pow.mk [.zero, .zero] bs_Pow) : RowTeleEvAt PTcorpus env `Pow.mk [.zero, .zero] :=
  rowTeleEvAt_of_forms hcl bs_Pow tm_39 rfl (by forms_tac) (by decide) (good_Pow) hT

theorem ptc_tele_Prod_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `Prod.mk [.zero, .zero] bs_Prod) : RowTeleEvAt PTcorpus env `Prod.mk [.zero, .zero] :=
  rowTeleEvAt_of_forms hcl bs_Prod tm_40 rfl (by forms_tac) (by decide) (good_Prod) hT

theorem ptc_tele_PProd_mk (hcl : EnvClosedL env)
    (hT : EnvForms env `PProd.mk [.succ .zero, .succ .zero] bs_Prod) : RowTeleEvAt PTcorpus env `PProd.mk [.succ .zero, .succ .zero] :=
  rowTeleEvAt_of_forms hcl bs_Prod tm_37 rfl (by forms_tac) (by decide) (good_Prod) hT

end rows


/-! ## §4 The keys of `PTcorpus` -/

def natLevel : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (natLevel n)

theorem lvNat_eq : ∀ (l : Level) (n : Nat), lvNat l = some n → l = natLevel n
  | .zero, n, h => by
    simp only [lvNat, Option.some.injEq] at h
    subst h; rfl
  | .succ l, n, h => by
    simp only [lvNat, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [natLevel, lvNat_eq l a ha]
  | .max _ _, n, h => by simp [lvNat] at h
  | .imax _ _, n, h => by simp [lvNat] at h
  | .param _, n, h => by simp [lvNat] at h
  | .mvar _, n, h => by simp [lvNat] at h

theorem lvNats_eq : ∀ (ls : List Level) (ns : List Nat), lvNats ls = some ns → ls = ns.map natLevel
  | [], ns, h => by
    simp only [lvNats, Option.some.injEq] at h
    subst h; rfl
  | l :: ls, ns, h => by
    simp only [lvNats] at h
    cases h1 : lvNat l with
    | none => simp [h1] at h
    | some a =>
      cases h2 : lvNats ls with
      | none => simp [h1, h2] at h
      | some b =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        simp [lvNat_eq l a h1, lvNats_eq ls b h2]

/-- A key with a `tms` row is one of the 51 table keys (the levels are numerals). -/
theorem tms_mem (c : Name) (ls : List Level) (h : PTcorpus.tms c ls ≠ none) :
    ∃ e ∈ tmsTable, e.1 = c ∧ ls = e.2.1.map natLevel := by
  have h' : (match lvNats ls with
      | none => none
      | some ns => (tmsTable.find? fun e => e.1 == c && e.2.1 == ns).map fun e => e.2.2.2.row) ≠ none := h
  cases hn : lvNats ls with
  | none => simp [hn] at h'
  | some ns =>
    simp only [hn] at h'
    cases hf : tmsTable.find? (fun e => e.1 == c && e.2.1 == ns) with
    | none => simp [hf] at h'
    | some e =>
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      refine ⟨e, hm, hp.1, ?_⟩
      rw [lvNats_eq ls ns hn, hp.2]


/-! ## §5 `OblRowTypedV PTcorpus` over one environment

`PTCorpusEnvFacts env` names every env fact that the 51 per-row theorems of `RowTypedAtV PTcorpus` take as hypotheses (`¬ IsDefn env D`, `EnvTypeL` / `EnvClosedPiL` / `EnvDepFirst` / `EnvDepSpine`). It is a `Prop` structure: nothing is assumed anywhere, the Check evaluates each field in the real environment. -/

structure PTCorpusEnvFacts (env : Environment) : Prop where
  hnd_Add_mk : ¬ IsDefn env `Add
  hT_Add_mk : EnvDepFirst env `Add.mk [.zero] 1 `Add [.zero]
  hnd_AndOp_mk : ¬ IsDefn env `AndOp
  hT_AndOp_mk : EnvDepFirst env `AndOp.mk [.zero] 1 `AndOp [.zero]
  hnd_Array_mk : ¬ IsDefn env `Array
  hT_Array_mk : EnvDepFirst env `Array.mk [.zero] 1 `Array [.zero]
  hnd_BEq_mk : ¬ IsDefn env `BEq
  hT_BEq_mk : EnvDepFirst env `BEq.mk [.zero] 1 `BEq [.zero]
  hnd_BitVec_ofFin : ¬ IsDefn env `BitVec
  hT_BitVec_ofFin : EnvDepSpine env `BitVec.ofFin [] 2 1 `BitVec []
  hnd_Bool_false : ¬ IsDefn env ``Bool
  hT_Bool_false : EnvTypeL env ``Bool.false [] (.const ``Bool [])
  hnd_Bool_true : ¬ IsDefn env ``Bool
  hT_Bool_true : EnvTypeL env ``Bool.true [] (.const ``Bool [])
  hnd_Complement_mk : ¬ IsDefn env `Complement
  hT_Complement_mk : EnvDepFirst env `Complement.mk [.zero] 1 `Complement [.zero]
  hnd_Div_mk : ¬ IsDefn env `Div
  hT_Div_mk : EnvDepFirst env `Div.mk [.zero] 1 `Div [.zero]
  hnd_HAdd_mk : ¬ IsDefn env `HAdd
  hT_HAdd_mk : EnvDepSpine env `HAdd.mk [.zero, .zero, .zero] 4 3 `HAdd [.zero, .zero, .zero]
  hnd_HAnd_mk : ¬ IsDefn env `HAnd
  hT_HAnd_mk : EnvDepSpine env `HAnd.mk [.zero, .zero, .zero] 4 3 `HAnd [.zero, .zero, .zero]
  hnd_HAppend_mk : ¬ IsDefn env `HAppend
  hT_HAppend_mk : EnvDepSpine env `HAppend.mk [.zero, .zero, .zero] 4 3 `HAppend [.zero, .zero, .zero]
  hnd_HDiv_mk : ¬ IsDefn env `HDiv
  hT_HDiv_mk : EnvDepSpine env `HDiv.mk [.zero, .zero, .zero] 4 3 `HDiv [.zero, .zero, .zero]
  hnd_HMod_mk : ¬ IsDefn env `HMod
  hT_HMod_mk : EnvDepSpine env `HMod.mk [.zero, .zero, .zero] 4 3 `HMod [.zero, .zero, .zero]
  hnd_HMul_mk : ¬ IsDefn env `HMul
  hT_HMul_mk : EnvDepSpine env `HMul.mk [.zero, .zero, .zero] 4 3 `HMul [.zero, .zero, .zero]
  hnd_HOr_mk : ¬ IsDefn env `HOr
  hT_HOr_mk : EnvDepSpine env `HOr.mk [.zero, .zero, .zero] 4 3 `HOr [.zero, .zero, .zero]
  hnd_HPow_mk : ¬ IsDefn env `HPow
  hT_HPow_mk : EnvDepSpine env `HPow.mk [.zero, .zero, .zero] 4 3 `HPow [.zero, .zero, .zero]
  hnd_HShiftLeft_mk : ¬ IsDefn env `HShiftLeft
  hT_HShiftLeft_mk : EnvDepSpine env `HShiftLeft.mk [.zero, .zero, .zero] 4 3 `HShiftLeft [.zero, .zero, .zero]
  hnd_HShiftRight_mk : ¬ IsDefn env `HShiftRight
  hT_HShiftRight_mk : EnvDepSpine env `HShiftRight.mk [.zero, .zero, .zero] 4 3 `HShiftRight [.zero, .zero, .zero]
  hnd_HSub_mk : ¬ IsDefn env `HSub
  hT_HSub_mk : EnvDepSpine env `HSub.mk [.zero, .zero, .zero] 4 3 `HSub [.zero, .zero, .zero]
  hnd_HXor_mk : ¬ IsDefn env `HXor
  hT_HXor_mk : EnvDepSpine env `HXor.mk [.zero, .zero, .zero] 4 3 `HXor [.zero, .zero, .zero]
  hnd_Inhabited_mk : ¬ IsDefn env `Inhabited
  hT_Inhabited_mk : EnvDepFirst env `Inhabited.mk [.succ (.zero)] 1 `Inhabited [.succ (.zero)]
  hnd_Int_negSucc : ¬ IsDefn env ``Int
  hT_Int_negSucc : EnvClosedPiL env ``Int.negSucc [] 1 (.const ``Int [])
  hnd_Int_ofNat : ¬ IsDefn env ``Int
  hT_Int_ofNat : EnvClosedPiL env ``Int.ofNat [] 1 (.const ``Int [])
  hnd_LE_mk : ¬ IsDefn env `LE
  hT_LE_mk : EnvDepFirst env `LE.mk [.zero] 1 `LE [.zero]
  hnd_LT_mk : ¬ IsDefn env `LT
  hT_LT_mk : EnvDepFirst env `LT.mk [.zero] 1 `LT [.zero]
  hnd_List_cons : ¬ IsDefn env `List
  hT_List_cons : EnvDepFirst env `List.cons [.zero] 2 `List [.zero]
  hnd_List_nil : ¬ IsDefn env `List
  hT_List_nil : EnvDepFirst env `List.nil [.zero] 0 `List [.zero]
  hnd_Mod_mk : ¬ IsDefn env `Mod
  hT_Mod_mk : EnvDepFirst env `Mod.mk [.zero] 1 `Mod [.zero]
  hnd_Mul_mk : ¬ IsDefn env `Mul
  hT_Mul_mk : EnvDepFirst env `Mul.mk [.zero] 1 `Mul [.zero]
  hnd_Nat_succ : ¬ IsDefn env ``Nat
  hT_Nat_succ : EnvClosedPiL env ``Nat.succ [] 1 (.const ``Nat [])
  hnd_Nat_zero : ¬ IsDefn env ``Nat
  hT_Nat_zero : EnvTypeL env ``Nat.zero [] (.const ``Nat [])
  hnd_NatCast_mk : ¬ IsDefn env `NatCast
  hT_NatCast_mk : EnvDepFirst env `NatCast.mk [.zero] 1 `NatCast [.zero]
  hnd_NatPow_mk : ¬ IsDefn env `NatPow
  hT_NatPow_mk : EnvDepFirst env `NatPow.mk [.zero] 1 `NatPow [.zero]
  hnd_Neg_mk : ¬ IsDefn env `Neg
  hT_Neg_mk : EnvDepFirst env `Neg.mk [.zero] 1 `Neg [.zero]
  hnd_OfNat_mk : ¬ IsDefn env `OfNat
  hT_OfNat_mk : EnvDepSpine env `OfNat.mk [.zero] 3 2 `OfNat [.zero]
  hnd_OrOp_mk : ¬ IsDefn env `OrOp
  hT_OrOp_mk : EnvDepFirst env `OrOp.mk [.zero] 1 `OrOp [.zero]
  hnd_PProd_mk : ¬ IsDefn env `PProd
  hT_PProd_mk : EnvDepSpine env `PProd.mk [.succ .zero, .succ .zero] 4 2 `PProd [.succ .zero, .succ .zero]
  hnd_PUnit_unit : ¬ IsDefn env ``PUnit
  hT_PUnit_unit : EnvTypeL env ``PUnit.unit [.succ .zero] (.const ``PUnit [.succ .zero])
  hnd_Pow_mk : ¬ IsDefn env `Pow
  hT_Pow_mk : EnvDepSpine env `Pow.mk [.zero, .zero] 3 2 `Pow [.zero, .zero]
  hnd_Prod_mk : ¬ IsDefn env `Prod
  hT_Prod_mk : EnvDepSpine env `Prod.mk [.zero, .zero] 4 2 `Prod [.zero, .zero]
  hnd_ShiftLeft_mk : ¬ IsDefn env `ShiftLeft
  hT_ShiftLeft_mk : EnvDepFirst env `ShiftLeft.mk [.zero] 1 `ShiftLeft [.zero]
  hnd_ShiftRight_mk : ¬ IsDefn env `ShiftRight
  hT_ShiftRight_mk : EnvDepFirst env `ShiftRight.mk [.zero] 1 `ShiftRight [.zero]
  hnd_Sparkle_Core_Domain_ActiveEdge_rising : ¬ IsDefn env `Sparkle.Core.Domain.ActiveEdge
  hT_Sparkle_Core_Domain_ActiveEdge_rising : EnvTypeL env `Sparkle.Core.Domain.ActiveEdge.rising [] (.const `Sparkle.Core.Domain.ActiveEdge [])
  hnd_Sparkle_Core_Domain_DomainConfig_mk : ¬ IsDefn env `Sparkle.Core.Domain.DomainConfig
  hT_Sparkle_Core_Domain_DomainConfig_mk : EnvClosedPiL env `Sparkle.Core.Domain.DomainConfig.mk [] 3 (.const `Sparkle.Core.Domain.DomainConfig [])
  hnd_Sparkle_Core_HasDomain_mk : ¬ IsDefn env `Sparkle.Core.HasDomain
  hT_Sparkle_Core_HasDomain_mk : EnvDepSpine env `Sparkle.Core.HasDomain.mk [] 2 2 `Sparkle.Core.HasDomain []
  hnd_Sparkle_Core_Signal_Signal_mk : ¬ IsDefn env `Sparkle.Core.Signal.Signal
  hT_Sparkle_Core_Signal_Signal_mk : EnvDepSpine env `Sparkle.Core.Signal.Signal.mk [.zero] 3 2 `Sparkle.Core.Signal.Signal [.zero]
  hnd_Sparkle_Core_Wireable_mk : ¬ IsDefn env `Sparkle.Core.Wireable
  hT_Sparkle_Core_Wireable_mk : EnvDepFirst env `Sparkle.Core.Wireable.mk [] 1 `Sparkle.Core.Wireable []
  hnd_Sparkle_IR_Type_ResetKind_synchronous : ¬ IsDefn env `Sparkle.IR.Type.ResetKind
  hT_Sparkle_IR_Type_ResetKind_synchronous : EnvTypeL env `Sparkle.IR.Type.ResetKind.synchronous [] (.const `Sparkle.IR.Type.ResetKind [])
  hnd_Sub_mk : ¬ IsDefn env `Sub
  hT_Sub_mk : EnvDepFirst env `Sub.mk [.zero] 1 `Sub [.zero]
  hnd_XorOp_mk : ¬ IsDefn env `XorOp
  hT_XorOp_mk : EnvDepFirst env `XorOp.mk [.zero] 1 `XorOp [.zero]

theorem ptcorpus_oblRowTypedV (env : Environment) (F : PTCorpusEnvFacts env) : OblRowTypedV PTcorpus env := by
  refine oblRowTypedV_of_keys PTcorpus env (tmsTable.map fun e => (e.1, e.2.1.map natLevel)) ?_ ?_
  · intro c ls h
    obtain ⟨e, he, h1, h2⟩ := tms_mem c ls h
    exact List.mem_map.2 ⟨e, he, by rw [h1, h2]⟩
  · intro k hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
    simp only [tmsTable, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_0 env F.hnd_Add_mk F.hT_Add_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_1 env F.hnd_AndOp_mk F.hT_AndOp_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_2 env F.hnd_Array_mk F.hT_Array_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_3 env F.hnd_BEq_mk F.hT_BEq_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_BitVec_ofFin env F.hnd_BitVec_ofFin F.hT_BitVec_ofFin
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_Bool_false env F.hnd_Bool_false F.hT_Bool_false
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_Bool_true env F.hnd_Bool_true F.hT_Bool_true
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_7 env F.hnd_Complement_mk F.hT_Complement_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_8 env F.hnd_Div_mk F.hT_Div_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HAdd_mk env F.hnd_HAdd_mk F.hT_HAdd_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HAnd_mk env F.hnd_HAnd_mk F.hT_HAnd_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HAppend_mk env F.hnd_HAppend_mk F.hT_HAppend_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HDiv_mk env F.hnd_HDiv_mk F.hT_HDiv_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HMod_mk env F.hnd_HMod_mk F.hT_HMod_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HMul_mk env F.hnd_HMul_mk F.hT_HMul_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HOr_mk env F.hnd_HOr_mk F.hT_HOr_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HPow_mk env F.hnd_HPow_mk F.hT_HPow_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HShiftLeft_mk env F.hnd_HShiftLeft_mk F.hT_HShiftLeft_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HShiftRight_mk env F.hnd_HShiftRight_mk F.hT_HShiftRight_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HSub_mk env F.hnd_HSub_mk F.hT_HSub_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_HXor_mk env F.hnd_HXor_mk F.hT_HXor_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_21 env F.hnd_Inhabited_mk F.hT_Inhabited_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_Int_negSucc env F.hnd_Int_negSucc F.hT_Int_negSucc
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_Int_ofNat env F.hnd_Int_ofNat F.hT_Int_ofNat
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_24 env F.hnd_LE_mk F.hT_LE_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_25 env F.hnd_LT_mk F.hT_LT_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_26 env F.hnd_List_cons F.hT_List_cons
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_27 env F.hnd_List_nil F.hT_List_nil
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_28 env F.hnd_Mod_mk F.hT_Mod_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_29 env F.hnd_Mul_mk F.hT_Mul_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_Nat_succ env F.hnd_Nat_succ F.hT_Nat_succ
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_Nat_zero env F.hnd_Nat_zero F.hT_Nat_zero
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_32 env F.hnd_NatCast_mk F.hT_NatCast_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_33 env F.hnd_NatPow_mk F.hT_NatPow_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_34 env F.hnd_Neg_mk F.hT_Neg_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_OfNat_mk env F.hnd_OfNat_mk F.hT_OfNat_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_36 env F.hnd_OrOp_mk F.hT_OrOp_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_PProd_mk env F.hnd_PProd_mk F.hT_PProd_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_PUnit_unit1 env F.hnd_PUnit_unit F.hT_PUnit_unit
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_Pow_mk env F.hnd_Pow_mk F.hT_Pow_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_Prod_mk env F.hnd_Prod_mk F.hT_Prod_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_41 env F.hnd_ShiftLeft_mk F.hT_ShiftLeft_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_42 env F.hnd_ShiftRight_mk F.hT_ShiftRight_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_ActiveEdge_rising env F.hnd_Sparkle_Core_Domain_ActiveEdge_rising F.hT_Sparkle_Core_Domain_ActiveEdge_rising
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_DomainConfig_mk env F.hnd_Sparkle_Core_Domain_DomainConfig_mk F.hT_Sparkle_Core_Domain_DomainConfig_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_Sparkle_Core_HasDomain_mk env F.hnd_Sparkle_Core_HasDomain_mk F.hT_Sparkle_Core_HasDomain_mk
    · exact Tools.ShippingGen5PTCorpusSpec.ptc_spine_rowTypedV_Sparkle_Core_Signal_Signal_mk env F.hnd_Sparkle_Core_Signal_Signal_mk F.hT_Sparkle_Core_Signal_Signal_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_47 env F.hnd_Sparkle_Core_Wireable_mk F.hT_Sparkle_Core_Wireable_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_ResetKind_synchronous env F.hnd_Sparkle_IR_Type_ResetKind_synchronous F.hT_Sparkle_IR_Type_ResetKind_synchronous
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_49 env F.hnd_Sub_mk F.hT_Sub_mk
    · exact Tools.ShippingGen5PTCorpus.ptc_rowTypedV_tm_50 env F.hnd_XorOp_mk F.hT_XorOp_mk

/-! ## §6 `RowTeleEvAt PTcorpus` over one environment

`PTCorpusTeleFacts env` names the env facts of the 34 rows that have a theorem (`ptc_teleEv_*`, `ptc_tele_*`, `rowTeleEvAt_nullary`). `PTCorpusTeleOpen env` is the list of the 17 rows that have none, as named `Prop`s (`RowTeleEvAt PTcorpus env c ls` itself): they are not assumed, they are the residue.
The other keys of the table are the 106 keys without a row (`rowTeleEvAt_of_none`). -/

structure PTCorpusTeleFacts (env : Environment) : Prop where
  closedL : EnvClosedL env
  nd_Nat : ¬ IsDefn env `Nat
  nd_Bool : ¬ IsDefn env `Bool
  nd_List : ¬ IsDefn env `List
  teleT_Add_mk : EnvForms env `Add.mk [.zero] bs_A2
  teleT_AndOp_mk : EnvForms env `AndOp.mk [.zero] bs_A2
  teleT_Array_mk : EnvForms env `Array.mk [.zero] bs_List
  teleT_BEq_mk : EnvForms env `BEq.mk [.zero] bs_BEq
  teleT_Complement_mk : EnvForms env `Complement.mk [.zero] bs_A1
  teleT_Div_mk : EnvForms env `Div.mk [.zero] bs_A2
  teleT_Inhabited_mk : EnvForms env `Inhabited.mk [.succ .zero] bs_V
  hnd_tele_Int_negSucc : ¬ IsDefn env ``Nat
  hT_tele_Int_negSucc : EnvConstPi env ``Int.negSucc [] [(``Nat, [])] (.const ``Int [])
  hnd_tele_Int_ofNat : ¬ IsDefn env ``Nat
  hT_tele_Int_ofNat : EnvConstPi env ``Int.ofNat [] [(``Nat, [])] (.const ``Int [])
  teleT_List_cons : EnvForms env `List.cons [.zero] bs_Cons
  teleT_List_nil : EnvForms env `List.nil [.zero] bs_Nil
  teleT_Mod_mk : EnvForms env `Mod.mk [.zero] bs_A2
  teleT_Mul_mk : EnvForms env `Mul.mk [.zero] bs_A2
  hnd_tele_Nat_succ : ¬ IsDefn env ``Nat
  hT_tele_Nat_succ : EnvConstPi env ``Nat.succ [] [(``Nat, [])] (.const ``Nat [])
  teleT_NatCast_mk : EnvForms env `NatCast.mk [.zero] bs_NatC
  teleT_NatPow_mk : EnvForms env `NatPow.mk [.zero] bs_NatP
  teleT_Neg_mk : EnvForms env `Neg.mk [.zero] bs_A1
  teleT_OfNat_mk : EnvForms env `OfNat.mk [.zero] bs_OfNat
  teleT_OrOp_mk : EnvForms env `OrOp.mk [.zero] bs_A2
  teleT_PProd_mk : EnvForms env `PProd.mk [.succ .zero, .succ .zero] bs_Prod
  teleT_Pow_mk : EnvForms env `Pow.mk [.zero, .zero] bs_Pow
  teleT_Prod_mk : EnvForms env `Prod.mk [.zero, .zero] bs_Prod
  teleT_ShiftLeft_mk : EnvForms env `ShiftLeft.mk [.zero] bs_A2
  teleT_ShiftRight_mk : EnvForms env `ShiftRight.mk [.zero] bs_A2
  hN_tele_Sparkle_Core_Domain_DomainConfig_mk : ¬ IsDefn env ``Nat
  hbd_tele_Sparkle_Core_Domain_DomainConfig_mk : BindersDen PTcorpus env [(``Nat, []), (`Sparkle.Core.Domain.ActiveEdge, []), (`Sparkle.Core.Domain.ResetKind, [])] [Nat, Sparkle.Core.Domain.ActiveEdge, Sparkle.IR.Type.ResetKind]
  hT_tele_Sparkle_Core_Domain_DomainConfig_mk : EnvConstPi env `Sparkle.Core.Domain.DomainConfig.mk [] [(``Nat, []), (`Sparkle.Core.Domain.ActiveEdge, []), (`Sparkle.Core.Domain.ResetKind, [])] (.const `Sparkle.Core.Domain.DomainConfig [])
  teleT_Sparkle_Core_Wireable_mk : EnvForms env `Sparkle.Core.Wireable.mk [] bs_Wire
  teleT_Sub_mk : EnvForms env `Sub.mk [.zero] bs_A2
  teleT_XorOp_mk : EnvForms env `XorOp.mk [.zero] bs_A2

structure PTCorpusTeleOpen (env : Environment) : Prop where
  open_BitVec_ofFin : RowTeleEvAt PTcorpus env `BitVec.ofFin []
  open_HAdd_mk : RowTeleEvAt PTcorpus env `HAdd.mk [.zero, .zero, .zero]
  open_HAnd_mk : RowTeleEvAt PTcorpus env `HAnd.mk [.zero, .zero, .zero]
  open_HAppend_mk : RowTeleEvAt PTcorpus env `HAppend.mk [.zero, .zero, .zero]
  open_HDiv_mk : RowTeleEvAt PTcorpus env `HDiv.mk [.zero, .zero, .zero]
  open_HMod_mk : RowTeleEvAt PTcorpus env `HMod.mk [.zero, .zero, .zero]
  open_HMul_mk : RowTeleEvAt PTcorpus env `HMul.mk [.zero, .zero, .zero]
  open_HOr_mk : RowTeleEvAt PTcorpus env `HOr.mk [.zero, .zero, .zero]
  open_HPow_mk : RowTeleEvAt PTcorpus env `HPow.mk [.zero, .zero, .zero]
  open_HShiftLeft_mk : RowTeleEvAt PTcorpus env `HShiftLeft.mk [.zero, .zero, .zero]
  open_HShiftRight_mk : RowTeleEvAt PTcorpus env `HShiftRight.mk [.zero, .zero, .zero]
  open_HSub_mk : RowTeleEvAt PTcorpus env `HSub.mk [.zero, .zero, .zero]
  open_HXor_mk : RowTeleEvAt PTcorpus env `HXor.mk [.zero, .zero, .zero]
  open_LE_mk : RowTeleEvAt PTcorpus env `LE.mk [.zero]
  open_LT_mk : RowTeleEvAt PTcorpus env `LT.mk [.zero]
  open_Sparkle_Core_HasDomain_mk : RowTeleEvAt PTcorpus env `Sparkle.Core.HasDomain.mk []
  open_Sparkle_Core_Signal_Signal_mk : RowTeleEvAt PTcorpus env `Sparkle.Core.Signal.Signal.mk [.zero]

theorem ptcorpus_rowTeleEvAt (env : Environment) (F : PTCorpusTeleFacts env) (O : PTCorpusTeleOpen env) :
    ∀ (c : Name) (ls : List Level), RowTeleEvAt PTcorpus env c ls := by
  intro c ls
  by_cases hn : PTcorpus.tms c ls = none
  · exact rowTeleEvAt_of_none PTcorpus env c ls hn
  obtain ⟨e, he, h1, h2⟩ := tms_mem c ls hn
  subst h1 h2
  simp only [tmsTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ptc_tele_Add_mk env F.closedL F.teleT_Add_mk
  · exact ptc_tele_AndOp_mk env F.closedL F.teleT_AndOp_mk
  · exact ptc_tele_Array_mk env F.closedL F.nd_List F.teleT_Array_mk
  · exact ptc_tele_BEq_mk env F.closedL F.nd_Bool F.teleT_BEq_mk
  · exact O.open_BitVec_ofFin
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_nullary env (t := tm_5) rfl
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_nullary env (t := tm_6) rfl
  · exact ptc_tele_Complement_mk env F.closedL F.teleT_Complement_mk
  · exact ptc_tele_Div_mk env F.closedL F.teleT_Div_mk
  · exact O.open_HAdd_mk
  · exact O.open_HAnd_mk
  · exact O.open_HAppend_mk
  · exact O.open_HDiv_mk
  · exact O.open_HMod_mk
  · exact O.open_HMul_mk
  · exact O.open_HOr_mk
  · exact O.open_HPow_mk
  · exact O.open_HShiftLeft_mk
  · exact O.open_HShiftRight_mk
  · exact O.open_HSub_mk
  · exact O.open_HXor_mk
  · exact ptc_tele_Inhabited_mk env F.closedL F.teleT_Inhabited_mk
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_Int_negSucc env F.hnd_tele_Int_negSucc F.hT_tele_Int_negSucc
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_Int_ofNat env F.hnd_tele_Int_ofNat F.hT_tele_Int_ofNat
  · exact O.open_LE_mk
  · exact O.open_LT_mk
  · exact ptc_tele_List_cons env F.closedL F.nd_List F.teleT_List_cons
  · exact ptc_tele_List_nil env F.closedL F.teleT_List_nil
  · exact ptc_tele_Mod_mk env F.closedL F.teleT_Mod_mk
  · exact ptc_tele_Mul_mk env F.closedL F.teleT_Mul_mk
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_Nat_succ env F.hnd_tele_Nat_succ F.hT_tele_Nat_succ
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_nullary env (t := tm_31) rfl
  · exact ptc_tele_NatCast_mk env F.closedL F.nd_Nat F.teleT_NatCast_mk
  · exact ptc_tele_NatPow_mk env F.closedL F.nd_Nat F.teleT_NatPow_mk
  · exact ptc_tele_Neg_mk env F.closedL F.teleT_Neg_mk
  · exact ptc_tele_OfNat_mk env F.closedL F.nd_Nat F.teleT_OfNat_mk
  · exact ptc_tele_OrOp_mk env F.closedL F.teleT_OrOp_mk
  · exact ptc_tele_PProd_mk env F.closedL F.teleT_PProd_mk
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_nullary env (t := tm_38) rfl
  · exact ptc_tele_Pow_mk env F.closedL F.teleT_Pow_mk
  · exact ptc_tele_Prod_mk env F.closedL F.teleT_Prod_mk
  · exact ptc_tele_ShiftLeft_mk env F.closedL F.teleT_ShiftLeft_mk
  · exact ptc_tele_ShiftRight_mk env F.closedL F.teleT_ShiftRight_mk
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_nullary env (t := tm_43) rfl
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_DomainConfig_mk env F.hN_tele_Sparkle_Core_Domain_DomainConfig_mk F.hbd_tele_Sparkle_Core_Domain_DomainConfig_mk F.hT_tele_Sparkle_Core_Domain_DomainConfig_mk
  · exact O.open_Sparkle_Core_HasDomain_mk
  · exact O.open_Sparkle_Core_Signal_Signal_mk
  · exact ptc_tele_Sparkle_Core_Wireable_mk env F.closedL F.nd_Nat F.teleT_Sparkle_Core_Wireable_mk
  · exact Tools.ShippingGen5PTCorpus.ptc_teleEv_nullary env (t := tm_48) rfl
  · exact ptc_tele_Sub_mk env F.closedL F.teleT_Sub_mk
  · exact ptc_tele_XorOp_mk env F.closedL F.teleT_XorOp_mk


/-! ## §7 Over `envAt cref w` (the environment of the FG statement) and the four named obligations -/

section envat
open Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5ConstValueESoundK (OblLbrZero)
open Tools.ShippingGen5EnvDeclClosed (KernelClosedInvariant envDeclClosed_of_kernel)

/-- `OblRowTypedV PTcorpus (envAt cref w)` from the named env facts about `envAt cref w`. -/
theorem ptcorpus_oblRowTypedV_envAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (F : PTCorpusEnvFacts (envAt cref w)) : OblRowTypedV PTcorpus (envAt cref w) := ptcorpus_oblRowTypedV _ F

/-- `∀ c ls, RowTeleEvAt PTcorpus (envAt cref w) c ls` from the named env facts and the named residue (the 17 rows without a theorem). -/
theorem ptcorpus_rowTeleEvAt_envAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (F : PTCorpusTeleFacts (envAt cref w)) (O : PTCorpusTeleOpen (envAt cref w)) :
    ∀ (c : Name) (ls : List Level), RowTeleEvAt PTcorpus (envAt cref w) c ls := ptcorpus_rowTeleEvAt _ F O

/-- The field `closedL` of `PTCorpusTeleFacts` follows from the two named premises of the FG statement. -/
theorem closedL_envAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (hz : OblLbrZero)
    (hK : KernelClosedInvariant (envAt cref w)) : EnvClosedL (envAt cref w) :=
  envClosedL_of_declClosed (envDeclClosed_of_kernel hz hK)

end envat

/-- `Fin.mk`, `Decidable.isTrue`, `Decidable.isFalse` have no row in `PTcorpus` (`MissingWhy.propBinder`): their `RowTeleEvAt` and `RowTypedAtV` hold with no hypothesis. NOT a typed row: no derivation reaches the key. -/
theorem oblTeleEv_Fin_mk_PTcorpus (env : Environment) : OblTeleEv_Fin_mk PTcorpus env := rowTeleEvAt_of_none PTcorpus env _ _ rfl
theorem oblTeleEv_Decidable_isTrue_PTcorpus (env : Environment) : OblTeleEv_Decidable_isTrue PTcorpus env := rowTeleEvAt_of_none PTcorpus env _ _ rfl
theorem oblTeleEv_Decidable_isFalse_PTcorpus (env : Environment) : OblTeleEv_Decidable_isFalse PTcorpus env := rowTeleEvAt_of_none PTcorpus env _ _ rfl
theorem rowTypedV_Fin_mk_PTcorpus (env : Environment) : RowTypedAtV PTcorpus env ``Fin.mk [] := rowTypedAtV_of_none PTcorpus env _ _ rfl
theorem rowTypedV_Decidable_isTrue_PTcorpus (env : Environment) : RowTypedAtV PTcorpus env ``Decidable.isTrue [] := rowTypedAtV_of_none PTcorpus env _ _ rfl
theorem rowTypedV_Decidable_isFalse_PTcorpus (env : Environment) : RowTypedAtV PTcorpus env ``Decidable.isFalse [] := rowTypedAtV_of_none PTcorpus env _ _ rfl

/-- NEGATIVE CONTROL: the vacuity is by absence of the row, not by a proof about it: `BitVec.ofFin` HAS a row, and `PTcorpus.tms` of it is not `none`. -/
theorem control_bitVec_ofFin_has_row : PTcorpus.tms `BitVec.ofFin [] ≠ none := by
  intro h; have : PTcorpus.tms `BitVec.ofFin [] = some tm_4.row := rfl
  rw [this] at h; cases h

end Tools.ShippingGen5PTCorpusTele
