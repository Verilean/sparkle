import Tools.PassPh.Beta
import Tools.PassPh.Rec
import Tools.PassPh.Iota
import Tools.PassPh.BetaAll
import Tools.PassPh.ListLit
import Tools.PassPh.Memo
set_option autoImplicit false
-- freeze rev2 + rev3 (scripts/gen5/RT_PASS_PH_FREEZE.md). Built in Pod (kjob lake build Tools.PassPh.Pass Tests.Gen5.PassPhCheck Tools.ShippingGen5ReaderTraceAbbrevS1 Tests.Gen5.ReaderTraceAbbrevS1Check, exit 0) on the tree of 18fa57ac6bdb999e9ac4747bbe7ad43143004dfd (Lean content identical; header comment-only). No sorry / axiom / native_decide in source (all of Tools/PassPh/*.lean). Conditional on BetaNonTargetAgrees, ExprEqvLaws (T1 +1 candidates), HeadBetaAgreesL (replaces T1L-74), RecRulePhU (hypothesis definition); none accepted. Clean build is the coder's.

/-! # pass_ph skeleton: Pass group (evalNode?_good, unfoldCall?_good, joint induction on passM/passStep/passSpine, passWith_ph, pass_ph).
Depends on all other groups. Memo invariant `MemoGoodL` (Defs): every (k, v) in the memo has `∀ L, GL L k → GL L v`. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Sparkle.Compiler.MachRecUnfold

theorem M_bind_ok {α β : Type} (x : M α) (f : α → M β) (r : β)
    (h : (x >>= f) = ExceptT.mk (some (.ok r))) :
    ∃ v, x = ExceptT.mk (some (.ok v)) ∧ f v = ExceptT.mk (some (.ok r)) := by
  have hx : x = ExceptT.mk x.run := rfl
  rcases ho : x.run with _ | (m | v)
  · have h' : (x.run >>= ExceptT.bindCont f) = some (Except.ok r) := h
    rw [ho] at h'; simp [ExceptT.bindCont] at h'
  · have h' : (x.run >>= ExceptT.bindCont f) = some (Except.ok r) := h
    rw [ho] at h'; simp [ExceptT.bindCont] at h'
  · refine ⟨v, by rw [hx, ho], ?_⟩
    rw [hx, ho] at h
    simpa [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont] using h

theorem M_pure_ok {α : Type} (a r : α) (h : (pure a : M α) = ExceptT.mk (some (.ok r))) : a = r := by
  have h' : (some (Except.ok a) : Option (Except String α)) = some (Except.ok r) := h
  exact Except.ok.inj (Option.some.inj h')

theorem M_stuck_ne {α : Type} (r : α) : (stuck : M α) ≠ ExceptT.mk (some (.ok r)) := by
  intro h
  have h' : (none : Option (Except String α)) = some (Except.ok r) := h
  cases h'

theorem GL_mkApp {L : Nat} {f a : Lean.Expr} (hf : GL L f) (ha : GL L a) : GL L (mkApp f a) := by
  simp [GL, NoPh, BvarLt, hf.1, hf.2, ha.1, ha.2]

theorem mkListLit_goodL (L : Nat) (α : Lean.Expr) (xs : List Lean.Expr) (ha : GL L α) (hx : ∀ x ∈ xs, GL L x) :
    GL L (mkListLit α xs) := by
  have hc : ∀ (n : Lean.Name), GL L (Lean.Expr.const n [Level.zero]) := fun n => by simp [GL, NoPh, BvarLt]
  induction xs with
  | nil => exact GL_mkApp (hc _) ha
  | cons a xs ih =>
    have := ih (fun x hx' => hx x (List.mem_cons_of_mem _ hx'))
    have h1 := hx a (List.mem_cons_self ..)
    exact GL_mkApp (GL_mkApp (GL_mkApp (hc _) ha) h1) this

theorem GL_args {L : Nat} {e : Lean.Expr} (he : GL L e) : ∀ a ∈ e.getAppArgs, GL L a :=
  fun a h => phArgs_getAppArgs he.1 he.2 a h

theorem headD_mem (xs : List Lean.Expr) (d : Lean.Expr) : xs.headD d = d ∨ xs.headD d ∈ xs := by
  cases xs with
  | nil => left; rfl
  | cons a xs => right; simp

theorem lit_armL (L : Nat) (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat) (e r : Lean.Expr) (he : GL L e)
    (h : (listLit? natLit? listLitLimit e >>= fun x => pure (mkListLit x.1 x.2) : M Lean.Expr) =
      ExceptT.mk (some (.ok r))) : GL L r := by
  obtain ⟨⟨α, xs⟩, hv, hf⟩ := M_bind_ok _ _ _ h
  have := listLit?_goodL hi1 natLit? listLitLimit L e α xs he hv
  have hr := M_pure_ok _ _ hf
  rw [← hr]
  exact mkListLit_goodL L α xs this.1 this.2

theorem headD_armL (L : Nat) (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat) (l d r : Lean.Expr) (hl : GL L l) (hd : GL L d)
    (h : (listLit? natLit? listLitLimit l >>= fun x => pure (x.2.headD d) : M Lean.Expr) =
      ExceptT.mk (some (.ok r))) : GL L r := by
  obtain ⟨⟨α, xs⟩, hv, hf⟩ := M_bind_ok _ _ _ h
  have := listLit?_goodL hi1 natLit? listLitLimit L l α xs hl hv
  have hr := M_pure_ok _ _ hf
  rw [← hr]
  rcases headD_mem xs d with h1 | h1
  · rw [h1]; exact hd
  · exact this.2 _ h1

theorem eq_armL (L : Nat) (natLit? : Lean.Expr → Option Nat) (ty x y a b r : Lean.Expr) (ha : GL L a) (hb : GL L b)
    (h : (if (!ty.isConstOf ``Bool) = true then stuck
        else do
          let vx ← boolVal? natLit? x
          let vy ← boolVal? natLit? y
          pure (if (vx == vy) = true then a else b) : M Lean.Expr) = ExceptT.mk (some (.ok r))) : GL L r := by
  by_cases hb' : (!ty.isConstOf ``Bool) = true
  · rw [if_pos hb'] at h; exact absurd h (M_stuck_ne r)
  · rw [if_neg hb'] at h
    obtain ⟨vx, _, h1⟩ := M_bind_ok _ _ _ h
    obtain ⟨vy, _, h2⟩ := M_bind_ok _ _ _ h1
    have hr := M_pure_ok _ _ h2
    rw [← hr]
    split
    · exact ha
    · exact hb

theorem evalNode?_goodL (hi1 : Inst1Agrees) (natLit? : Lean.Expr → Option Nat) :
    ∀ (L : Nat) (e r : Lean.Expr), GL L e → evalNode? natLit? e = ExceptT.mk (some (.ok r)) → GL L r := by

  intro L e r he h
  have hargs := GL_args he
  unfold evalNode? at h
  generalize e.getAppFn = F at h
  generalize hA : e.getAppArgs = A at h hargs
  cases F <;> try exact absurd h (M_stuck_ne r)
  rename_i n us
  rcases n with _ | ⟨p1, s1⟩ | ⟨p1, k1⟩ <;> try exact absurd h (M_stuck_ne r)
  rcases p1 with _ | ⟨p2, s2⟩ | ⟨p2, k2⟩ <;> try exact absurd h (M_stuck_ne r)
  · by_cases hs : s1 = "ite"
    · subst hs
      rcases A with ⟨l⟩
      rcases l with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, l⟩⟩⟩⟩⟩⟩ <;>
        try exact absurd h (M_stuck_ne r)
      have ha4 : GL L a4 := hargs a4 (by simp)
      have ha5 : GL L a5 := hargs a5 (by simp)
      conv at h => lhs; whnf
      dsimp [Array.getLit] at h
      generalize a2.consumeMData.getAppFn = F2 at h
      generalize hA2 : a2.consumeMData.getAppArgs = A2 at h
      cases F2 <;> try exact absurd h (M_stuck_ne r)
      rename_i n2 us2
      rcases n2 with _ | ⟨p3, s3⟩ | ⟨p3, k3⟩ <;> try exact absurd h (M_stuck_ne r)
      rcases p3 with _ | ⟨p4, s4⟩ | ⟨p4, k4⟩ <;> try exact absurd h (M_stuck_ne r)
      · by_cases hs3 : s3 = "Eq"
        · subst hs3
          rcases A2 with ⟨l2⟩
          rcases l2 with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, l2⟩⟩⟩⟩ <;>
            try exact absurd h (M_stuck_ne r)
          conv at h => lhs; whnf
          dsimp [Array.getLit] at h
          exact eq_armL L natLit? _ _ _ _ _ _ ha4 ha5 h
        · exfalso
          revert h
          unfold evalNode?.match_1
          dsimp only [ctorApp?._sparseCasesOn_5, iota._sparseCasesOn_14, listLit?._sparseCasesOn_7]
          rw [dif_neg hs3]
          exact M_stuck_ne r
    · exfalso
      revert h
      unfold evalNode?.match_3
      dsimp only [ctorApp?._sparseCasesOn_5, iota._sparseCasesOn_14, evalNode?._sparseCasesOn_3]
      rw [dif_neg hs]
      exact M_stuck_ne r
  rcases p2 with _ | ⟨p3, s3⟩ | ⟨p3, k3⟩ <;> try exact absurd h (M_stuck_ne r)
  · by_cases hL : s2 = "List"
    · subst hL
      by_cases hz : s1 = "zipIdx"
      · subst hz; exact lit_armL L hi1 natLit? e r he h
      · by_cases hh : s1 = "headD"
        · subst hh
          rcases A with ⟨l⟩
          rcases l with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, l⟩⟩⟩⟩ <;>
            try exact absurd h (M_stuck_ne r)
          have ha2 : GL L a2 := hargs a2 (by simp)
          have ha3 : GL L a3 := hargs a3 (by simp)
          conv at h => lhs; whnf
          dsimp [Array.getLit] at h
          exact headD_armL L hi1 natLit? _ _ r ha2 ha3 h
        · exfalso
          revert h
          unfold evalNode?.match_3
          dsimp only [ctorApp?._sparseCasesOn_5, iota._sparseCasesOn_14, evalNode?._sparseCasesOn_3,
            listLit?._sparseCasesOn_7]
          rw [dif_pos rfl, dif_neg hz, dif_neg hh]
          exact M_stuck_ne r
    · by_cases hAr : s2 = "Array"
      · subst hAr
        by_cases ht : s1 = "toList"
        · subst ht; exact lit_armL L hi1 natLit? e r he h
        · exfalso
          revert h
          unfold evalNode?.match_3
          dsimp only [ctorApp?._sparseCasesOn_5, iota._sparseCasesOn_14, evalNode?._sparseCasesOn_3,
            listLit?._sparseCasesOn_7]
          rw [dif_neg hL, dif_pos rfl, dif_neg ht]
          exact M_stuck_ne r
      · exfalso
        revert h
        unfold evalNode?.match_3
        dsimp only [ctorApp?._sparseCasesOn_5, iota._sparseCasesOn_14, evalNode?._sparseCasesOn_3,
          listLit?._sparseCasesOn_7]
        rw [dif_neg hL, dif_neg hAr]
        exact M_stuck_ne r

theorem unfoldCall?_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (L : Nat) (e r : Lean.Expr), GL L e → unfoldCall? env natLit? isUser e = ExceptT.mk (some (.ok r)) → GL L r := by

  intro L e r he h
  have hargs := GL_args he
  unfold unfoldCall? at h
  generalize e.getAppFn = F at h
  cases F <;> try exact absurd h (M_stuck_ne r)
  rename_i n ls
  dsimp only at h
  by_cases hu : (!isUser n) = true
  · rw [if_pos hu] at h; exact absurd h (M_stuck_ne r)
  · rw [if_neg hu] at h
    generalize hf : env.find? (Lean.Meta.mkSmartUnfoldingNameFor n) = o at h
    rcases o with _ | ci
    · exact absurd h (M_stuck_ne r)
    cases ci <;> try exact absurd h (M_stuck_ne r)
    rename_i d
    obtain ⟨r1, h1, h2⟩ := M_bind_ok _ _ _ h
    have hv : GL L (d.value.instantiateLevelParams d.levelParams ls) :=
      GL_mono (Nat.zero_le L) (ilp_ph hrep _ _ _ (hd _ d hf))
    have hb : GL L ((d.value.instantiateLevelParams d.levelParams ls).beta e.getAppArgs) :=
      beta_goodL hh hbt L _ _ hv hargs
    have hr1 : GL L r1 := reduceHead_goodL env natLit? hd hr hrep hh hbt 64 L _ r1 hb h1
    have h3 : (some (betaAll betaAllLimit r1) : Option (Except String Lean.Expr)) = some (Except.ok r) := h2
    exact betaAll_goodL hh hbt _ L _ _ hr1 (Option.some.inj h3)

abbrev St := Std.HashMap Lean.Expr Lean.Expr

theorem PM_bind_ok {α β : Type} (x : PM α) (f : α → PM β) (s : St) (r : β) (s' : St)
    (h : (ExceptT.bind x f).run.run s = (Except.ok r, s')) :
    ∃ v s1, x.run.run s = (Except.ok v, s1) ∧ (f v).run.run s1 = (Except.ok r, s') := by
  rcases hx : x.run.run s with ⟨o, s1⟩
  have key : (ExceptT.bind x f).run.run s = (match x.run.run s with
      | (a, s1) => (ExceptT.bindCont f a).run s1) := rfl
  rw [key, hx] at h
  cases o with
  | error m => exfalso; have := Prod.mk.inj h; cases this.1
  | ok v => exact ⟨v, s1, rfl, h⟩

theorem PM_pure_ok {α : Type} (a r : α) (s s' : St) (h : (ExceptT.pure a : PM α).run.run s = (Except.ok r, s')) : a = r ∧ s = s' := by
  have h2 := Prod.mk.inj h
  exact ⟨Except.ok.inj h2.1, h2.2⟩

theorem PM_get_ok (s s' : St) {r : St} (h : (get : PM St).run.run s = (Except.ok r, s')) : r = s ∧ s = s' := by
  have h2 := Prod.mk.inj h
  exact ⟨(Except.ok.inj h2.1).symm, h2.2⟩


theorem liftStep_ok {α : Type} (x : M α) (s s' : St) (o : Option α)
    (h : (liftStep x).run.run s = (Except.ok o, s')) :
    s = s' ∧ (o = none ∨ ∃ a, o = some a ∧ x = ExceptT.mk (some (.ok a))) := by
  have hx : x = ExceptT.mk x.run := rfl
  unfold liftStep at h
  rcases hr : x.run with _ | (m | a)
  · rw [hr] at h
    have h2 := Prod.mk.inj h
    exact ⟨h2.2, Or.inl (Except.ok.inj h2.1).symm⟩
  · rw [hr] at h
    have h2 := Prod.mk.inj h
    cases h2.1
  · rw [hr] at h
    have h2 := Prod.mk.inj h
    refine ⟨h2.2, Or.inr ⟨a, (Except.ok.inj h2.1).symm, ?_⟩⟩
    rw [hx, hr]


theorem PM_modify_ok (f : St → St) (s s' : St) (u : Unit) (h : (modify f : PM Unit).run.run s = (Except.ok u, s')) : s' = f s := by
  exact (Prod.mk.inj h).2.symm

theorem PM_reenter {α : Type} (m : String) (fuel : Nat) (k : Nat → PM α) (s s' : St) (r : α)
    (h : (match fuel with | 0 => throw m | n+1 => k n : PM α).run.run s = (Except.ok r, s')) :
    ∃ n, fuel = n+1 ∧ (k n).run.run s = (Except.ok r, s') := by
  cases fuel with
  | zero => exact absurd (Prod.mk.inj h).1 (by intro h'; cases h')
  | succ n => exact ⟨n, rfl, h⟩

theorem gl_lam {L : Nat} {n : Lean.Name} {t b : Lean.Expr} {bi : Lean.BinderInfo} :
    GL L (.lam n t b bi) ↔ GL L t ∧ GL (L+1) b := by
  simp only [GL, NoPh, BvarLt, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem gl_letE {L : Nat} {n : Lean.Name} {t v b : Lean.Expr} {nd : Bool} :
    GL L (.letE n t v b nd) ↔ GL L t ∧ GL L v ∧ GL (L+1) b := by
  simp only [GL, NoPh, BvarLt, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩, h6⟩; exact ⟨⟨h1, h4⟩, ⟨h2, h5⟩, h3, h6⟩
  · rintro ⟨⟨h1, h4⟩, ⟨h2, h5⟩, h3, h6⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩, h6⟩

theorem gl_mdata' {L : Nat} {d : Lean.MData} {b : Lean.Expr} : GL L (.mdata d b) ↔ GL L b := by
  simp [GL, NoPh, BvarLt]

def PMOk (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool) (fuel : Nat) (e : Lean.Expr) : Prop :=
  ∀ (r : Lean.Expr) (s s' : St), MemoGoodL s → (passM env natLit? isUser fuel e).run.run s = (Except.ok r, s') →
    MemoGoodL s' ∧ ∀ L, GL L e → GL L r

def PStOk (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool) (fuel : Nat) (e : Lean.Expr) : Prop :=
  ∀ (r : Lean.Expr) (s s' : St), MemoGoodL s → (passStep env natLit? isUser fuel e).run.run s = (Except.ok r, s') →
    MemoGoodL s' ∧ ∀ L, GL L e → GL L r

def PSpOk (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool) (fuel : Nat) (e : Lean.Expr) : Prop :=
  ∀ (h : Lean.Expr) (args : Array Lean.Expr) (s s' : St), MemoGoodL s →
    (passSpine env natLit? isUser fuel e).run.run s = (Except.ok (h, args), s') →
    MemoGoodL s' ∧ ∀ L, GL L e → GL L h ∧ ∀ a ∈ args, GL L a

theorem passJoint (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees)
    (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws) :
    ∀ fuel, (∀ e, PMOk env natLit? isUser fuel e) ∧ (∀ e, PStOk env natLit? isUser fuel e) ∧
      (∀ e, PSpOk env natLit? isUser fuel e) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ihF =>
  suffices H : ∀ n e, sizeOf e = n → PMOk env natLit? isUser fuel e ∧ PStOk env natLit? isUser fuel e ∧
      PSpOk env natLit? isUser fuel e from
    ⟨fun e => (H _ e rfl).1, fun e => (H _ e rfl).2.1, fun e => (H _ e rfl).2.2⟩
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihN =>
  intro e hn
  have sm : ∀ e', sizeOf e' < sizeOf e → PMOk env natLit? isUser fuel e' ∧ PStOk env natLit? isUser fuel e' ∧
      PSpOk env natLit? isUser fuel e' := fun e' h => ihN _ (hn ▸ h) e' rfl
  have hstep : PStOk env natLit? isUser fuel e := by
    intro r s s' hs h
    cases e with
    | app f a =>
      rw [passStep] at h
      obtain ⟨⟨hd', args⟩, s1, h1, h2⟩ := PM_bind_ok _ _ _ _ _ h
      obtain ⟨a', s2, h3, h4⟩ := PM_bind_ok _ _ _ _ _ h2
      obtain ⟨hs1, hsp⟩ := (sm f (by simp <;> omega)).2.2 _ _ _ _ hs h1
      obtain ⟨hs2, hma⟩ := (sm a (by simp <;> omega)).1 _ _ _ hs1 h3
      dsimp only at h4
      obtain ⟨o, s3, h5, h6⟩ := PM_bind_ok _ _ _ _ _ h4
      obtain ⟨hs23, ho⟩ := liftStep_ok _ _ _ _ h5
      subst hs23
      have hge : ∀ L, GL L (f.app a) → GL L (mkAppN hd' (args.push a')) := by
        intro L he
        obtain ⟨hf, ha⟩ := gl_app_split he
        obtain ⟨h1', h2'⟩ := (hsp L hf)
        refine mkAppN_goodL L _ _ h1' ?_
        intro x hx
        rcases Array.mem_push.mp hx with h | h
        · exact h2' x h
        · subst h; exact hma L ha
      rcases ho with rfl | ⟨r1, rfl, hev⟩
      · dsimp only at h6
        obtain ⟨o2, s4, h7, h8⟩ := PM_bind_ok _ _ _ _ _ h6
        obtain ⟨hs34, ho2⟩ := liftStep_ok _ _ _ _ h7
        subst hs34
        rcases ho2 with rfl | ⟨r2, rfl, hun⟩
        · dsimp only at h8
          obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h8
          exact ⟨hs2, fun L he => hge L he⟩
        · dsimp only at h8
          obtain ⟨n, rfl, h9⟩ := PM_reenter _ _ (fun n => passM env natLit? isUser n r2) _ _ _ h8
          obtain ⟨hs', hr2⟩ := (ihF n (Nat.lt_succ_self n)).1 r2 _ _ _ hs2 h9
          exact ⟨hs', fun L he => hr2 L (unfoldCall?_goodL env natLit? isUser hd hr hrep hh hbt L _ _ (hge L he) hun)⟩
      · dsimp only at h6
        obtain ⟨n, rfl, h9⟩ := PM_reenter _ _ (fun n => passM env natLit? isUser n r1) _ _ _ h6
        obtain ⟨hs', hr1⟩ := (ihF n (Nat.lt_succ_self n)).1 r1 _ _ _ hs2 h9
        exact ⟨hs', fun L he => hr1 L (evalNode?_goodL hi1 natLit? L _ _ (hge L he) hev)⟩
    | lam n t b bi =>
      rw [passStep] at h
      obtain ⟨b', s1, h1, h2⟩ := PM_bind_ok _ _ _ _ _ h
      obtain ⟨hs1, hb⟩ := (sm b (by simp <;> omega)).1 _ _ _ hs h1
      obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h2
      refine ⟨hs1, fun L he => ?_⟩
      rw [gl_lam] at he ⊢
      exact ⟨he.1, hb _ he.2⟩
    | mdata d b =>
      rw [passStep] at h
      obtain ⟨b', s1, h1, h2⟩ := PM_bind_ok _ _ _ _ _ h
      obtain ⟨hs1, hb⟩ := (sm b (by simp <;> omega)).1 _ _ _ hs h1
      obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h2
      refine ⟨hs1, fun L he => ?_⟩
      rw [gl_mdata'] at he ⊢
      exact hb _ he
    | letE n t v b nd =>
      rw [passStep] at h
      obtain ⟨v', s1, h1, h2⟩ := PM_bind_ok _ _ _ _ _ h
      obtain ⟨hs1, hv⟩ := (sm v (by simp <;> omega)).1 _ _ _ hs h1
      obtain ⟨o, s2, h3, h4⟩ := PM_bind_ok _ _ _ _ _ h2
      obtain ⟨hs12, ho⟩ := liftStep_ok _ _ _ _ h3
      subst hs12
      by_cases hc : (!v'.hasLooseBVars && !v'.hasFVar && o.isSome) = true
      · rw [if_pos hc] at h4
        obtain ⟨n', rfl, h9⟩ := PM_reenter _ _ (fun k => passM env natLit? isUser k (b.instantiate1 v')) _ _ _ h4
        obtain ⟨hs', hr1⟩ := (ihF n' (Nat.lt_succ_self n')).1 (b.instantiate1 v') _ _ _ hs1 h9
        refine ⟨hs', fun L he => hr1 L ?_⟩
        rw [gl_letE] at he
        have hv' := hv L he.2.1
        have := inst1Ph_of_agrees hi1 b v' L L he.2.2.1 hv'.1 he.2.2.2 hv'.2 (Nat.le_refl L)
        exact ⟨this.1, this.2⟩
      · rw [if_neg hc] at h4
        obtain ⟨b', s3, h5, h6⟩ := PM_bind_ok _ _ _ _ _ h4
        obtain ⟨hs3, hb⟩ := (sm b (by simp <;> omega)).1 _ _ _ hs1 h5
        obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h6
        refine ⟨hs3, fun L he => ?_⟩
        rw [gl_letE] at he ⊢
        exact ⟨he.1, hv L he.2.1, hb _ he.2.2⟩
    | bvar i =>
      rw [passStep] at h
      · obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h
        exact ⟨hs, fun L he => he⟩
      all_goals (intros; contradiction)
    | fvar i =>
      rw [passStep] at h
      · obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h
        exact ⟨hs, fun L he => he⟩
      all_goals (intros; contradiction)
    | mvar i =>
      rw [passStep] at h
      · obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h
        exact ⟨hs, fun L he => he⟩
      all_goals (intros; contradiction)
    | sort i =>
      rw [passStep] at h
      · obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h
        exact ⟨hs, fun L he => he⟩
      all_goals (intros; contradiction)
    | const i j =>
      rw [passStep] at h
      · obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h
        exact ⟨hs, fun L he => he⟩
      all_goals (intros; contradiction)
    | forallE i j k l =>
      rw [passStep] at h
      · obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h
        exact ⟨hs, fun L he => he⟩
      all_goals (intros; contradiction)
    | lit i =>
      rw [passStep] at h
      · obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h
        exact ⟨hs, fun L he => he⟩
      all_goals (intros; contradiction)
    | proj i j k =>
      rw [passStep] at h
      · obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h
        exact ⟨hs, fun L he => he⟩
      all_goals (intros; contradiction)
  have hM : PMOk env natLit? isUser fuel e := by
    intro r s s' hs h
    rw [passM] at h
    obtain ⟨st, s1, h1, h2⟩ := PM_bind_ok _ _ _ _ _ h
    obtain ⟨rfl, rfl⟩ := PM_get_ok _ _ h1
    rcases hg : st.get? e with _ | v
    · rw [hg] at h2
      dsimp only at h2
      obtain ⟨r0, s2, h3, h4⟩ := PM_bind_ok _ _ _ _ _ h2
      obtain ⟨hs2, hr0⟩ := hstep _ _ _ hs h3
      obtain ⟨u, s3, h5, h6⟩ := PM_bind_ok _ _ _ _ _ h4
      have h7 := PM_modify_ok _ _ _ _ h5
      obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h6
      subst h7
      exact ⟨memoGoodL_insert hEq hs2 e r0 hr0, hr0⟩
    · rw [hg] at h2
      dsimp only at h2
      obtain ⟨rfl, rfl⟩ := PM_pure_ok _ _ _ _ h2
      exact ⟨hs, memoGoodL_hit hs hg⟩
  have hsp : PSpOk env natLit? isUser fuel e := by
    intro hh' args s s' hs h
    cases e with
    | app f a =>
      rw [passSpine] at h
      obtain ⟨⟨hd', args'⟩, s1, h1, h2⟩ := PM_bind_ok _ _ _ _ _ h
      obtain ⟨a', s2, h3, h4⟩ := PM_bind_ok _ _ _ _ _ h2
      obtain ⟨hs1, hsp'⟩ := (sm f (by simp <;> omega)).2.2 _ _ _ _ hs h1
      obtain ⟨hs2, hma⟩ := (sm a (by simp <;> omega)).1 _ _ _ hs1 h3
      obtain ⟨he, rfl⟩ := PM_pure_ok _ _ _ _ h4
      have he' := Prod.mk.inj he
      obtain ⟨rfl, rfl⟩ := he'
      refine ⟨hs2, fun L hL => ?_⟩
      obtain ⟨hf, ha⟩ := gl_app_split hL
      obtain ⟨hh1, hh2⟩ := hsp' L hf
      refine ⟨hh1, fun x hx => ?_⟩
      rcases Array.mem_push.mp hx with h | h
      · exact hh2 x h
      · subst h; exact hma L ha
    | _ =>
      rw [passSpine] at h
      · obtain ⟨r0, s1, h1, h2⟩ := PM_bind_ok _ _ _ _ _ h
        obtain ⟨hs1, hr0⟩ := hM _ _ _ hs h1
        obtain ⟨he, rfl⟩ := PM_pure_ok _ _ _ _ h2
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨hs1, fun L hL => ⟨hr0 L hL, by simp⟩⟩
      all_goals (intros; contradiction)
  exact ⟨hM, hstep, hsp⟩


/-- the statement of `pass_ph` (freeze §1 with rev3: `ExprEqvLaws` added), as a Prop -/
def PassPh' : Prop :=
  ∀ (natLit? : Lean.Expr → Option Nat),
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    Tools.Assume.ExprEqvGL.ExprEqvLaws →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true

/-- joint induction on `passM` / `passStep` / `passSpine` (done in `passJoint`) -/
theorem passM_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees)
    (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), MemoGoodL s →
      (passM env natLit? isUser fuel e).run.run s = (Except.ok r, s') → MemoGoodL s' ∧ ∀ L, GL L e → GL L r :=
  fun fuel e r s s' hs h => (passJoint env natLit? isUser hd hr hrep hi1 hh hbt hEq fuel).1 e r s s' hs h

theorem passStep_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees)
    (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), MemoGoodL s →
      (passStep env natLit? isUser fuel e).run.run s = (Except.ok r, s') → MemoGoodL s' ∧ ∀ L, GL L e → GL L r :=
  fun fuel e r s s' hs h => (passJoint env natLit? isUser hd hr hrep hi1 hh hbt hEq fuel).2.1 e r s s' hs h

theorem passSpine_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees)
    (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws) :
    ∀ (fuel : Nat) (e h : Lean.Expr) (args : Array Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr),
      MemoGoodL s → (passSpine env natLit? isUser fuel e).run.run s = (Except.ok (h, args), s') →
      MemoGoodL s' ∧ ∀ L, GL L e → GL L h ∧ ∀ a ∈ args, GL L a :=
  fun fuel e h args s s' hs h' => (passJoint env natLit? isUser hd hr hrep hi1 hh hbt hEq fuel).2.2 e h args s s' hs h'

theorem passWith_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    Tools.Assume.ExprEqvGL.ExprEqvLaws →
    ∀ (fuel : Nat) (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.passWith fuel env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true := by
  intro env hd hr hrep hi1 hh hbt hEq fuel isUser e r hn hb h
  unfold Sparkle.Compiler.MachRecUnfold.passWith at h
  rcases hx : (passM env natLit? isUser fuel e).run.run {} with ⟨o, s'⟩
  have h' : o = Except.ok r := by
    have : ((passM env natLit? isUser fuel e).run.run' {}) = o := by
      show (fun p => p.1) <$> (passM env natLit? isUser fuel e).run.run {} = o
      rw [hx]; rfl
    rw [this] at h; exact h
  subst h'
  exact (passM_goodL env natLit? isUser hd hr hrep hi1 hh hbt hEq fuel e r {} s' memoGoodL_empty hx).2 0 ⟨hn, hb⟩

theorem pass_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    Tools.Assume.ExprEqvGL.ExprEqvLaws →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true :=
  fun env hd hr hrep hi1 hh hbt hEq isUser e r hn hb h =>
    passWith_ph natLit? env hd hr hrep hi1 hh hbt hEq _ isUser e r hn hb h

theorem passPh' : PassPh' := fun natLit? => pass_ph natLit?

end Tools.PassPh
