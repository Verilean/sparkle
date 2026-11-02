import Tools.PassPh.Beta
import Tools.PassPh.Rec
import Tools.PassPh.Iota
import Tools.PassPh.BetaAll
import Tools.PassPh.ListLit
set_option autoImplicit false
-- rev2 L version (scripts/gen5/RT_PASS_PH_FREEZE.md rev2). Built in Pod (kjob lake build Tools.PassPh.Pass, exit 0) on the tree of aa24f5ed161ebaf66322fc58f0d153e215e4d94f (Lean content identical; header comment-only). sorry 7 (evalNode?, unfoldCall?, passM/passStep/passSpine, passWith_ph, pass_ph). Clean build is the coder's. Exploration branch, not an acceptance target.

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

/-- joint induction on `passM` / `passStep` / `passSpine` (measure as in the definitions); the three statements are proved together -/
theorem passM_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), MemoGoodL s →
      (passM env natLit? isUser fuel e).run.run s = (Except.ok r, s') → MemoGoodL s' ∧ ∀ L, GL L e → GL L r := by
  sorry

theorem passStep_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e r : Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr), MemoGoodL s →
      (passStep env natLit? isUser fuel e).run.run s = (Except.ok r, s') → MemoGoodL s' ∧ ∀ L, GL L e → GL L r := by
  sorry

theorem passSpine_goodL (env : Lean.Environment) (natLit? : Lean.Expr → Option Nat) (isUser : Lean.Name → Bool)
    (hd : Tools.Assume.EnvDeclValue.DeclValuePh env) (hr : RecRulePhU env)
    (hrep : ReplaceAgrees) (hi1 : Inst1Agrees) (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel : Nat) (e h : Lean.Expr) (args : Array Lean.Expr) (s s' : Std.HashMap Lean.Expr Lean.Expr),
      MemoGoodL s → (passSpine env natLit? isUser fuel e).run.run s = (Except.ok (h, args), s') →
      MemoGoodL s' ∧ ∀ L, GL L e → GL L h ∧ ∀ a ∈ args, GL L a := by
  sorry

theorem passWith_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    ∀ (fuel : Nat) (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.passWith fuel env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true := by
  sorry

theorem pass_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgreesL → BetaNonTargetAgrees →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true := by
  sorry

theorem passPh' : PassPh' := fun natLit? => pass_ph natLit?

end Tools.PassPh
