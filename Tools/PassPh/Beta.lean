import Tools.PassPh.Defs
set_option autoImplicit false
-- SKELETON: sorry あり、探索ブランチのみ（受理の対象ではない）. Built in Pod (kjob lake build Tools.PassPh.Pass, exit 0) on the tree of dec1b348 (Lean content identical; header comment-only). Types follow scripts/gen5/RT_PASS_PH_FREEZE.md rev1 (approved as document/types only).

/-! # pass_ph skeleton: Beta group, rev2 L version (freeze rev2 §2/§4: beta_target, beta_goodL, headBetaM_goodL; proofs from scripts/gen5/RT_PASS_PH_REV2_SCRATCH2.lean.txt). Depends on Defs only. -/

namespace Tools.PassPh
open Lean Tools.ShippingLetsReaderInv Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern Tools.ShippingGen5ReaderTraceAbbrevS1

theorem arr_push_ind {α : Type} {motive : Array α → Prop} (h0 : motive #[])
    (hs : ∀ (as : Array α) (a : α), motive as → motive (as.push a)) : ∀ as, motive as := by
  intro as
  obtain ⟨l⟩ := as
  suffices ∀ (n : Nat) (l : List α), l.length = n → motive ⟨l⟩ from this _ l rfl
  intro n
  induction n with
  | zero => intro l hl; rw [List.length_eq_zero_iff.mp hl]; exact h0
  | succ n ih =>
    intro l hl
    obtain ⟨l', a, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left (by rintro rfl; simp at hl)
    have := hs ⟨l'⟩ a (ih l' (by simpa using hl))
    simpa using this

theorem mkAppN_push (f a : Lean.Expr) (args : Array Lean.Expr) : mkAppN f (args.push a) = .app (mkAppN f args) a := by
  simp [mkAppN]; rfl

theorem getAppFn_mkAppN (f : Lean.Expr) (hf : ¬f.isApp = true) (args : Array Lean.Expr) : (mkAppN f args).getAppFn = f := by
  induction args using arr_push_ind with
  | h0 => cases f <;> simp_all [mkAppN, Lean.Expr.getAppFn, Lean.Expr.isApp]
  | hs as a ih => rw [mkAppN_push]; simpa [Lean.Expr.getAppFn] using ih

theorem revArgsAux_mkAppN (f : Lean.Expr) (hf : ¬f.isApp = true) (args : Array Lean.Expr) :
    ∀ (as : Array Lean.Expr), (priv% Lean.Expr.getAppRevArgsAux) (mkAppN f args) as = as ++ args.reverse := by
  induction args using arr_push_ind with
  | h0 =>
    intro as
    cases f <;> simp_all [mkAppN, Lean.Expr.isApp] <;> (unfold_priv Lean.Expr.getAppRevArgsAux; simp)
  | hs bs a ih =>
    intro as
    rw [mkAppN_push]
    show (priv% Lean.Expr.getAppRevArgsAux) (mkAppN f bs) (as.push a) = _
    rw [ih]
    simp [Array.reverse_push]

theorem beta_target : ∀ (f : Lean.Expr) (args : Array Lean.Expr),
    f.isHeadBetaTargetFn false = true → ¬f.isApp = true → f.beta args = (mkAppN f args).headBeta := by
  intro f args ht hf
  have h1 := getAppFn_mkAppN f hf args
  have h2 : (mkAppN f args).getAppRevArgs = args.reverse := by
    unfold Lean.Expr.getAppRevArgs
    rw [revArgsAux_mkAppN f hf args]
    simp
  unfold Lean.Expr.headBeta Lean.Expr.beta
  rw [h1, h2, if_pos ht]

theorem isHeadBetaTargetFn_not_app : ∀ (f : Lean.Expr), f.isHeadBetaTargetFn false = true → ¬f.isApp = true := by
  intro f
  induction f with
  | mdata _ x ih =>
    intro h
    have := ih (by simpa [Lean.Expr.isHeadBetaTargetFn] using h)
    simpa [Lean.Expr.isApp] using this
  | app _ _ _ _ => intro h; simp [Lean.Expr.isHeadBetaTargetFn] at h
  | _ => intro _; simp [Lean.Expr.isApp]

theorem gl_default (K : Nat) : GL K (default : Lean.Expr) := ⟨rfl, rfl⟩

theorem getBang_goodL {K : Nat} {as : Array Lean.Expr} (hs : ∀ a ∈ as, GL K a) (i : Nat) : GL K as[i]! := by
  by_cases h : i < as.size
  · rw [getElem!_pos as i h]; exact hs _ (Array.getElem_mem h)
  · rw [getElem!_neg as i h]; exact gl_default K

theorem instSpec_bvarLtL (K : Nat) : ∀ (subst : Array Lean.Expr), (∀ a ∈ subst, GL K a) →
    ∀ (b e : Nat) (x : Lean.Expr) (off m : Nat), K ≤ m →
      BvarLt (m + (e - b) + off) x = true → BvarLt (m + off) (instSpec subst b e x off) = true := by
  intro subst hs b e x
  induction x with
  | bvar i =>
    intro off m hK h
    simp only [BvarLt, decide_eq_true_eq] at h
    simp only [instSpec]
    split
    · simp only [BvarLt, decide_eq_true_eq]; omega
    · split
      · exact bvarLt_mono (by omega) (liftSpec_bvarLt _ 0 off K (getBang_goodL hs _).2)
      · simp only [BvarLt, decide_eq_true_eq]; omega
  | app f a ihf iha =>
    intro off m hK h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [instSpec, BvarLt, Bool.and_eq_true]; exact ⟨ihf _ _ hK h.1, iha _ _ hK h.2⟩
  | lam _ t bd _ iht ihb =>
    intro off m hK h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [instSpec, BvarLt, Bool.and_eq_true]
    refine ⟨iht _ _ hK h.1, ?_⟩
    have := ihb (off + 1) m hK (by rw [show m + (e - b) + (off + 1) = m + (e - b) + off + 1 by omega]; exact h.2)
    rwa [show m + (off + 1) = m + off + 1 by omega] at this
  | forallE _ t bd _ iht ihb =>
    intro off m hK h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [instSpec, BvarLt, Bool.and_eq_true]
    refine ⟨iht _ _ hK h.1, ?_⟩
    have := ihb (off + 1) m hK (by rw [show m + (e - b) + (off + 1) = m + (e - b) + off + 1 by omega]; exact h.2)
    rwa [show m + (off + 1) = m + off + 1 by omega] at this
  | letE _ t v bd _ iht ihv ihb =>
    intro off m hK h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [instSpec, BvarLt, Bool.and_eq_true]
    refine ⟨⟨iht _ _ hK h.1.1, ihv _ _ hK h.1.2⟩, ?_⟩
    have := ihb (off + 1) m hK (by rw [show m + (e - b) + (off + 1) = m + (e - b) + off + 1 by omega]; exact h.2)
    rwa [show m + (off + 1) = m + off + 1 by omega] at this
  | mdata _ x ih => intro off m hK h; simp only [BvarLt] at h; simp only [instSpec, BvarLt]; exact ih _ _ hK h
  | proj _ _ x ih => intro off m hK h; simp only [BvarLt] at h; simp only [instSpec, BvarLt]; exact ih _ _ hK h
  | fvar _ => intro off m _ h; rfl
  | mvar _ => intro off m _ _; rfl
  | sort _ => intro off m _ _; rfl
  | const _ _ => intro off m _ _; rfl
  | lit _ => intro off m _ _; rfl

theorem instSpec_noPhL (K : Nat) : ∀ (subst : Array Lean.Expr), (∀ a ∈ subst, GL K a) →
    ∀ (b e : Nat) (x : Lean.Expr) (off : Nat), NoPh x = true → NoPh (instSpec subst b e x off) = true := by
  intro subst hs b e x
  induction x with
  | bvar i =>
    intro off _
    simp only [instSpec]
    split
    · simp [NoPh]
    · split
      · exact liftSpec_noPh _ _ _ (getBang_goodL hs _).1
      · simp [NoPh]
  | app f a ihf iha =>
    intro off h; simp only [NoPh, Bool.and_eq_true] at h
    simp only [instSpec, NoPh, Bool.and_eq_true]; exact ⟨ihf _ h.1, iha _ h.2⟩
  | lam _ t bd _ iht ihb =>
    intro off h; simp only [NoPh, Bool.and_eq_true] at h
    simp only [instSpec, NoPh, Bool.and_eq_true]; exact ⟨iht _ h.1, ihb _ h.2⟩
  | forallE _ t bd _ iht ihb =>
    intro off h; simp only [NoPh, Bool.and_eq_true] at h
    simp only [instSpec, NoPh, Bool.and_eq_true]; exact ⟨iht _ h.1, ihb _ h.2⟩
  | letE _ t v bd _ iht ihv ihb =>
    intro off h; simp only [NoPh, Bool.and_eq_true] at h
    simp only [instSpec, NoPh, Bool.and_eq_true]; exact ⟨⟨iht _ h.1.1, ihv _ h.1.2⟩, ihb _ h.2⟩
  | mdata _ x ih => intro off h; simp only [NoPh] at h; simp only [instSpec, NoPh]; exact ih _ h
  | proj _ _ x ih => intro off h; simp only [NoPh] at h; simp only [instSpec, NoPh]; exact ih _ h
  | fvar _ => intro off h; exact h
  | mvar _ => intro off _; rfl
  | sort _ => intro off _; rfl
  | const _ _ => intro off _; rfl
  | lit _ => intro off _; rfl

theorem getAppFn_goodL (L : Nat) : ∀ (e : Lean.Expr), NoPh e = true → BvarLt L e = true → GL L e.getAppFn := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    exact ihf hn.1 hb.1
  | _ => intro hn hb; exact ⟨hn, hb⟩

theorem revArgsAux_goodL (L : Nat) : ∀ (e : Lean.Expr) (as : Array Lean.Expr), NoPh e = true → BvarLt L e = true →
    (∀ a ∈ as, GL L a) → ∀ a ∈ (priv% Lean.Expr.getAppRevArgsAux) e as, GL L a := by
  intro e
  induction e with
  | app f x ihf _ =>
    intro as hn hb hs
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    show ∀ a ∈ (priv% Lean.Expr.getAppRevArgsAux) f (as.push x), GL L a
    refine ihf (as.push x) hn.1 hb.1 ?_
    intro a ha
    rcases Array.mem_push.mp ha with h | h
    · exact hs a h
    · subst h; exact ⟨hn.2, hb.2⟩
  | _ => intro as _ _ hs; exact hs

theorem getAppRevArgs_goodL (L : Nat) (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt L e = true) :
    ∀ a ∈ e.getAppRevArgs, GL L a :=
  revArgsAux_goodL L e (Array.mkEmpty e.getAppNumArgs) hn hb (by intro a ha; simp at ha)

theorem mkAppRevRangeAux_goodL (L : Nat) (revArgs : Array Lean.Expr) (hs : ∀ a ∈ revArgs, GL L a) (start : Nat) :
    ∀ (i : Nat) (b : Lean.Expr), GL L b → GL L ((priv% Lean.Expr.mkAppRevRangeAux) revArgs start b i) := by
  intro i
  induction i with
  | zero => intro b hb; unfold_priv Lean.Expr.mkAppRevRangeAux; simpa using hb
  | succ i ih =>
    intro b hb
    unfold_priv Lean.Expr.mkAppRevRangeAux
    split
    · exact hb
    · simp only [Nat.add_sub_cancel]
      refine ih _ ?_
      have := getBang_goodL hs i
      simp only [GL, NoPh, BvarLt, Bool.and_eq_true] at hb this ⊢
      exact ⟨⟨hb.1, this.1⟩, ⟨hb.2, this.2⟩⟩

theorem betaDone_goodL (L : Nat) (revArgs : Array Lean.Expr) (hs : ∀ a ∈ revArgs, GL L a) (sz : Nat) (x : Lean.Expr) (i : Nat)
    (hi : i < sz) (hn : NoPh x = true) (hb : BvarLt (L + i) x = true) :
    GL L (Lean.Expr.mkAppRevRange (instSpec revArgs (sz - i) sz x 0) 0 (sz - i) revArgs) := by
  refine mkAppRevRangeAux_goodL L revArgs hs 0 _ _ ⟨instSpec_noPhL L revArgs hs _ _ x 0 hn, ?_⟩
  have := instSpec_bvarLtL L revArgs hs (sz - i) sz x 0 L (Nat.le_refl _) (by rwa [show L + (sz - (sz - i)) + 0 = L + i by omega])
  simpa using this

theorem betaGo_goodL (L : Nat) : ∀ (revArgs : Array Lean.Expr), (∀ a ∈ revArgs, GL L a) →
    ∀ (sz : Nat), sz = revArgs.size →
      ∀ (x : Lean.Expr) (i : Nat), i < sz → NoPh x = true → BvarLt (L + i) x = true → GL L (betaGo revArgs sz x i) := by
  intro revArgs hs sz hsz x
  induction x with
  | lam n t bd bi iht ihb =>
    intro i hi hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    simp only [betaGo]
    split
    · rename_i h; exact ihb (i + 1) h hn.2 (by rw [show L + (i + 1) = L + i + 1 by omega]; exact hb.2)
    · rename_i h
      have h1 : i + 1 = sz := by omega
      refine ⟨instSpec_noPhL L revArgs hs 0 sz bd 0 hn.2, ?_⟩
      have := instSpec_bvarLtL L revArgs hs 0 sz bd 0 L (Nat.le_refl _) (by rw [show L + (sz - 0) + 0 = L + i + 1 by omega]; exact hb.2)
      simpa using this
  | mdata m bd ih =>
    intro i hi hn hb
    simp only [NoPh, BvarLt] at hn hb
    simp only [betaGo]
    exact ih i hi hn hb
  | bvar j => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | fvar _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | mvar _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | sort _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | const _ _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | app _ _ _ _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | forallE _ _ _ _ _ _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | letE _ _ _ _ _ _ _ _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | lit _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb
  | proj _ _ _ _ => intro i hi hn hb; exact betaDone_goodL L revArgs hs sz _ i hi hn hb

theorem headBetaSpec_goodL (L : Nat) : ∀ (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
    NoPh (headBetaSpec e) = true ∧ BvarLt L (headBetaSpec e) = true := by
  intro e hn hb
  have hf := getAppFn_goodL L e hn hb
  have hr := getAppRevArgs_goodL L e hn hb
  unfold headBetaSpec betaRevSpec
  simp only
  split
  · split
    · exact hf
    · rename_i h1 h2
      have hpos : 0 < e.getAppRevArgs.size := by
        rcases Nat.eq_zero_or_pos e.getAppRevArgs.size with h0 | h0
        · exact absurd (by simp [h0]) h2
        · exact h0
      exact betaGo_goodL L _ hr _ rfl _ 0 hpos hf.1 (by simpa using hf.2)
  · exact ⟨hn, hb⟩

theorem headBeta_goodL (L : Nat) : HeadBetaAgreesL → ∀ (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
    NoPh e.headBeta = true ∧ BvarLt L e.headBeta = true := by
  intro h e hn hb
  rw [h L e hn hb]
  exact headBetaSpec_goodL L e hn hb

theorem beta_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (L : Nat) (f : Lean.Expr) (args : Array Lean.Expr), GL L f → (∀ a ∈ args, GL L a) → GL L (f.beta args) := by
  intro L f args hf hs
  by_cases ht : f.isHeadBetaTargetFn false = true
  · have hnapp : ¬ f.isApp = true := by
      cases f <;> simp_all [Lean.Expr.isHeadBetaTargetFn, Lean.Expr.isApp]
    rw [beta_target f args ht hnapp]
    have := mkAppN_goodL L f args hf hs
    exact headBeta_goodL L hh _ this.1 this.2
  · have ht' : f.isHeadBetaTargetFn false = false := by simpa using ht
    rw [hbt f args ht']
    exact mkAppN_goodL L f args hf hs

theorem consumeMData_goodL (L : Nat) : ∀ (e : Lean.Expr), GL L e → GL L e.consumeMData := by
  intro e
  induction e with
  | mdata m b ih =>
    intro h
    simp only [GL, NoPh, BvarLt] at h
    unfold Lean.Expr.consumeMData
    exact ih h
  | _ => intro h; first | exact h | (unfold Lean.Expr.consumeMData; exact h)

theorem getAppArgsAux_goodL (L : Nat) : ∀ (e : Lean.Expr) (as : Array Lean.Expr) (i : Nat), NoPh e = true → BvarLt L e = true →
    (∀ a ∈ as, GL L a) → ∀ a ∈ (priv% Lean.Expr.getAppArgsAux) e as i, GL L a := by
  intro e
  induction e with
  | app f x ihf _ =>
    intro as i hn hb hs
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    show ∀ a ∈ (priv% Lean.Expr.getAppArgsAux) f (as.set! i x) (i - 1), GL L a
    refine ihf (as.set! i x) (i - 1) hn.1 hb.1 ?_
    intro a ha
    have := (Array.mem_or_eq_of_mem_setIfInBounds ha)
    rcases this with h | h
    · exact hs a h
    · subst h; exact ⟨hn.2, hb.2⟩
  | _ => intro as _ _ _ hs; exact hs

theorem getAppArgs_goodL (L : Nat) (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt L e = true) :
    ∀ a ∈ e.getAppArgs, GL L a := by
  unfold Lean.Expr.getAppArgs
  exact getAppArgsAux_goodL L e _ _ hn hb (by intro a ha; simp [Array.mem_replicate] at ha; rw [ha.2]; exact gl_default L)

theorem headBetaM_goodL (hh : HeadBetaAgreesL) (hbt : BetaNonTargetAgrees) :
    ∀ (fuel L : Nat) (e r : Lean.Expr), GL L e → Sparkle.Compiler.MachRecUnfold.headBetaM fuel e = .ok r → GL L r := by
  intro fuel
  induction fuel with
  | zero =>
    intro L e r he h
    unfold Sparkle.Compiler.MachRecUnfold.headBetaM at h
    dsimp only at h
    split at h
    · cases h
    · injection h with h; subst h; exact consumeMData_goodL L e he
  | succ n ih =>
    intro L e r he h
    unfold Sparkle.Compiler.MachRecUnfold.headBetaM at h
    dsimp only at h
    split at h
    · refine ih L _ r ?_ h
      have he' := consumeMData_goodL L e he
      have hf := consumeMData_goodL L _ (getAppFn_goodL L _ he'.1 he'.2)
      exact beta_goodL hh hbt L _ _ hf (getAppArgs_goodL L _ he'.1 he'.2)
    · injection h with h; subst h; exact consumeMData_goodL L e he


end Tools.PassPh
