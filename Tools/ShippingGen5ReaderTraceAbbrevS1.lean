import Tools.Assume.AbbrevExtern
import Tools.Assume.N3Extern
import Tools.ShippingGen5ReaderTraceLift
import Tools.ShippingGen5ReaderTraceDirect
import Tools.ShippingInlCand
set_option autoImplicit false
-- NOT BUILT: written against `scripts/gen5/RT_ABBREV_S1_FREEZE.md` rev2 (types copied from its #check output).

/-! # RT abbrev S1: `inlAbbrevs` preserves `NoPh ∧ BvarLt 0` (freeze `scripts/gen5/RT_ABBREV_S1_FREEZE.md` rev2)

Assumptions (statements only, `Tools/Assume/AbbrevExtern.lean`): `ReplaceAgrees` (U-1, replaces T1L-54) and `HeadBetaAgrees0` (U-2).
Proved here: `zeroLitAgrees0_of_replace` (`ReplaceAgrees → ZeroLitAgrees0`), preservation of `NoPh ∧ BvarLt 0` by the models (`instSpec_*`, `betaGo_good`,
`headBetaSpec_good`), `headBeta_good` (from `HeadBetaAgrees0`), `rnc_ph`, `abbrevFn_ph`, `inlAbbrevs_ph` (from `DeclValuePh`, `ReplaceAgrees`, `HeadBetaAgrees0`).
`DeclValuePh` (N1-a) stays a theorem hypothesis (not registered). Conditional (intermediate) result: no hypothesis is shown to hold for accepted sources.
Private core helpers (`getAppRevArgsAux`, `mkAppRevRangeAux`) are reached through the small `priv%` / `unfold_priv` meta helpers below (their names contain a numeric component). -/

namespace Tools.ShippingGen5ReaderTraceAbbrevS1
open Lean Tools.ShippingGen5ReaderTrace Tools.Assume.AbbrevExtern

/-! ## meta helpers for the private core definitions -/

open Lean.Elab Lean.Elab.Tactic Lean.Meta in
/-- the declaration whose user-facing name is `n` (private names carry a numeric component, so they cannot be written) -/
def findPriv (n : Name) : CoreM Name := do
  let env ← getEnv
  match env.constants.fold (init := (none : Option Name))
      (fun acc c _ => if acc.isSome then acc else if privateToUserName? c == some n then some c else acc) with
  | some c => pure c
  | none => throwError "findPriv: no private declaration {n}"

open Lean.Elab Lean.Elab.Term in
/-- the constant of the private declaration `n` -/
elab "priv% " n:ident : term => do
  let pn ← findPriv n.getId
  Lean.Meta.mkConstWithFreshMVarLevels pn

open Lean.Elab Lean.Elab.Tactic Lean.Meta in
/-- `Meta.unfold` the private declaration `n` in the goal -/
elab "unfold_priv " n:ident : tactic => withMainContext do
  let pn ← findPriv n.getId
  let g ← getMainGoal
  let t ← g.getType
  let r ← Meta.unfold t pn
  if r.expr == t then throwError "unfold_priv: no progress"
  replaceMainGoal [← applySimpResultToTarget g t r]

/-! ## U-1 consequence -/

theorem zeroLitAgrees0_of_replace (h : ReplaceAgrees) : Tools.Assume.N3Extern.ZeroLitAgrees0 := by
  intro e _
  unfold Sparkle.Compiler.MachRawSurface.zeroLit
  exact h _ e

/-! ## preservation facts about the models -/

def Good (a : Lean.Expr) : Prop := NoPh a = true ∧ BvarLt 0 a = true

theorem good_default : Good (default : Lean.Expr) := ⟨rfl, rfl⟩

theorem getBang_good {as : Array Lean.Expr} (hs : ∀ a ∈ as, Good a) (i : Nat) : Good as[i]! := by
  by_cases h : i < as.size
  · rw [getElem!_pos as i h]; exact hs _ (Array.getElem_mem h)
  · rw [getElem!_neg as i h]; exact good_default

theorem instSpec_noPh : ∀ (subst : Array Lean.Expr), (∀ a ∈ subst, Good a) →
    ∀ (b e : Nat) (x : Lean.Expr) (off : Nat), NoPh x = true → NoPh (instSpec subst b e x off) = true := by
  intro subst hs b e x
  induction x with
  | bvar i =>
    intro off _
    simp only [instSpec]
    split
    · simp [NoPh]
    · split
      · exact liftSpec_noPh _ _ _ (getBang_good hs _).1
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

theorem instSpec_bvarLt : ∀ (subst : Array Lean.Expr), (∀ a ∈ subst, Good a) →
    ∀ (b e : Nat) (x : Lean.Expr) (off m : Nat),
      BvarLt (m + (e - b) + off) x = true → BvarLt (m + off) (instSpec subst b e x off) = true := by
  intro subst hs b e x
  induction x with
  | bvar i =>
    intro off m h
    simp only [BvarLt, decide_eq_true_eq] at h
    simp only [instSpec]
    split
    · simp only [BvarLt, decide_eq_true_eq]; omega
    · split
      · exact bvarLt_mono (by omega) (liftSpec_bvarLt _ 0 off 0 (getBang_good hs _).2)
      · simp only [BvarLt, decide_eq_true_eq]; omega
  | app f a ihf iha =>
    intro off m h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [instSpec, BvarLt, Bool.and_eq_true]; exact ⟨ihf _ _ h.1, iha _ _ h.2⟩
  | lam _ t bd _ iht ihb =>
    intro off m h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [instSpec, BvarLt, Bool.and_eq_true]
    refine ⟨iht _ _ h.1, ?_⟩
    have := ihb (off + 1) m (by rw [show m + (e - b) + (off + 1) = m + (e - b) + off + 1 by omega]; exact h.2)
    rwa [show m + (off + 1) = m + off + 1 by omega] at this
  | forallE _ t bd _ iht ihb =>
    intro off m h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [instSpec, BvarLt, Bool.and_eq_true]
    refine ⟨iht _ _ h.1, ?_⟩
    have := ihb (off + 1) m (by rw [show m + (e - b) + (off + 1) = m + (e - b) + off + 1 by omega]; exact h.2)
    rwa [show m + (off + 1) = m + off + 1 by omega] at this
  | letE _ t v bd _ iht ihv ihb =>
    intro off m h; simp only [BvarLt, Bool.and_eq_true] at h
    simp only [instSpec, BvarLt, Bool.and_eq_true]
    refine ⟨⟨iht _ _ h.1.1, ihv _ _ h.1.2⟩, ?_⟩
    have := ihb (off + 1) m (by rw [show m + (e - b) + (off + 1) = m + (e - b) + off + 1 by omega]; exact h.2)
    rwa [show m + (off + 1) = m + off + 1 by omega] at this
  | mdata _ x ih => intro off m h; simp only [BvarLt] at h; simp only [instSpec, BvarLt]; exact ih _ _ h
  | proj _ _ x ih => intro off m h; simp only [BvarLt] at h; simp only [instSpec, BvarLt]; exact ih _ _ h
  | fvar _ => intro off m h; rfl
  | mvar _ => intro off m _; rfl
  | sort _ => intro off m _; rfl
  | const _ _ => intro off m _; rfl
  | lit _ => intro off m _; rfl

theorem getAppFn_good : ∀ (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true → Good e.getAppFn := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    exact ihf hn.1 hb.1
  | _ => intro hn hb; exact ⟨hn, hb⟩

theorem revArgsAux_good : ∀ (e : Lean.Expr) (as : Array Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    (∀ a ∈ as, Good a) → ∀ a ∈ (priv% Lean.Expr.getAppRevArgsAux) e as, Good a := by
  intro e
  induction e with
  | app f x ihf _ =>
    intro as hn hb hs
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    show ∀ a ∈ (priv% Lean.Expr.getAppRevArgsAux) f (as.push x), Good a
    refine ihf (as.push x) hn.1 hb.1 ?_
    intro a ha
    rcases Array.mem_push.mp ha with h | h
    · exact hs a h
    · subst h; exact ⟨hn.2, hb.2⟩
  | _ => intro as _ _ hs; exact hs

theorem getAppRevArgs_good (e : Lean.Expr) (hn : NoPh e = true) (hb : BvarLt 0 e = true) :
    ∀ a ∈ e.getAppRevArgs, Good a :=
  revArgsAux_good e (Array.mkEmpty e.getAppNumArgs) hn hb (by intro a ha; simp at ha)

theorem mkAppRevRangeAux_good (revArgs : Array Lean.Expr) (hs : ∀ a ∈ revArgs, Good a) (start : Nat) :
    ∀ (i : Nat) (b : Lean.Expr), Good b → Good ((priv% Lean.Expr.mkAppRevRangeAux) revArgs start b i) := by
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
      have := getBang_good hs i
      simp only [Good, NoPh, BvarLt, Bool.and_eq_true] at hb this ⊢
      exact ⟨⟨hb.1, this.1⟩, ⟨hb.2, this.2⟩⟩

theorem mkAppRevRange_good (revArgs : Array Lean.Expr) (hs : ∀ a ∈ revArgs, Good a) (f : Lean.Expr) (hf : Good f)
    (bi ei : Nat) : Good (Lean.Expr.mkAppRevRange f bi ei revArgs) :=
  mkAppRevRangeAux_good revArgs hs bi ei f hf

theorem betaDone_good (revArgs : Array Lean.Expr) (hs : ∀ a ∈ revArgs, Good a) (sz : Nat) (x : Lean.Expr) (i : Nat)
    (hi : i < sz) (hn : NoPh x = true) (hb : BvarLt i x = true) :
    Good (Lean.Expr.mkAppRevRange (instSpec revArgs (sz - i) sz x 0) 0 (sz - i) revArgs) := by
  refine mkAppRevRange_good revArgs hs _ ⟨instSpec_noPh revArgs hs _ _ x 0 hn, ?_⟩ _ _
  have := instSpec_bvarLt revArgs hs (sz - i) sz x 0 0 (by rwa [show 0 + (sz - (sz - i)) + 0 = i by omega])
  simpa using this

theorem betaGo_good : ∀ (revArgs : Array Lean.Expr), (∀ a ∈ revArgs, Good a) →
    ∀ (sz : Nat), sz = revArgs.size →
      ∀ (x : Lean.Expr) (i : Nat), i < sz → NoPh x = true → BvarLt i x = true → Good (betaGo revArgs sz x i) := by
  intro revArgs hs sz hsz x
  induction x with
  | lam n t bd bi iht ihb =>
    intro i hi hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    simp only [betaGo]
    split
    · rename_i h; exact ihb (i + 1) h hn.2 hb.2
    · rename_i h
      have h1 : i + 1 = sz := by omega
      refine ⟨instSpec_noPh revArgs hs 0 sz bd 0 hn.2, ?_⟩
      have := instSpec_bvarLt revArgs hs 0 sz bd 0 0 (by rw [show 0 + (sz - 0) + 0 = i + 1 by omega]; exact hb.2)
      simpa using this
  | mdata m bd ih =>
    intro i hi hn hb
    simp only [NoPh, BvarLt] at hn hb
    simp only [betaGo]
    exact ih i hi hn hb
  | bvar j => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | fvar _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | mvar _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | sort _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | const _ _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | app _ _ _ _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | forallE _ _ _ _ _ _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | letE _ _ _ _ _ _ _ _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | lit _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb
  | proj _ _ _ _ => intro i hi hn hb; exact betaDone_good revArgs hs sz _ i hi hn hb

theorem headBetaSpec_good : ∀ (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    NoPh (headBetaSpec e) = true ∧ BvarLt 0 (headBetaSpec e) = true := by
  intro e hn hb
  have hf := getAppFn_good e hn hb
  have hr := getAppRevArgs_good e hn hb
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
      exact betaGo_good _ hr _ rfl _ 0 hpos hf.1 hf.2
  · exact ⟨hn, hb⟩

theorem headBeta_good : HeadBetaAgrees0 → ∀ (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    NoPh e.headBeta = true ∧ BvarLt 0 e.headBeta = true := by
  intro h e hn hb
  rw [h e hn hb]
  exact headBetaSpec_good e hn hb

/-! ## `replaceNoCache` preserves `NoPh ∧ BvarLt` when the replacement results are good -/

section Rnc
open Lean.Expr
variable (f : Lean.Expr → Option Lean.Expr)

theorem rnc_app (a b : Lean.Expr) : replaceNoCache f (.app a b) =
    match f (.app a b) with | some v => v | none => .app (replaceNoCache f a) (replaceNoCache f b) := by rw [Lean.Expr.replaceNoCache.eq_def]; rfl
theorem rnc_lam (n : Name) (t b : Lean.Expr) (bi : BinderInfo) : replaceNoCache f (.lam n t b bi) =
    match f (.lam n t b bi) with | some v => v | none => .lam n (replaceNoCache f t) (replaceNoCache f b) bi := by rw [Lean.Expr.replaceNoCache.eq_def]; rfl
theorem rnc_forallE (n : Name) (t b : Lean.Expr) (bi : BinderInfo) : replaceNoCache f (.forallE n t b bi) =
    match f (.forallE n t b bi) with | some v => v | none => .forallE n (replaceNoCache f t) (replaceNoCache f b) bi := by rw [Lean.Expr.replaceNoCache.eq_def]; rfl
theorem rnc_letE (n : Name) (t v b : Lean.Expr) (nd : Bool) : replaceNoCache f (.letE n t v b nd) =
    match f (.letE n t v b nd) with
    | some w => w | none => .letE n (replaceNoCache f t) (replaceNoCache f v) (replaceNoCache f b) nd := by rw [Lean.Expr.replaceNoCache.eq_def]; rfl
theorem rnc_mdata (m : MData) (b : Lean.Expr) : replaceNoCache f (.mdata m b) =
    match f (.mdata m b) with | some v => v | none => .mdata m (replaceNoCache f b) := by rw [Lean.Expr.replaceNoCache.eq_def]; rfl
theorem rnc_proj (n : Name) (i : Nat) (b : Lean.Expr) : replaceNoCache f (.proj n i b) =
    match f (.proj n i b) with | some v => v | none => .proj n i (replaceNoCache f b) := by rw [Lean.Expr.replaceNoCache.eq_def]; rfl
end Rnc

theorem rnc_ph : ∀ (f : Lean.Expr → Option Lean.Expr),
    (∀ (x v : Lean.Expr), f x = some v → NoPh v = true ∧ BvarLt 0 v = true) →
    ∀ (e : Lean.Expr) (L : Nat), NoPh e = true → BvarLt L e = true →
      NoPh (Lean.Expr.replaceNoCache f e) = true ∧ BvarLt L (Lean.Expr.replaceNoCache f e) = true := by
  intro f hf e
  have hsome : ∀ (e v : Lean.Expr) (L : Nat), f e = some v → NoPh v = true ∧ BvarLt L v = true :=
    fun e v L h => ⟨(hf e v h).1, bvarLt_mono (Nat.zero_le L) (hf e v h).2⟩
  have leaf : ∀ (e : Lean.Expr), Lean.Expr.replaceNoCache f e = (match f e with | some v => v | none => e) →
      ∀ L, NoPh e = true → BvarLt L e = true →
        NoPh (Lean.Expr.replaceNoCache f e) = true ∧ BvarLt L (Lean.Expr.replaceNoCache f e) = true := by
    intro e hr L hn hb
    rw [hr]
    rcases hfx : f e with _ | v
    · exact ⟨hn, hb⟩
    · exact hsome _ v L hfx
  induction e with
  | app a b iha ihb =>
    intro L hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [rnc_app]
    rcases hfx : f (.app a b) with _ | v
    · simp only [NoPh, BvarLt, Bool.and_eq_true]
      have h1 := iha L hn.1 hb.1; have h2 := ihb L hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
    · exact hsome _ v L hfx
  | lam n t b bi iht ihb =>
    intro L hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [rnc_lam]
    rcases hfx : f (.lam n t b bi) with _ | v
    · simp only [NoPh, BvarLt, Bool.and_eq_true]
      have h1 := iht L hn.1 hb.1; have h2 := ihb (L + 1) hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
    · exact hsome _ v L hfx
  | forallE n t b bi iht ihb =>
    intro L hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [rnc_forallE]
    rcases hfx : f (.forallE n t b bi) with _ | v
    · simp only [NoPh, BvarLt, Bool.and_eq_true]
      have h1 := iht L hn.1 hb.1; have h2 := ihb (L + 1) hn.2 hb.2
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩
    · exact hsome _ v L hfx
  | letE n t v b nd iht ihv ihb =>
    intro L hn hb
    simp only [NoPh, BvarLt, Bool.and_eq_true] at hn hb
    rw [rnc_letE]
    rcases hfx : f (.letE n t v b nd) with _ | w
    · simp only [NoPh, BvarLt, Bool.and_eq_true]
      have h1 := iht L hn.1.1 hb.1.1; have h2 := ihv L hn.1.2 hb.1.2; have h3 := ihb (L + 1) hn.2 hb.2
      exact ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, ⟨⟨h1.2, h2.2⟩, h3.2⟩⟩
    · exact hsome _ w L hfx
  | mdata m b ih =>
    intro L hn hb
    simp only [NoPh, BvarLt] at hn hb
    rw [rnc_mdata]
    rcases hfx : f (.mdata m b) with _ | v
    · simp only [NoPh, BvarLt]; exact ih L hn hb
    · exact hsome _ v L hfx
  | proj n i b ih =>
    intro L hn hb
    simp only [NoPh, BvarLt] at hn hb
    rw [rnc_proj]
    rcases hfx : f (.proj n i b) with _ | v
    · simp only [NoPh, BvarLt]; exact ih L hn hb
    · exact hsome _ v L hfx
  | bvar _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | fvar _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | mvar _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | sort _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | const _ _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb
  | lit _ => intro L hn hb; exact leaf _ (by rw [Lean.Expr.replaceNoCache.eq_def]; rfl) L hn hb

/-! ## the abbreviation step and `inlAbbrevs` -/

theorem userAbbrev?_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (c : Lean.Name) (v : Lean.Expr) (h : Sparkle.Compiler.Elab.userAbbrev? env c = some v) :
    NoPh v = true ∧ BvarLt 0 v = true := by
  unfold Sparkle.Compiler.Elab.userAbbrev? at h
  split at h
  · rename_i d hd
    revert h
    split
    · intro h; cases h; exact hv c d hd
    · intro h; cases h
  · cases h

theorem abbrevFn_ph : ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env →
    ∀ (x v : Lean.Expr), Tools.ShippingInlCand.abbrevFn env x = some v → NoPh v = true ∧ BvarLt 0 v = true := by
  intro env hv x v h
  cases x with
  | const c ls =>
    cases ls with
    | nil => exact userAbbrev?_ph env hv c v h
    | cons _ _ => cases h
  | _ => cases h

theorem inlAbbrevs_ph : ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env →
    ReplaceAgrees → HeadBetaAgrees0 →
    ∀ (n : Nat) (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      NoPh (Sparkle.Compiler.Elab.inlAbbrevs env n e) = true ∧ BvarLt 0 (Sparkle.Compiler.Elab.inlAbbrevs env n e) = true := by
  intro env hv hr hb n
  induction n with
  | zero => intro e hn hb0; exact ⟨hn, hb0⟩
  | succ n ih =>
    intro e hn hb0
    simp only [Sparkle.Compiler.Elab.inlAbbrevs]
    rw [hr _ e]
    split
    · exact ⟨hn, hb0⟩
    · have gen : ∀ g : Lean.Expr → Option Lean.Expr, (∀ x v, g x = some v → NoPh v = true ∧ BvarLt 0 v = true) →
          NoPh (Sparkle.Compiler.Elab.inlAbbrevs env n (e.replaceNoCache g).headBeta) = true ∧
          BvarLt 0 (Sparkle.Compiler.Elab.inlAbbrevs env n (e.replaceNoCache g).headBeta) = true := by
        intro g hg
        have hrn := rnc_ph g hg e 0 hn hb0
        have := headBeta_good hb _ hrn.1 hrn.2
        exact ih _ this.1 this.2
      refine gen _ ?_
      intro x v h
      cases x with
      | const c ls =>
        cases ls with
        | nil => exact userAbbrev?_ph env hv c v h
        | cons _ _ => cases h
      | _ => cases h

end Tools.ShippingGen5ReaderTraceAbbrevS1
