import Tools.ShippingGen4ParamEntry
import Tools.ShippingLegacySemEntryIn
set_option autoImplicit false

/-! # F-θ: each retained parameter name is a top-level Nat binder (scripts/gen4/FTHETA_FREEZE.md) -/

namespace Tools.ShippingGen4FTheta
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingLegacySem Tools.ShippingGen4ParamEntry

theorem MRunsIn.throw {α : Type} {e : Exception} {mctx : Meta.Context} {a : α}
    (h : MRunsIn (throw e : MetaM α) mctx a) : False :=
  MReturns.throw h.returns

theorem MRunsIn.throwError {α : Type} (msg : MessageData) {mctx : Meta.Context} {a : α}
    (h : MRunsIn (Lean.throwError msg : MetaM α) mctx a) : False := by
  unfold Lean.throwError at h
  obtain ⟨_, -, h⟩ := MRunsIn.bind h
  obtain ⟨_, -, h⟩ := MRunsIn.bind h
  exact MRunsIn.throw h

/-- The body of the inner `for x in xs` of the `foundNatBinder` loop. -/
def innerF (nm : String) (x : Lean.Expr) (s : Bool) : MetaM (ForInStep Bool) := do
  let decl ← x.fvarId!.getDecl
  if (decl.userName.toString == nm) = true then do
    let binderType ← Meta.whnf decl.type
    if binderType.isConstOf `Nat = true then pure (ForInStep.yield true)
    else pure (ForInStep.yield s)
  else pure (ForInStep.yield s)

/-- What a found binder means. -/
def NatBinderAt (mctx : Meta.Context) (nm : String) (x : Lean.Expr) : Prop :=
  ∃ (decl : LocalDecl) (t : Lean.Expr),
    MRunsIn x.fvarId!.getDecl mctx decl ∧ decl.userName.toString = nm ∧
    MRunsIn (Meta.whnf decl.type) mctx t ∧ t.isConstOf ``Nat = true

theorem inner_list {mctx : Meta.Context} {nm : String} :
    ∀ (l : List Lean.Expr) (b0 b : Bool), MRunsIn (forIn l b0 (innerF nm)) mctx b → b = true →
      b0 = true ∨ ∃ x ∈ l, NatBinderAt mctx nm x := by
  intro l
  induction l with
  | nil =>
    intro b0 b h hb
    rw [List.forIn_nil] at h
    have := MRunsIn.pure h
    left; rw [← this]; exact hb
  | cons x l ih =>
    intro b0 b h hb
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, hk⟩ := MRunsIn.bind h
    unfold innerF at hs
    obtain ⟨decl, hd, hs2⟩ := MRunsIn.bind hs
    by_cases hn : (decl.userName.toString == nm) = true
    · rw [if_pos hn] at hs2
      obtain ⟨bt, hw, hs3⟩ := MRunsIn.bind hs2
      by_cases hnat : bt.isConstOf `Nat = true
      · rw [if_pos hnat] at hs3
        right
        exact ⟨x, List.mem_cons_self, decl, bt, hd, by simpa using hn, hw, hnat⟩
      · rw [if_neg hnat] at hs3
        have e := MRunsIn.pure hs3
        subst e
        simp only at hk
        rcases ih _ _ hk hb with h1 | ⟨y, hy, hy2⟩
        · left; exact h1
        · right; exact ⟨y, List.mem_cons_of_mem _ hy, hy2⟩
    · rw [if_neg hn] at hs2
      have e := MRunsIn.pure hs2
      subst e
      simp only at hk
      rcases ih _ _ hk hb with h1 | ⟨y, hy, hy2⟩
      · left; exact h1
      · right; exact ⟨y, List.mem_cons_of_mem _ hy, hy2⟩

/-- The body of the outer `for (parameterName, _) in parameters` loop. -/
def outerF (xs : Array Lean.Expr) (declName : Name) (x : String × Nat) (_ : PUnit) :
    MetaM (ForInStep PUnit) := do
  let __s ← forIn xs false (innerF x.fst)
  if (!__s) = true then do
    Lean.throwError
      ((MessageData.ofFormat ∘ format)
        (toString "Requested retained hardware parameter '" ++ toString x.fst ++
            toString "' is not a top-level Nat binder of " ++ toString declName))
    pure (ForInStep.yield PUnit.unit)
  else pure (ForInStep.yield PUnit.unit)

theorem outer_list {mctx : Meta.Context} {xs : Array Lean.Expr} {declName : Name} :
    ∀ (l : List (String × Nat)) (r : PUnit), MRunsIn (forIn l PUnit.unit (outerF xs declName)) mctx r →
      ∀ p ∈ l, ∃ x ∈ xs, NatBinderAt mctx p.1 x := by
  intro l
  induction l with
  | nil => intro r _ p hp; cases hp
  | cons y l ih =>
    intro r h p hp
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, hk⟩ := MRunsIn.bind h
    unfold outerF at hs
    obtain ⟨f, hf, hs2⟩ := MRunsIn.bind hs
    by_cases hc : (!f) = true
    · rw [if_pos hc] at hs2
      obtain ⟨_, h3, -⟩ := MRunsIn.bind hs2
      exact (MRunsIn.throwError _ h3).elim
    · rw [if_neg hc] at hs2
      have e := MRunsIn.pure hs2
      subst e
      simp only at hk
      rcases List.mem_cons.mp hp with rfl | hp
      · have hf' : f = true := by simpa using hc
        rw [← Array.forIn_toList] at hf
        rcases inner_list _ _ _ hf hf' with h1 | ⟨x, hx, hx2⟩
        · cases h1
        · exact ⟨x, by simpa using hx, hx2⟩
      · exact ih _ hk p hp

theorem fTheta_natBinder
    {translate : TranslateFn} {logProf : String → IO Unit}
    {declName : Name} {parameters : List (String × Nat)} {cfe : Bool}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {M : Sparkle.IR.AST.Module} {D : Design}
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (fun _ _ _ => True))
    (hr : MReturns (synthesizeFromConst translate logProf declName parameters true cfe
      (.defnInfo dv) isInst) (M, D)) :
    ∃ (body0 : Lean.Expr) (mctx : Meta.Context) (xs : Array Lean.Expr),
      MReturns (openRecordInputs dv.value) body0 ∧
      ∀ p ∈ parameters, ∃ x ∈ xs, NatBinderAt mctx p.1 x := by
  unfold synthesizeFromConst at hr
  simp only [certifiedShape_off true parameters (.defnInfo dv) (by simp),
    mixedCertifiedShape_off true parameters (.defnInfo dv) isInst (by simp), ite_self,
    Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hr
  obtain ⟨y, hy, a3⟩ := MReturns.bind hr
  obtain rfl := MReturns.pure hy
  dsimp only at a3
  obtain ⟨y2, hy2, h2⟩ := MReturns.bind a3
  obtain rfl := MReturns.pure hy2
  dsimp only at h2
  obtain ⟨_, _, h5⟩ := MReturns.bind h2
  obtain ⟨_, _, h6⟩ := MReturns.bind h5
  obtain ⟨_, _, h7⟩ := MReturns.bind h6
  obtain ⟨_, _, h8⟩ := MReturns.bind h7
  obtain ⟨body0, hopen, h9⟩ := MReturns.bind h8
  obtain ⟨_, _, h10⟩ := MReturns.bind h9
  obtain ⟨_, _, h11⟩ := MReturns.bind h10
  obtain ⟨mctx, xs, inner, -, h12⟩ := htele body0 hopen _ _ _ h11
  obtain ⟨_, _, h13⟩ := MRunsIn.bind h12
  obtain ⟨r, hl, -⟩ := MRunsIn.bind h13
  exact ⟨body0, mctx, xs, hopen, outer_list _ _ hl⟩

end Tools.ShippingGen4FTheta
