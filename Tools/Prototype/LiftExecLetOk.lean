import Tools.Prototype.LiftScalarModelLetOk

/-! # Unit LC19 (1/2): `execLift`, a kernel-visible EXECUTABLE model of `machLiftScalarN`, adequate for LC17's fuel model

BUILT (unit LC19): l1-l5 exit 0/1 while developing (my tactic errors), l19 exit 0 (`liftStep_cont`), l20 exit 0 (this file, final).
No sorry / axiom / native_decide. `#print axioms` of every theorem below: [propext, Classical.choice, Quot.sound] (the standard three).

`execLift senv dom vars` is the `partial_fixpoint` of LC17's `liftStep` (one unfolding of the text of `machLiftScalarN`), exactly as
LC11b made `execNorm`. Monotonicity (`liftStep_monotone`, needed for `partial_fixpoint`) is proved with the `monotonicity` tactic
plus `monotone_const` / `hfg _` closers; no premise.
PROVED: `execLift_unfold` (equation), `liftStep_mono`, `liftN_le` (fuel monotone), `fuel_to_exec` (`liftN n e = some r` implies
`execLift e = some r`), `liftStep_cont` (a step over an oracle whose successes each have a fuel is realised at ONE fuel: arm by arm),
`execLift_to_fuel` (fixpoint induction with `Option.admissible_eq_some`), **`execLift_iff` (adequacy)**:
`execLift … = some r ↔ ∃ n, liftN … n e = some r`, **`execLift_ok`** (`LetOk 0` preserved, from LC17's `liftN_ok` through the adequacy),
`liftRangeP_execLift` (the `LiftScalarRange` shape, for the model, NO premise).
NOT PROVED / OPEN: the PRODUCTION correspondence (the shipped `partial def machLiftScalarN` is `execLift`). `execLift` is the
text of `machLiftScalarN` and agrees with it on a finite executed grid (Tests/Compiler/LiftExecAgreeTest.lean, evidence only);
no equation between the shipped partial function and the model exists in the kernel. -/

namespace Tools.Prototype.LiftExecLetOk
open Lean Lean.Order Sparkle.Compiler.Elab Tools.Prototype.LiftScalarModelLetOk
open Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeRangeLetOk Tools.Prototype.BoolMapModelLetOk

theorem liftStep_monotone (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
    monotone (fun (f : Lean.Expr → Option (Nat × Lean.Expr)) e => liftStep f senv dom vars e) := by
  unfold liftStep
  monotonicity
  split
  all_goals iterate 12
    (all_goals first | exact monotone_const _ | (intro f g hfg; exact hfg _) | monotonicity | skip)

def execLift (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) :
    Option (Nat × Lean.Expr) :=
  liftStep (execLift senv dom vars) senv dom vars e
partial_fixpoint monotonicity by exact liftStep_monotone senv dom vars

theorem execLift_unfold (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) :
    execLift senv dom vars e = liftStep (execLift senv dom vars) senv dom vars e :=
  execLift.eq_1 senv dom vars e

theorem liftStep_mono {s s' : Lean.Expr → Option (Nat × Lean.Expr)} (senv : StructEnv) (dom : Lean.Expr)
    (vars : List (Nat × Lean.Expr)) (hm : ∀ x r, s x = some r → s' x = some r) (e : Lean.Expr)
    (r : Nat × Lean.Expr) (h : liftStep s senv dom vars e = some r) : liftStep s' senv dom vars e = some r := by
  have hrel : PartialOrder.rel s s' := by
    intro x
    cases hx : s x with
    | none => exact FlatOrder.rel.bot
    | some v => rw [hm x v hx]; try exact FlatOrder.rel.refl
  have h2 : FlatOrder.rel (b := (none : Option (Nat × Lean.Expr))) (liftStep s senv dom vars e)
      (liftStep s' senv dom vars e) := liftStep_monotone senv dom vars s s' hrel e
  rw [h] at h2
  generalize liftStep s' senv dom vars e = Y at h2 ⊢
  cases h2 with
  | refl => rfl

theorem liftN_le (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
    ∀ (a b : Nat) (x : Lean.Expr) (r : Nat × Lean.Expr), liftN senv dom vars a x = some r →
      liftN senv dom vars (a + b) x = some r := by
  intro a
  induction a with
  | zero => intro b x r h; simp [liftN] at h
  | succ a ih =>
    intro b x r h
    have : a + 1 + b = (a + b) + 1 := by omega
    rw [this]
    exact liftStep_mono senv dom vars (fun y p hy => ih b y p hy) x r h

theorem liftN_mono (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) {a K : Nat}
    (hle : a ≤ K) {x : Lean.Expr} {r : Nat × Lean.Expr} (h : liftN senv dom vars a x = some r) :
    liftN senv dom vars K x = some r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact liftN_le senv dom vars a d x r h

theorem fuel_to_exec (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
    ∀ (n : Nat) (e : Lean.Expr) (r : Nat × Lean.Expr), liftN senv dom vars n e = some r →
      execLift senv dom vars e = some r := by
  intro n
  induction n with
  | zero => intro e r h; simp [liftN] at h
  | succ n ih =>
    intro e r h
    rw [execLift_unfold]
    exact liftStep_mono senv dom vars (fun y p hy => ih y p hy) e r h

theorem liftStep_cont (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr))
    {f : Lean.Expr → Option (Nat × Lean.Expr)}
    (hP : ∀ x r, f x = some r → ∃ n, liftN senv dom vars n x = some r) :
    ∀ (e : Lean.Expr) (r : Nat × Lean.Expr), liftStep f senv dom vars e = some r →
      ∃ k, liftStep (liftN senv dom vars k) senv dom vars e = some r := by
  intro e r h
  unfold liftStep at h
  split at h
  · exact ⟨0, by simpa [liftStep] using h⟩
  · rename_i e0 m us t1 t2 t3 inst x y
    dsimp only at h
    by_cases hm : (m == ``HAppend.hAppend) = true
    · simp only [hm, if_true, bind, Option.bind_eq_some_iff] at h
      obtain ⟨mw, hmw, nw, hnw, h⟩ := h
      by_cases hi : inst.getAppFn.isConstOf ``BitVec.instHAppendHAddNat = true
      · simp only [hi, if_true, bind, Option.bind_eq_some_iff] at h
        obtain ⟨p, hx', q, hy', h⟩ := h
        by_cases hc : (p.fst != mw || q.fst != nw) = true
        · simp [hc] at h
        · obtain ⟨kx, hkx⟩ := hP _ _ hx'
          obtain ⟨ky, hky⟩ := hP _ _ hy'
          simp only [Bool.not_eq_true] at hc
          simp [hc] at h
          subst h
          refine ⟨kx + ky, ?_⟩
          have hLx := liftN_mono senv dom vars (by omega : kx ≤ kx + ky) hkx
          have hLy := liftN_mono senv dom vars (by omega : ky ≤ kx + ky) hky
          have hc2 : p.fst = mw ∧ q.fst = nw := by simpa using hc
          simp [liftStep, hm, hmw, hnw, hi, hLx, hLy, hc2.1, hc2.2]
      · simp [hi] at h
    · have hm' : ¬(m == ``HAppend.hAppend) = true := hm
      rw [if_neg hm'] at h
      rcases hsi : machSigInst m with _ | si
      · simp only [hsi] at h
        exact ⟨0, by simp [liftStep, hm', hsi, h]⟩
      · rcases hb : liftBitsW senv t1 with _ | w0
        · simp only [hsi, hb] at h
          exact ⟨0, by simp [liftStep, hm', hsi, hb, h]⟩
        · simp only [hsi, hb] at h
          by_cases hc : (liftBitsW senv t2 == some w0 && liftBitsW senv t3 == some w0 && machScalarInst m w0 inst) = true
          · rw [if_pos hc] at h
            simp only [bind, Option.bind_eq_some_iff] at h
            obtain ⟨p, hx', q, hy', h⟩ := h
            by_cases hc3 : (p.fst != w0 || q.fst != w0) = true
            · simp [hc3] at h
            · obtain ⟨kx, hkx⟩ := hP _ _ hx'
              obtain ⟨ky, hky⟩ := hP _ _ hy'
              simp only [Bool.not_eq_true] at hc3
              simp [hc3] at h
              subst h
              refine ⟨kx + ky, ?_⟩
              have hLx := liftN_mono senv dom vars (by omega : kx ≤ kx + ky) hkx
              have hLy := liftN_mono senv dom vars (by omega : ky ≤ kx + ky) hky
              have hc2 : p.fst = w0 ∧ q.fst = w0 := by simpa using hc3
              simp [liftStep, hm', hsi, hb, hc, hLx, hLy, hc2.1, hc2.2]
          · rw [if_neg hc] at h
            exact ⟨0, by simp [liftStep, hm', hsi, hb, hc, h]⟩
  · rename_i e0 us nE mE x y
    by_cases hl : (!x.hasLooseBVars && !y.hasLooseBVars) = true
    · rw [if_pos hl] at h
      exact ⟨0, by simp [liftStep, hl, h]⟩
    · rw [if_neg hl] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, hn, m, hm, p, hx', q, hy', h⟩ := h
      obtain ⟨kx, hkx⟩ := hP _ _ hx'
      obtain ⟨ky, hky⟩ := hP _ _ hy'
      have hLx := liftN_mono senv dom vars (by omega : kx ≤ kx + ky) hkx
      have hLy := liftN_mono senv dom vars (by omega : ky ≤ kx + ky) hky
      refine ⟨kx + ky, ?_⟩
      by_cases hc : (p.fst != n || q.fst != m) = true
      · simp [hc] at h
      · have hc2 : p.fst = n ∧ q.fst = m := by simpa using hc
        simpa [liftStep, hl, hn, hm, hLx, hLy, hc2.1, hc2.2] using h
  · rename_i e0 ls nE sE lE x
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨n, hn, st, hst, l, hl, h⟩ := h
    by_cases hx0 : (!x.hasLooseBVars) = true
    · rw [if_pos hx0] at h
      exact ⟨0, by simp [liftStep, hn, hst, hl, hx0, h]⟩
    · rw [if_neg hx0] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, hx', h⟩ := h
      obtain ⟨kx, hkx⟩ := hP _ _ hx'
      by_cases hw : (p.fst != n) = true
      · simp [hw] at h
      · have hw2 : p.fst = n := by simpa using hw
        refine ⟨kx, ?_⟩
        simpa [liftStep, hn, hst, hl, hx0, hkx, hw2] using h
  · rename_i e0 us nE x
    by_cases hx0 : (!x.hasLooseBVars) = true
    · rw [if_pos hx0] at h
      exact ⟨0, by simp [liftStep, hx0, h]⟩
    · rw [if_neg hx0] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, hn, p, hx', h⟩ := h
      obtain ⟨kx, hkx⟩ := hP _ _ hx'
      by_cases hw : (p.fst != n) = true
      · simp [hw] at h
      · have hw2 : p.fst = n := by simpa using hw
        refine ⟨kx, ?_⟩
        simpa [liftStep, hx0, hn, hkx, hw2] using h
  · rename_i e0 us wE vE x
    by_cases hx0 : (!x.hasLooseBVars) = true
    · rw [if_pos hx0] at h
      exact ⟨0, by simp [liftStep, hx0, h]⟩
    · rw [if_neg hx0] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨w, hw, v, hv, p, hx', h⟩ := h
      obtain ⟨kx, hkx⟩ := hP _ _ hx'
      refine ⟨kx, ?_⟩
      simpa [liftStep, hx0, hw, hv, hkx] using h
  · rename_i e0 us nE x s
    by_cases hx0 : (!x.hasLooseBVars) = true
    · rw [if_pos hx0] at h
      exact ⟨0, by simp [liftStep, hx0, h]⟩
    · rw [if_neg hx0] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, hn, h⟩ := h
      by_cases hn0 : (n == 0) = true
      · simp [hn0] at h
      · rw [if_neg hn0] at h
        simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨p, hx', h⟩ := h
        obtain ⟨kx, hkx⟩ := hP _ _ hx'
        by_cases hw : (p.fst != n) = true
        · simp [hw] at h
        · have hw2 : p.fst = n := by simpa using hw
          have hn0' : ¬n = 0 := by simpa using hn0
          rw [if_neg hw] at h
          split at h
          · rename_i mE y
            by_cases hm : (canonicalNatLitValue? mE != some n) = true
            · rw [if_pos hm] at h
              simp at h
            · rw [if_neg hm] at h
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨q, hy', h⟩ := h
              obtain ⟨ky, hky⟩ := hP _ _ hy'
              by_cases hw3 : (q.fst != n) = true
              · rw [if_pos hw3] at h
                simp at h
              · rw [if_neg hw3] at h
                simp at h
                subst h
                have hm2 : canonicalNatLitValue? mE = some n := by simpa using hm
                have hw4 : q.fst = n := by simpa using hw3
                refine ⟨kx + ky, ?_⟩
                have hLx := liftN_mono senv dom vars (by omega : kx ≤ kx + ky) hkx
                have hLy := liftN_mono senv dom vars (by omega : ky ≤ kx + ky) hky
                simp [liftStep, hx0, hn, hn0', hLx, hLy, hw2, hm2, hw4]
          · rename_i hne
            by_cases hs0 : s.hasLooseBVars = true
            · rw [if_pos hs0] at h
              simp at h
            · rw [if_neg hs0] at h
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨k, hk, h⟩ := h
              by_cases hk2 : k ≥ 2 ^ n
              · rw [if_pos hk2] at h
                simp at h
              · rw [if_neg hk2] at h
                simp at h
                subst h
                refine ⟨kx, ?_⟩
                simp [liftStep, hx0, hn, hn0', hkx, hw2]
                have hs0' : s.hasLooseBVars = false := by simpa using hs0
                have hk' : (canonicalNatLitValue? s).or (senv.natOf s) = some k := by simpa using hk
                have hk3 : ¬2 ^ n ≤ k := by simpa using hk2
                simp [hs0', hk', hk3]
  · rename_i e0 nE x y
    obtain ⟨k, hk⟩ := hP _ _ h
    exact ⟨k, by simpa [liftStep] using hk⟩
  · rename_i e0 us us' nE a x
    by_cases hx0 : (!x.hasLooseBVars) = true
    · rw [if_pos hx0] at h
      exact ⟨0, by simp [liftStep, hx0, h]⟩
    · rw [if_neg hx0] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, hn, p, hx', h⟩ := h
      obtain ⟨kx, hkx⟩ := hP _ _ hx'
      by_cases hw : (p.fst != n) = true
      · simp [hw] at h
      · have hw2 : p.fst = n := by simpa using hw
        refine ⟨kx, ?_⟩
        simpa [liftStep, hx0, hn, hkx, hw2] using h
  · rename_i e0 us us' nE a x
    by_cases hx0 : (!x.hasLooseBVars) = true
    · rw [if_pos hx0] at h
      exact ⟨0, by simp [liftStep, hx0, h]⟩
    · rw [if_neg hx0] at h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, hn, p, hx', h⟩ := h
      obtain ⟨kx, hkx⟩ := hP _ _ hx'
      by_cases hw : (p.fst != n) = true
      · simp [hw] at h
      · have hw2 : p.fst = n := by simpa using hw
        refine ⟨kx, ?_⟩
        simpa [liftStep, hx0, hn, hkx, hw2] using h
  · refine ⟨0, ?_⟩
    rw [liftStep.eq_11]
    · exact h
    all_goals assumption

/-- Fixpoint induction: every success of the executable `execLift` is reached by the fuel model at some fuel. -/
theorem execLift_to_fuel (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
    ∀ (e : Lean.Expr) (r : Nat × Lean.Expr), execLift senv dom vars e = some r →
      ∃ n, liftN senv dom vars n e = some r := by
  refine execLift.fixpoint_induct senv dom vars
    (fun f => ∀ e r, f e = some r → ∃ n, liftN senv dom vars n e = some r) ?_ ?_
  · apply admissible_pi_apply
      (fun e v => ∀ r, v = some r → ∃ n, liftN senv dom vars n e = some r)
    intro e
    exact admissible_pi _ (fun r => Option.admissible_eq_some _ r)
  · intro f hf e r h
    obtain ⟨k, hk⟩ := liftStep_cont senv dom vars hf e r h
    exact ⟨k + 1, hk⟩

/-- **PROVED (adequacy)**: `execLift` succeeds with `r` exactly when the finite fuel model does at some fuel. -/
theorem execLift_iff (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr))
    (e : Lean.Expr) (r : Nat × Lean.Expr) :
    execLift senv dom vars e = some r ↔ ∃ n, liftN senv dom vars n e = some r :=
  ⟨execLift_to_fuel senv dom vars e r, fun ⟨n, hn⟩ => fuel_to_exec senv dom vars n e r hn⟩

/-- **PROVED**: `LetOk 0` is preserved by `execLift` (from LC17's `liftN_ok` through the adequacy). -/
theorem execLift_ok {senv : StructEnv} {dom : Lean.Expr} {vars : List (Nat × Lean.Expr)}
    (hd : LetOk 0 dom = true) (hv : ∀ p ∈ vars, LetOk 0 p.2 = true) {e : Lean.Expr} {w : Nat} {r : Lean.Expr}
    (he : LetOk 0 e = true) (h : execLift senv dom vars e = some (w, r)) : LetOk 0 r = true := by
  obtain ⟨n, hn⟩ := execLift_to_fuel senv dom vars e (w, r) h
  exact liftN_ok hd hv n e w r he hn

/-- The `LiftScalarRange` shape, for an arbitrary lifting function. -/
def LiftRangeP (lift : Lean.Expr → List (Nat × Lean.Expr) → Lean.Expr → Option (Nat × Lean.Expr)) : Prop :=
  ∀ (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) (w : Nat) (r : Lean.Expr),
    LetOk 0 dom = true → (∀ p ∈ vars, LetOk 0 p.2 = true) → LetOk 0 e = true →
    lift dom vars e = some (w, r) → LetOk 0 r = true

/-- **PROVED, no premise**: the executable lift satisfies the `LiftScalarRange` shape. -/
theorem liftRangeP_execLift (senv : StructEnv) : LiftRangeP (execLift senv) :=
  fun _ _ _ _ _ hd hv he h => execLift_ok hd hv he h

#print axioms execLift_iff
#print axioms execLift_ok
#print axioms liftRangeP_execLift

end Tools.Prototype.LiftExecLetOk
