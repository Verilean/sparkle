import Tools.Prototype.LiftScalarModelLetOk
import Tools.ShippingLetsExternSpec
import Tools.PartialTotal.Measure
set_option autoImplicit false
-- NOT BUILT: K1 skeleton (the four theorems carry `sorry`). Skeleton content built OK at 6e3739fd (Tests.Gen3.PartialTotalCheck exit 0).

/-! # Partial-total agreement theorems (scripts/gen3/PARTIAL_TOTAL_FREEZE.md §3)

`machBoolMap`, `machLiftScalarN` (Sparkle/Compiler/Elab.lean) and `rootFloat` (Sparkle/Compiler/MachRawSurface.lean) are now
total definitions (K1 compiler edit: `partial` removed; `rootFloat` is `rootFloatF` with a fuel `rootFloatNu e + 1`).
The models are the ones already in the tree and are imported, not copied:
`Tools.Prototype.BoolMapModelLetOk.boolMapModel`, `Tools.Prototype.LiftScalarModelLetOk.liftN` / `liftStep`,
`Tools.ShippingLetsReaderInv.rootFloatS` / `liftSpec` / `nu`.
The premise definitions `BoolMapCorr`, `LiftScalarCorr`, `RootFloatAgrees` are the existing ones (unchanged); these theorems
prove them. `rootFloatAgrees` depends on the existing `LiftAgrees` (an open C++ extern premise that stays). -/
namespace Tools.PartialTotal.Agree
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.BoolMapModelLetOk
  Tools.Prototype.LiftScalarModelLetOk

/-- T1L-59, as an equation (stronger than `BoolMapCorr`, which is the `→` direction). -/
theorem boolMap_eq (senv : StructEnv) (dom a : Lean.Expr) (wa : Nat) :
    ∀ (body : Lean.Expr), machBoolMap senv dom a wa body
      = boolMapModel (machLiftScalarN senv dom [(wa, a)]) dom body := by
  intro body
  induction body with
  | app f x ihf ihx =>
    unfold machBoolMap boolMapModel
    split <;> simp_all
  | _ => unfold machBoolMap boolMapModel; simp

theorem boolMapCorr (senv : StructEnv) : BoolMapCorr senv := by
  intro dom a wa body r h
  rw [← boolMap_eq]; exact h

theorem lift_step (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) :
    machLiftScalarN senv dom vars e = liftStep (machLiftScalarN senv dom vars) senv dom vars e := by
  rw [machLiftScalarN.eq_def]
  split <;> first | (unfold liftStep; rfl) | (simp only [liftStep]; done) | (simp [liftStep]; done) | skip
  case h_7 =>
    rw [liftStep]
    repeat' split
    all_goals first | rfl | simp_all
  case h_8 =>
    rw [liftStep]
    conv => rhs; rw [machLiftScalarN.eq_def]
    rfl


/-! ### fuel measure: `csz` / `isToNatHead` / `isAshrHead` are defined in `Tools/PartialTotal/Measure.lean` -/
theorem csz_A (f a : Lean.Expr) : csz a < csz (.app f a) := by
  rw [csz]; split <;> split <;> omega

theorem csz_B (g1 g2 a b : Lean.Expr) : csz a < csz (.app (.app (.app g1 g2) a) b) := by
  have h1 : isToNatHead (.app (.app g1 g2) a) = false := by simp [isToNatHead]
  have := csz_A (.app g1 g2) a
  rw [csz, h1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split <;> omega

theorem csz_C (f g y : Lean.Expr) : csz y < csz (.app f (.app g y)) := by
  have := csz_A g y
  have := csz_A f (.app g y)
  omega


theorem csz_ashr (nE x y : Lean.Expr) :
    csz (mkApp3 (.const ``BitVec.sshiftRight []) nE x (mkApp2 (.const ``BitVec.toNat []) nE y))
      < csz (.app (.app (.app (.const ``Sparkle.Core.Signal.ashr []) nE) x) y) := by
  simp [mkApp3, mkApp2, mkApp, csz, isToNatHead, isAshrHead]
  omega

theorem liftStep_cong (self self' : Lean.Expr → Option (Nat × Lean.Expr)) (senv : StructEnv) (dom : Lean.Expr)
    (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) (hc : ∀ z, csz z < csz e → self z = self' z) :
    liftStep self senv dom vars e = liftStep self' senv dom vars e := by
  unfold liftStep
  split
  all_goals first | rfl | (try simp (disch := first | exact csz_A _ _ | exact csz_B _ _ _ _ | exact csz_C _ _ _ | exact csz_ashr _ _ _) [hc])
  case h_8 => exact hc _ (csz_ashr _ _ _)
  case h_7 =>
    rename_i _ us nE x s
    by_cases hs : ∃ u mE y, s = ((Expr.const ``BitVec.toNat u).app mE).app y
    · obtain ⟨u, mE, y, rfl⟩ := hs
      simp (disch := first | exact csz_A _ _ | exact csz_B _ _ _ _ | exact csz_C _ _ _ | exact csz_ashr _ _ _) [hc]
    · have hs' : ∀ u mE y, s ≠ ((Expr.const ``BitVec.toNat u).app mE).app y := fun u mE y h => hs ⟨u, mE, y, h⟩
      repeat' split
      all_goals first | rfl | simp_all
  all_goals (try split) <;> (try simp (disch := first | exact csz_A _ _ | exact csz_B _ _ _ _ | exact csz_C _ _ _ | exact csz_ashr _ _ _) [hc])

/-- T1L-58. -/
theorem lift_fuel (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
    ∀ (k : Nat) (e : Lean.Expr), csz e < k → liftN senv dom vars k e = machLiftScalarN senv dom vars e := by
  intro k
  induction k with
  | zero => intro e h; omega
  | succ k ih =>
    intro e he
    rw [lift_step]
    show liftStep (liftN senv dom vars k) senv dom vars e = _
    exact liftStep_cong _ _ senv dom vars e (fun z hz => ih z (by omega))

theorem liftScalarCorr (senv : StructEnv) : LiftScalarCorr senv := by
  intro dom vars e w r h
  exact ⟨csz e + 1, by rw [lift_fuel senv dom vars (csz e + 1) e (by omega)]; exact h⟩

/-- T1L-52, under the existing open premise `LiftAgrees`. -/
theorem rootFloatAgrees (hl : LiftAgrees) : RootFloatAgrees := by
  have hsz : ∀ e, Sparkle.Compiler.MachRawSurface.rootFloatNsz e = nsz e := by
    intro e
    induction e <;> simp_all [Sparkle.Compiler.MachRawSurface.rootFloatNsz, nsz]
  have hnu : ∀ e, Sparkle.Compiler.MachRawSurface.rootFloatNu e = nu e := by
    intro e
    induction e <;> simp_all [Sparkle.Compiler.MachRawSurface.rootFloatNu, nu, hsz]
  have key : ∀ (k : Nat) (e : Lean.Expr), LetOk 0 e = true → nu e < k →
      Sparkle.Compiler.MachRawSurface.rootFloatF k e = rootFloatS e := by
    intro k
    induction k with
    | zero => intro e _ h; omega
    | succ k ih =>
      intro e he hk
      revert he hk
      cases e with
      | letE n t v b nd =>
        intro he hk
        by_cases hv : ∃ n2 t2 v2 w nd2, v = Lean.Expr.letE n2 t2 v2 w nd2
        · obtain ⟨n2, t2, v2, w, nd2, rfl⟩ := hv
          simp only [LetOk, Bool.and_eq_true, and_assoc] at he
          obtain ⟨ht, ht2, hv2, hw, hb⟩ := he
          have hl' := hl t ht
          have hl2 := hl b hb
          rw [rootFloatS]
          simp only [Sparkle.Compiler.MachRawSurface.rootFloatF]
          rw [hl'.1, hl2.2]
          refine ih _ ?_ ?_
          · simp only [LetOk, Bool.and_eq_true, and_assoc]
            exact ⟨ht2, hv2, liftSpec_ok 0 t _ _ ht, hw, liftSpec_ok 0 b _ _ hb⟩
          · simp [nu, nsz, nu_liftSpec, nsz_liftSpec] at hk ⊢
            omega
        · have h1 : rootFloatS (.letE n t v b nd) = .letE n t v (rootFloatS b) nd := by
            rw [rootFloatS]
            exact fun n2 t2 v2 w nd2 h => hv ⟨n2, t2, v2, w, nd2, h⟩
          have h2 : Sparkle.Compiler.MachRawSurface.rootFloatF (k + 1) (.letE n t v b nd)
              = .letE n t v (Sparkle.Compiler.MachRawSurface.rootFloatF k b) nd := by
            cases v <;> first | rfl | (exfalso; exact hv ⟨_, _, _, _, _, rfl⟩)
          rw [h1, h2]
          simp only [LetOk, Bool.and_eq_true] at he
          have : nu b < k := by simp [nu, nsz] at hk; omega
          rw [ih b he.2 this]
      | app f a =>
        intro he hk
        by_cases hv : ∃ n t v b nd, a = Lean.Expr.letE n t v b nd
        · obtain ⟨n, t, v, b, nd, rfl⟩ := hv
          simp only [LetOk, Bool.and_eq_true, and_assoc] at he
          obtain ⟨hf, ht, hv', hb⟩ := he
          have hl' := hl f hf
          rw [rootFloatS]
          simp only [Sparkle.Compiler.MachRawSurface.rootFloatF]
          rw [hl'.1]
          rw [ih]
          · simp only [LetOk, Bool.and_eq_true]
            exact ⟨liftSpec_ok 0 f _ _ hf, hb⟩
          · simp [nu, nsz, nu_liftSpec, nsz_liftSpec] at hk ⊢
            omega
        · have h1 : rootFloatS (.app f a) = .app f a := by
            rw [rootFloatS]
            all_goals (intros; simp_all)
          have h2 : Sparkle.Compiler.MachRawSurface.rootFloatF (k + 1) (.app f a) = .app f a := by
            cases a <;> simp_all [Sparkle.Compiler.MachRawSurface.rootFloatF]
          rw [h1, h2]
      | _ =>
        intro he hk
        rw [rootFloatS]
        all_goals first | rfl | (intros; simp_all) | skip
        all_goals simp [Sparkle.Compiler.MachRawSurface.rootFloatF]
  intro e he
  unfold Sparkle.Compiler.MachRawSurface.rootFloat
  rw [hnu]
  exact key _ e he (by omega)

end Tools.PartialTotal.Agree
