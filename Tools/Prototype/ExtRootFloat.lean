import Tools.Prototype.ExtModelLetOk
import Tools.ShippingLetsExternSpec

/-! # Unit EXT2 (0/N): fuel adequacy of the `rootFloat` fuel model against the TOTAL model `rootFloatS`

STATUS: see REPORT-EXT2.md for the build log. No sorry / axiom / native_decide.

`rootFloatS` (LC6, `Tools/ShippingLetsExternSpec.lean`) is a TOTAL model of `rootFloat` (`partial def`) whose termination is PROVED (measure
`nu`). EXT's `rootFloatN` is the fuel model. PROVED here, no premise: `liftM = liftSpec` and `rootFloatN k e = some (rootFloatS e)` as soon as
`nu e < k` (the fuel `nu e + 1` suffices). The link `rootFloat = rootFloatS` of the SHIPPED `partial def` stays the PREMISE `RootFloatAgrees`
(LC6); with this file EXT's `RootFloatCorr` follows from it. The reader copies use `rootFloatS` directly (total, no fuel fallback). -/

namespace Tools.Prototype.ExtRootFloat
open Lean Tools.ShippingLetsReaderInv
open Tools.Prototype.ExtModelLetOk (rootFloatN letOk_liftM)

theorem liftM_eq_liftSpec : ∀ (e : Lean.Expr) (s d : Nat), ExtModelLetOk.liftM e s d = liftSpec e s d := by
  intro e
  induction e with
  | bvar i =>
    intro s d
    unfold ExtModelLetOk.liftM liftSpec
    by_cases h : s ≤ i
    · have h' : ¬ i < s := Nat.not_lt.mpr h
      simp [h, h']
    · have h' : i < s := Nat.lt_of_not_le h
      simp [h, h']
  | app f a ihf iha => intro s d; simp [ExtModelLetOk.liftM, liftSpec, ihf, iha]
  | lam n t b bi iht ihb => intro s d; simp [ExtModelLetOk.liftM, liftSpec, iht, ihb]
  | forallE n t b bi iht ihb => intro s d; simp [ExtModelLetOk.liftM, liftSpec, iht, ihb]
  | letE n t v b nd iht ihv ihb => intro s d; simp [ExtModelLetOk.liftM, liftSpec, iht, ihv, ihb]
  | mdata m e ih => intro s d; simp [ExtModelLetOk.liftM, liftSpec, ih]
  | proj sn i e ih => intro s d; simp [ExtModelLetOk.liftM, liftSpec, ih]
  | fvar _ => intro s d; rfl
  | mvar _ => intro s d; rfl
  | sort _ => intro s d; rfl
  | const _ _ => intro s d; rfl
  | lit _ => intro s d; rfl

/-- **Fuel adequacy**: `rootFloatN` at any fuel above the measure `nu e` is the total model. -/
theorem rootFloatN_eq_rootFloatS : ∀ (e : Lean.Expr) (k : Nat), nu e < k → rootFloatN k e = some (rootFloatS e) := by
  intro e
  induction e using rootFloatS.induct with
  | case1 nm t n2 t2 v2 w nd2 b nd ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k' =>
      rw [rootFloatS]
      simp only [rootFloatN, ExtRootFloat.liftM_eq_liftSpec]
      refine ih k' ?_
      simp [nu, nsz, nu_liftSpec, nsz_liftSpec] at hk ⊢
      omega
  | case2 nm t v b nd hv ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k' =>
      rw [rootFloatS]
      · cases v with
        | letE n2 t2 v2 w nd2 => exact (hv n2 t2 v2 w nd2 rfl).elim
        | _ =>
          simp only [rootFloatN]
          rw [ih k' (by simp [nu] at hk; omega)]
          rfl
      · exact hv
  | case3 f nm t v b nd ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k' =>
      rw [rootFloatS]
      simp only [rootFloatN]
      rw [ExtRootFloat.liftM_eq_liftSpec, ih k' (by simp [nu, nsz_liftSpec] at hk ⊢; omega)]
      rfl
  | case4 e h1 h2 h3 =>
    intro k hk
    cases k with
    | zero => omega
    | succ k' =>
      rw [rootFloatS]
      · cases e with
        | letE nm t v b nd =>
          cases v with
          | letE n2 t2 v2 w nd2 => exact (h1 nm t n2 t2 v2 w nd2 b nd rfl).elim
          | _ => exact (h2 nm t _ b nd rfl).elim
        | app f a =>
          cases a with
          | letE nm t v b nd => exact (h3 f nm t v b nd rfl).elim
          | _ => simp [rootFloatN]
        | _ => simp [rootFloatN]
      · exact h1
      · exact h2
      · exact h3

#print axioms liftM_eq_liftSpec
#print axioms rootFloatN_eq_rootFloatS

end Tools.Prototype.ExtRootFloat
