import Tools.ShippingLetsReaderInvMain
import Tools.ShippingSparseCasesTac

/-! # Unit LC4a: `BundleIotaRange` PROVED (one of LC3's five premises)

`Sparkle.Compiler.MachRawSurface.bundleIota` is a TOTAL, non-`partial`, non-`extern` function of one `Expr`; its
result is the input, a component of the input (an element of `getAppArgs`), or `mkApp5` of the constant
`Signal.bundle2` applied to five such components — so it invents no `_machLet j` placeholder. No environment
condition is involved. PROVED (no `sorry`, no axiom, no `native_decide`):
`bundleIota_key1` / `_key2` / `_key3` (the three inner `match`es), `bundleIotaRange : BundleIotaRange`, and the
LC3 final theorems with the premise discharged (`machConvF_post'` … `real_conv_post'`), each still taking the
FOUR premises `RootFloatRange`, `LiftRange`, `Inst1Range`, `SigTyRange senv` (not proved here).
STILL OPEN (unchanged): `TwinCoverAt` (twin → real), loose `bvar` in a `let` value, deep range of saved table
values, typed `quote`/`letFields` link.

Method: the nested name-literal/array-literal `match`es have no equation lemmas in v4.32.1, so each is
analysed from its definition (cases on the scrutinees, `unfold` of the matcher, `dsimp_sparse_aux`, a `dite`
splitter `dite_goal` because `split` hits the simp step limit), as in `regView_ok`.

BUILT: lc4a50 exit 0 (Tools.ShippingBundleIotaRange, whole file incl. corollaries); audit lc4a51 exit 0 (ChildVertAuditTest; bundleIotaRange axioms propext, Quot.sound only). -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsAliasInv Tools.ShippingReaderFuel
open Sparkle.Compiler.MachRawSurface Tools.ShippingSparseCasesTac

theorem dite_goal {c : Prop} [Decidable c] {α : Sort _} {t : c → α} {f : ¬c → α} {P : α → Prop}
    (h1 : ∀ h, P (t h)) (h2 : ∀ h, P (f h)) : P (dite c t f) := by
  by_cases h : c
  · simpa [h] using h1 h
  · simpa [h] using h2 h

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bundleIota_key1 (n : Nat) (e : Lean.Expr) (he : LetOk n e = true) (p : Name) (s : Lean.Expr)
    (hs : LetOk n s = true) :
    LetOk n (match s.getAppFn, s.getAppArgs, p with
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, a, _],
        ``Sparkle.Core.Signal.Signal.fst => a
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, _, b],
        ``Sparkle.Core.Signal.Signal.snd => b
    -- a triple is a pair whose second component is a pair
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, a, _, _],
        ``Sparkle.Core.Signal.Signal.fst => a
    | .const ``Sparkle.Core.Signal.bundle3 _, #[d, _, β, γ, _, b, c],
        ``Sparkle.Core.Signal.Signal.snd => mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) d β γ b c
    | _, _, _ => e) = true := by
  have hargs := ok_getAppArgs hs
  generalize s.getAppFn = G at *
  generalize s.getAppArgs = B at *
  revert hargs
  rcases B with ⟨L⟩
  rcases G with _ | _ | _ | _ | ⟨nm, us⟩ | _ | _ | _ | _ | _ | _ | _
  case const =>
    rcases nm with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold_matchers_aux)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals (try (exact fun _ => he))
    all_goals (try rcases p with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨pp5, ss5⟩ | ⟨pp5, ii5⟩, ss4⟩ | ⟨pp4, ii4⟩, ss3⟩ |
      ⟨pp3, ii3⟩, ss2⟩ | ⟨pp2, ii2⟩, ss1⟩ | ⟨pp1, ii1⟩, ss0⟩ | ⟨pp0, ii0⟩)
    all_goals (try dsimp only)
    all_goals (repeat' split)
    all_goals (try (exact fun _ => he))
    all_goals (try (intro hargs
                    rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, L'⟩⟩⟩⟩⟩⟩⟩⟩))
    all_goals (try (repeat' (refine dite_goal (P := fun x => LetOk n x = true) ?_ ?_ <;> intro hh <;> (try subst hh) <;> (try dsimp only))))
    all_goals first
      | exact he
      | (exfalso; simp at *; done)
      | (simp [he]; done)
      | (subst_vars; exact he)
      | (repeat' split; all_goals first | exact he | (subst_vars; exact he) | (exfalso; simp at *; done) | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done))
      | (rcases L' with _ | ⟨a8, L''⟩ <;> (first | (subst_vars; exact he) | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done) | (exfalso; simp at *; done)))
      | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
      | (simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
    all_goals first
      | (apply hargs; simp [Array.getLit]; done)
      | (subst_vars; simp_all [Array.getLit, LetOk]; done)
      | (subst_vars; exact hargs.2.2.2.1)
      | (simp_all [Array.getLit, LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
  all_goals (try unfold_matchers_aux)
  all_goals (try dsimp only)
  all_goals (intro _; exact he)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bundleIota_key3 (n : Nat) (e : Lean.Expr) (he : LetOk n e = true) (p : Name) (s : Lean.Expr)
    (hs : LetOk n s = true) :
    LetOk n (match s.getAppFn, s.getAppArgs, p with
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, a, _, _],
        ``Sparkle.Core.Signal.Signal.proj3_1 => a
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, _, b, _],
        ``Sparkle.Core.Signal.Signal.proj3_2 => b
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, _, _, c],
        ``Sparkle.Core.Signal.Signal.proj3_3 => c
    | _, _, _ => e) = true := by
  have hargs := ok_getAppArgs hs
  generalize s.getAppFn = G at *
  generalize s.getAppArgs = B at *
  revert hargs
  rcases B with ⟨L⟩
  rcases G with _ | _ | _ | _ | ⟨nm, us⟩ | _ | _ | _ | _ | _ | _ | _
  case const =>
    rcases nm with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold_matchers_aux)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals (try (exact fun _ => he))
    all_goals (try rcases p with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨pp5, ss5⟩ | ⟨pp5, ii5⟩, ss4⟩ | ⟨pp4, ii4⟩, ss3⟩ |
      ⟨pp3, ii3⟩, ss2⟩ | ⟨pp2, ii2⟩, ss1⟩ | ⟨pp1, ii1⟩, ss0⟩ | ⟨pp0, ii0⟩)
    all_goals (try dsimp only)
    all_goals (repeat' split)
    all_goals (try (exact fun _ => he))
    all_goals (try (intro hargs
                    rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, L'⟩⟩⟩⟩⟩⟩⟩⟩))
    all_goals (try (repeat' (refine dite_goal (P := fun x => LetOk n x = true) ?_ ?_ <;> intro hh <;> (try subst hh) <;> (try dsimp only))))
    all_goals first
      | exact he
      | (exfalso; simp at *; done)
      | (simp [he]; done)
      | (subst_vars; exact he)
      | (repeat' split; all_goals first | exact he | (subst_vars; exact he) | (exfalso; simp at *; done) | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done))
      | (rcases L' with _ | ⟨a8, L''⟩ <;> (first | (subst_vars; exact he) | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done) | (exfalso; simp at *; done)))
      | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
      | (simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
    all_goals first
      | (apply hargs; simp [Array.getLit]; done)
      | (subst_vars; simp_all [Array.getLit, LetOk]; done)
      | (subst_vars; exact hargs.2.2.2.1)
      | (simp_all [Array.getLit, LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
  all_goals (try unfold_matchers_aux)
  all_goals (try dsimp only)
  all_goals (intro _; exact he)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bundleIota_key2 (n : Nat) (e : Lean.Expr) (he : LetOk n e = true) (f s : Lean.Expr)
    (hs : LetOk n s = true) :
    LetOk n (match s.getAppFn, s.getAppArgs, f.getAppFn, f.getAppNumArgs with
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, a, _], .const ``Prod.fst _, 2 => a
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, _, b], .const ``Prod.snd _, 2 => b
    | _, _, _, _ => e) = true := by
  have hargs := ok_getAppArgs hs
  generalize s.getAppFn = G at *
  generalize s.getAppArgs = B at *
  generalize f.getAppFn = H
  generalize f.getAppNumArgs = k
  revert hargs
  rcases B with ⟨L⟩
  rcases G with _ | _ | _ | _ | ⟨nm, us⟩ | _ | _ | _ | _ | _ | _ | _
  case const =>
    rcases nm with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold_matchers_aux)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals (try (exact fun _ => he))
    all_goals (try rcases H with _ | _ | _ | _ | ⟨hn, hus⟩ | _ | _ | _ | _ | _ | _ | _)
    all_goals (try rcases hn with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨pp5, ss5⟩ | ⟨pp5, ii5⟩, ss4⟩ | ⟨pp4, ii4⟩, ss3⟩ |
      ⟨pp3, ii3⟩, ss2⟩ | ⟨pp2, ii2⟩, ss1⟩ | ⟨pp1, ii1⟩, ss0⟩ | ⟨pp0, ii0⟩)
    all_goals (try rcases k with _ | _ | _ | k)
    all_goals (try dsimp only)
    all_goals (repeat' split)
    all_goals (try (exact fun _ => he))
    all_goals (try (intro hargs
                    rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, L'⟩⟩⟩⟩⟩⟩⟩⟩))
    all_goals (try (repeat' (refine dite_goal (P := fun x => LetOk n x = true) ?_ ?_ <;> intro hh <;> (try subst hh) <;> (try dsimp only))))
    all_goals first
      | exact he
      | (exfalso; simp at *; done)
      | (simp [he]; done)
      | (subst_vars; exact he)
      | (repeat' split; all_goals first | exact he | (subst_vars; exact he) | (exfalso; simp at *; done) | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done))
      | (rcases L' with _ | ⟨a8, L''⟩ <;> (first | (subst_vars; exact he) | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done) | (exfalso; simp at *; done)))
      | (subst_vars; simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
      | (simp_all [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
    all_goals first
      | (apply hargs; simp [Array.getLit]; done)
      | (subst_vars; simp_all [Array.getLit, LetOk]; done)
      | (subst_vars; exact hargs.2.2.2.1)
      | (simp_all [Array.getLit, LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]; done)
  all_goals (try unfold_matchers_aux)
  all_goals (try dsimp only)
  all_goals (intro _; exact he)


set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **PROVED**: `bundleIota` preserves `LetOk` (discharges `BundleIotaRange`). -/
theorem bundleIotaRange : BundleIotaRange := by
  intro n e he
  have hargs := ok_getAppArgs he
  unfold Sparkle.Compiler.MachRawSurface.bundleIota
  generalize e.getAppFn = F
  generalize e.getAppArgs = A at *
  revert hargs
  rcases A with ⟨L⟩
  rcases F with _ | _ | _ | _ | ⟨nm, us⟩ | _ | _ | _ | _ | _ | _ | _
  case const =>
    rcases nm with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold Sparkle.Compiler.MachRawSurface.bundleIota.match_7)
    all_goals (try dsimp_sparse_aux)
    all_goals (try (exact fun _ => he))
    all_goals (try (intro hargs
                    rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, L'⟩⟩⟩⟩⟩⟩))
    all_goals (try (repeat' (refine dite_goal (P := fun x => LetOk n x = true) ?_ ?_ <;> intro hh <;> (try subst hh) <;> (try dsimp only))))
    all_goals first
      | exact he
      | (subst_vars; exact he)
      | (exfalso; simp at *; done)
      | (subst_vars; refine bundleIota_key1 n e he _ _ (hargs _ ?_); simp; done)
      | (subst_vars; refine bundleIota_key3 n e he _ _ (hargs _ ?_); simp; done)
      | (subst_vars; refine bundleIota_key2 n e he _ _ (hargs _ ?_); simp; done)
  all_goals (try unfold_matchers_aux)
  all_goals (try dsimp only)
  all_goals (intro _; exact he)
/-! ## LC3's final theorems with the `BundleIotaRange` premise discharged

Each is the LC3 theorem applied to `bundleIotaRange`; the four premises `RootFloatRange`, `LiftRange`,
`Inst1Range`, `SigTyRange senv` remain (PREMISES, not proved here). -/

section
variable {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range)
  (hsig : SigTyRange senv)
include hroot hlift hinst1 hsig

theorem machConvF_post' {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e st = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true :=
  machConvF_post hroot hlift hinst1 hsig bundleIotaRange hst hE hl h

theorem machNestedF_post' {n : Nat} {env : List MachVal}
    {dom αs initsE body : Lean.Expr} {st st' : MachRead} {r : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hd : LetOk 0 dom = true) (hb : LetOk 0 body = true)
    (h : machNestedF n senv env dom αs initsE body st = some (some (r, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true :=
  machNestedF_post hroot hlift hinst1 hsig bundleIotaRange hst hE hd hb h

theorem machChainF_post' {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machChainF n senv env e st = some (some (ws, v, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size v = true :=
  machChainF_post hroot hlift hinst1 hsig bundleIotaRange hst hE hl h

theorem machLoopBodyF_post' {n : Nat} {base : Nat} {env : List MachVal}
    {e : Lean.Expr} {st st' : MachRead} (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) (h : machLoopBodyF n senv base env e st = some (some st')) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size :=
  machLoopBodyF_post hroot hlift hinst1 hsig bundleIotaRange hst hE hl h

theorem machLoopRootF_post' {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st st' : MachRead} {mv : MachVal} (hst : RdOk st) (hE : EnvOk st.lets.size env)
    (hl : LetOk 0 e = true) (h : machLoopRootF n senv env e st = some (some (mv, st'))) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ MvOk st'.lets.size mv :=
  machLoopRootF_post hroot hlift hinst1 hsig bundleIotaRange hst hE hl h

theorem alias_premise_of_conv' {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st st1 : MachRead} {v' : Lean.Expr} (hst : RdOk st)
    (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e st = some (some (v', st1))) :
    ∀ j, v' = machLet j → j < st1.lets.size :=
  alias_premise_of_conv hroot hlift hinst1 hsig bundleIotaRange hst hE hl h

theorem machConvF_init' {n : Nat} {env : List MachVal} {d : Nat}
    {e : Lean.Expr} {st' : MachRead} {r : Lean.Expr} (hE : EnvOk 0 env) (hl : LetOk 0 e = true)
    (h : machConvF n senv env d e ({} : MachRead) = some (some (r, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, r = machLet j → j < st'.lets.size :=
  machConvF_init hroot hlift hinst1 hsig bundleIotaRange hE hl h

theorem machChainF_init' {n : Nat} {env : List MachVal} {e : Lean.Expr}
    {st' : MachRead} {ws : List (Nat × Lean.Expr)} {v : Lean.Expr} (hE : EnvOk 0 env)
    (hl : LetOk 0 e = true)
    (h : machChainF n senv env e ({} : MachRead) = some (some (ws, v, st'))) :
    NoLetAlias st'.lets ∧ ∀ j, v = machLet j → j < st'.lets.size :=
  machChainF_init hroot hlift hinst1 hsig bundleIotaRange hE hl h

theorem real_conv_post' {G : OldFns} {S : Call → Prop} (hcov : TwinCoverAt senv G S)
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st st' : MachRead} {r : Lean.Expr}
    (hS : S (Call.conv env d e st))
    (hst : RdOk st) (hE : EnvOk st.lets.size env) (hl : LetOk 0 e = true)
    (h : G.conv env d e st = some (r, st')) :
    RdOk st' ∧ st.lets.size ≤ st'.lets.size ∧ LetOk st'.lets.size r = true :=
  real_conv_post hroot hlift hinst1 hsig bundleIotaRange hcov hS hst hE hl h
end

end Tools.ShippingLetsReaderInv
