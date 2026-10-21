import Tools.ShippingLetsReaderInvMain
import Tools.ShippingSparseCasesTac
namespace Tools.ShippingLetsReaderInv
open Lean Tools.ShippingLetsAliasInv
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


end Tools.ShippingLetsReaderInv
