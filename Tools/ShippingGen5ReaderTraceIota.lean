import Tools.ShippingBundleIotaRange
import Tools.ShippingGen5ReaderTraceApp
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceIota, exit 0) on the tree of f053d6018560ba5dfe5d501bb447716ba5c1bd6f (this header is comment-only). Written against freeze rev7 `scripts/gen5/DG_READERTRACE_FREEZE_REV7.md` (U-R4c, part 1); clean issue-linked build pending (coder). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R4c (part 1): `bundleIota` and `machProjIota` preserve a hereditary predicate

`bundleIota_pres` is `Tools.ShippingBundleIotaRange.bundleIotaRange` (same case analysis, same tactic scripts) with `LetOk n` replaced by an arbitrary predicate `Q` that
satisfies `QApp` (`Q (f a) ↔ Q f ∧ Q a`) and `QConst`. Conditional on nothing but `QApp Q` / `QConst Q`; no extern fact, no `PureFacts`.
Not supplied: the other U-R4c lemmas (`liftSpec` / `rootFloatS`), U-R4d, `TraceGood senv nDecl (readF senv n)`, the real run and FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingSparseCasesTac Sparkle.Compiler.MachRawSurface
  Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel

/-- hereditary under application -/
abbrev QApp (Q : Lean.Expr → Prop) : Prop := ∀ f a, Q (.app f a) ↔ Q f ∧ Q a
abbrev QConst (Q : Lean.Expr → Prop) : Prop := ∀ c ls, Q (.const c ls)

theorem q_argsAcc (Q : Lean.Expr → Prop) (happ : QApp Q) : ∀ (e : Lean.Expr) (acc : List Lean.Expr), Q e →
    (∀ a ∈ acc, Q a) → ∀ a ∈ Tools.ShippingReaderMatcherArity.argsAcc e acc, Q a
  | .app f a, acc, he, hacc => by
    have h := (happ f a).mp he
    refine q_argsAcc Q happ f (a :: acc) h.1 ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.2
    · exact hacc x hx
  | .bvar _, _, _, hacc => hacc
  | .fvar _, _, _, hacc => hacc
  | .mvar _, _, _, hacc => hacc
  | .sort _, _, _, hacc => hacc
  | .const _ _, _, _, hacc => hacc
  | .lit _, _, _, hacc => hacc
  | .lam _ _ _ _, _, _, hacc => hacc
  | .forallE _ _ _ _, _, _, hacc => hacc
  | .letE _ _ _ _ _, _, _, hacc => hacc
  | .mdata _ _, _, _, hacc => hacc
  | .proj _ _ _, _, _, hacc => hacc

theorem q_getAppArgs (Q : Lean.Expr → Prop) (happ : QApp Q) {e : Lean.Expr} (he : Q e) :
    ∀ a ∈ e.getAppArgs, Q a := by
  intro a ha
  rw [Tools.ShippingReaderMatcherArityArray.getAppArgs_eq] at ha
  exact q_argsAcc Q happ e [] he (by simp) a (List.mem_toArray.mp ha)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bundleIota_key1 (Q : Lean.Expr → Prop) (happ : QApp Q) (hconst : QConst Q) (e : Lean.Expr) (he : Q e) (p : Name) (s : Lean.Expr)
    (hs : Q s) :
    Q (match s.getAppFn, s.getAppArgs, p with
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, a, _],
        ``Sparkle.Core.Signal.Signal.fst => a
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, _, b],
        ``Sparkle.Core.Signal.Signal.snd => b
    -- a triple is a pair whose second component is a pair
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, a, _, _],
        ``Sparkle.Core.Signal.Signal.fst => a
    | .const ``Sparkle.Core.Signal.bundle3 _, #[d, _, β, γ, _, b, c],
        ``Sparkle.Core.Signal.Signal.snd => mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) d β γ b c
    | _, _, _ => e) := by
  have hargs := q_getAppArgs Q happ hs
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
    all_goals (try (repeat' (refine Tools.ShippingLetsReaderInv.dite_goal (P := Q) ?_ ?_ <;> intro hh <;> (try subst hh) <;> (try dsimp only))))
    all_goals first
      | exact he
      | (exfalso; simp at *; done)
      | (simp [he]; done)
      | (subst_vars; exact he)
      | (repeat' split; all_goals first | exact he | (subst_vars; exact he) | (exfalso; simp at *; done) | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done))
      | (rcases L' with _ | ⟨a8, L''⟩ <;> (first | (subst_vars; exact he) | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done) | (exfalso; simp at *; done)))
      | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
      | (simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
    all_goals first
      | (apply hargs; simp [Array.getLit]; done)
      | (subst_vars; simp_all [Array.getLit, happ, hconst]; done)
      | (subst_vars; exact hargs.2.2.2.1)
      | (simp_all [Array.getLit, happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
  all_goals (try unfold_matchers_aux)
  all_goals (try dsimp only)
  all_goals (intro _; exact he)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bundleIota_key3 (Q : Lean.Expr → Prop) (happ : QApp Q) (hconst : QConst Q) (e : Lean.Expr) (he : Q e) (p : Name) (s : Lean.Expr)
    (hs : Q s) :
    Q (match s.getAppFn, s.getAppArgs, p with
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, a, _, _],
        ``Sparkle.Core.Signal.Signal.proj3_1 => a
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, _, b, _],
        ``Sparkle.Core.Signal.Signal.proj3_2 => b
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, _, _, c],
        ``Sparkle.Core.Signal.Signal.proj3_3 => c
    | _, _, _ => e) := by
  have hargs := q_getAppArgs Q happ hs
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
    all_goals (try (repeat' (refine Tools.ShippingLetsReaderInv.dite_goal (P := Q) ?_ ?_ <;> intro hh <;> (try subst hh) <;> (try dsimp only))))
    all_goals first
      | exact he
      | (exfalso; simp at *; done)
      | (simp [he]; done)
      | (subst_vars; exact he)
      | (repeat' split; all_goals first | exact he | (subst_vars; exact he) | (exfalso; simp at *; done) | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done))
      | (rcases L' with _ | ⟨a8, L''⟩ <;> (first | (subst_vars; exact he) | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done) | (exfalso; simp at *; done)))
      | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
      | (simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
    all_goals first
      | (apply hargs; simp [Array.getLit]; done)
      | (subst_vars; simp_all [Array.getLit, happ, hconst]; done)
      | (subst_vars; exact hargs.2.2.2.1)
      | (simp_all [Array.getLit, happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
  all_goals (try unfold_matchers_aux)
  all_goals (try dsimp only)
  all_goals (intro _; exact he)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bundleIota_key2 (Q : Lean.Expr → Prop) (happ : QApp Q) (hconst : QConst Q) (e : Lean.Expr) (he : Q e) (f s : Lean.Expr)
    (hs : Q s) :
    Q (match s.getAppFn, s.getAppArgs, f.getAppFn, f.getAppNumArgs with
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, a, _], .const ``Prod.fst _, 2 => a
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, _, b], .const ``Prod.snd _, 2 => b
    | _, _, _, _ => e) := by
  have hargs := q_getAppArgs Q happ hs
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
    all_goals (try subst_vars)
    all_goals (try dsimp only)
    all_goals (repeat' split)
    all_goals (try (exact fun _ => he))
    all_goals (try (intro hargs
                    rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, L'⟩⟩⟩⟩⟩⟩⟩⟩))
    all_goals (try (repeat' (refine Tools.ShippingLetsReaderInv.dite_goal (P := Q) ?_ ?_ <;> intro hh <;> (try subst hh) <;> (try dsimp only))))
    all_goals first
      | exact he
      | (exfalso; simp at *; done)
      | (simp [he]; done)
      | (subst_vars; exact he)
      | (repeat' split; all_goals first | exact he | (subst_vars; exact he) | (exfalso; simp at *; done) | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done))
      | (rcases L' with _ | ⟨a8, L''⟩ <;> (first | (subst_vars; exact he) | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done) | (exfalso; simp at *; done)))
      | (subst_vars; simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
      | (simp_all [happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
    all_goals first
      | (apply hargs; simp [Array.getLit]; done)
      | (subst_vars; simp_all [Array.getLit, happ, hconst]; done)
      | (subst_vars; exact hargs.2.2.2.1)
      | (simp_all [Array.getLit, happ, hconst, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]; done)
  all_goals (try unfold_matchers_aux)
  all_goals (try dsimp only)
  all_goals (intro _; exact he)


set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `bundleIota` preserves any hereditary predicate `Q` (same method as `bundleIotaRange`). -/
theorem bundleIota_pres (Q : Lean.Expr → Prop) (happ : QApp Q) (hconst : QConst Q) (e : Lean.Expr) (he : Q e) :
    Q (Sparkle.Compiler.MachRawSurface.bundleIota e) := by
  have hargs := q_getAppArgs Q happ he
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
    all_goals (try (repeat' (refine Tools.ShippingLetsReaderInv.dite_goal (P := Q) ?_ ?_ <;> intro hh <;> (try subst hh) <;> (try dsimp only))))
    all_goals first
      | exact he
      | (subst_vars; exact he)
      | (exfalso; simp at *; done)
      | (subst_vars; refine bundleIota_key1 Q happ hconst e he _ _ (hargs _ ?_); simp; done)
      | (subst_vars; refine bundleIota_key3 Q happ hconst e he _ _ (hargs _ ?_); simp; done)
      | (subst_vars; refine bundleIota_key2 Q happ hconst e he _ _ (hargs _ ?_); simp; done)
  all_goals (try unfold_matchers_aux)
  all_goals (try dsimp only)
  all_goals (intro _; exact he)

theorem q_spine (Q : Lean.Expr → Prop) (happ : QApp Q) (e : Lean.Expr) : ∀ (acc : List Lean.Expr), Q e →
    (∀ a ∈ acc, Q a) → Q (inlSpine e acc).1 ∧ ∀ a ∈ (inlSpine e acc).2, Q a := by
  induction e with
  | app f a ihf iha =>
    intro acc he hacc
    have h := (happ f a).mp he
    have := ihf (a :: acc) h.1 (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.2
      · exact hacc x hx)
    simpa only [inlSpine] using this
  | _ =>
    intro acc he hacc
    simp only [inlSpine]
    exact ⟨he, hacc⟩

theorem getD_q (Q : Lean.Expr → Prop) {e : Lean.Expr} {o : Option Lean.Expr} (he : Q e)
    (ho : ∀ x, o = some x → Q x) : Q (o.getD e) := by
  cases o with
  | none => exact he
  | some x => exact ho x rfl

theorem projIota_pres (Q : Lean.Expr → Prop) (happ : QApp Q) (projs : Name → Option (Name × Nat × Nat))
    (e : Lean.Expr) (he : Q e) : Q (machProjIota projs e) := by
  have hs := q_spine Q happ e [] he (by simp)
  unfold machProjIota
  split
  · rename_i heq0
    rw [heq0] at hs
    dsimp only at hs
    split
    · rename_i r _ hq
      split
      · have hrm := List.mem_of_getLast? hq
        have hrok : Q r := hs.2 r hrm
        have hs2 := q_spine Q happ r [] hrok (by simp)
        split
        · rename_i heq2
          rw [heq2] at hs2
          dsimp only at hs2
          split
          · exact getD_q Q he (fun x hx => hs2.2 x (List.mem_of_getElem? hx))
          · exact he
        · exact he
      · exact he
    · exact he
  · exact he

/-! ## The predicate the trace needs: `InRange ∧ NoLoose` is hereditary -/

theorem qApp_inRangeNoLoose (nDecl : Nat) (st : MachRead) (k d : Nat) :
    QApp (fun e => InRange nDecl st k e ∧ NoLoose d e) := by
  intro f a
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨⟨⟨fun i hi => h.1 i (Or.inl hi), fun i hi => h.2.1 i (Or.inl hi),
        fun i hi => h.2.2.1 i (Or.inl hi), fun i hi => h.2.2.2 i (Or.inl hi)⟩, fun b hb => hn b (Or.inl hb)⟩,
      ⟨⟨fun i hi => h.1 i (Or.inr hi), fun i hi => h.2.1 i (Or.inr hi),
        fun i hi => h.2.2.1 i (Or.inr hi), fun i hi => h.2.2.2 i (Or.inr hi)⟩, fun b hb => hn b (Or.inr hb)⟩⟩
  · rintro ⟨⟨hf, hnf⟩, ⟨ha, hna⟩⟩
    exact ⟨inRange_app hf ha, noLoose_app hnf hna⟩

theorem qConst_inRangeNoLoose (nDecl : Nat) (st : MachRead) (k d : Nat) :
    QConst (fun e => InRange nDecl st k e ∧ NoLoose d e) :=
  fun _ _ => ⟨inRange_closed (fun _ _ h => (h : False)), noLoose_const⟩

/-- the output of `convStep`'s general `app` arm is `InRange ∧ NoLoose` when its two converted parts are -/
theorem bundleProj_ph {nDecl : Nat} {st : MachRead} {k d : Nat} (proj : Name → Option (Name × Nat × Nat))
    {f' a' : Lean.Expr} (hf : InRange nDecl st k f' ∧ NoLoose d f') (ha : InRange nDecl st k a' ∧ NoLoose d a') :
    InRange nDecl st k (bundleIota (machProjIota proj (.app f' a'))) ∧
    NoLoose d (bundleIota (machProjIota proj (.app f' a'))) := by
  have hq := qApp_inRangeNoLoose nDecl st k d
  exact bundleIota_pres _ hq (qConst_inRangeNoLoose nDecl st k d) _
    (projIota_pres _ hq proj _ ((hq f' a').mpr ⟨hf, ha⟩))

end Tools.ShippingGen5ReaderTrace
