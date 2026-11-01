import Tools.ShippingGen5ReaderTraceDomKeepF
import Tools.ShippingGen5ReaderTraceShape
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceDomKeepS, exit 0) on the tree of 237f86d9179ae02cd11f4a9766bcb668fb4bdeab (Lean content identical; this header is comment-only). Clean build is the coder's. No sorry / axiom / native_decide in source.
-- Written against freeze rev21.1 `scripts/gen5/DG_READERTRACE_FREEZE_REV21.md` §4, §5 (`shapeRootLet_domKeepF`, `rootLets_domKeepF`, `shapeBody_domKeepF`, `shapePost_domForm`).

/-! # DG-READERTRACE rev21.1: the wrapper's three reader stages keep the `dom` relation (`DomKeepF`), and `shapePost` yields `DomForm`

`hK : DomKeepF (readF senv n)` is a theorem hypothesis here (supplied by `readF_domKeepF` under `EqvAtom`, `Tools/ShippingGen5ReaderTraceDomKeepF.lean`);
nothing is assumed in this file. `shapePost_domForm`: a successful `shapePost` whose state has `dom = some d` read `machDom? _ d = some _`, so `DomForm d`.
Conditional (intermediate) result. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderLenOk

theorem shapeRootLet_domKeepF (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n))
    (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    {s' : List MachVal × MachRead} (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s'))
    (d : Lean.Expr) (hd : s.2.dom = some d) :
    ∃ d', s'.2.dom = some d' ∧ (DomForm d' → d' = d) := by
  obtain ⟨env, st⟩ := s
  obtain ⟨nm, ty, v⟩ := a
  simp only at hd
  simp only [shapeRootLet] at hr
  split at hr
  · -- a `Signal.loop` root
    obtain ⟨⟨mv, s1⟩, hl, hr⟩ := bindO_some_inv hr
    obtain ⟨d1, hd1, r1⟩ := hK (Call.loopRoot env v st) (mv, s1) hl d hd
    have e := okO_run_inv hr
    subst e
    exact ⟨d1, hd1, r1⟩
  · split at hr
    · -- an ordinary root `let`
      obtain ⟨⟨v', s1⟩, hc, hr⟩ := bindO_some_inv hr
      obtain ⟨d1, hd1, r1⟩ := hK (Call.conv env 0 v st) (v', s1) hc d hd
      have e := okO_run_inv hr
      subst e
      exact ⟨d1, hd1, r1⟩
    · exact (failO_run_inv hr).elim

theorem rootLets_domKeepF (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n)) :
    ∀ (l : List (Name × Lean.Expr × Lean.Expr)) (env : List MachVal) (st : MachRead)
      {env' : List MachVal} {st' : MachRead},
    (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
    ∀ d : Lean.Expr, st.dom = some d → ∃ d', st'.dom = some d' ∧ (DomForm d' → d' = d)
  | [], env, st, env', st', hr, d, hd => by
    have hr' : (okO (env, st) : FM WCall WCall.Res (Option (List MachVal × MachRead))).run (wtab senv n) =
        some (some (env', st')) := hr
    have e := okO_run_inv hr'
    injection e with e1 e2
    subst e1
    subst e2
    exact ⟨d, hd, fun _ => rfl⟩
  | a :: l, env, st, env', st', hr, d, hd => by
    have hr' : (bindO (shapeRootLet senv (env, st) a) fun s1 => foldO (shapeRootLet senv) s1 l).run (wtab senv n) =
        some (some (env', st')) := hr
    obtain ⟨s1, h1, h2⟩ := bindO_some_inv hr'
    obtain ⟨d1, hd1, r1⟩ := shapeRootLet_domKeepF senv n hK (env, st) a h1 d hd
    obtain ⟨d2, hd2, r2⟩ := rootLets_domKeepF senv n hK l s1.1 s1.2 h2 d1 hd1
    exact ⟨d2, hd2, domKeepF_seq r1 r2⟩

theorem shapeBody_domKeepF (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n))
    (m : ShapeMid) (env : List MachVal) (st1 : MachRead) {st : MachRead} {v : Lean.Expr}
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v)))
    (d : Lean.Expr) (hd : st1.dom = some d) :
    ∃ d', st.dom = some d' ∧ (DomForm d' → d' = d) := by
  unfold shapeBody at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    dsimp only at hr
    obtain ⟨⟨v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    dsimp only at hr
    obtain ⟨d1, hd1, r1⟩ := hK (Call.conv env 0 m.root st1) (v0, st2) hc d hd
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    exact ⟨d1, hd1, r1⟩
  · rw [hm] at hr
    dsimp only at hr
    obtain ⟨⟨ws, v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    dsimp only at hr
    obtain ⟨d1, hd1, r1⟩ := hK (Call.chain (MachVal.regs 0 :: env) body st1) (ws, v0, st2) hc d hd
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    exact ⟨d1, hd1, r1⟩

theorem domForm_of_machDom? {m : Nat} {d : Lean.Expr} {r : Lean.Expr × Sparkle.IR.Type.ResetKind}
    (h : machDom? m d = some r) : DomForm d := by
  unfold machDom? at h
  split at h
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · cases h

theorem shapePost_domForm {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (h : shapePost ai p m st v = some sp)
    {d : Lean.Expr} (hd : st.dom = some d) : DomForm d := by
  by_cases hf : DomForm d
  · exact hf
  · exfalso
    have hn : ∀ k : Nat, machDom? k d = none := by
      intro k
      cases hh : machDom? k d with
      | none => rfl
      | some r => exact absurd (domForm_of_machDom? hh) hf
    simp [shapePost, hd, hn] at h

end Tools.ShippingGen5ReaderTrace
