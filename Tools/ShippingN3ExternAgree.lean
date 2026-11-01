import Tools.Prototype.PreprocLetOk
import Tools.ShippingLetsExternSpec
import Tools.Prototype.RawNodeRangeLetOk
import Tools.Assume.N3Extern
set_option autoImplicit false
-- NOT BUILT: candidate S3 (proofs from n3impl1 C3 278b4cf1; assumptions imported from Tools/Assume/N3Extern).

/-! # N3 extern agreement premises → range lemmas (skeleton)

The types of `scripts/gen3/N3_EXTERN_MIN.md` §3.4.2 (reviewer-approved design, rev 2).

* The behaviour assumptions `LiftAgrees0` / `LowerAgreesEq` / `ZeroLitAgrees0` and the definitions their statements
  use (`lowerGo` / `lowerSpec` / `zeroLitF`) live in `Tools/Assume/N3Extern.lean`, not here; this file only proves.
* `r1` / `r2` / `r3` (and `lowerGo_ok`, `lowerSpec_ok`): the range statements are PROVED from the equalities.
* `rawNode_ok_of_agrees`: `rawNode_ok` with `LiftLooseRange` / `LowerLooseRange` replaced by `LiftAgrees0` / `LowerAgreesEq`.

Nothing here is a new axiom, law, or TRUSTED boundary. -/

namespace Tools.ShippingN3ExternAgree
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsAliasInv Tools.ShippingLetsReaderInv
open Tools.Prototype.PreprocLetOk Tools.Prototype.RawNodeRangeLetOk
open Tools.Assume.N3Extern
open Sparkle.Compiler.MachRawSurface (rawNode projChain listElems)

/-- Range statements (derived below, NOT assumed). -/
def LiftLooseRange0 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), LetOk 0 e = true → LetOk 0 (e.liftLooseBVars 0 d) = true

def LowerLooseRangeEq : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), LetOk 0 e = true → LetOk 0 (e.lowerLooseBVars i i) = true

def ZeroLitRange0 : Prop :=
  ∀ (e : Lean.Expr), LetOk 0 e = true →
    LetOk 0 (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true

theorem lowerGo_ok (n : Nat) : ∀ (e : Expr) s d, LetOk n e = true → LetOk n (lowerGo e s d) = true := by
  intro e
  induction e with
  | bvar i =>
    intro s d _
    show LetOk n (if i < s then Expr.bvar i else Expr.bvar (i - d)) = true
    split <;> rfl
  | app f a ihf iha =>
    intro s d h; simp only [LetOk, Bool.and_eq_true] at h
    show LetOk n (.app (lowerGo f s d) (lowerGo a s d)) = true
    simp only [LetOk, Bool.and_eq_true]; exact ⟨ihf _ _ h.1, iha _ _ h.2⟩
  | lam nm t b bi iht ihb =>
    intro s d h; simp only [LetOk, Bool.and_eq_true] at h
    show LetOk n (.lam nm (lowerGo t s d) (lowerGo b (s + 1) d) bi) = true
    simp only [LetOk, Bool.and_eq_true]; exact ⟨iht _ _ h.1, ihb _ _ h.2⟩
  | forallE nm t b bi iht ihb =>
    intro s d h; simp only [LetOk, Bool.and_eq_true] at h
    show LetOk n (.forallE nm (lowerGo t s d) (lowerGo b (s + 1) d) bi) = true
    simp only [LetOk, Bool.and_eq_true]; exact ⟨iht _ _ h.1, ihb _ _ h.2⟩
  | letE nm t v b nd iht ihv ihb =>
    intro s d h; simp only [LetOk, Bool.and_eq_true] at h
    show LetOk n (.letE nm (lowerGo t s d) (lowerGo v s d) (lowerGo b (s + 1) d) nd) = true
    simp only [LetOk, Bool.and_eq_true]
    exact ⟨⟨iht _ _ h.1.1, ihv _ _ h.1.2⟩, ihb _ _ h.2⟩
  | mdata m e ih =>
    intro s d h; simp only [LetOk] at h
    show LetOk n (.mdata m (lowerGo e s d)) = true
    simp only [LetOk]; exact ih _ _ h
  | proj nm i e ih =>
    intro s d h; simp only [LetOk] at h
    show LetOk n (.proj nm i (lowerGo e s d)) = true
    simp only [LetOk]; exact ih _ _ h
  | fvar _ => intro s d h; exact h
  | mvar _ => intro s d h; exact h
  | sort _ => intro s d h; exact h
  | const _ _ => intro s d h; exact h
  | lit _ => intro s d h; exact h

theorem lowerSpec_ok (n : Nat) : ∀ (e : Expr) s d, LetOk n e = true → LetOk n (lowerSpec e s d) = true := by
  intro e s d h
  show LetOk n (if s < d then e else lowerGo e s d) = true
  split
  · exact h
  · exact lowerGo_ok n e s d h

theorem r1 (h : LiftAgrees0) : LiftLooseRange0 := by
  intro e d he
  rw [h e d he]; exact liftSpec_ok 0 e 0 d he

theorem r2 (h : LowerAgreesEq) : LowerLooseRangeEq := by
  intro e i he
  rw [h e i he]; exact lowerSpec_ok 0 e i i he

theorem r3 (h : ZeroLitAgrees0) : ZeroLitRange0 := by
  intro e he
  rw [h e he]
  refine replaceNoCache_ok 0 zeroLitF ?_ e he
  intro x r hx
  delta zeroLitF at hx
  split at hx
  · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp hx
    simp only [mkApp2, LetOk, Bool.and_eq_true, Bool.true_and]
    exact ⟨letOk_natLit _ _, letOk_natLit _ _⟩
  · simp at hx

theorem build_ok0 (hl : LiftLooseRange0) {k : Nat} {regs body : Lean.Expr} {tys : List Lean.Expr}
    (hr : LetOk 0 regs = true) (hbody : LetOk 0 body = true) (ht : ∀ t ∈ tys, LetOk 0 t = true) :
    ∀ (l : List (Nat × Name × Lean.Expr)), (∀ x ∈ l, LetOk 0 x.2.2 = true) → ∀ r : Lean.Expr,
      rawNode.build k regs body tys l = some r → LetOk 0 r = true
  | [], _, r, h => by
    rw [build_nil] at h
    have := Option.some.inj h
    subst this
    exact hbody
  | (j, nm, t) :: rest, hlist, r, h => by
    rw [build_cons] at h
    obtain ⟨v, hv, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr', h3⟩ := Option.bind_eq_some_iff.mp h2
    have h4 := Option.some.inj h3
    subst h4
    have hv' : LetOk 0 v = true := by
      refine projChain_ok (hl regs j hr) ?_ hv
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hl y j (ht y hy)
    have hrest := build_ok0 hl hr hbody ht rest (fun x hx => hlist x (List.mem_cons_of_mem _ hx)) r' hr'
    have htt : LetOk 0 t = true := hlist (j, nm, t) List.mem_cons_self
    simp [LetOk, htt, hv', hrest]

theorem rawNode_ok0 (hl : LiftLooseRange0) (hlo : LowerLooseRangeEq) (hb : BetaRange) (pm : Name → Option Nat) :
    ∀ e e', LetOk 0 e = true → rawNode pm e = some e' → LetOk 0 e' = true := by
  intro e e' he h
  have hF := ok_getAppFn he
  have hA := ok_getAppArgs he
  have hA2 : ∀ x ∈ e.getAppArgs, ∀ y ∈ x.getAppArgs, LetOk 0 y = true :=
    fun x hx => ok_getAppArgs (hA x hx)
  clear he
  revert h
  first
    | unfold rawNode
    | delta rawNode
    | simp only [rawNode]
  generalize e.getAppFn = F at hF ⊢
  generalize e.getAppArgs = A at hA hA2 ⊢
  refine match15_elim (fun o => o = some e' → LetOk 0 e' = true) F A _ _ _ _ _ _ _ ?c1 ?c2 ?c3 ?c4 ?c5 ?c6 ?c7
  case c7 => intro h; cases h
  case c1 =>
    intro us dom S τ W r hFe hAe h
    subst hAe
    cases h
    simp_all [LetOk, mkApp3, mkApp2, mkApp4, mkApp]
  case c2 =>
    intro us m inst α β x k hFe hAe h
    subst hAe
    try dsimp only at h
    revert h
    refine match1_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ _ ?d1 ?d2
    case d2 => intro h; cases h
    case d1 =>
      intro us' dom S us1 hF' hA' hG' h
      try dsimp only at h
      cases h
      apply ok_mkAppN_list (by simp [LetOk])
      simp_all
  case c3 =>
    intro us m inst α a hFe hAe h
    subst hAe
    try dsimp only at h
    revert h
    refine match3_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ _ ?d1 ?d2
    case d2 => intro h; cases h
    case d1 =>
      intro us' dom S us1 hF' hA' hG' h
      try dsimp only at h
      cases h
      apply ok_mkAppN_list (by simp [LetOk])
      simp_all
  case c4 =>
    intro us dom S head β x k hFe hAe h
    subst hAe
    try dsimp only at h
    revert h
    refine match7_elim (fun o => o = some e' → LetOk 0 e' = true) _ _ _ _ ?d1 ?d2
    case d2 => intro h; cases h
    case d1 =>
      intro us' a b c as f hFe' hAe' h
      try dsimp only at h
      split at h
      · cases h
      · rename_i xs hxs
        try dsimp only at h
        cases h
        try dsimp only
        have has : ∀ a ∈ xs, LetOk 0 a = true := by
          refine listElems_ok (n := 0) _ _ ‹listElems _ = some _› ?_
          simp_all
        refine ok_foldr _ _ ?_ ?_
        · exact hb _ _ (hl _ _ (by simp_all)) (by simp [LetOk])
        · intro p hp r hr
          obtain ⟨⟨a, i0⟩, hq, rfl⟩ := List.mem_map.mp hp
          dsimp only
          apply ok_mkAppN_list (by simp [LetOk])
          intro y hy
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hl _ _ (by simp_all)
          · exact hl _ _ (by simp_all)
          · simp [LetOk]
          · exact hl _ _ (by simp_all)
          · exact hb _ _ (hl _ _ (by simp_all)) (hl _ _ (has a (of_mem_zipIdx xs 0 a i0 hq)))
          · simp [LetOk, hr]
  case c5 =>
    intro us m inst head as f hFe hAe h
    subst hAe
    try dsimp only at h
    split at h
    · cases h
    · rename_i xs hxs
      try dsimp only at h
      cases h
      try dsimp only
      have has : ∀ a ∈ xs, LetOk 0 a = true := by
        refine listElems_ok (n := 0) _ _ ‹listElems _ = some _› ?_
        simp_all
      refine ok_foldr _ _ ?_ ?_
      · refine hl _ _ ?_
        apply ok_mkAppN_list (by simp [LetOk])
        simp_all [LetOk, mkApp2, mkApp]
      · intro p hp r hr
        obtain ⟨⟨a, i0⟩, hq, rfl⟩ := List.mem_map.mp hp
        dsimp only
        apply ok_mkAppN_list (by simp [LetOk])
        intro y hy
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hl _ _ (by simp_all)
        · simp only [LetOk, mkApp2, mkApp, Bool.and_eq_true]
          exact ⟨⟨by simp [LetOk], hl _ _ (by simp_all)⟩, hl _ _ (by simp_all)⟩
        · simp [LetOk]
        · simp [LetOk]
        · exact hb _ _ (hl _ _ (by simp_all)) (hl _ _ (has a (of_mem_zipIdx xs 0 a i0 hq)))
        · simp [LetOk, hr]
  case c6 =>
    intro n us hFe h
    try dsimp only at h
    split at h
    · split at h
      · cases h
      · try dsimp only at h
        split at h
        · cases h
        · try dsimp only at h
          have hpeel := peel_ok _ _ _ _ _ ‹rawNode.peel _ _ _ = some _› (ok_getElem! hA 2) (by simp)
          refine build_ok0 hl (ok_getElem! hA 1) hpeel.1 ?_ _ ?_ _ h
          · exact tys_ok _ hpeel.2 (fun nm t i ht => hlo t i ht)
          · exact list_ok _ hpeel.2 (fun _ _ _ => rfl)
    · cases h

theorem rawNode_ok_of_agrees (hl : LiftAgrees0) (hlo : LowerAgreesEq) (hb : BetaRange) (pm : Name → Option Nat) :
    ∀ e e', LetOk 0 e = true → rawNode pm e = some e' → LetOk 0 e' = true :=
  rawNode_ok0 (r1 hl) (r2 hlo) hb pm

end Tools.ShippingN3ExternAgree
