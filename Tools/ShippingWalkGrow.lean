import Tools.ShippingCacheCoherentCert
import Tools.ShippingChildFallback
import Tools.ShippingWalkStill

/-! # A world-level logic over `CompilerM` in which the child cache GROWS (round par/b-37)

WRITTEN, NOT BUILT.

`Tools/ShippingWalkStill.lean` (BUILT) has `WHo`: partial correctness of a
`CompilerM` action between worlds whose child-cache VALUE is one fixed map.
The instance arm of the translator is the operation that changes that value
(`childSynthEntry` → `synthesizeChild` inserts the child's result), so it is
outside `WHo`.

`WG` here is the variant for it:

    WG L D ctx P c Q :=
      ∀ st w p w', InvV L w → L.dval w = D → P (L.val w) →
        RunsTo (c ctx st) … w p w' →
        InvV L w' ∧ L.dval w' = D ∧ SubMap (L.val w) (L.val w') ∧ Q p.1 (L.val w')

— a returning run from an invariant world of synthesis depth `D` whose cache
satisfies `P` ends in an invariant world of the same depth whose cache
CONTAINS the start cache (`SubMap`: every entry kept, with its value) and
satisfies `Q` of the result.

Differences from the form asked ("`InvV L w ∧ SubMap mb (L.val w)` and a
postcondition on the result"), each for a reason found by reading:

* the precondition is a predicate `P` of the cache and the postcondition
  sees the END cache: "the child's result is an entry of the end cache" is
  a statement about the end cache, and a later call's hit needs it as a
  precondition. `SubMap mb` is the instance `WG.grow` (any up-closed
  predicate is carried: `WG.frame`);
* the DEPTH is in the invariant: `SubMap` across a child synthesis is
  `Tools.ShippingCacheCoherentRun.child_sub_runs`, which asks
  `L.dval w ≠ 0` (at depth 0 the entry clears the cache). `WHo` does not
  speak of the depth, so a `WSt` lemma ALONE does not transfer; the
  transfer (`WG.ofStill`) takes, besides the still lemma, the action's
  `Keeps (J L' D)` fact — which the BUILT `@[keeps]` lemmas of
  `Tools/ShippingChildFallback.lean` / `ShippingChildBody.lean` give for
  every translator operation, the instance arm's included
  (`instArgs_keepsC`, `instAddModules_keepsC`, `instClkRst_keepsC`,
  `translateInstanceOrFallback_keepsC`, …). `WG.ofKeeps` alone gives the
  invariant, the depth and `SubMap` for any such action (the witness's
  auxiliary predicate set to `SubMap (L.val w)`, as `child_sub` does).

Result facts that do not depend on the world come from the existing
`Returns`-level lemmas (`WG.withReturns`: a run is a `Returns`).

The instance arm's own step (item 1 of
`docs/parallel/B-slotless-parents-2.md` §2.3):

* `childSynthEntry_post`: a returning run of `childSynthEntry c` from an
  invariant world of positive depth returns a `RealChild`, keeps the
  invariant and the depth, keeps every entry, leaves its result as THE
  entry of `c` in the end cache, and on a hit returns the cached value;
* `WG.child`, `WG.child_hit`: the same as `WG` rules for the lifted action
  (`CompilerM.liftMetaM (childSynthEntry c)`, as the arm calls it).

NOT here (the next statement, in the doc): the S6 shape proof of the arm
against `WG`. -/
namespace Tools.ShippingWalkGrow
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingEntrySoundness Tools.ShippingChildInv
open Tools.ShippingCacheCoherentRun Tools.ShippingCallsSame
open Tools.ShippingWalkStill (WHo WSI)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

section Logic
variable (mctx cctx)

/-- Partial correctness with a growing child cache (file header). -/
def WG (L : RefLaws mref cref) (D : Nat) (ctx : CompilerState)
    (P : Std.HashMap Lean.Name Res → Prop) {α : Type} (c : CompilerM α)
    (Q : α → Std.HashMap Lean.Name Res → Prop) : Prop :=
  ∀ (st : CircuitState) (w : Void IO.RealWorld) (p : α × CircuitState) (w' : Void IO.RealWorld),
    InvV L w → L.dval w = D → P (L.val w) →
    RunsTo (c ctx st) mctx mref cctx cref w p w' →
    InvV L w' ∧ L.dval w' = D ∧ SubMap (L.val w) (L.val w') ∧ Q p.1 (L.val w')

end Logic

variable {L : RefLaws mref cref} {D : Nat} {ctx : CompilerState}

/-! ## Structural rules -/

theorem WG.pure {α : Type} (a : α) {P : Std.HashMap Lean.Name Res → Prop}
    {Q : α → Std.HashMap Lean.Name Res → Prop} (hq : ∀ m, P m → Q a m) :
    WG mctx cctx L D ctx P (Pure.pure a : CompilerM α) Q := by
  intro st w p w' hw hd hp hr
  obtain ⟨hpe, hww⟩ := RunsTo.pure_world (a := (a, st)) hr
  rw [hpe, hww]
  exact ⟨hw, hd, sub_refl _, hq _ hp⟩

theorem WG.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    {P : Std.HashMap Lean.Name Res → Prop} {Q1 : α → Std.HashMap Lean.Name Res → Prop}
    {Q2 : β → Std.HashMap Lean.Name Res → Prop}
    (h1 : WG mctx cctx L D ctx P c Q1)
    (h2 : ∀ a, WG mctx cctx L D ctx (Q1 a) (f a) Q2) :
    WG mctx cctx L D ctx P (c >>= f) Q2 := by
  intro st w p w' hw hd hp hr
  obtain ⟨⟨a, s⟩, w1, r1, r2⟩ := RunsTo.bind hr
  obtain ⟨hw1, hd1, hs1, hq1⟩ := h1 st w (a, s) w1 hw hd hp r1
  obtain ⟨hw2, hd2, hs2, hq2⟩ := h2 a s w1 p w' hw1 hd1 hq1 r2
  exact ⟨hw2, hd2, sub_trans hs1 hs2, hq2⟩

/-- Weaker precondition, stronger postcondition. -/
theorem WG.conseq {α : Type} {c : CompilerM α}
    {P P' : Std.HashMap Lean.Name Res → Prop} {Q Q' : α → Std.HashMap Lean.Name Res → Prop}
    (h : WG mctx cctx L D ctx P c Q) (hP : ∀ m, P' m → P m)
    (hQ : ∀ a m, Q a m → Q' a m) :
    WG mctx cctx L D ctx P' c Q' := by
  intro st w p w' hw hd hp hr
  obtain ⟨h1, h2, h3, h4⟩ := h st w p w' hw hd (hP _ hp) hr
  exact ⟨h1, h2, h3, hQ _ _ h4⟩

/-- **A predicate of the cache that survives growth is carried across any
action.** -/
theorem WG.frame {α : Type} {c : CompilerM α}
    {P : Std.HashMap Lean.Name Res → Prop} {Q : α → Std.HashMap Lean.Name Res → Prop}
    {R : Std.HashMap Lean.Name Res → Prop}
    (hR : ∀ m m', SubMap m m' → R m → R m')
    (h : WG mctx cctx L D ctx P c Q) :
    WG mctx cctx L D ctx (fun m => P m ∧ R m) c (fun a m => Q a m ∧ R m) := by
  intro st w p w' hw hd hp hr
  obtain ⟨h1, h2, h3, h4⟩ := h st w p w' hw hd hp.1 hr
  exact ⟨h1, h2, h3, h4, hR _ _ h3 hp.2⟩

/-- The form "the cache only grows from the start value `mb`". -/
theorem WG.grow {α : Type} {c : CompilerM α}
    {P : Std.HashMap Lean.Name Res → Prop} {Q : α → Std.HashMap Lean.Name Res → Prop}
    (mb : Std.HashMap Lean.Name Res) (h : WG mctx cctx L D ctx P c Q) :
    WG mctx cctx L D ctx (fun m => P m ∧ SubMap mb m) c (fun a m => Q a m ∧ SubMap mb m) :=
  WG.frame (fun _ _ hs hm => sub_trans hm hs) h

/-- An entry of the cache survives any action (an instance of `WG.frame`). -/
theorem WG.keepEntry {α : Type} {c : CompilerM α}
    {P : Std.HashMap Lean.Name Res → Prop} {Q : α → Std.HashMap Lean.Name Res → Prop}
    (k : Lean.Name) (y : Res) (h : WG mctx cctx L D ctx P c Q) :
    WG mctx cctx L D ctx (fun m => P m ∧ m.get? k = some y) c
      (fun a m => Q a m ∧ m.get? k = some y) :=
  WG.frame (fun _ _ hs hm => hs k y hm) h

/-- A lifted `MetaM` action. -/
theorem WG.lift {α : Type} {m : Lean.Meta.MetaM α}
    {P : Std.HashMap Lean.Name Res → Prop} {Q : α → Std.HashMap Lean.Name Res → Prop}
    (hm : ∀ (w : Void IO.RealWorld) (a : α) (w' : Void IO.RealWorld),
      InvV L w → L.dval w = D → P (L.val w) → RunsTo m mctx mref cctx cref w a w' →
      InvV L w' ∧ L.dval w' = D ∧ SubMap (L.val w) (L.val w') ∧ Q a (L.val w')) :
    WG mctx cctx L D ctx P (CompilerM.liftMetaM m) Q := by
  intro st w p w' hw hd hp hr
  obtain ⟨a, w1, r1, r2⟩ := RunsTo.bind hr
  obtain ⟨hpe, hww⟩ := RunsTo.pure_world r2
  rw [hpe, hww]
  exact hm w a w1 hw hd hp r1

/-! ## Transfers from the built material -/

/-- **From the `Keeps` lemmas**: an action that keeps `J L' D` for every law
witness keeps the invariant and the depth and only grows the cache (the
witness's auxiliary predicate set to `SubMap (L.val w)`). -/
theorem WG.ofKeeps {α : Type} {c : CompilerM α} {P : Std.HashMap Lean.Name Res → Prop}
    (hk : ∀ (L' : RefLaws mref cref) (st : CircuitState),
      Keeps mctx mref cctx cref (J L' D) (c ctx st)) :
    WG mctx cctx L D ctx P c (fun _ _ => True) := by
  intro st w p w' hw hd _ hr
  have h := (hk (L.withAux (SubMap (L.val w)) (sub_insert (L.val w))) st w
    ⟨hw, hd, sub_refl _⟩).1
  rw [endW_of_runs hr] at h
  exact ⟨h.1, h.2.1, h.2.2, trivial⟩

/-- **A world-free fact of the result**, from a `Returns`-level lemma: a run
is a `Returns`. -/
theorem WG.withReturns {α : Type} {c : CompilerM α}
    {P : Std.HashMap Lean.Name Res → Prop} {Q : α → Std.HashMap Lean.Name Res → Prop}
    {Q0 : α → Prop} (h : WG mctx cctx L D ctx P c Q)
    (hq : ∀ (st : CircuitState) (a : α) (s' : CircuitState),
      Tools.ShippingTranslateSoundness.Returns c ctx st a s' → Q0 a) :
    WG mctx cctx L D ctx P c (fun a m => Q a m ∧ Q0 a) := by
  intro st w p w' hw hd hp hr
  obtain ⟨h1, h2, h3, h4⟩ := h st w p w' hw hd hp hr
  have hret : Tools.ShippingTranslateSoundness.Returns c ctx st p.1 p.2 :=
    ⟨mctx, mref, cctx, cref, w, w', hr⟩
  exact ⟨h1, h2, h3, h4, hq st p.1 p.2 hret⟩

/-- **From a still lemma** (`WHo`, for every cache value) and the action's
`Keeps` fact (which supplies the depth `WHo` does not speak of): the cache
is unchanged, so `P` is kept, and the result satisfies the still lemma's
postcondition. -/
theorem WG.ofStill {α : Type} {c : CompilerM α} {P : Std.HashMap Lean.Name Res → Prop}
    {Q0 : α → Prop}
    (hk : ∀ (L' : RefLaws mref cref) (st : CircuitState),
      Keeps mctx mref cctx cref (J L' D) (c ctx st))
    (hs : ∀ mb : Std.HashMap Lean.Name Res, WHo mctx cctx L mb ctx c Q0) :
    WG mctx cctx L D ctx P c (fun a m => P m ∧ Q0 a) := by
  intro st w p w' hw hd hp hr
  obtain ⟨⟨hw', hv⟩, hq⟩ := hs (L.val w) st w p w' ⟨hw, rfl⟩ hr
  have hdk := ((hk L.plain st w ⟨hw, hd, trivial⟩).1)
  rw [endW_of_runs hr] at hdk
  refine ⟨hw', hdk.2.1, ?_, ?_, hq⟩
  · rw [hv]
    exact sub_refl _
  · rw [hv]
    exact hp

/-! ## The instance arm's child synthesis -/

/-- **A returning run of the translator's child synthesis** from an
invariant world of positive depth: the result is a `RealChild`; the
invariant and the depth are kept; every entry of the cache is kept; the
result is THE entry of `c` in the end cache; on a hit it is the cached
value. (`childSynthEntry` reads the synthesis ref — `synthesizeChild` in an
invariant world — and runs it: `synthesizeChild_post`, `child_sub_runs`,
`synthesizeChild_depth`.) -/
theorem childSynthEntry_post (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c : Lean.Name} {w w' : Void IO.RealWorld} {y : Res}
    (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (childSynthEntry c) mctx mref cctx cref w y w') :
    RealChild mref cref c y ∧ InvV L w' ∧ L.dval w' = L.dval w ∧
      SubMap (L.val w) (L.val w') ∧ (L.val w').get? c = some y ∧
      ∀ y0, (L.val w).get? c = some y0 → y = y0 := by
  unfold childSynthEntry at hr
  obtain ⟨s, w1, hget, hrest⟩ := RunsTo.bind hr
  have hs : s = some synthesizeChild := by
    rw [L.synthGet _ _ _ hget]
    exact hw.2.1
  subst hs
  have hw1 : InvV L w1 := invV_framed L .synthGet hget hw
  have hsame := L.same .synthGet hget
  have hv1 : L.val w1 = L.val w := hsame.1
  have hd1 : L.dval w1 = L.dval w := hsame.2.2
  have hrun : RunsTo (synthesizeChild c) mctx mref cctx cref w1 y w' := hrest
  obtain ⟨hreal, hw', hgetc, hhit⟩ := synthesizeChild_post L hB hw1 hrun
  have hsub : SubMap (L.val w1) (L.val w') :=
    child_sub_runs L hB hw1 (by rw [hd1]; exact hd) hrun
  have hdep : L.dval w' = L.dval w1 := synthesizeChild_depth L hB hw1 hrun
  refine ⟨hreal, hw', hdep.trans hd1, ?_, hgetc, ?_⟩
  · rw [← hv1]
    exact hsub
  · intro y0 h0
    exact hhit y0 (by rw [hv1]; exact h0)

/-- **The child synthesis as the arm calls it**: the result is a `RealChild`
and an entry of the END cache. -/
theorem WG.child (hB : ∀ L' : RefLaws mref cref, BodyRel L') (hD : D ≠ 0) (c : Lean.Name)
    {P : Std.HashMap Lean.Name Res → Prop} :
    WG mctx cctx L D ctx P (CompilerM.liftMetaM (childSynthEntry c))
      (fun y m => RealChild mref cref c y ∧ m.get? c = some y) := by
  apply WG.lift
  intro w y w' hw hd _ hr
  obtain ⟨hreal, hw', hdep, hsub, hgetc, -⟩ :=
    childSynthEntry_post L hB hw (by rw [hd]; exact hD) hr
  exact ⟨hw', hdep.trans hd, hsub, hreal, hgetc⟩

/-- **A repeated call is a hit**: when the cache holds `y0` for `c`, the
child synthesis returns `y0` (and all of `WG.child`). With `WG.keepEntry`
this is the argument for the later calls of a parent. -/
theorem WG.child_hit (hB : ∀ L' : RefLaws mref cref, BodyRel L') (hD : D ≠ 0) (c : Lean.Name)
    (y0 : Res) :
    WG mctx cctx L D ctx (fun m => m.get? c = some y0)
      (CompilerM.liftMetaM (childSynthEntry c))
      (fun y m => y = y0 ∧ RealChild mref cref c y ∧ m.get? c = some y) := by
  apply WG.lift
  intro w y w' hw hd hp hr
  obtain ⟨hreal, hw', hdep, hsub, hgetc, hhit⟩ :=
    childSynthEntry_post L hB hw (by rw [hd]; exact hD) hr
  exact ⟨hw', hdep.trans hd, hsub, hhit y0 hp, hreal, hgetc⟩

end Tools.ShippingWalkGrow
