import Tools.ShippingCacheCoherentClose
import Tools.ShippingMachineInstG

variable {tenv : Lean.Environment}

/-! # Provenance for declarations on the certified (machine) route

`Tools.ShippingCacheCoherentRun` left `CoreFresh c` (unrestricted) and
`Tools.ShippingCacheCoherentClose` left `HarnessProv` (the translator keeps
`Prov`) as statements. This file replaces both, for a declaration whose core
run takes the MACHINE route, by per-declaration facts of a smaller kind, and
derives the rest.

## The unit: `EntryOk L c K`

A returning run of the FULL entry of `c` from an invariant world of positive
depth whose cache satisfies `Prov` and does not hold `c`: the end cache
satisfies `Prov`, the result is `Fresh` for it, and every key the run added
is in `K` (`KeysIn`). The key set is what removes "the run does not insert
its own key" (H3) as a separate obligation: the keys a parent's run adds are
its callees' and theirs, and "the parent is none of them" is `¬ K c` — a
statement about NAMES, decided per declaration.

## Derived here (WRITTEN, NOT BUILT)

* `synthesizeChild_ok`, `child_ok`: the memoised entry keeps `Prov` and the
  key bound, and its result is the end cache's entry — relative to `EntryOk`
  of THAT declaration only (not of every declaration).
* `mapM_inv`: a `mapM` whose steps keep an invariant and return memory
  children or end-cache entries (`KidOk`).
* `closeInstsM_all`, `closeInstsGM_all`: BOTH closings, memory children
  included: the invariant is kept; a returned module has the transition's
  name; every module of a returned design is a memory module or the module
  of an entry of the END cache (`design_prov_of_kids`, pure).
* `machine_all`: a run of the machine synthesis — whatever it returns —
  relative to `HarnessStill` of its transition and `EntryOk` of its callees.
* `entryOk_machine`: `EntryOk L c K` for a machine-route declaration, from
  `CoreVia`, `HarnessStill`, the harness's result facts (`hout`: the shape of
  `Tools.ShippingClosedKinds.closedBody_kinds_of_run`, BUILT, per
  declaration data), `EntryOk` of the callees and `¬ K c`.
* `entryOk_leaf`: `EntryOk` for a declaration without children, from
  `EntryStill` and the child-side name/design facts on `RealChild`.
* `machine_closes_of_entryOk`: the consumer — the built relative closing
  `MachineClosesAtS` fires from a `Prov` start world.

## The statements that remain (NOT derived)

* `HarnessStill L declName bs body`: a returning run of the harness on THIS
  transition leaves the cache. It replaces `HarnessProv` (every body, `Prov`
  kept) by a statement about one body with a concrete consequence. Not
  derivable today: the built relative theorems (`harnessRel_of`,
  `translateRel`) carry only invariants closed under an insert of ANY value
  (`RefLaws.auxInsert`), and "nothing was inserted" is not one; the
  certified translation's soundness proofs are stated on `MReturns`, without
  worlds.
* `CoreVia L c shape`: a returning core run of `c` from an invariant world of
  positive depth IS a machine synthesis that returns the run's result, whose
  start world has the run's start cache and whose end world has the run's
  end cache. Route (`MachineDefines`, the closing) plus FRAME steps only (the
  entry's prefix at positive depth, the machine arm's log and memo insert,
  the `finally`); derivable from `RefLaws`, NOT written: the built
  `core_reads_inv` / `synthesizeFromConst_machine_inv` /
  `RunsTo.try_finally` do not relate the cache values of the worlds they
  produce.
* `EntryStill L c` (leaves): a returning run of the full entry leaves the
  cache. The same two facts for a leaf. -/
namespace Tools.ShippingCacheCoherentCert
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Sparkle.Compiler.MachMemory (memModule memChild?)
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingCallsKidsS Tools.ShippingCacheCoherent
open Tools.ShippingCacheCoherentRun Tools.ShippingCacheCoherentClose Tools.ShippingCallsSame
open Tools.ShippingDesignWithG (mem_visited)

/-! ## Pure: the key bound, the children -/

/-- Every key of `m'` is a key of `m` or in `K`. -/
def KeysIn (m : Std.HashMap Name Res) (K : Name → Prop) (m' : Std.HashMap Name Res) : Prop :=
  ∀ (k : Name) (y : Res), m'.get? k = some y → (∃ y0 : Res, m.get? k = some y0) ∨ K k

theorem keysIn_refl (m : Std.HashMap Name Res) (K : Name → Prop) : KeysIn m K m :=
  fun k y h => Or.inl ⟨y, h⟩

theorem keysIn_trans {m0 m1 m2 : Std.HashMap Name Res} {K : Name → Prop}
    (h1 : KeysIn m0 K m1) (h2 : KeysIn m1 K m2) : KeysIn m0 K m2 := by
  intro k y hk
  rcases h2 k y hk with ⟨y1, e1⟩ | e
  · exact h1 k y1 e1
  · exact Or.inr e

theorem keysIn_mono {m m' : Std.HashMap Name Res} {K K' : Name → Prop}
    (hK : ∀ k, K k → K' k) (h : KeysIn m K m') : KeysIn m K' m' :=
  fun k y hk => (h k y hk).imp id (hK k)

/-- A key that was absent and is not in `K` is still absent. -/
theorem keysIn_none {m m' : Std.HashMap Name Res} {K : Name → Prop} {c : Name}
    (hk : KeysIn m K m') (h0 : m.get? c = none) (hK : ¬ K c) : m'.get? c = none := by
  cases h : m'.get? c with
  | none => rfl
  | some y =>
    rcases hk c y h with ⟨y0, e⟩ | e
    · rw [h0] at e
      cases e
    · exact absurd e hK

/-- A child of a closing: a built memory child, or an entry of `m`. -/
def KidOk (m : Std.HashMap Name Res) (y : Res) : Prop :=
  (∃ (cb : Bool) (aw dw : Nat), y = memModule cb aw dw) ∨ ∃ c : Name, m.get? c = some y

theorem kidOk_mono {m m' : Std.HashMap Name Res} (hs : SubMap m m') {y : Res}
    (h : KidOk m y) : KidOk m' y := by
  rcases h with h | ⟨c, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hs c y hc⟩

theorem memModule_design (cb : Bool) (aw dw : Nat) :
    (memModule cb aw dw).2.modules = [(memModule cb aw dw).1] := rfl

/-- **The joined design of children that are memory children or cache
entries, over a parent design without modules: every module is a memory
module or the module of a cache entry.** -/
theorem design_prov_of_kids {m : Std.HashMap Name Res} (hp : Prov m)
    {children : List Res} (hk : ∀ c ∈ children, KidOk m c)
    {d₀ : Sparkle.IR.AST.Design} (hd0 : d₀.modules = []) :
    ∀ a ∈ (Sparkle.IR.Machine.designWith children d₀).modules, IsMem a ∨ IsTop m a := by
  intro a ha
  rcases mem_designWith ha with h1 | h1
  · rw [hd0] at h1
    cases h1
  · obtain ⟨c, hc, hac⟩ := mem_visited.mp h1
    rcases hk c hc with ⟨cb, aw, dw, e⟩ | ⟨k, hkc⟩
    · refine Or.inl ⟨cb, aw, dw, ?_⟩
      rcases hac with hac | hac
      · rw [hac, e]
      · rw [e, memModule_design] at hac
        exact List.mem_singleton.mp hac
    · rcases hac with hac | hac
      · exact Or.inr ⟨k, c, hkc, hac⟩
      · exact (hp k c hkc).2 a hac

/-- The one-output closing's module has the closed module's name. -/
theorem closeInsts_name {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    m.name = m₀.name := by
  unfold Sparkle.IR.Machine.closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
    rfl
  · cases h

/-- The general closing's module has the closed module's name. -/
theorem closeInstsG_name {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    {m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (h : Sparkle.IR.Machine.closeInstsG nIn kI n portNames insts fields children (m₀, d₀) =
      some (m, d)) :
    m.name = m₀.name := by
  unfold Sparkle.IR.Machine.closeInstsG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
    exact (Sparkle.IR.Machine.withClockFor_same children m₀).1
  · cases h

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The unit -/

/-- **The per-declaration unit.** A returning run of the full entry of `c`,
from an invariant world of positive depth whose cache satisfies `Prov` and
does not hold `c`: `Prov` of the end cache, the result `Fresh` for it, and
every added key in `K`. -/
def EntryOk (L : RefLaws mref cref) (c : Name) (K : Name → Prop) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) (r : Res)
    (w' : Void IO.RealWorld),
    InvV L w → L.dval w ≠ 0 → Prov (L.val w) → (L.val w).get? c = none →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' →
    Prov (L.val w') ∧ Fresh (L.val w') c r ∧ KeysIn (L.val w) K (L.val w')

theorem EntryOk.mono {L : RefLaws mref cref} {c : Name} {K K' : Name → Prop}
    (h : EntryOk L c K) (hK : ∀ k, K k → K' k) : EntryOk L c K' := by
  intro mctx cctx w r w' hw hd hp hc hrun
  obtain ⟨h1, h2, h3⟩ := h mctx cctx w r w' hw hd hp hc hrun
  exact ⟨h1, h2, keysIn_mono hK h3⟩

/-- The invariant carried through a closing: the cache invariant, a positive
depth, `Prov`, and the key bound against the base map `mb`. -/
def PK (L : RefLaws mref cref) (mb : Std.HashMap Name Res) (K : Name → Prop)
    (w : Void IO.RealWorld) : Prop :=
  InvV L w ∧ L.dval w ≠ 0 ∧ Prov (L.val w) ∧ KeysIn mb K (L.val w)

/-- **The memoised entry keeps `Prov` and bounds the added keys**, relative
to `EntryOk` of ITS declaration, which is in `K`. -/
theorem synthesizeChild_ok (L : RefLaws mref cref) {K : Name → Prop} {c : Name}
    {w w' : Void IO.RealWorld} {y : Res} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hp : Prov (L.val w)) (hK : K c) (hR : EntryOk L c K)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    Prov (L.val w') ∧ KeysIn (L.val w) K (L.val w') := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hv, -⟩ := L.get hget
  have hw1 : InvV L w1 := invV_framed L .cacheGet hget hw
  have hd1 : L.dval w1 ≠ 0 := by
    rw [(L.same .cacheGet hget).2.2]
    exact hd
  have hp1 : Prov (L.val w1) := by
    rw [hv]
    exact hp
  cases hcm : m.get? c with
  | some r =>
    simp only [hcm] at h
    obtain ⟨-, hww⟩ := RunsTo.pure_world h
    rw [hww, hv]
    exact ⟨hp, keysIn_refl _ _⟩
  | none =>
    simp only [hcm] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    obtain ⟨hv3, -, -⟩ := L.cacheModify _ _ _ _ hmod
    obtain ⟨-, hww⟩ := RunsTo.pure_world h
    have hc1 : (L.val w1).get? c = none := by
      rw [hv, ← hm]
      exact hcm
    obtain ⟨hp2, hf, hk2⟩ := hR mctx cctx w1 r w2 hw1 hd1 hp1 hc1 hrun
    have hfin : Prov ((L.val w2).insert c r) := prov_insert hp2 hf
    have hkeys : KeysIn (L.val w) K ((L.val w2).insert c r) := by
      intro k y hk
      rw [Std.HashMap.get?_insert] at hk
      split at hk
      · rename_i heq
        have hck : c = k := by simpa using heq
        rw [← hck]
        exact Or.inr hK
      · rcases hk2 k y hk with ⟨y0, h0⟩ | h0
        · rw [hv] at h0
          exact Or.inl ⟨y0, h0⟩
        · exact Or.inr h0
    rw [hww, hv3]
    exact ⟨hfin, hkeys⟩

/-- One call of the memoised entry in a closing: the invariant, every entry
kept, and the result an entry of the end cache. -/
theorem child_ok (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {mb : Std.HashMap Name Res} {K : Name → Prop} {c : Name}
    {w w' : Void IO.RealWorld} {y : Res} (hK : K c) (hR : EntryOk L c K)
    (hp : PK L mb K w) (hy : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    PK L mb K w' ∧ SubMap (L.val w) (L.val w') ∧ KidOk (L.val w') y := by
  obtain ⟨hw, hd, hpv, hkeys⟩ := hp
  obtain ⟨-, hw', hget, -⟩ := synthesizeChild_post L hB hw hy
  obtain ⟨hpv', hk'⟩ := synthesizeChild_ok L hw hd hpv hK hR hy
  have hd' : L.dval w' ≠ 0 := by
    rw [synthesizeChild_depth L hB hw hy]
    exact hd
  exact ⟨⟨hw', hd', hpv', keysIn_trans hkeys hk'⟩, child_sub_runs L hB hw hd hy,
    Or.inr ⟨c, hget⟩⟩

/-- **A `mapM` whose steps keep `P`, keep every cache entry and return a
memory child or an entry of the cache they end in**: the same of the whole
`mapM`, every result against the END cache. The step is asked only of the
list's elements satisfying `G`. -/
theorem mapM_loop_inv {α : Type} (f : α → MetaM Res) (L : RefLaws mref cref)
    (P : Void IO.RealWorld → Prop) (G : α → Prop)
    (hf : ∀ x w y w', G x → P w → RunsTo (f x) mctx mref cctx cref w y w' →
      P w' ∧ SubMap (L.val w) (L.val w') ∧ KidOk (L.val w') y) :
    ∀ (l : List α) (acc r : List Res) w w', (∀ x ∈ l, G x) → P w →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ P w' ∧ SubMap (L.val w) (L.val w') ∧
        ∀ y ∈ ys, KidOk (L.val w') y
  | [], acc, r, w, w', _, hp, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, hp, sub_refl _, fun y hy => by simp at hy⟩
  | x :: xs, acc, r, w, w', hg, hp, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hp1, hs1, hk1⟩ := hf x w y w1 (hg x (List.mem_cons_self ..)) hp hy
    obtain ⟨ys, hr, hp', hs', hk'⟩ := mapM_loop_inv f L P G hf xs (y :: acc) r w1 w'
      (fun z hz => hg z (List.mem_cons_of_mem _ hz)) hp1 h
    refine ⟨y :: ys, by simp [hr], hp', sub_trans hs1 hs', fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with hzy | hz
    · rw [hzy]
      exact kidOk_mono hs' hk1
    · exact hk' z hz

theorem mapM_inv {α : Type} {f : α → MetaM Res} (G : α → Prop) (L : RefLaws mref cref)
    (P : Void IO.RealWorld → Prop)
    (hf : ∀ x w y w', G x → P w → RunsTo (f x) mctx mref cctx cref w y w' →
      P w' ∧ SubMap (L.val w) (L.val w') ∧ KidOk (L.val w') y)
    (l : List α) (r : List Res) {w w'} (hg : ∀ x ∈ l, G x) (hp : P w)
    (h : RunsTo (l.mapM f) mctx mref cctx cref w r w') :
    P w' ∧ SubMap (L.val w) (L.val w') ∧ ∀ y ∈ r, KidOk (L.val w') y := by
  obtain ⟨ys, hr, hp', hs, hk⟩ := mapM_loop_inv f L P G hf l [] r w w' hg hp h
  simp only [List.reverse_nil, List.nil_append] at hr
  subst hr
  exact ⟨hp', hs, hk⟩

/-! ## The two closings -/

/-- **The one-output closing**: the invariant is kept; a returned module has
the closed module's name; every module of a returned design is a memory
module or the module of an entry of the end cache. -/
theorem closeInstsM_all (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {mb : Std.HashMap Name Res} {K : Name → Prop} {shape t m₀ d₀ r}
    {w w' : Void IO.RealWorld}
    (hins : ∀ x ∈ shape.insts, K x.1) (hR : ∀ c, K c → EntryOk L c K)
    (hp : PK L mb K w) (hd0 : d₀.modules = [])
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    PK L mb K w' ∧ ∀ (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design),
      r = some (m, d) → m.name = m₀.name ∧ ∀ a ∈ d.modules, IsMem a ∨ IsTop (L.val w') a := by
  obtain ⟨hw, hd, hpv, hkeys⟩ := hp
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hs1 := L.same .synthGet hget
  have hp1 : PK L mb K w1 :=
    ⟨hw1, by rw [hs1.2.2]; exact hd, by rw [hs1.1]; exact hpv, by rw [hs1.1]; exact hkeys⟩
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, hww⟩ := RunsTo.pure_world hr
  obtain ⟨hp2, -, hkids⟩ := mapM_inv
    (fun (x : Name × List Nat × MixedGateBinder) => K x.1) L (PK L mb K)
    (fun x w y w' hg hp hy => by
      -- a tactic block: elaborated after `hch` has fixed the mapped function
      exact child_ok L hB hg (hR _ hg) hp hy)
    shape.insts children hins hp1 hch
  rw [hww]
  refine ⟨hp2, fun m d hmd => ?_⟩
  rw [hmd] at heq
  have hdes : d = Sparkle.IR.Machine.designWith children d₀ := closeInsts_design heq.symm
  refine ⟨closeInsts_name heq.symm, ?_⟩
  rw [hdes]
  exact design_prov_of_kids hp2.2.2.1 hkids hd0

/-- **The general closing**, memory children included: the same. -/
theorem closeInstsGM_all (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {mb : Std.HashMap Name Res} {K : Name → Prop} {shape t m₀ d₀ r}
    {w w' : Void IO.RealWorld}
    (hins : ∀ x ∈ shape.insts, memChild? x.1 = none → K x.1)
    (hR : ∀ c, K c → EntryOk L c K)
    (hp : PK L mb K w) (hd0 : d₀.modules = [])
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    PK L mb K w' ∧ ∀ (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design),
      r = some (m, d) → m.name = m₀.name ∧ ∀ a ∈ d.modules, IsMem a ∨ IsTop (L.val w') a := by
  obtain ⟨hw, hd, hpv, hkeys⟩ := hp
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hs1 := L.same .synthGet hget
  have hp1 : PK L mb K w1 :=
    ⟨hw1, by rw [hs1.2.2]; exact hd, by rw [hs1.1]; exact hpv, by rw [hs1.1]; exact hkeys⟩
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, hww⟩ := RunsTo.pure_world hr
  obtain ⟨hp2, -, hkids⟩ := mapM_inv
    (fun (x : Name × List Nat × MixedGateBinder) => memChild? x.1 = none → K x.1) L (PK L mb K)
    (fun x w y w' hg hp hy => by
      obtain ⟨c, b, k'⟩ := x
      dsimp only at hy
      cases hmc : memChild? c with
      | some md =>
        rw [hmc] at hy
        obtain ⟨hmy, hwy⟩ := RunsTo.pure_world hy
        rw [hwy, hmy]
        exact ⟨hp, sub_refl _, Or.inl (Tools.ShippingMachineInstG.memChild_eq hmc)⟩
      | none =>
        rw [hmc] at hy
        exact child_ok L hB (hg hmc) (hR _ (hg hmc)) hp hy)
    shape.insts children hins hp1 hch
  rw [hww]
  refine ⟨hp2, fun m d hmd => ?_⟩
  rw [hmd] at heq
  have hdes : d = Sparkle.IR.Machine.designWith children d₀ := closeInstsG_design heq.symm
  refine ⟨closeInstsG_name heq.symm, ?_⟩
  rw [hdes]
  exact design_prov_of_kids hp2.2.2.1 hkids hd0

/-! ## The machine synthesis -/

/-- **A STATEMENT, not derived**: a returning run of the harness on THIS
transition, from an invariant world of positive depth, leaves the cache. -/
def HarnessStill (L : RefLaws mref cref) (declName : Name)
    (bs : List (Name × MixedGateBinder)) (body : Lean.Expr) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (mctx : Meta.Context) (cctx : Core.Context) (b : Bool)
    (w : Void IO.RealWorld) (r : Res) (w' : Void IO.RealWorld),
    InvV L w → L.dval w ≠ 0 →
    RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
      bs body) mctx mref cctx cref w r w' → L.val w' = L.val w

/-- **A run of the machine synthesis, whatever it returns**: the invariant
is kept (`Prov`, the key bound against the START cache); a returned module
is named after the declaration and every module of a returned design is a
memory module or the module of an entry of the end cache. Relative to
`HarnessStill` of the transition and `EntryOk` of the callees; `hout` is the
harness's result facts (per declaration data:
`Tools.ShippingClosedKinds.closedBody_kinds_of_run`). -/
theorem machine_all (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') {K : Name → Prop}
    {b : Bool} {declName : Name} {shape : MachineShape} {r : Option Res}
    {w w' : Void IO.RealWorld}
    (hstill : HarnessStill L declName shape.binders shape.body)
    (hout : ∀ (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design),
      MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) →
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
      (Sparkle.IR.Machine.closeMachine shape.layout t').name = ofDecl declName ∧
        d₀.modules = [])
    (hinsM : shape.instFields.isEmpty = true → ∀ x ∈ shape.insts, K x.1)
    (hinsG : ∀ x ∈ shape.insts, memChild? x.1 = none → K x.1)
    (hR : ∀ c, K c → EntryOk L c K)
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w') :
    PK L (L.val w) K w' ∧ ∀ (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design),
      r = some (m, d) →
        m.name = ofDecl declName ∧ ∀ a ∈ d.modules, IsMem a ∨ IsTop (L.val w') a := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 : InvV L w1 := harness_inv L hB hH hw run
  have hd1 : L.dval w1 ≠ 0 := by
    rw [harness_depth L hB hH hw run]
    exact hd
  have hv1 : L.val w1 = L.val w := hstill mctx cctx b w (t, d') w1 hw hd run
  have hp1 : PK L (L.val w) K w1 :=
    ⟨hw1, hd1, by rw [hv1]; exact hp, by rw [hv1]; exact keysIn_refl _ _⟩
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    obtain ⟨hnm, hd0⟩ := hout t t' d' run.mreturns hcl
    split at hr
    · obtain ⟨he, hww⟩ := RunsTo.pure_world hr
      rw [hww]
      refine ⟨hp1, fun m d hmd => ?_⟩
      rw [hmd] at he
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hm, hdd⟩ := he
      rw [hm, hdd]
      refine ⟨hnm, fun a ha => ?_⟩
      rw [hd0] at ha
      cases ha
    · split at hr
      · rename_i hf
        obtain ⟨hpk, hres⟩ := closeInstsM_all L hB (hinsM hf) hR hp1 hd0 hr
        refine ⟨hpk, fun m d hmd => ?_⟩
        obtain ⟨hn, hdes⟩ := hres m d hmd
        exact ⟨hn.trans hnm, hdes⟩
      · obtain ⟨hpk, hres⟩ := closeInstsGM_all L hB hinsG hR hp1 hd0 hr
        refine ⟨hpk, fun m d hmd => ?_⟩
        obtain ⟨hn, hdes⟩ := hres m d hmd
        exact ⟨hn.trans hnm, hdes⟩
  · obtain ⟨he, hww⟩ := RunsTo.pure_world hr
    rw [hww]
    refine ⟨hp1, fun m d hmd => ?_⟩
    rw [hmd] at he
    cases he

/-! ## The entry of a machine-route declaration, and of a leaf -/

/-- **A STATEMENT, not derived (route + frame steps)**: a returning core run
of `c` from an invariant world of positive depth is a machine synthesis of
`shape` that returns the run's result; the machine synthesis starts in a
world with the run's start cache (invariant, positive depth) and ends in a
world with the run's end cache. -/
def CoreVia (L : RefLaws mref cref) (c : Name) (shape : MachineShape) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld)
    (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w' : Void IO.RealWorld),
    InvV L w → L.dval w ≠ 0 →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w' →
    ∃ (tenv : Lean.Environment) (b : Bool) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
        mctx mref cctx cref w9 (some (M, D)) w10 ∧
      InvV L w9 ∧ L.dval w9 ≠ 0 ∧ L.val w9 = L.val w ∧ L.val w' = L.val w10

/-- **`EntryOk` of a machine-route declaration.** The keys its run adds are
its callees' and theirs (`K`); the declaration is not one of them (`hc`) —
which is what "the run does not insert its own key" comes down to. -/
theorem entryOk_machine (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') {K : Name → Prop}
    {c : Name} {shape : MachineShape}
    (hvia : CoreVia L c shape)
    (hstill : HarnessStill L c shape.binders shape.body)
    (hout : ∀ {tenv : Lean.Environment} (b : Bool) (t t' : Sparkle.IR.AST.Module)
      (d₀ : Sparkle.IR.AST.Design),
      MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c
        shape.binders shape.body) (t, d₀) →
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
      (Sparkle.IR.Machine.closeMachine shape.layout t').name = ofDecl c ∧ d₀.modules = [])
    (hinsM : shape.instFields.isEmpty = true → ∀ x ∈ shape.insts, K x.1)
    (hinsG : ∀ x ∈ shape.insts, memChild? x.1 = none → K x.1)
    (hR : ∀ c', K c' → EntryOk L c' K) (hc : ¬ K c) : EntryOk L c K := by
  intro mctx cctx w r w' hw hd hp hc0 hrun
  obtain ⟨M', D'⟩ := r
  obtain ⟨M, D, wc, hcore, hval, hname, hmods⟩ := full_split L hrun
  obtain ⟨_, b, w9, w10, hmach, hw9, hd9, hv9, hv10⟩ := hvia mctx cctx w M D wc hw hd hcore
  have hp9 : Prov (L.val w9) := by
    rw [hv9]
    exact hp
  obtain ⟨hpk, hres⟩ := machine_all L hB hH hstill (hout b) hinsM hinsG hR hw9 hd9 hp9 hmach
  obtain ⟨hnm, hdes⟩ := hres M D rfl
  obtain ⟨-, -, hp10, hk10⟩ := hpk
  have hc9 : (L.val w9).get? c = none := by
    rw [hv9]
    exact hc0
  have hfresh : Fresh (L.val w10) c (M, D) := ⟨keysIn_none hk10 hc9 hc, hnm, hdes⟩
  have hk : KeysIn (L.val w) K (L.val w10) := by
    rw [← hv9]
    exact hk10
  rw [hval, hv10]
  exact ⟨hp10, fresh_post hp10 hfresh hname hmods, hk⟩

/-- **A STATEMENT, not derived**: a returning run of the full entry of `c`
from an invariant world of positive depth leaves the cache (a declaration
without children). -/
def EntryStill (L : RefLaws mref cref) (c : Name) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) (r : Res)
    (w' : Void IO.RealWorld),
    InvV L w → L.dval w ≠ 0 →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' → L.val w' = L.val w

/-- **`EntryOk` of a leaf**, from `EntryStill` and the child-side facts every
real compile of it satisfies (`hkid`: the name and a design without modules
— the last two clauses of `Tools.ShippingCallsGate.ChildIface`). -/
theorem entryOk_leaf (L : RefLaws mref cref) {K : Name → Prop} {c : Name}
    (hstill : EntryStill L c)
    (hkid : ∀ y : Res, RealChild mref cref c y → y.1.name = ofDecl c ∧ y.2.modules = []) :
    EntryOk L c K := by
  intro mctx cctx w r w' hw hd hp hc0 hrun
  have hv : L.val w' = L.val w := hstill mctx cctx w r w' hw hd hrun
  obtain ⟨hn, hm⟩ := hkid r (RealChild.of_inv (invW_of_invV L hw) hrun)
  rw [hv]
  refine ⟨hp, ⟨hc0, hn, fun a ha => ?_⟩, keysIn_refl _ _⟩
  rw [hm] at ha
  cases ha

/-! ## Consumption -/

/-- **The closing of a parent from a `Prov` start world**: the built
relative closing `MachineClosesAtS` (any declaration list) fires — the world
the machine synthesis ends in satisfies `Prov`, hence is coherent. Relative
to `HarnessStill` of the parent's transition and `EntryOk` of its callees;
nothing is asked of the parent's own entry. -/
theorem machine_closes_of_entryOk {declName : Name} {shape : MachineShape} (decls : List Name)
    (hS : MachineClosesAtS mctx mref cctx cref declName shape decls)
    (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') {K : Name → Prop} {b : Bool}
    {r : Option Res} {w w' : Void IO.RealWorld}
    (hstill : HarnessStill L declName shape.binders shape.body)
    (hout : ∀ (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design),
      MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) →
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
      (Sparkle.IR.Machine.closeMachine shape.layout t').name = ofDecl declName ∧
        d₀.modules = [])
    (hinsM : shape.instFields.isEmpty = true → ∀ x ∈ shape.insts, K x.1)
    (hinsG : ∀ x ∈ shape.insts, memChild? x.1 = none → K x.1)
    (hR : ∀ c, K c → EntryOk L c K)
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : Prov (L.val w))
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w') : r ≠ none :=
  hS b w r w' (invW_of_invV L hw) (depthPos_of L hd) hr
    (cacheAgrees_of_coherentAt decls
      (coherentAt_of_val L
        (coherent_of_prov (machine_all L hB hH hstill hout hinsM hinsG hR hw hd hp hr).1.2.2.1)))

end Tools.ShippingCacheCoherentCert
