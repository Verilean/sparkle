import Tools.ShippingChildCache

/-! # The child cache along the run: an invariant threaded world by world

`CacheReads` (every read of the cache, in any world, returns a sound map) is
replaced here by pre/post conditions on the worlds the run actually passes
through. The runtime is modelled by a `CacheModel`: the cache's value in each
world and the laws of the primitives on it (`get` returns it and keeps it,
`set v` makes it `v`, `modify f` makes it `f` of it), and the frame of the one
other primitive met on the way (reading `sparkleChildSynth` leaves it). These
are GENERIC laws of `IO.Ref` (opaque in the logic) and are explicit theorem
parameters — nothing about the compiler is assumed in them.

The compiler-specific invariant `InvW` (every entry of the cache, in this
world, is a real-entry result) is then PROVED to be kept by the memoised entry
(`synthesizeChild_hoare`: hit — the world unchanged; miss — the real entry,
then the modify of the cache AS IT IS after the child's run, inserting its
real result) and threaded through the closings' children calls
(`closeInstsGM_hoare` / `closeInstsM_hoare`), given that the real entry's
runs keep it (`EntryHoare`: the entry's writers are the depth-0 clear and
`synthesizeChild`'s modify, each of which keeps it — the depth-0 clear by
`cacheInv_empty`, the modify by `cacheInv_insert`). -/
namespace Tools.ShippingChildCacheRun
open Lean Meta
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildSynth (RealChild ChildrenReal)
open Tools.ShippingChildCache (CacheInv cacheInv_empty cacheInv_insert)
open Tools.ShippingMachineEntry (MemChildren machNIn)
open Sparkle.Compiler.Elab

/-- The runtime laws of `sparkleChildCache` (and the frame of reading
`sparkleChildSynth`), in one context: generic `IO.Ref` laws, a parameter. -/
structure CacheModel (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) where
  val : Void IO.RealWorld → Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)
  get : ∀ w m w', RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w' →
    m = val w ∧ val w' = val w
  set : ∀ v w u w', RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' →
    val w' = v
  modify : ∀ (f : Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) →
      Std.HashMap Name (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → val w' = f (val w)
  synthGet : ∀ w r w', RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w r w' →
    val w' = val w

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The cache invariant in a world. -/
def InvW (M : CacheModel mctx mref cctx cref) (w : Void IO.RealWorld) : Prop :=
  CacheInv mctx mref cctx cref (M.val w)

/-- The real entry's runs keep the invariant (a scoped pre/post condition). -/
def EntryHoare (M : CacheModel mctx mref cctx cref) : Prop :=
  ∀ c w y w', InvW M w → RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w' → InvW M w'

/-- After the depth-0 clear the invariant holds. -/
theorem invW_after_clear (M : CacheModel mctx mref cctx cref) {w u w'}
    (h : RunsTo (sparkleChildCache.set {} : MetaM Unit) mctx mref cctx cref w u w') : InvW M w' := by
  unfold InvW; rw [M.set _ _ _ _ h]; exact cacheInv_empty

theorem RunsTo.pure_world {α : Type} {a b : α} {w w' : Void IO.RealWorld}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') : b = a ∧ w' = w := by
  unfold RunsTo at h
  change EST.Out.ok a w = _ at h
  cases h; exact ⟨rfl, rfl⟩

/-- **The memoised entry, world by world.** From a world satisfying the
invariant, a run of `synthesizeChild c` returns a real-entry result and ends in
a world satisfying it: a hit keeps the world's cache; a miss runs the real
entry (keeping it, `EntryHoare`) and then modifies the cache as it is AFTER
that run, inserting the real result. -/
theorem synthesizeChild_hoare (M : CacheModel mctx mref cctx cref) (hE : EntryHoare M)
    {c : Name} {w w' : Void IO.RealWorld} {y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (hw : InvW M w) (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    RealChild mctx mref cctx cref c y ∧ InvW M w' := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hv⟩ := M.get _ _ _ hget
  have hw1 : InvW M w1 := by unfold InvW; rw [hv]; exact hw
  cases hc : m.get? c with
  | some r =>
    simp only [hc] at h
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    refine ⟨?_, hw1⟩
    rw [hm] at hc
    exact hw c _ hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hw2 := hE c w1 r w2 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    have hv3 := M.modify _ _ _ _ hmod
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    have hr : RealChild mctx mref cctx cref c y := ⟨w1, w2, hrun⟩
    refine ⟨hr, ?_⟩
    unfold InvW; rw [hv3]; exact cacheInv_insert hw2 hr

/-- A `List.mapM` run whose steps keep `P` and establish `Q` of each result. -/
theorem mapM_loop_hoare {α β : Type} (f : α → MetaM β) (P : Void IO.RealWorld → Prop)
    (Q : α → β → Prop)
    (hf : ∀ x w y w', P w → RunsTo (f x) mctx mref cctx cref w y w' → Q x y ∧ P w') :
    ∀ (l : List α) (acc r : List β) w w', P w →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ Q l[k] y) ∧ P w'
  | [], acc, r, w, w', hp, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hp⟩
  | x :: xs, acc, r, w, w', hp, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hq, hp1⟩ := hf x w y w1 hp hy
    obtain ⟨ys, hr, hlen, hget, hp'⟩ := mapM_loop_hoare f P Q hf xs (y :: acc) r w1 w' hp1 h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk => ?_, hp'⟩
    cases k with
    | zero => exact ⟨y, rfl, hq⟩
    | succ k =>
      obtain ⟨z, hz, hqz⟩ := hget k (by simpa using hk)
      exact ⟨z, by simpa using hz, by simpa using hqz⟩

theorem mapM_hoare {α β : Type} (f : α → MetaM β) (P : Void IO.RealWorld → Prop)
    (Q : α → β → Prop)
    (hf : ∀ x w y w', P w → RunsTo (f x) mctx mref cctx cref w y w' → Q x y ∧ P w')
    (l : List α) (r : List β) {w w'} (hp : P w)
    (h : RunsTo (l.mapM f) mctx mref cctx cref w r w') :
    r.length = l.length ∧ (∀ k (hk : k < l.length), ∃ y, r[k]? = some y ∧ Q l[k] y) ∧ P w' := by
  obtain ⟨ys, hr, hlen, hget, hp'⟩ := mapM_loop_hoare f P Q hf l [] r w w' hp h
  simp only [List.reverse_nil, List.nil_append] at hr
  subst hr
  exact ⟨hlen, hget, hp'⟩

/-- The ref's content, in this context: a read returns `synthesizeChild`. -/
def RefIsC (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  Tools.ShippingChildCache.RefIs mctx mref cctx cref

/-- **The general closing's children, world by world.** -/
theorem closeInstsGM_hoare (M : CacheModel mctx mref cctx cref) (hE : EntryHoare M)
    (href : RefIsC mctx mref cctx cref)
    {shape t m₀ d₀ m d} {w w'} (hw : InvW M w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧
      ChildrenReal mctx mref cctx cref shape children ∧ InvW M w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  have hw1 : InvW M w1 := by unfold InvW; rw [M.synthGet _ _ _ hget]; exact hw
  have hs := href _ _ _ hget
  subst hs
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoare _ (InvW M)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      Sparkle.Compiler.MachMemory.memChild? x.1 = some y ∨ RealChild mctx mref cctx cref x.1 y)
    (fun x w y w' hp hy => by
      obtain ⟨c, b, k'⟩ := x
      dsimp only at hy ⊢
      cases hmc : Sparkle.Compiler.MachMemory.memChild? c with
      | some md =>
        rw [hmc] at hy
        obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
        exact ⟨Or.inl rfl, hp⟩
      | none =>
        rw [hmc] at hy
        obtain ⟨hrc, hp'⟩ := synthesizeChild_hoare M hE hp hy
        exact ⟨Or.inr hrc, hp'⟩)
    shape.insts children hw1 hch
  exact ⟨children, heq.symm, ⟨hlen, hk⟩, hw2⟩

/-- **The one-output closing's children, world by world.** -/
theorem closeInstsM_hoare (M : CacheModel mctx mref cctx cref) (hE : EntryHoare M)
    (href : RefIsC mctx mref cctx cref)
    {shape t m₀ d₀ m d} {w w'} (hw : InvW M w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      ChildrenReal mctx mref cctx cref shape children ∧ InvW M w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  have hw1 : InvW M w1 := by unfold InvW; rw [M.synthGet _ _ _ hget]; exact hw
  have hs := href _ _ _ hget
  subst hs
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoare _ (InvW M)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      Sparkle.Compiler.MachMemory.memChild? x.1 = some y ∨ RealChild mctx mref cctx cref x.1 y)
    (fun x w y w' hp hy => by
      obtain ⟨hrc, hp'⟩ := synthesizeChild_hoare M hE hp hy
      exact ⟨Or.inr hrc, hp'⟩)
    shape.insts children hw1 hch
  exact ⟨children, heq.symm, ⟨hlen, hk⟩, hw2⟩

end Tools.ShippingChildCacheRun
