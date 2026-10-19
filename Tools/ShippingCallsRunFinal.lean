import Tools.ShippingCallsRunG

/-! # The general closing on a real run: what the cache holds when it ends

`closeInstsGM_run_all` (`Tools/ShippingCallsRunG.lean`) says what the
closing's children are (real children; two entries of one declaration get one
child). It says nothing about the CACHE the closing's `mapM` ends in. This
file adds that: every entry's child is, at the end, the cache's value under
the entry's declaration.

* `mapM_loop_final`: a `mapM` of the memoised entry from a world of positive
  depth — the `k`-th result is the END world's cache value under the `k`-th
  key (the call left it there: `synthesizeChild_post`; every later call kept
  it: `synthesizeChild_pin`), and the end cache extends the start cache.
* `closeInstsGM_run_allF`: `closeInstsGM_run_all` with that clause.

Why: two DIFFERENT entries (different declarations) are related only through
the cache — nothing in `RealChild` relates a child's design to another
child's module (`docs/parallel/A-shared-descendant.md`). A statement about
the modules two different callees share is therefore a statement about the
cache the closing ends in; this file is what lets such a statement be USED.
It proves nothing about what the cache's entries have in common.

WRITTEN, NOT BUILT (par/a-17). ORIGIN DISPATCH: `closeInstsGM_run_allF`
restated on the entries' origins (`hnotag`, over `shape.instTagged`) —
WRITTEN, NOT BUILT against patched compiler (par/o-close). -/
namespace Tools.ShippingCallsRunFinal
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingCallsGate Tools.ShippingCallsAssemblyG Tools.ShippingCallsStmtsG
open Tools.ShippingInstStmtG Tools.ShippingChildInv Tools.ShippingCallsSame
open Tools.ShippingCallsRunG Tools.ShippingInstTagged

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A `mapM` of the memoised entry, from a world of positive depth: the end
cache.** The `k`-th result is the end world's cache value under the `k`-th
key, and every entry of the start cache is an entry of the end cache. -/
theorem mapM_loop_final {α : Type} (f : α → MetaM Res) (key : α → Name) (L : RefLaws mref cref)
    (hf : ∀ x w y w', InvV L w → L.dval w ≠ 0 → RunsTo (f x) mctx mref cctx cref w y w' →
      InvV L w' ∧ L.dval w' = L.dval w ∧ (L.val w').get? (key x) = some y ∧
        (∀ c0 y0, (L.val w).get? c0 = some y0 → (L.val w').get? c0 = some y0)) :
    ∀ (l : List α) (acc r : List Res) w w', InvV L w → L.dval w ≠ 0 →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ (L.val w').get? (key l[k]) = some y) ∧
        (∀ c0 y0, (L.val w).get? c0 = some y0 → (L.val w').get? c0 = some y0)
  | [], acc, r, w, w', _, _, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), fun _ _ h0 => h0⟩
  | x :: xs, acc, r, w, w', hp, hd, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hp1, hd1, hin, hkeep⟩ := hf x w y w1 hp hd hy
    obtain ⟨ys, hr, hlen, hget, hkeep'⟩ :=
      mapM_loop_final f key L hf xs (y :: acc) r w1 w' hp1 (by rw [hd1]; exact hd) h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk => ?_,
      fun c0 y0 h0 => hkeep' c0 y0 (hkeep c0 y0 h0)⟩
    cases k with
    | zero => exact ⟨y, rfl, hkeep' _ _ hin⟩
    | succ k => exact hget k (by simpa using hk)

/-- **A run of the general closing, from an invariant world of positive
depth, no memory ORIGIN** — `closeInstsGM_run_all`, and: each entry's child is
the END world's cache value under the entry's declaration. -/
theorem closeInstsGM_run_allF (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hnotag : ∀ o ∈ shape.instTagged, o.2.child?.isNone = true)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      (children.length = shape.insts.length ∧
        ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
          RealChild mref cref (shape.insts[k]).1 y) ∧
      (∀ (i j : Nat) (c : Name), i < j → (shape.insts.map (·.1))[i]? = some c →
        (shape.insts.map (·.1))[j]? = some c → children[i]? = children[j]?) ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        (L.val w').get? (shape.insts[k]).1 = some y) ∧ InvV L w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hd1 : L.dval w1 ≠ 0 := by rw [(L.same .synthGet hget).2.2]; exact hd
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  have hch' := runs_mapM_congr
    (g := fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) => synthesizeChild x.1) hch
    (fun x hx => by
      obtain ⟨c, o⟩ := x
      have e : o.child? = none := Option.isNone_iff_eq_none.mp (hnotag (c, o) hx)
      dsimp only
      rw [e])
  obtain ⟨ys, hys, hlen, hk, -, hpair, hw2⟩ := mapM_loop_all _
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) => x.1) L
    (fun x w y w' hp hdw hy => by
      obtain ⟨h1, h2, h3, h4⟩ := synthesizeChild_post L hB hp hy
      exact ⟨h1, h2, synthesizeChild_depth L hB hp hy, h3, h4,
        fun c0 y0 h0 => (synthesizeChild_pin L hB hp hdw h0 hy).1⟩)
    shape.instTagged [] children w1 _ hw1 hd1 hch'
  obtain ⟨zs, hzs, -, hfin, -⟩ := mapM_loop_final _
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) => x.1) L
    (fun x w y w' hp hdw hy => by
      obtain ⟨-, h2, h3, -⟩ := synthesizeChild_post L hB hp hy
      exact ⟨h2, synthesizeChild_depth L hB hp hy, h3,
        fun c0 y0 h0 => (synthesizeChild_pin L hB hp hdw h0 hy).1⟩)
    shape.instTagged [] children w1 _ hw1 hd1 hch'
  simp only [List.reverse_nil, List.nil_append] at hys hzs
  subst hys
  subst hzs
  refine ⟨children, heq, ⟨by rw [hlen, instTagged_length], fun k hkl => ?_⟩,
    fun i j c hij hi hj => ?_, fun k hkl => ?_, hw2⟩
  · have hkT : k < shape.instTagged.length := by rw [instTagged_length]; exact hkl
    obtain ⟨y, hy, hre⟩ := hk k hkT
    refine ⟨y, hy, ?_⟩
    rw [← instTagged_getElem_fst shape hkT]
    exact hre
  · rw [← instTagged_map_fst] at hi hj
    exact hpair i j c hij hi hj
  · have hkT : k < shape.instTagged.length := by rw [instTagged_length]; exact hkl
    obtain ⟨y, hy, hget⟩ := hfin k hkT
    refine ⟨y, hy, ?_⟩
    rw [← instTagged_getElem_fst shape hkT]
    exact hget

end Tools.ShippingCallsRunFinal
