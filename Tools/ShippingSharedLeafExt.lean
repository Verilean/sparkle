import Tools.ShippingSharedLeafHit
import Tools.ShippingChildPinC
-- BUILT (unit SR8): e3 exit 0 on the tree committed with this header; see REPORT-SR8.md for the final-SHA run.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # Shared leaf: `hext` (cache monotonicity across a non-leaf callee's nested run) from the PIN, and the F1 insert (unit SR8, L8an)

**Where an insert could overwrite an existing key, or the cache could be reset** (read off the existing
`Tools.ShippingChildPinC` walk, `jqp_insert_runs` / `core_tripleAP`):
* the only cache WRITES inside a nested run are (a) the miss insert of `synthesizeChild n`, which happens only
  when `n` was ABSENT at the cache read of that same call, hence is none of the keys the pin `L` lists
  (`jqp_insert_runs`, hypothesis `hn`, discharged by `synthesizeChild_tripleP` from `pinL` at the read);
  (b) the clear `sparkleChildCache.set {}`, which the entry executes only when the depth read is `0`
  (`core_tripleAP`: the depth-`0` branch is excluded by `1 ≤ D`, the nested branch has NO cache write).
  Inside a nested run the world is `JQC O D` with `D ≥ 1` (the entry bumps the depth to `D + 1`), so (b) cannot
  occur there; the D = 0 entry (and its clear) is the OUTERMOST call only.
So the pin `L := (cv w1).toList` is kept by the whole nested run: `CacheExtends (cv w1) (cv wm)`.

PROVED here (relative to the existing boundary `O`, `hA`, and `T : RefLawsATele`, i.e. exactly the assumptions
of `Tools.ShippingChildPinC.synthesizeChild_pinned`; no new premise, no body premise):
`cacheExtends_of_synthesizeChild` (one run of `synthesizeChild c`, any callee `c`, depth `D ≥ 1`),
`sharedLeaf_nested_ext_run` (`sharedLeaf_nested_ext` with `hext` replaced by one such intermediate run),
and, for F1, the pure `mem_designWith` / `cacheClosed_insert_kids` (a non-leaf result whose design is
`designWith kids d₀` with `d₀` empty and `kids` cache entries, inserted at an absent key into a `CacheClosed`
cache, keeps `CacheClosed`). NOT derived here: `CacheClosed` of the cache AT that insert (see REPORT-SR8). -/

namespace Tools.ShippingSharedLeafExt
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMixedEntrySoundness

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The pin listing every entry of the world's cache holds in that world. -/
theorem pinL_toList (w : Void IO.RealWorld) : pinL (cv w).toList w := by
  intro p hp
  have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
  rw [Std.HashMap.get?_eq_getElem?]
  exact this

/-- A pin that holds in `wm` for the entry list of `m` is `CacheExtends m (cv wm)`. -/
theorem cacheExtends_of_pin {m : Std.HashMap Name Res} {wm : Void IO.RealWorld}
    (h : pinL m.toList wm) : CacheExtends m (cv wm) := by
  intro c r hc
  have hm : (c, r) ∈ m.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
    (by rw [← Std.HashMap.get?_eq_getElem?]; exact hc)
  exact h (c, r) hm

/-- **`hext`, derived: one nested run of `synthesizeChild c` (any callee, leaf or not) from a `JQC O D`
world (`D ≥ 1`) ends in `JQC O D` and its cache EXTENDS the start cache.** Boundary: `O`, `hA`, `T` (the
assumptions of `synthesizeChild_pinned`). -/
theorem cacheExtends_of_synthesizeChild (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D)
    {c : Name} {w wm : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y wm) :
    JQC O D wm ∧ CacheExtends (cv w) (cv wm) := by
  have hT := synthesizeChild_pinned O T hA hD (cv w).toList c
  have hq := runs_of_triple hT ⟨hw, pinL_toList w⟩ h
  exact ⟨hq.2.1.1, cacheExtends_of_pin hq.2.1.2⟩

/-- Two intermediate runs compose (`CacheExtends` is transitive). -/
theorem cacheExtends_of_two_runs (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D)
    {c c' : Name} {w w1 w2 : Void IO.RealWorld} {y y' : Res} (hw : JQC O D w)
    (h1 : RunsTo (synthesizeChild c) mctx mref cctx cref w y w1)
    (h2 : RunsTo (synthesizeChild c') mctx mref cctx cref w1 y' w2) :
    JQC O D w2 ∧ CacheExtends (cv w) (cv w2) := by
  obtain ⟨hj1, he1⟩ := cacheExtends_of_synthesizeChild O T hA hD hw h1
  obtain ⟨hj2, he2⟩ := cacheExtends_of_synthesizeChild O T hA hD hj1 h2
  exact ⟨hj2, cacheExtends_trans he1 he2⟩

/-- **Shared leaf, the hit after one real nested run of ANOTHER callee `c`** (e.g. the non-leaf `wrap3`/`wrap`
whose own body contains the other call): the SR7 `sharedLeaf_nested_ext` with `hext` DERIVED from the pin.
The end of the leaf miss `w1` is the start of the `synthesizeChild c` run (`wm`); the second call of the
leaf key `n` is made from `wm`. Remaining premises (exact): the data premises of the SR6/SR7 leaf miss
(`d`, `ok`, `hbody`, `hno`, `outTy`, `entry`, `closes`), start clauses `hcl`/`hk`/`hmiss`, and the
boundary `O`, `hA`, `T`. NOT a premise: `hext`. -/
theorem sharedLeaf_nested_ext_run (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : D ≠ 0)
    {n c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
    {w w1 wm w3 : Void IO.RealWorld} {y1 yc y2 : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w)) (hmiss : (cv w).get? n = none)
    (h1 : RunsTo (synthesizeChild n) mctx mref cctx cref w y1 w1)
    (hmid : RunsTo (synthesizeChild c) mctx mref cctx cref w1 yc wm)
    (h2 : RunsTo (synthesizeChild n) mctx mref cctx cref wm y2 w3) :
    y2 = y1 ∧ JQC O D w3 ∧ cv w3 = cv wm := by
  obtain ⟨hj1, -, -, -, -, -⟩ :=
    synthesizeChild_leafMiss_nested_ins O hA hD d ok hbody hno outTy entry closes hw hcl hk hmiss h1
  obtain ⟨hjm, hext⟩ := cacheExtends_of_synthesizeChild O T hA (Nat.one_le_iff_ne_zero.mpr hD) hj1 hmid
  exact sharedLeaf_nested_ext O hA hD d ok hbody hno outTy entry closes hw hcl hk hmiss h1 hjm hext h2

/-! ## F1 for a non-leaf result: the pure insert step -/

/-- Members of the folded design: from the start module list or from a child (its design or its top). -/
theorem mem_foldl_designWith (kids : List Res) :
    ∀ (acc : List Sparkle.IR.AST.Module) (a : Sparkle.IR.AST.Module),
      a ∈ kids.foldl (fun acc (x : Res) =>
        (x.2.modules ++ [x.1]).foldl (fun acc c =>
          if acc.any (·.name == c.name) then acc else acc ++ [c]) acc) acc →
      a ∈ acc ∨ ∃ k ∈ kids, a ∈ k.2.modules ∨ a = k.1 := by
  have inner : ∀ (l : List Sparkle.IR.AST.Module) (acc : List Sparkle.IR.AST.Module) (a : Sparkle.IR.AST.Module),
      a ∈ l.foldl (fun acc c => if acc.any (·.name == c.name) then acc else acc ++ [c]) acc →
      a ∈ acc ∨ a ∈ l := by
    intro l
    induction l with
    | nil => intro acc a h; exact Or.inl h
    | cons x xs ih =>
      intro acc a h
      rw [List.foldl_cons] at h
      rcases ih _ a h with h' | h'
      · split at h'
        · exact Or.inl h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact Or.inl h''
          · exact Or.inr (by simp at h''; simp [h''])
      · exact Or.inr (List.mem_cons_of_mem _ h')
  intro acc a
  induction kids generalizing acc with
  | nil => intro h; exact Or.inl h
  | cons k ks ih =>
    intro h
    rw [List.foldl_cons] at h
    rcases ih _ h with h' | ⟨k', hk', hk''⟩
    · rcases inner _ acc a h' with h'' | h''
      · exact Or.inl h''
      · refine Or.inr ⟨k, List.mem_cons_self .., ?_⟩
        rcases List.mem_append.mp h'' with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (by simpa using h3)
    · exact Or.inr ⟨k', List.mem_cons_of_mem _ hk', hk''⟩

/-- Every module of `designWith kids d` is a module of `d` or of a child (its design or its top). -/
theorem mem_designWith {kids : List Res} {d : Design} {a : Sparkle.IR.AST.Module}
    (h : a ∈ (designWith kids d).modules) :
    a ∈ d.modules ∨ ∃ k ∈ kids, a ∈ k.2.modules ∨ a = k.1 :=
  mem_foldl_designWith kids d.modules a h

/-- **F1 for a non-leaf result: the insert step.** `r`'s design is `designWith kids d₀` with `d₀` having no
module of its own, and every child is an entry of the cache `m` (what the pin of `closeInstsGM_runP`/
`mapM_loop_pinG` records at the end of the closing, for non-memory entries). If `m` is `CacheClosed` and `n`
is absent from `m`, then `m.insert n r` is `CacheClosed`. -/
theorem cacheClosed_insert_kids {m : Std.HashMap Name Res} {n : Name} {r : Res} {kids : List Res}
    {d₀ : Design}
    (hcl : CacheClosed m) (hmiss : m.get? n = none) (hr : r.2 = designWith kids d₀)
    (hd₀ : d₀.modules = []) (hkids : ∀ k ∈ kids, ∃ c, m.get? c = some k) :
    CacheClosed (m.insert n r) := by
  intro c x hx a ha
  rcases insert_get_cases hx with ⟨-, hxr⟩ | ⟨hne, hx⟩
  · rw [hxr] at ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨n, r, get?_insert_self m n r, rfl⟩
    · rw [hr] at ha'
      rcases mem_designWith ha' with h0 | ⟨k, hk, hak⟩
      · rw [hd₀] at h0; cases h0
      · obtain ⟨c0, hc0⟩ := hkids k hk
        have hmods : a ∈ ModsOf k := by
          rcases hak with h | h
          · exact List.mem_cons_of_mem _ h
          · rw [h]; exact List.mem_cons_self ..
        obtain ⟨c', r', hr', rfl⟩ := hcl c0 k hc0 a hmods
        have hne' : c' ≠ n := fun e => by subst e; rw [hmiss] at hr'; cases hr'
        exact ⟨c', r', get?_insert_ne m hne' r ▸ hr', rfl⟩
  · obtain ⟨c', r', hr', rfl⟩ := hcl c x hx a ha
    have hne' : c' ≠ n := fun e => by subst e; rw [hmiss] at hr'; cases hr'
    exact ⟨c', r', get?_insert_ne m hne' r ▸ hr', rfl⟩

end Tools.ShippingSharedLeafExt

#print axioms Tools.ShippingSharedLeafExt.cacheExtends_of_synthesizeChild
#print axioms Tools.ShippingSharedLeafExt.cacheExtends_of_two_runs
#print axioms Tools.ShippingSharedLeafExt.sharedLeaf_nested_ext_run
#print axioms Tools.ShippingSharedLeafExt.mem_designWith
#print axioms Tools.ShippingSharedLeafExt.cacheClosed_insert_kids
