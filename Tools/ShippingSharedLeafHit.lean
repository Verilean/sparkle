import Tools.ShippingLeafTermKeeps
-- BUILT at the final committed SHA: see REPORT-SR7.md for run names / exits (s1 exit 1, s2 exit 0 on intermediate trees).
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # Shared leaf (`topshare`): a real leaf MISS followed by a real cache HIT of the same key (unit SR7, L8am)

The first call of `synthesizeChild n` is the real leaf miss (`Tools.ShippingLeafBodyCi`/
`Tools.ShippingLeafTermKeeps`, SR6): it inserts the result `y` at key `n`. A later call of `synthesizeChild n`
from a world whose cache holds the entry at `n` is a cache hit and returns that entry. Hence the miss result and
the hit result COINCIDE (`y₂ = y₁`), by the run's cache. SCOPE: this file does NOT mention the two callees' runs
(wrap/wrap3 of `topshare`) nor the modules inside their designs: connecting the leaf modules of the two callee
designs to these two calls is NOT done here, and this is not a `topshare` proof. No equality of two modules /
designs is assumed anywhere.

PROVED here: `synthesizeChild_hit` (hit returns the cache entry, keeps `JQC` and the cache value);
`synthesizeChild_leafMiss_nested_ins` (the SR6 miss with the extra conclusions `JQC O D w'` and
`cv w' = (cv w).insert n y`); `sharedLeaf_nested` (miss then hit, adjacent: `y₂ = y₁`, `CacheClosed`/`KeyTop`/
`CacheCoh` of the end cache); `sharedLeaf_nested_ext` (hit later, at a world whose cache EXTENDS the post-miss
cache). Provenance F1 (child designs of a NON-leaf result are cache-derived) is NOT derived on this route: it is
the clause `CacheClosed (cv w)` at the start and the premise `hext` (`CacheExtends`) for the intermediate run. -/

namespace Tools.ShippingSharedLeafHit
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingLeafKeepCache
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMixedEntrySoundness
open Tools.ShippingLeafBodyCi Tools.ShippingLeafTermKeeps

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **Cache hit.** From a `JQC` world whose cache holds `r` at `n`, `synthesizeChild n` returns `r` and
leaves the world in `JQC` with the same cache value. -/
theorem synthesizeChild_hit (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {n : Name} {r : Res} {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (hhit : (cv w).get? n = some r)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    y = r ∧ JQC O D w' ∧ cv w' = cv w := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hw1⟩ := jqc_cacheGet O hA hw hget
  have hc1 := cacheGet_cv O hA hw hget
  have hc : m.get? n = some r := by rw [hm]; exact hhit
  simp only [hc] at h
  obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
  exact ⟨rfl, hw1, hc1⟩

/-- **The SR6 nested leaf miss, with the cache equation.** Same premises as
`synthesizeChild_leafMiss_nested_final`; additionally: the end world is `JQC O D` and the end cache is the
start cache with `y` inserted at `n`. -/
theorem synthesizeChild_leafMiss_nested_ins (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : D ≠ 0) {n : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w)) (hmiss : (cv w).get? n = none)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    JQC O D w' ∧ cv w' = (cv w).insert n y ∧
    CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CohWith (cv w) y ∧ CacheCoh (cv w') := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hw1⟩ := jqc_cacheGet O hA hw hget
  have hc1 := cacheGet_cv O hA hw hget
  cases hc : m.get? n with
  | some r' => rw [hm] at hc; rw [hmiss] at hc; cases hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hr : RealChildA O n r := RealChildA.of_jqc O hA hw1 hrun
    have hI := seqChild_of_realA O d ok hbody hno outTy entry closes hr
    obtain ⟨hw2, hk2⟩ := hkeep_nestedL O hA hD d.shape hno entry (closes mctx cctx)
      (fun c0 => leafTranslatorKeeps_of_machineData O hA (stableK O (D + 1) c0) d ok hbody)
      w1 r w2 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw2.1.1 hmod).1
    have hj3 := jqc_insert_runs O hA hw2 hr hmod
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    have hcv : cv w' = (cv w).insert n y := by rw [hc3, hk2, hc1]
    have := leafMiss_cacheCoh hcl hk hmiss hI.name hI.design
    rw [hcv]
    exact ⟨hj3, rfl, this⟩

/-- **Cache extension** (a clause on the intermediate run, NOT derived here): every entry of `m` is still
an entry of `m'`. -/
def CacheExtends (m m' : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → m'.get? c = some r

theorem cacheExtends_refl (m : Std.HashMap Name Res) : CacheExtends m m := fun _ _ h => h

theorem cacheExtends_of_eq {m m' : Std.HashMap Name Res} (h : m' = m) : CacheExtends m m' := by
  subst h; exact cacheExtends_refl _

theorem cacheExtends_insert_missing {m : Std.HashMap Name Res} {n : Name} (r : Res)
    (hmiss : m.get? n = none) : CacheExtends m (m.insert n r) := by
  intro c x hx
  by_cases hc : c = n
  · subst hc; rw [hmiss] at hx; cases hx
  · rw [get?_insert_ne m hc]; exact hx

theorem cacheExtends_trans {a b c : Std.HashMap Name Res} (h1 : CacheExtends a b)
    (h2 : CacheExtends b c) : CacheExtends a c := fun x r h => h2 x r (h1 x r h)

/-- **Shared leaf, adjacent calls (nested depth).** The first call of `synthesizeChild n` is the real leaf
miss, the second (from the end world of the first) is the cache hit. The second result IS the first
(`y₂ = y₁`): the two callees' same-named leaf modules are one cache value, with no agreement premise. The end
cache is the start cache with `y₁` inserted, and still satisfies `CacheClosed`/`KeyTop`/`CacheCoh`. -/
theorem sharedLeaf_nested (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : D ≠ 0) {n : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
    {w w1 w2 : Void IO.RealWorld} {y1 y2 : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w)) (hmiss : (cv w).get? n = none)
    (h1 : RunsTo (synthesizeChild n) mctx mref cctx cref w y1 w1)
    (h2 : RunsTo (synthesizeChild n) mctx mref cctx cref w1 y2 w2) :
    y2 = y1 ∧ JQC O D w2 ∧ cv w2 = (cv w).insert n y1 ∧
    CacheClosed (cv w2) ∧ KeyTop (cv w2) ∧ CacheCoh (cv w2) := by
  obtain ⟨hj1, hc1, hcl1, hk1, -, hcoh1⟩ :=
    synthesizeChild_leafMiss_nested_ins O hA hD d ok hbody hno outTy entry closes hw hcl hk hmiss h1
  have hhit : (cv w1).get? n = some y1 := by rw [hc1]; simp
  obtain ⟨hy, hj2, hc2⟩ := synthesizeChild_hit O hA hj1 hhit h2
  refine ⟨hy, hj2, hc2.trans hc1, ?_, ?_, ?_⟩ <;> rw [hc2] <;> assumption

/-- **Shared leaf, the hit later** (e.g. after the rest of the first callee's run). `w2` is any `JQC` world
whose cache extends the post-miss cache (`hext`, a premise about the INTERMEDIATE run, named: not derived
here — the non-leaf callee's nested run is not shown cache-monotone on this route). Then the second call
returns the first call's result. -/
theorem sharedLeaf_nested_ext (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : D ≠ 0) {n : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref n d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref n d.shape)
    {w w1 wm w3 : Void IO.RealWorld} {y1 y2 : Res} (hw : JQC O D w)
    (hcl : CacheClosed (cv w)) (hk : KeyTop (cv w)) (hmiss : (cv w).get? n = none)
    (h1 : RunsTo (synthesizeChild n) mctx mref cctx cref w y1 w1)
    (hwm : JQC O D wm) (hext : CacheExtends (cv w1) (cv wm))
    (h2 : RunsTo (synthesizeChild n) mctx mref cctx cref wm y2 w3) :
    y2 = y1 ∧ JQC O D w3 ∧ cv w3 = cv wm := by
  obtain ⟨-, hc1, -⟩ :=
    synthesizeChild_leafMiss_nested_ins O hA hD d ok hbody hno outTy entry closes hw hcl hk hmiss h1
  have hhit : (cv wm).get? n = some y1 := hext n y1 (by rw [hc1]; simp)
  exact synthesizeChild_hit O hA hwm hhit h2

end Tools.ShippingSharedLeafHit

#print axioms Tools.ShippingSharedLeafHit.synthesizeChild_hit
#print axioms Tools.ShippingSharedLeafHit.synthesizeChild_leafMiss_nested_ins
#print axioms Tools.ShippingSharedLeafHit.sharedLeaf_nested
#print axioms Tools.ShippingSharedLeafHit.sharedLeaf_nested_ext
