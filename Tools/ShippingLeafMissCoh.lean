import Tools.ShippingSharedLeafCoh
-- BUILT: s1 exit 1, s2 exit 1 (name/open errors), s3 exit 0 (unit SR4, branch par/u-sr4; base 5f60aef0).
-- UNBUILT (unit SR4): see REPORT-SR4.md for run names / exits.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # One real non-memory LEAF cache miss supplies `CacheClosed` / `CohWith` (unit SR4, L8aj)

Consumer of `Tools.ShippingSharedLeafCoh` for the miss branch of `synthesizeChild` when the nested run
`synthesizeCombinational n` is a machine LEAF (no calls, `seqChild_of_realA`'s premises).

The three facts of F2 (each separate, with its source):
 (a) injectivity of `ModuleName.ofDecl`: PROVED (`Tools.ShippingModuleName.ofDecl_injective`);
 (b) key correspondence `KeyTop m` (`r.1.name = ofDecl c` for every entry `m.get? c = some r`): a CLAUSE on the
     cache; for the entry inserted by a LEAF miss it is PROVED from the run (`ChildIfaceG.name`, from
     `seqChild_of_realA`); for entries of other kinds (non-leaf, memory-bearing) it is NOT derived here
     (the machine route's `transition_closed` name fact is for machine runs only);
 (c) uniqueness of lookup for one key: PROVED (`get?` is a function; `Option.some.inj`).
`cacheTopAgree_of_keyTop`: (a)+(b)+(c) ⇒ F2.

Not derived here: `cv w2 = cv w` for the leaf run (hypothesis `hkeep`, the exact missing step: the leaf run's
effect on the cache is not in the `Triple` infrastructure), and the clauses `CacheClosed`/`KeyTop` of the
cache at the START of the miss. An assumed `hkeep`/`CohWith` is not a closing. -/

namespace Tools.ShippingLeafMissCoh
open Lean Tools.ShippingSharedLeafCoh
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildCacheA Tools.ShippingChildBndCore
open Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineCloses
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildFresh

/-- **(b) key correspondence as a clause.** The top module of the entry at key `c` is named `ofDecl c`. -/
def KeyTop (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → r.1.name = Sparkle.IR.ModuleName.ofDecl c

theorem insert_get_cases {m : Std.HashMap Name Res} {n c : Name} {r x : Res}
    (h : (m.insert n r).get? c = some x) :
    (c = n ∧ x = r) ∨ (c ≠ n ∧ m.get? c = some x) := by
  rw [Std.HashMap.get?_insert] at h
  split at h
  · rename_i hb
    cases h
    exact Or.inl ⟨(beq_iff_eq.mp hb).symm, rfl⟩
  · rename_i hb
    exact Or.inr ⟨fun e => hb (by simp [e]), h⟩

theorem get?_insert_self (m : Std.HashMap Name Res) (n : Name) (r : Res) :
    (m.insert n r).get? n = some r := by simp

theorem get?_insert_ne (m : Std.HashMap Name Res) {n c : Name} (h : c ≠ n) (r : Res) :
    (m.insert n r).get? c = m.get? c := by
  rw [Std.HashMap.get?_insert]
  have : ¬ (n == c) = true := fun e => h (beq_iff_eq.mp e).symm
  simp [this]

theorem keyTop_empty : KeyTop ({} : Std.HashMap Name Res) := by
  intro c r h; simp at h

theorem keyTop_insert {m : Std.HashMap Name Res} {n : Name} {r : Res} (h : KeyTop m)
    (hr : r.1.name = Sparkle.IR.ModuleName.ofDecl n) : KeyTop (m.insert n r) := by
  intro c x hx
  rcases insert_get_cases hx with ⟨rfl, rfl⟩ | ⟨_, hx⟩
  · exact hr
  · exact h c x hx

/-- **F2 from (a)+(b)+(c).** (a) `ofDecl_injective`, (b) `KeyTop`, (c) functionality of `get?`. -/
theorem cacheTopAgree_of_keyTop {m : Std.HashMap Name Res} (h : KeyTop m) : CacheTopAgree m := by
  intro c r c' r' hc hc' hn
  have e : c = c' := Tools.ShippingModuleName.ofDecl_injective ((h c r hc).symm.trans (hn.trans (h c' r' hc')))
  subst e
  have : r = r' := Option.some.inj (hc.symm.trans hc')
  rw [this]

theorem cacheClosed_empty : CacheClosed ({} : Std.HashMap Name Res) := by
  intro c r h; simp at h

/-- **Insert of a leaf entry keeps `CacheClosed`** (no module besides its top; key `n` absent). -/
theorem cacheClosed_insert_leaf {m : Std.HashMap Name Res} {n : Name} {r : Res}
    (h : CacheClosed m) (hmiss : m.get? n = none) (hleaf : r.2.modules = []) :
    CacheClosed (m.insert n r) := by
  intro c x hx a ha
  rcases insert_get_cases hx with ⟨-, hxr⟩ | ⟨hne, hx⟩
  · refine ⟨n, r, get?_insert_self m n r, ?_⟩
    rw [hxr] at ha
    simp only [ModsOf, hleaf, List.mem_cons, List.not_mem_nil, or_false] at ha
    exact ha
  · obtain ⟨c', r', hr', rfl⟩ := h c x hx a ha
    have hne' : c' ≠ n := fun e => by subst e; rw [hmiss] at hr'; cases hr'
    exact ⟨c', r', get?_insert_ne m hne' r ▸ hr', rfl⟩

/-- **`CohWith` of a leaf miss, derived.** From `CacheClosed`, `KeyTop` of the cache, the absence of `n`, and
the leaf facts of the run (name `ofDecl n`, no module besides the top). -/
theorem cohWith_leaf {m : Std.HashMap Name Res} {n : Name} {r : Res}
    (hcl : CacheClosed m) (hk : KeyTop m) (hmiss : m.get? n = none)
    (hname : r.1.name = Sparkle.IR.ModuleName.ofDecl n) (hleaf : r.2.modules = []) :
    CohWith m r := by
  have hmods : ∀ a ∈ ModsOf r, a = r.1 := by
    intro a ha
    simp only [ModsOf, hleaf, List.mem_cons, List.not_mem_nil, or_false] at ha
    exact ha
  -- no old entry has a module named `ofDecl n`
  have hno : ∀ c' r', m.get? c' = some r' → ∀ b ∈ ModsOf r', b.name ≠ Sparkle.IR.ModuleName.ofDecl n := by
    intro c' r' hr' b hb e
    obtain ⟨c'', r'', h'', rfl⟩ := hcl c' r' hr' b hb
    have := Tools.ShippingModuleName.ofDecl_injective ((hk c'' r'' h'').symm.trans e)
    subst this
    rw [hmiss] at h''; cases h''
  refine ⟨fun a ha b hb _ => (hmods a ha).trans (hmods b hb).symm, fun c' r' hr' => ⟨?_, ?_⟩⟩
  · intro a ha b hb hab
    exact absurd (by rw [hmods a ha] at hab; exact (hname.symm.trans hab).symm) (hno c' r' hr' b hb)
  · intro a ha b hb hab
    rw [hmods b hb] at hab
    exact absurd (hab.trans hname) (hno c' r' hr' a ha)

/-- **The leaf miss.** Under the cache clauses before the insert, a leaf result inserted at a missing key keeps
`CacheClosed`, `KeyTop` and `CacheCoh`; `CohWith` is supplied, not assumed. -/
theorem leafMiss_cacheCoh {m : Std.HashMap Name Res} {n : Name} {r : Res}
    (hcl : CacheClosed m) (hk : KeyTop m) (hmiss : m.get? n = none)
    (hname : r.1.name = Sparkle.IR.ModuleName.ofDecl n) (hleaf : r.2.modules = []) :
    CacheClosed (m.insert n r) ∧ KeyTop (m.insert n r) ∧ CohWith m r ∧ CacheCoh (m.insert n r) := by
  have hkn := keyTop_insert hk hname
  have hcn := cacheClosed_insert_leaf hcl hmiss hleaf
  exact ⟨hcn, hkn, cohWith_leaf hcl hk hmiss hname hleaf,
    cacheCoh_of_closed_topAgree hcn (cacheTopAgree_of_keyTop hkn)⟩

/-! ## Scope of `CacheClosed`: memory-origin modules -/

/-- Module names of memory origin (`ofMem`). -/
def MemNamed (s : String) : Prop := ∃ cb aw dw, s = Sparkle.IR.ModuleName.ofMem cb aw dw

/-- **Exclusion / counterexample.** Under `KeyTop`, a cache with an entry whose design contains a memory-origin
module is NOT `CacheClosed` (a memory module is not the top of any cache entry: `ofDecl_ne_ofMem`). So
`CacheClosed` applies only to caches whose entries' designs carry no memory-origin module. -/
theorem not_cacheClosed_of_mem {m : Std.HashMap Name Res} (hk : KeyTop m) {c : Name} {r : Res}
    (hr : m.get? c = some r) {a : Sparkle.IR.AST.Module} (ha : a ∈ ModsOf r) (hmem : MemNamed a.name) :
    ¬ CacheClosed m := by
  intro hcl
  obtain ⟨c', r', h', rfl⟩ := hcl c r hr a ha
  obtain ⟨cb, aw, dw, e⟩ := hmem
  exact Tools.ShippingModuleName.ofDecl_ne_ofMem c' cb aw dw ((hk c' r' h').symm.trans e)

/-- The restriction a consumer uses: closure for the non-memory modules only. -/
def CacheClosedNM (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → ∀ a ∈ ModsOf r, ¬ MemNamed a.name → ∃ c' r', m.get? c' = some r' ∧ a = r'.1

theorem cacheClosedNM_of_closed {m : Std.HashMap Name Res} (h : CacheClosed m) : CacheClosedNM m :=
  fun c r hc a ha _ => h c r hc a ha

/-- Coherence restricted to non-memory-named modules (`CacheCoh` for the memory ones is not claimed). -/
def CacheCohNM (m : Std.HashMap Name Res) : Prop :=
  ∀ c r c' r', m.get? c = some r → m.get? c' = some r' →
    ∀ a ∈ ModsOf r, ∀ b ∈ ModsOf r', ¬ MemNamed a.name → ¬ MemNamed b.name → a.name = b.name → a = b

theorem cacheCohNM_of_closedNM {m : Std.HashMap Name Res} (h1 : CacheClosedNM m) (h2 : CacheTopAgree m) :
    CacheCohNM m := by
  intro c r c' r' hc hc' a ha b hb na nb hab
  obtain ⟨x, rx, hx, rfl⟩ := h1 c r hc a ha na
  obtain ⟨y, ry, hy, rfl⟩ := h1 c' r' hc' b hb nb
  exact h2 x rx y ry hx hy hab

/-- `CacheCohNM` is what `CacheClosedNM` + `KeyTop` give; memory children's agreement must come from elsewhere. -/
theorem cacheCohNM_of_keyTop {m : Std.HashMap Name Res} (h1 : CacheClosedNM m) (hk : KeyTop m) :
    CacheCohNM m := cacheCohNM_of_closedNM h1 (cacheTopAgree_of_keyTop hk)

/-! ## The real miss branch of `synthesizeChild` for a leaf -/

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`synthesizeChild` miss for a machine leaf supplies `CacheClosed`, `KeyTop`, `CohWith`, `CacheCoh`** of the
inserted cache. From the real run: the nested run's result is a `RealChildA` (`RealChildA.of_jqc`), a leaf by
`seqChild_of_realA` (name `ofDecl n`, `design.modules = []`), and the insert is the real `modify`
(`cv w3 = (cv w2).insert n r`). Premises left OPEN and named: `hentry` (as in `synthesizeChild_realA`), `hkeep`
(`cv w2 = cv w`: the leaf run leaves the cache alone; the exact missing step), the cache clauses `CacheClosed`/
`KeyTop` of `cv w`, and the data premises of `seqChild_of_realA`. -/
theorem synthesizeChild_leafMiss (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} {n : Name}
    (hentry : ∀ w1 r1 w2, JQC O D w1 →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 → JQC O D w2)
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
    (hkeep : ∀ w1 r1 w2, JQC O D w1 →
      RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 → cv w2 = cv w)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w y w') :
    CacheClosed (cv w') ∧ KeyTop (cv w') ∧ CohWith (cv w) y ∧ CacheCoh (cv w') := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hw1⟩ := jqc_cacheGet O hA hw hget
  cases hc : m.get? n with
  | some r' => rw [hm] at hc; rw [hmiss] at hc; cases hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hr : RealChildA O n r := RealChildA.of_jqc O hA hw1 hrun
    have hI := seqChild_of_realA O d ok hbody hno outTy entry closes hr
    have hw2 := hentry w1 r w2 hw1 hrun
    have hk2 := hkeep w1 r w2 hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    have hc3 := (O.cacheModify' hA (fun m : Std.HashMap Name Res => m.insert n r) hw2.1.1 hmod).1
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    rw [hc3, hk2]
    obtain ⟨a, b, c, d'⟩ := leafMiss_cacheCoh hcl hk hmiss hI.name hI.design
    exact ⟨a, b, c, d'⟩

end Tools.ShippingLeafMissCoh

#print axioms Tools.ShippingLeafMissCoh.cacheTopAgree_of_keyTop
#print axioms Tools.ShippingLeafMissCoh.cohWith_leaf
#print axioms Tools.ShippingLeafMissCoh.leafMiss_cacheCoh
#print axioms Tools.ShippingLeafMissCoh.not_cacheClosed_of_mem
#print axioms Tools.ShippingLeafMissCoh.cacheCohNM_of_keyTop
#print axioms Tools.ShippingLeafMissCoh.synthesizeChild_leafMiss
