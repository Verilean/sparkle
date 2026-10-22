import Tools.ShippingSharedLeafExt
import Tools.ShippingMemOnlyNames
-- BUILT (unit SRM1): c1 exit 0 (dev run); the final-SHA rebuild is in REPORT-SRM1.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # Shared leaf with a MEMORY child: the cache clauses (unit SRM1, ledger L8bd)

SCOPE.  The shared-leaf chain (`Tools/ShippingSharedLeaf*.lean`, `Tools/ShippingTopShare*.lean`, `Tools/ShippingQuad*.lean`, `Tools/ShippingKary*.lean`) keeps the cache clause
`CacheClosed` (every module of a cached design is the top module of a cached entry) and derives `CacheCoh` from it.  A cache entry whose design carries a MEMORY module is
NOT `CacheClosed` (`Tools.ShippingLeafMissCoh.not_cacheClosed_of_mem`: a memory module is never the top of a cache entry, under `KeyTop`), so the chain cannot be applied to a shared
leaf (or a callee) that has a memory child.  PROVED here (pure facts about a `Std.HashMap Name Res`): the replacement pair `CacheClosedNM` (the existing
`Tools.ShippingLeafMissCoh.CacheClosedNM`: closure for the non-memory-named modules) and `MemDet` (a memory-named module of a cached design IS the built `memModule cb aw dw`),
which together with `KeyTop` give `CacheCoh` (`cacheCoh_of_nm`), and the insert lemmas for a result whose design is `designWith kids d₀` with every kid a cache entry or a built
memory module.  A memory module as a kid is justified by the memory ORIGIN of the call (`child? = some md` and `md = memModule …`), not by the cache.
NOT proved here: that a real run keeps these clauses (`Tools/ShippingMemLeafRun.lean`), nor anything about interfaces / `KidFactsA` of a machine with a memory child. -/

namespace Tools.ShippingMemLeafCache
open Lean
open Tools.ShippingChildInv Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafExt
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.Compiler.MachMemory

/-- the built memory module of the parameters, as a cache entry (`MachMemory.memModule`) is NOT a cache key's value; this is the module itself -/
def MemMod (a : Sparkle.IR.AST.Module) : Prop := ∃ cb aw dw, a = (memModule cb aw dw).1

/-- **Memory modules of cached designs are the built ones.** -/
def MemDet (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → ∀ a ∈ ModsOf r, MemNamed a.name → MemMod a

/-- a kid of a closing: a built memory child (the child of a memory origin) -/
def MemKid (k : Res) : Prop := ∃ cb aw dw, k = memModule cb aw dw

theorem memModule_memNamed (cb : Bool) (aw dw : Nat) : MemNamed (memModule cb aw dw).1.name :=
  ⟨cb, aw, dw, Tools.ShippingMemOnlyNames.memModule_name cb aw dw⟩

theorem memDet_empty : MemDet ({} : Std.HashMap Name Res) := by
  intro c r h; simp at h

theorem cacheClosedNM_empty : CacheClosedNM ({} : Std.HashMap Name Res) := by
  intro c r h; simp at h

/-- the modules of a built memory kid are built memory modules -/
theorem mods_of_memKid {k : Res} (h : MemKid k) {a : Sparkle.IR.AST.Module}
    (ha : a ∈ k.2.modules ∨ a = k.1) : MemMod a := by
  obtain ⟨cb, aw, dw, rfl⟩ := h
  have e : (memModule cb aw dw).2.modules = [(memModule cb aw dw).1] := rfl
  rcases ha with ha | ha
  · rw [e] at ha
    exact ⟨cb, aw, dw, List.mem_singleton.mp ha⟩
  · exact ⟨cb, aw, dw, ha⟩

theorem memMod_memNamed {a : Sparkle.IR.AST.Module} (h : MemMod a) : MemNamed a.name := by
  obtain ⟨cb, aw, dw, rfl⟩ := h
  exact memModule_memNamed cb aw dw

/-- **`CacheCoh` from the memory-aware clauses.**  `CacheClosedNM` + `KeyTop` + `MemDet` give the coherence the chain needs, although `CacheClosed` itself is false
of a cache with a memory-bearing entry. -/
theorem cacheCoh_of_nm {m : Std.HashMap Name Res} (h1 : CacheClosedNM m) (hk : KeyTop m) (h3 : MemDet m) :
    CacheCoh m := by
  intro c r c' r' hc hc' a ha b hb hab
  by_cases hma : MemNamed a.name
  · have hmb : MemNamed b.name := hab ▸ hma
    obtain ⟨cb, aw, dw, rfl⟩ := h3 c r hc a ha hma
    obtain ⟨cb', aw', dw', rfl⟩ := h3 c' r' hc' b hb hmb
    have hn := hab
    rw [Tools.ShippingMemOnlyNames.memModule_name, Tools.ShippingMemOnlyNames.memModule_name] at hn
    obtain ⟨e1, e2, e3⟩ := Tools.ShippingModuleName.ofMem_injective hn
    subst e1 e2 e3
    rfl
  · have hmb : ¬ MemNamed b.name := fun h => hma (hab ▸ h)
    obtain ⟨x, rx, hx, rfl⟩ := h1 c r hc a ha hma
    obtain ⟨y, ry, hy, rfl⟩ := h1 c' r' hc' b hb hmb
    exact cacheTopAgree_of_keyTop hk x rx y ry hx hy hab

/-- the modules of an entry that is (the design of) a cache entry or a built memory kid -/
private theorem kid_mods_sub {k : Res} {a : Sparkle.IR.AST.Module}
    (hak : a ∈ k.2.modules ∨ a = k.1) : a ∈ ModsOf k := by
  rcases hak with h | h
  · exact List.mem_cons_of_mem _ h
  · rw [h]; exact List.mem_cons_self ..

/-- **`CacheClosedNM` of an insert.**  `r`'s design is `designWith kids d₀` (`d₀` without modules); every kid is a cache entry or a built memory kid. -/
theorem cacheClosedNM_insert_kids {m : Std.HashMap Name Res} {n : Name} {r : Res} {kids : List Res}
    {d₀ : Design}
    (hcl : CacheClosedNM m) (hmiss : m.get? n = none) (hr : r.2 = designWith kids d₀)
    (hd₀ : d₀.modules = []) (hkids : ∀ k ∈ kids, (∃ c, m.get? c = some k) ∨ MemKid k) :
    CacheClosedNM (m.insert n r) := by
  intro c x hx a ha hna
  rcases insert_get_cases hx with ⟨-, hxr⟩ | ⟨hne, hx⟩
  · rw [hxr] at ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨n, r, get?_insert_self m n r, rfl⟩
    · rw [hr] at ha'
      rcases mem_designWith ha' with h0 | ⟨k, hk, hak⟩
      · rw [hd₀] at h0; cases h0
      · rcases hkids k hk with ⟨c0, hc0⟩ | hmk
        · obtain ⟨c', r', hr', rfl⟩ := hcl c0 k hc0 a (kid_mods_sub hak) hna
          have hne' : c' ≠ n := fun e => by subst e; rw [hmiss] at hr'; cases hr'
          exact ⟨c', r', get?_insert_ne m hne' r ▸ hr', rfl⟩
        · exact absurd (memMod_memNamed (mods_of_memKid hmk hak)) hna
  · obtain ⟨c', r', hr', rfl⟩ := hcl c x hx a ha hna
    have hne' : c' ≠ n := fun e => by subst e; rw [hmiss] at hr'; cases hr'
    exact ⟨c', r', get?_insert_ne m hne' r ▸ hr', rfl⟩

/-- **`MemDet` of an insert.**  Same shape; `r`'s top module is named like the declaration `n` (so it is not memory-named). -/
theorem memDet_insert_kids {m : Std.HashMap Name Res} {n : Name} {r : Res} {kids : List Res}
    {d₀ : Design}
    (hmd : MemDet m) (hrname : r.1.name = Sparkle.IR.ModuleName.ofDecl n) (hr : r.2 = designWith kids d₀)
    (hd₀ : d₀.modules = []) (hkids : ∀ k ∈ kids, (∃ c, m.get? c = some k) ∨ MemKid k) :
    MemDet (m.insert n r) := by
  intro c x hx a ha hma
  rcases insert_get_cases hx with ⟨-, hxr⟩ | ⟨hne, hx⟩
  · rw [hxr] at ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · obtain ⟨cb, aw, dw, e⟩ := hma
      exact absurd (hrname.symm.trans e) (Tools.ShippingModuleName.ofDecl_ne_ofMem n cb aw dw)
    · rw [hr] at ha'
      rcases mem_designWith ha' with h0 | ⟨k, hk, hak⟩
      · rw [hd₀] at h0; cases h0
      · rcases hkids k hk with ⟨c0, hc0⟩ | hmk
        · exact hmd c0 k hc0 a (kid_mods_sub hak) hma
        · exact mods_of_memKid hmk hak
  · exact hmd c x hx a ha hma

end Tools.ShippingMemLeafCache

#print axioms Tools.ShippingMemLeafCache.cacheCoh_of_nm
#print axioms Tools.ShippingMemLeafCache.cacheClosedNM_insert_kids
#print axioms Tools.ShippingMemLeafCache.memDet_insert_kids
