import Tools.ShippingChildCacheA
-- BUILT: c1 exit 1 (GetElem? binder types), c2 exit 0 (unit SR3z, branch par/u-sr3z; base a0c5789e).
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # Shared leaf: F1 (provenance) and F2 (agreement) as typed cache clauses (unit SR3z, L8ai)

PROVED here (pure, about a `Std.HashMap Name Res`): the clause `CacheCoh` (any two modules of one name
occurring in any two cached designs are equal) follows from `CacheClosed` (F1: every module of a cached
design is the top module of a cached entry) and `CacheTopAgree` (F2: two cached tops with one module name
are equal); `CacheCoh` yields the shape of the `hcross` obligation of `closeInstsG_of_kidsPT` for children
that are cache entries; the empty cache and an insert preserve it under a named side condition.

NOT proved here: that `synthesizeChild` / the real entry keeps `CacheCoh` (the side condition of
`cacheCoh_insert` concerns the OUTPUT of `synthesizeCombinational`, outside the `Triple` infrastructure). -/

namespace Tools.ShippingSharedLeafCoh
open Lean

/-- The modules of a result: its top module and its design's modules. -/
def ModsOf (r : Tools.ShippingChildInv.Res) : List Sparkle.IR.AST.Module := r.1 :: r.2.modules

/-- **Coherence clause.** Same-named modules in any two cached designs are equal. -/
def CacheCoh (m : Std.HashMap Name Tools.ShippingChildInv.Res) : Prop :=
  ∀ c r c' r', m.get? c = some r → m.get? c' = some r' →
    ∀ a ∈ ModsOf r, ∀ b ∈ ModsOf r', a.name = b.name → a = b

/-- **F1 (provenance) as a clause.** Every module of a cached design is the top module of a cached entry. -/
def CacheClosed (m : Std.HashMap Name Tools.ShippingChildInv.Res) : Prop :=
  ∀ c r, m.get? c = some r → ∀ a ∈ ModsOf r, ∃ c' r', m.get? c' = some r' ∧ a = r'.1

/-- **F2 (agreement) as a clause.** Two cached tops with one module name are equal. -/
def CacheTopAgree (m : Std.HashMap Name Tools.ShippingChildInv.Res) : Prop :=
  ∀ c r c' r', m.get? c = some r → m.get? c' = some r' → r.1.name = r'.1.name → r.1 = r'.1

theorem cacheCoh_of_closed_topAgree {m : Std.HashMap Name Tools.ShippingChildInv.Res}
    (h1 : CacheClosed m) (h2 : CacheTopAgree m) : CacheCoh m := by
  intro c r c' r' hc hc' a ha b hb hab
  obtain ⟨x, rx, hx, rfl⟩ := h1 c r hc a ha
  obtain ⟨y, ry, hy, rfl⟩ := h1 c' r' hc' b hb
  exact h2 x rx y ry hx hy hab

/-- Conversely `CacheCoh` gives F2 (a top is among the modules of its own entry). -/
theorem cacheTopAgree_of_coh {m : Std.HashMap Name Tools.ShippingChildInv.Res}
    (h : CacheCoh m) : CacheTopAgree m := fun c r c' r' hc hc' hn =>
  h c r c' r' hc hc' r.1 (List.mem_cons_self ..) r'.1 (List.mem_cons_self ..) hn

theorem cacheCoh_empty : CacheCoh ({} : Std.HashMap Name Tools.ShippingChildInv.Res) := by
  intro c r c' r' h
  simp at h

/-- **The `hcross` shape.** Children that are entries of a coherent cache agree on same-named modules
(for every pair, so in particular for the pairs `hcross` asks about). Restricted to children that ARE
cache entries: a memory origin's child (`memModule`) is not a cache entry and is not covered. -/
theorem hcross_of_cacheCoh {m : Std.HashMap Name Tools.ShippingChildInv.Res}
    (h : CacheCoh m) {children : List Tools.ShippingChildInv.Res}
    (hin : ∀ (k : Nat) (c : Tools.ShippingChildInv.Res), children[k]? = some c → ∃ n, m.get? n = some c)
    (i j : Nat) (ci cj : Tools.ShippingChildInv.Res)
    (hci : children[i]? = some ci) (hcj : children[j]? = some cj) :
    ∀ a ∈ ci.1 :: ci.2.modules, ∀ b ∈ cj.1 :: cj.2.modules, a.name = b.name → a = b := by
  obtain ⟨n, hn⟩ := hin i ci hci
  obtain ⟨n', hn'⟩ := hin j cj hcj
  exact h n ci n' cj hn hn'

/-- **Side condition of an insert** (the miss branch of `synthesizeChild`): the new entry is coherent
with itself and with every old entry. -/
def CohWith (m : Std.HashMap Name Tools.ShippingChildInv.Res) (r : Tools.ShippingChildInv.Res) : Prop :=
  (∀ a ∈ ModsOf r, ∀ b ∈ ModsOf r, a.name = b.name → a = b) ∧
  ∀ c' r', m.get? c' = some r' →
    (∀ a ∈ ModsOf r, ∀ b ∈ ModsOf r', a.name = b.name → a = b) ∧
    (∀ a ∈ ModsOf r', ∀ b ∈ ModsOf r, a.name = b.name → a = b)

theorem cacheCoh_insert {m : Std.HashMap Name Tools.ShippingChildInv.Res} {n : Name}
    {r : Tools.ShippingChildInv.Res} (h : CacheCoh m) (hr : CohWith m r) :
    CacheCoh (m.insert n r) := by
  intro c x c' y hx hy
  rw [Std.HashMap.get?_insert] at hx hy
  split at hx <;> split at hy
  · cases hx; cases hy; exact hr.1
  · cases hx
    rename_i _ hne
    exact (hr.2 c' y (by simpa using hy)).1
  · cases hy
    exact (hr.2 c x (by simpa using hx)).2
  · exact h c x c' y hx hy

end Tools.ShippingSharedLeafCoh

#print axioms Tools.ShippingSharedLeafCoh.cacheCoh_of_closed_topAgree
#print axioms Tools.ShippingSharedLeafCoh.hcross_of_cacheCoh
#print axioms Tools.ShippingSharedLeafCoh.cacheCoh_insert
