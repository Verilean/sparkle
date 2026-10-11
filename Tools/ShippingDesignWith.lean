import Sparkle.IR.Machine

/-! # Name resolution in the merged design (`designWith`)

`designWith children d` appends each child's design and module to `d`'s
modules, FIRST of a name wins. An instance is resolved by name
(`moduleByName`). Here, for a parent design without modules and children
whose own designs have none: every child module resolves to ITSELF provided
the children are name-consistent (two of the same name are equal — the same
declaration called twice). Two DIFFERENT modules of one name do not resolve
to themselves: `closeInsts` then returns nothing; that case is outside this
theorem, not excluded by it. Pure. -/
namespace Tools.ShippingDesignWith
open Sparkle.IR.AST Sparkle.IR.Machine

/-- Append unless a module of that name is there. -/
def addM (acc : List Module) (c : Module) : List Module :=
  if acc.any (·.name == c.name) then acc else acc ++ [c]

theorem designWith_flat (children : List (Module × Design)) (d : Design)
    (hc : ∀ c ∈ children, c.2.modules = []) :
    (designWith children d).modules = (children.map (·.1)).foldl addM d.modules := by
  unfold designWith
  simp only
  generalize d.modules = acc
  induction children generalizing acc with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨mc, dc⟩ := c
    have hdc : dc.modules = [] := hc (mc, dc) (List.mem_cons_self ..)
    simp only [List.foldl_cons, List.map_cons, hdc, List.nil_append, List.foldl_nil]
    exact ih (fun c h => hc c (List.mem_cons_of_mem _ h)) _

theorem fold_facts : ∀ (L : List Module) (acc : List Module),
    (acc.map (·.name)).Nodup →
    ((L.foldl addM acc).map (·.name)).Nodup ∧
      (∀ x ∈ L.foldl addM acc, x ∈ acc ∨ x ∈ L) ∧
      (∀ x, x ∈ acc ∨ x ∈ L → ∃ y ∈ L.foldl addM acc, y.name = x.name)
  | [], acc, h => ⟨h, fun x hx => Or.inl hx, fun x hx => hx.elim (fun h => ⟨x, h, rfl⟩)
      (fun h => by cases h)⟩
  | c :: L, acc, h => by
    have hacc : ((addM acc c).map (·.name)).Nodup ∧ (∀ x ∈ addM acc c, x ∈ acc ∨ x = c) ∧
        (∀ x, x ∈ acc ∨ x = c → ∃ y ∈ addM acc c, y.name = x.name) := by
      unfold addM
      by_cases hany : acc.any (·.name == c.name) = true
      · rw [if_pos hany]
        refine ⟨h, fun x hx => Or.inl hx, fun x hx => ?_⟩
        rcases hx with hx | rfl
        · exact ⟨x, hx, rfl⟩
        · obtain ⟨y, hy, he⟩ := List.any_eq_true.mp hany
          exact ⟨y, hy, by simpa using he⟩
      · rw [if_neg hany]
        refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
        · rw [List.map_append, List.nodup_append]
          refine ⟨h, by simp, fun a ha b hb => ?_⟩
          have hb' : b = c.name := by simpa using hb
          subst hb'
          intro e
          obtain ⟨y, hy, hn⟩ := List.mem_map.mp ha
          exact hany (List.any_eq_true.mpr ⟨y, hy, by simpa using hn.trans e⟩)
        · rcases List.mem_append.mp hx with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (by simpa using h1)
        · rcases hx with hx | rfl
          · exact ⟨x, List.mem_append_left _ hx, rfl⟩
          · exact ⟨x, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl⟩
    obtain ⟨n1, s1, c1⟩ := fold_facts L (addM acc c) hacc.1
    refine ⟨n1, fun x hx => ?_, fun x hx => ?_⟩
    · rcases s1 x hx with h1 | h1
      · rcases hacc.2.1 x h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (h2 ▸ List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h1)
    · rcases hx with hx | hx
      · obtain ⟨y, hy, he⟩ := hacc.2.2 x (Or.inl hx)
        obtain ⟨z, hz, he'⟩ := c1 y (Or.inl hy)
        exact ⟨z, hz, he'.trans he⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · obtain ⟨y, hy, he⟩ := hacc.2.2 x (Or.inr rfl)
          obtain ⟨z, hz, he'⟩ := c1 y (Or.inl hy)
          exact ⟨z, hz, he'.trans he⟩
        · exact c1 x (Or.inr hx)

theorem find_of_nodup : ∀ (R : List Module), (R.map (·.name)).Nodup → ∀ y ∈ R,
    moduleByName R y.name = some y
  | c :: R, h, y, hy => by
    have h' := List.nodup_cons.mp (show (c.name :: R.map (·.name)).Nodup from h)
    unfold moduleByName
    rw [List.find?_cons]
    by_cases he : (c.name == y.name) = true
    · rw [he]
      rcases List.mem_cons.mp hy with rfl | hy
      · rfl
      · have hcy : c.name = y.name := by simpa using he
        exact absurd (List.mem_map.mpr ⟨y, hy, rfl⟩) (hcy ▸ h'.1)
    · have hne : (c.name == y.name) = false := by simpa using he
      rw [hne]
      rcases List.mem_cons.mp hy with rfl | hy
      · simp at he
      · exact find_of_nodup R h'.2 y hy

/-- **Every child resolves to itself**, in a design built from none, for
name-consistent children without designs of their own; and the merged
design's modules are children's modules. -/
theorem designWith_resolves {children : List (Module × Design)} {d : Design}
    (hd : d.modules = []) (hc : ∀ c ∈ children, c.2.modules = [])
    (hcons : ∀ a ∈ children, ∀ b ∈ children, a.1.name = b.1.name → a.1 = b.1) :
    (∀ c ∈ children, moduleByName (designWith children d).modules c.1.name = some c.1) ∧
    (∀ g ∈ (designWith children d).modules, ∃ c ∈ children, g = c.1) := by
  rw [designWith_flat children d hc, hd]
  obtain ⟨hn, hs, hcv⟩ := fold_facts (children.map (·.1)) [] (by simp)
  have hmem : ∀ g ∈ (children.map (·.1)).foldl addM [], ∃ c ∈ children, g = c.1 := by
    intro g hg
    rcases hs g hg with h | h
    · cases h
    · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp h
      exact ⟨c, hc', rfl⟩
  refine ⟨fun c hc' => ?_, hmem⟩
  obtain ⟨y, hy, he⟩ := hcv c.1 (Or.inr (List.mem_map_of_mem hc'))
  obtain ⟨c2, hc2, rfl⟩ := hmem y hy
  have : c2.1 = c.1 := hcons c2 hc2 c hc' he
  rw [← he, find_of_nodup _ hn _ hy, this]

end Tools.ShippingDesignWith
