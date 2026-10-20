import Tools.ShippingDesignWith
import Sparkle.Compiler.MachMemory

/-! # Name resolution in the merged design, children with designs of their own

`designWith children d` over children whose OWN designs have modules (a child
with calls: its design holds its children's modules and theirs). With `U` the
modules the join visits — each child's design modules, then the child — and a
parent design without modules: if `U` is name-consistent (two of one name are
equal), every module of `U` resolves to ITSELF and the merged design's
modules are modules of `U`. Name consistency is the hypothesis — that two
compiles of one declaration are one module, and different declarations print
differently, is a fact about the run (the child cache) and the names, not
proved here. Pure. -/
namespace Tools.ShippingDesignWithG
open Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingDesignWith

/-- The modules the join visits, in order. -/
def visited (children : List (Module × Design)) : List Module :=
  children.flatMap fun c => c.2.modules ++ [c.1]

theorem designWith_flatG (children : List (Module × Design)) (d : Design) :
    (designWith children d).modules = (visited children).foldl addM d.modules := by
  unfold designWith visited
  simp only
  generalize d.modules = acc
  induction children generalizing acc with
  | nil => rfl
  | cons c rest ih =>
    rw [List.foldl_cons, List.flatMap_cons]
    refine (ih _).trans ?_
    exact (List.foldl_append ..).symm

/-- **Every visited module resolves to itself**, in a design built from none,
when the visited modules are name-consistent; and the merged design's modules
are visited modules. -/
theorem designWith_resolvesG {children : List (Module × Design)} {d : Design}
    (hd : d.modules = [])
    (hcons : ∀ a ∈ visited children, ∀ b ∈ visited children, a.name = b.name → a = b) :
    (∀ g ∈ visited children, moduleByName (designWith children d).modules g.name = some g) ∧
    (∀ g ∈ (designWith children d).modules, g ∈ visited children) := by
  rw [designWith_flatG children d, hd]
  obtain ⟨hn, hs, hcv⟩ := fold_facts (visited children) [] (by simp)
  have hmem : ∀ g ∈ (visited children).foldl addM [], g ∈ visited children := by
    intro g hg
    rcases hs g hg with h | h
    · cases h
    · exact h
  refine ⟨fun g hg => ?_, hmem⟩
  obtain ⟨y, hy, he⟩ := hcv g (Or.inr hg)
  have : y = g := hcons y (hmem y hy) g hg he
  subst this
  exact find_of_nodup _ hn y hy

/-- The joined design of a parent design without modules: distinct names,
every module a visited one — whatever the children. -/
theorem designWith_modules {children : List (Module × Design)} {d : Design}
    (hd : d.modules = []) :
    ((designWith children d).modules.map (·.name)).Nodup ∧
    ∀ g ∈ (designWith children d).modules, g ∈ visited children := by
  rw [designWith_flatG children d, hd]
  obtain ⟨hn, hs, -⟩ := fold_facts (visited children) [] (by simp)
  refine ⟨hn, fun g hg => ?_⟩
  rcases hs g hg with h | h
  · cases h
  · exact h

theorem mem_visited {children : List (Module × Design)} {g : Module} :
    g ∈ visited children ↔ ∃ c ∈ children, g = c.1 ∨ g ∈ c.2.modules := by
  unfold visited
  simp only [List.mem_flatMap, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨c, hc, h | h⟩
    · exact ⟨c, hc, Or.inr h⟩
    · exact ⟨c, hc, Or.inl h⟩
  · rintro ⟨c, hc, h | h⟩
    · exact ⟨c, hc, Or.inr h⟩
    · exact ⟨c, hc, Or.inl h⟩

/-- **The design checks of the general closing**, from name consistency of
the visited modules and two facts about each: it is not a memory-shaped body
unless found as one (`hmem`), and it has no instance of the parent. -/
theorem design_checks {children : List (Module × Design)} {d : Design} {parent : String}
    (hd : d.modules = [])
    (hcons : ∀ a ∈ visited children, ∀ b ∈ visited children, a.name = b.name → a = b)
    (hmem : ∀ c ∈ children, Sparkle.Compiler.MachMemory.memParams? c.1 = none)
    (hno : ∀ g ∈ visited children, noInstOfB parent g.body = true) :
    children.all (fun c => Sparkle.Compiler.MachMemory.memSelf
      (moduleByName (designWith children d).modules) c.1) = true ∧
    children.all (fun c =>
      decide (moduleByName (designWith children d).modules c.1.name = some c.1) &&
      c.2.modules.all (fun g =>
        decide (moduleByName (designWith children d).modules g.name = some g))) = true ∧
    (designWith children d).modules.all (fun g => noInstOfB parent g.body) = true := by
  obtain ⟨hres, hmods⟩ := designWith_resolvesG hd hcons
  refine ⟨?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro c hc
    unfold Sparkle.Compiler.MachMemory.memSelf
    rw [hmem c hc]
  · rw [List.all_eq_true]
    intro c hc
    rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨hres c.1 (mem_visited.mpr ⟨c, hc, Or.inl rfl⟩), fun g hg => ?_⟩
    rw [decide_eq_true_eq]
    exact hres g (mem_visited.mpr ⟨c, hc, Or.inr hg⟩)
  · rw [List.all_eq_true]
    intro g hg
    exact hno g (hmods g hg)

end Tools.ShippingDesignWithG
