import Tools.ShippingKidsChildIfaceM
import Tools.ShippingModuleName

/-! # Names of memory modules among a child's descendants (round par/c-3)

WRITTEN, NOT BUILT.

A kid whose calls are all memory placeholders has, as the names of its
children and descendants (`namesOfP d nameK namesK`,
`Tools/ShippingKidsChildIfaceM.lean`), memory-module names only
(`ModuleName.ofMem …`). No declaration's module has such a name
(`Tools.ShippingModuleName.ofDecl_ne_ofMem`), so the name conditions a
parent's closing asks about that kid's descendants (`hself`, `hparentD`,
`hselfD`, `hdisjD`) hold whatever the declarations are — no `decide` on
names, no premise.

* `AllMem L`: every name of `L` is a memory-module name.
* `ofDecl_not_mem_allMem`: a declaration's module name is not in such a list.
* `namesOfP_allMem`: the names of a kid whose children are all named by
  memory-module names and have such names below them.
* `namesOfP_const_allMem`: the case of one memory module for every entry. -/
namespace Tools.ShippingMemNamesP
open Lean (Name)
open Sparkle.IR.ModuleName
open Tools.ShippingMachineAuto
open Tools.ShippingKidsChildIfaceM

/-- Every name of the list is a memory-module name. -/
def AllMem (L : List String) : Prop :=
  ∀ x ∈ L, ∃ (cb : Bool) (aw dw : Nat), x = ofMem cb aw dw

theorem allMem_nil : AllMem [] := fun _ h => nomatch h

theorem allMem_singleton (cb : Bool) (aw dw : Nat) : AllMem [ofMem cb aw dw] :=
  fun _ h => ⟨cb, aw, dw, List.mem_singleton.mp h⟩

/-- **A declaration's module name is not among memory-module names.** -/
theorem ofDecl_not_mem_allMem (c : Name) {L : List String} (h : AllMem L) : ofDecl c ∉ L := by
  intro hm
  obtain ⟨cb, aw, dw, e⟩ := h _ hm
  exact Tools.ShippingModuleName.ofDecl_ne_ofMem c cb aw dw e

/-- Lists of memory-module names share no name with a list they are not in:
nothing to prove of an EMPTY list. -/
theorem not_mem_nil_of (x : String) : x ∉ ([] : List String) := fun h => nomatch h

/-- **The names of a kid whose children are memory modules.** -/
theorem namesOfP_allMem (d : MachineData) (nameK : Nat → String) (namesK : Nat → List String)
    (hname : ∀ k, k < d.shape.insts.length → ∃ (cb : Bool) (aw dw : Nat), nameK k = ofMem cb aw dw)
    (hnames : ∀ k, k < d.shape.insts.length → AllMem (namesK k)) :
    AllMem (namesOfP d nameK namesK) := by
  intro x hx
  unfold namesOfP at hx
  rcases List.mem_append.mp hx with h | h
  · obtain ⟨k, hk, e⟩ := List.mem_map.mp h
    obtain ⟨cb, aw, dw, e'⟩ := hname k (List.mem_range.mp hk)
    exact ⟨cb, aw, dw, e.symm.trans e'⟩
  · obtain ⟨k, hk, hxk⟩ := List.mem_flatMap.mp h
    exact hnames k (List.mem_range.mp hk) x hxk

/-- One memory module for every entry. -/
theorem namesOfP_const_allMem (d : MachineData) (cb : Bool) (aw dw : Nat) :
    AllMem (namesOfP d (fun _ => ofMem cb aw dw) (fun _ => [ofMem cb aw dw])) :=
  namesOfP_allMem d _ _ (fun _ _ => ⟨cb, aw, dw, rfl⟩) (fun _ _ => allMem_singleton cb aw dw)

end Tools.ShippingMemNamesP
