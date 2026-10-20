import Tools.ShippingMemNamesP
import Tools.ShippingModuleName

/-! # The names below the call entries of a parent of memory machines, by a TAG per entry (round par/e-1)

WRITTEN, NOT BUILT.

The closing of a parent under the general closing
(`Tools.ShippingCallsKidsD.machineClosesAt_of_kidsD`) asks three conditions
about the names below its call entries (`namesK k`): the parent's module name
is in none (`hparentD`), a callee's module name is not below itself
(`hselfD`), and two DIFFERENT callees are separated (`hdisjD`: the first's
name is not below the second, and they share no name below them).

The hand proof for `memParent` (`Tests/Compiler/MemParentClosesTest.lean`
113-135, 180-189) uses that only ONE entry has names below it (`namesT_two`).
A generator cannot: with two memory-machine callees two entries have names.
Here each entry carries a TAG — `none` for a leaf callee (no name below it),
`some (cb, aw, dw)` for a memory machine whose every call is the placeholder
of that one memory module — and

* `Tagged t L`: every name of `L` is the memory-module name of the tag (so
  `L` has no name when the tag is `none`);
* `Tagged.allMem`: such a list has memory-module names only — `hparentD`,
  `hselfD` and the first half of `hdisjD` follow by the built
  `Tools.ShippingMemNamesP.ofDecl_not_mem_allMem` (a declaration's module
  name is not a memory-module name), whatever the declarations are;
* `tagged_disj`: two lists with DIFFERENT tags (or the first without a tag)
  share no name — by the injectivity of the memory-module name
  (`Tools.ShippingModuleName.ofMem_injective`); the second half of `hdisjD`.
  The condition on the tags is decided per declaration by the generator.

Two different memory-machine callees with the SAME memory module have equal
tags: the condition is false, and so is `hdisjD` itself (the memory module is
a shared descendant — the `mixDeep` obstacle). The generator refuses that
shape; nothing here is about it. -/
namespace Tools.ShippingMemKidTags
open Lean (Name)
open Sparkle.IR.ModuleName
open Tools.ShippingMachineAuto
open Tools.ShippingKidsChildIfaceM Tools.ShippingMemNamesP

/-- Every name of `L` is the memory-module name of the tag `t`; with no tag,
`L` has no name. -/
def Tagged (t : Option (Bool × Nat × Nat)) (L : List String) : Prop :=
  ∀ x ∈ L, ∃ p : Bool × Nat × Nat, t = some p ∧ x = ofMem p.1 p.2.1 p.2.2

/-- The empty list, under any tag. -/
theorem tagged_nil (t : Option (Bool × Nat × Nat)) : Tagged t [] :=
  fun _ h => nomatch h

/-- A tagged list has memory-module names only. -/
theorem Tagged.allMem {t : Option (Bool × Nat × Nat)} {L : List String} (h : Tagged t L) :
    AllMem L := by
  intro x hx
  obtain ⟨p, _, e⟩ := h x hx
  exact ⟨p.1, p.2.1, p.2.2, e⟩

/-- **The names below a memory machine whose every call is the placeholder
of ONE memory module**: all are that module's name. -/
theorem tagged_namesOfP_const (d : MachineData) (cb : Bool) (aw dw : Nat) :
    Tagged (some (cb, aw, dw))
      (namesOfP d (fun _ => ofMem cb aw dw) (fun _ => [ofMem cb aw dw])) := by
  intro x hx
  unfold namesOfP at hx
  rcases List.mem_append.mp hx with h | h
  · obtain ⟨k, _, e⟩ := List.mem_map.mp h
    have e' : ofMem cb aw dw = x := e
    exact ⟨(cb, aw, dw), rfl, e'.symm⟩
  · obtain ⟨k, _, hxk⟩ := List.mem_flatMap.mp h
    have hxk' : x ∈ [ofMem cb aw dw] := hxk
    exact ⟨(cb, aw, dw), rfl, List.mem_singleton.mp hxk'⟩

/-- **Two tagged lists with different tags share no name** (also when the
first has no tag: it has no name). -/
theorem tagged_disj {t t' : Option (Bool × Nat × Nat)} {L L' : List String}
    (h : Tagged t L) (h' : Tagged t' L') (hne : t = none ∨ t ≠ t') :
    ∀ x ∈ L, x ∉ L' := by
  intro x hx hx'
  obtain ⟨p, hp, e⟩ := h x hx
  obtain ⟨p', hp', e'⟩ := h' x hx'
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := p'
  have e1 : x = ofMem p1 p2 p3 := e
  have e2 : x = ofMem q1 q2 q3 := e'
  obtain ⟨a, b, c⟩ := Tools.ShippingModuleName.ofMem_injective (e1.symm.trans e2)
  rcases hne with h0 | h1
  · exact nomatch (h0.symm.trans hp)
  · apply h1
    rw [hp, hp', a, b, c]

end Tools.ShippingMemKidTags
