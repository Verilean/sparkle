import Tools.ShippingGen5DCEntryD
import Tools.ShippingMachineLinked
set_option autoImplicit false
-- NOT BUILT: U-TOPNAME, scripts/gen5/DC_CONNECT_SUPPLY_SURVEY.md §13 (freeze 35d1b243 approved). No clean issue-linked build yet.

/-! # DC-CONNECT U-TOPNAME: lookups in `topMap`

Name preservation of the three post-processors, and what `moduleByName` / `childMap` of `topMap f m d` do: unchanged at every name
other than `m.name`, the `map f` of the old lookup at `m.name`. Does NOT transport `TopShips`/`ResetNk` from `D` to `D'` (which
needs a premise on the descendants that this unit does not supply), does not adopt `Post`. -/

open Tools.ShippingGen5DCEntryD (topMap PostEntry)

namespace Tools.ShippingGen5DCEntryN

theorem dropZeroWidthModule_name (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).name = m.name := by
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split <;> rfl

theorem mergeDuplicates_name (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.RegDedup.mergeDuplicates m).name = m.name := by
  unfold Sparkle.IR.RegDedup.mergeDuplicates
  dsimp only
  split
  · split <;> rfl
  · rfl

theorem mergeChecked_name (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.RefineCheck.mergeChecked m).name = m.name := by
  rcases Sparkle.IR.RefineCheck.mergeChecked_cases m with h | h <;> rw [h]
  · exact mergeDuplicates_name m

theorem find_map_ne {f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module} {m : Sparkle.IR.AST.Module} {mn : String}
    (hf : ∀ x, (f x).name = x.name) (hne : mn ≠ m.name) (ms : List Sparkle.IR.AST.Module) :
    (ms.map fun x => if x.name == m.name then f x else x).find? (fun c => c.name == mn) =
      ms.find? (fun c => c.name == mn) := by
  induction ms with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : (x.name == m.name) = true
    · have hxn : x.name = m.name := beq_iff_eq.mp hx
      have hn : (x.name == mn) = false := by
        rw [hxn]; exact beq_false_of_ne (Ne.symm hne)
      rw [List.map_cons, List.find?_cons, List.find?_cons, if_pos hx, hf x, hn]
      exact ih
    · rw [List.map_cons, List.find?_cons, List.find?_cons, if_neg hx, ih]

theorem find_map_self {f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module} {m : Sparkle.IR.AST.Module}
    (hf : ∀ x, (f x).name = x.name) (ms : List Sparkle.IR.AST.Module) :
    (ms.map fun x => if x.name == m.name then f x else x).find? (fun c => c.name == m.name) =
      (ms.find? (fun c => c.name == m.name)).map f := by
  induction ms with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : (x.name == m.name) = true
    · rw [List.map_cons, List.find?_cons, List.find?_cons, if_pos hx, hf x, hx]
      rfl
    · rw [List.map_cons, List.find?_cons, List.find?_cons, if_neg hx]
      cases hxm : (x.name == m.name)
      · exact ih
      · exact absurd hxm hx

theorem moduleByName_topMap_ne {f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {mn : String}
    (hf : ∀ x, (f x).name = x.name) (hne : mn ≠ m.name) :
    Sparkle.IR.Machine.moduleByName (topMap f m d).modules mn = Sparkle.IR.Machine.moduleByName d.modules mn :=
  find_map_ne hf hne d.modules

theorem moduleByName_topMap_self {f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hf : ∀ x, (f x).name = x.name) :
    Sparkle.IR.Machine.moduleByName (topMap f m d).modules m.name =
      (Sparkle.IR.Machine.moduleByName d.modules m.name).map f :=
  find_map_self hf d.modules

theorem childMap_topMap_ne {f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {mn : String}
    (hf : ∀ x, (f x).name = x.name) (hne : mn ≠ m.name) :
    Tools.ShippingMachineLinked.childMap (topMap f m d).modules mn = Tools.ShippingMachineLinked.childMap d.modules mn := by
  unfold Tools.ShippingMachineLinked.childMap
  rw [moduleByName_topMap_ne hf hne]

/-- the two designs of one entry agree on every name other than the top module's -/
theorem postEntry_lookup_ne {b raw : Sparkle.IR.AST.Module} {D D' : Sparkle.IR.AST.Design} {mn : String}
    (h : PostEntry b raw D D') (hne : mn ≠ raw.name) :
    Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn ∧
    Tools.ShippingMachineLinked.childMap D'.modules mn = Tools.ShippingMachineLinked.childMap D.modules mn := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨moduleByName_topMap_ne dropZeroWidthModule_name hne, childMap_topMap_ne dropZeroWidthModule_name hne⟩
  · refine ⟨?_, ?_⟩
    · rw [moduleByName_topMap_ne mergeChecked_name hne, moduleByName_topMap_ne dropZeroWidthModule_name hne]
    · rw [childMap_topMap_ne mergeChecked_name hne, childMap_topMap_ne dropZeroWidthModule_name hne]

end Tools.ShippingGen5DCEntryN
