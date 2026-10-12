import Sparkle.Backend.VerilogDesign
import Tools.ShippingMachineLinked

/-! # The design writer prints the endpoints' artifact (finding D; isolated branch `fix/design-writer`)

The design endpoints (`Tools.ShippingNoDesign.machine_design_noDesign`, the
generated `f.machine_design_noDesignNR{n}`, and the heads they come from)
conclude `DesignSV (childMap D.modules) n (checkedOptimize b) …`:

* the top is `checkedOptimize b`, `b` the module of the full entry
  `synthesizeCombinational`;
* an instance's child is `childMap D.modules mn`, the first module named `mn`
  of the CORE run's design `D`, taken as it is (not optimized).

`Sparkle.Backend.Verilog.toVerilogDesignChecked` (what the hierarchical
commands call on this branch) prints `designArtifact d`: the module named
`d.topModule` through `checkedOptimize`, every other module as it is, each by
`emitModule`, joined by a newline. This file relates the two as PURE
statements about lists of modules (no run; the run is in
`Tools.ShippingDesignWriterRun`):

* `toVerilogDesignChecked_eq` — the writer's text is the join of the emitted
  texts of `designArtifact d` (by `rfl`);
* `hier_artifact` — on the design `synthesizeHierarchical` builds
  (`hierDesign b design`, with `design` the core design `D` up to its two
  fields) the printed modules are `D.modules ++ [checkedOptimize b]`, when no
  module of `D` is named as the top and `b` is named as the top;
* `toVerilogDesignChecked_hier` — the same for the text;
* `childMap_artifact_kid` — the lookup the endpoints use (`childMap
  D.modules`) is, wherever it is defined, the lookup in the printed modules.

NOT here: that the text `emitModule m` denotes the runs `DesignSV` speaks
about (`TextRun m` is stated over `EmitSem.emitAssigns/emitRegs/emitMemWrites
(wofOf m) m.body`, a model of the emitted items, not over the string; the
byte-level bridge `Tools.ShippingModulePrintSoundness.emitModule_render`
covers modules whose body is assignments only).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingDesignWriter
open Sparkle.IR.AST
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.Backend.Verilog (emitModule designArtifact toVerilogDesignChecked)
open Tools.ShippingMachineLinked (childMap)

/-- **The writer's text is the join of the emitted texts of the artifact's
modules** (definitional). -/
theorem toVerilogDesignChecked_eq (d : Design) :
    toVerilogDesignChecked d =
      String.intercalate "\n" ((designArtifact d).map emitModule) := rfl

/-- The design `synthesizeHierarchical` builds from the full entry's module
and design (its `design'`, before the name check, which returns it or
throws). -/
def hierDesign (b : Sparkle.IR.AST.Module) (design : Design) : Design :=
  if design.modules.any (·.name == b.name) then design else design.addModule b

/-- The artifact map leaves a list with no module named `t` unchanged. -/
theorem artifact_other (t : String) :
    ∀ (l : List Sparkle.IR.AST.Module), (∀ x ∈ l, x.name ≠ t) →
      (l.map fun m => if m.name == t then checkedOptimize m else m) = l
  | [], _ => rfl
  | x :: l, h => by
    have hx : (x.name == t) = false := by simpa using h x (List.mem_cons_self ..)
    simp only [List.map_cons, hx, Bool.false_eq_true, if_false]
    exact congrArg _ (artifact_other t l (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- The artifact of a design with the top appended last. -/
theorem designArtifact_addModule (D : Design) (b : Sparkle.IR.AST.Module)
    (hno : ∀ x ∈ D.modules, x.name ≠ D.topModule) (htop : b.name = D.topModule) :
    designArtifact (D.addModule b) = D.modules ++ [checkedOptimize b] := by
  show List.map (fun m => if m.name == D.topModule then checkedOptimize m else m)
      (D.modules ++ [b]) = D.modules ++ [checkedOptimize b]
  rw [List.map_append, artifact_other D.topModule D.modules hno]
  simp [htop]

/-- `synthesizeHierarchical` appends the top when no module has its name. -/
theorem hierDesign_fresh {b : Sparkle.IR.AST.Module} {design : Design}
    (hno : ∀ x ∈ design.modules, x.name ≠ b.name) :
    hierDesign b design = design.addModule b := by
  have h : design.modules.any (fun x => x.name == b.name) = false := by
    rw [List.any_eq_false]
    intro x hx
    simpa using hno x hx
  simp [hierDesign, h]

/-- **The modules the writer prints for a hierarchical design are the
endpoints' modules**: the core design's modules as they are, in their order,
then `checkedOptimize b`. -/
theorem hier_artifact {D design : Design} {b : Sparkle.IR.AST.Module}
    (hmods : design.modules = D.modules) (htopD : design.topModule = D.topModule)
    (hno : ∀ x ∈ D.modules, x.name ≠ D.topModule) (htop : b.name = D.topModule) :
    designArtifact (hierDesign b design) = D.modules ++ [checkedOptimize b] := by
  have hd : design = D := by
    cases design
    cases D
    simp only [Design.mk.injEq]
    exact ⟨htopD, hmods⟩
  have hnb : ∀ x ∈ D.modules, x.name ≠ b.name := fun x hx hxe => hno x hx (hxe.trans htop)
  rw [hd, hierDesign_fresh (b := b) (design := D) hnb]
  exact designArtifact_addModule D b hno htop

/-- **The writer's text for a hierarchical design**: the emitted text of
each module of the core design, as it is, then the emitted text of
`checkedOptimize b`, joined by a newline. -/
theorem toVerilogDesignChecked_hier {D design : Design} {b : Sparkle.IR.AST.Module}
    (hmods : design.modules = D.modules) (htopD : design.topModule = D.topModule)
    (hno : ∀ x ∈ D.modules, x.name ≠ D.topModule) (htop : b.name = D.topModule) :
    toVerilogDesignChecked (hierDesign b design) =
      String.intercalate "\n"
        (D.modules.map emitModule ++ [emitModule (checkedOptimize b)]) := by
  show String.intercalate "\n" ((designArtifact (hierDesign b design)).map emitModule) = _
  rw [hier_artifact hmods htopD hno htop, List.map_append] <;> rfl

/-- A module found by name in a list is found in the list extended at the end. -/
theorem moduleByName_append {ms : List Sparkle.IR.AST.Module} {mn : String}
    {c : Sparkle.IR.AST.Module} (t : Sparkle.IR.AST.Module)
    (h : Sparkle.IR.Machine.moduleByName ms mn = some c) :
    Sparkle.IR.Machine.moduleByName (ms ++ [t]) mn = some c := by
  have h' : ms.find? (fun c => c.name == mn) = some c := h
  show (ms ++ [t]).find? (fun c => c.name == mn) = some c
  simp [List.find?_append, h']

/-- **The endpoints' child lookup is the lookup in the printed modules**:
wherever `childMap D.modules` is defined, the printed module list
`D.modules ++ [checkedOptimize b]` gives the same module and width map. -/
theorem childMap_artifact_kid {D : Design} {b : Sparkle.IR.AST.Module} {mn : String}
    {r : Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv}
    (h : childMap D.modules mn = some r) :
    childMap (D.modules ++ [checkedOptimize b]) mn = some r := by
  have h1 : (Sparkle.IR.Machine.moduleByName D.modules mn).map
      (fun c => (c, Sparkle.IR.RegDedup.declWidth c)) = some r := h
  show (Sparkle.IR.Machine.moduleByName (D.modules ++ [checkedOptimize b]) mn).map
      (fun c => (c, Sparkle.IR.RegDedup.declWidth c)) = some r
  cases hm : Sparkle.IR.Machine.moduleByName D.modules mn with
  | none =>
    rw [hm] at h1
    simp at h1
  | some c =>
    rw [moduleByName_append (checkedOptimize b) hm]
    rw [hm] at h1
    exact h1

end Tools.ShippingDesignWriter
