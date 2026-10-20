import Tools.ShippingHierOpen
import Tools.ShippingHierState
import Tools.ShippingHierMono
import Tools.ShippingMachineLinked
import Sparkle.IR.RefineCheck

/-! # The shipping theorems' module premises, as checkers

The shipping theorems for machines with instances (`machine_ships_hier`,
`machine_ships_hierH`) need facts about the modules of the run: the
optimizer check binds, the bodies are linked-well-formed, instance names are
distinct, no instance reads its own output, the instance-driven wires are
extracted inputs of the check, … Each is a decidable CHECKER here, with its
soundness lemma (`checker = true ⇒ the semantic fact the proof uses`), and
the shipping theorems take one bundled checker per route (`hierCheck`,
`shipsHierCheck`, `shipsHierHCheck`) — what a run's modules satisfy is then
one evaluation of the checker the theorem names. The depth boundary's
structural facts (`ExtendsAway`, `NoInstOf`) get checkers too
(`extendsAwayB`, `noInstOfB`). -/
namespace Tools.ShippingHierPremisesBase
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingMachineLinked
open Tools.ShippingHierMono (NoInstOf ExtendsAway)

/-- No instance reads (through an input connection) a wire one of its own
outputs drives. -/
def noSelfRead (C : String → Option (Module × WEnv)) (body : List Stmt) : Bool :=
  body.all fun st => match st with
    | .inst mn _ conns => match C mn with
      | some (child, _) => (inConns child.outputs conns).all fun c => match c.2 with
        | .ref w => !(instOutWires child.outputs conns).contains w
        | _ => true
      | none => true
    | _ => true

theorem noSelfRead_sound {C : String → Option (Module × WEnv)} {body : List Stmt}
    (h : noSelfRead C body = true) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
      C mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns := by
  intro mn iname conns hm child cwe hc c hcin w hw
  have h1 := List.all_eq_true.mp h _ hm
  simp only [hc] at h1
  have h2 := List.all_eq_true.mp h1 c hcin
  rw [hw] at h2
  simpa [List.contains_eq_mem] using h2

/-- Every instance-driven wire is an extracted input of the optimizer check. -/
def outsExtracted (C : String → Option (Module × WEnv)) (b : Module) : Bool :=
  (bodyInstOuts C b.body).all fun w =>
    ((Sparkle.IR.HierCheck.openIns b).map (·.name)).contains w

theorem outsExtracted_sound {C : String → Option (Module × WEnv)} {b : Module}
    (h : outsExtracted C b = true) :
    ∀ w ∈ bodyInstOuts C b.body, w ∈ (Sparkle.IR.HierCheck.openIns b).map (·.name) := by
  intro w hw
  have := List.all_eq_true.mp h w hw
  simpa [List.contains_eq_mem] using this

/-- The facts common to both instance routes, on the full entry's module `b`
and its shipped optimization `checkedOptimize b`. (`b`'s own linked
well-formedness is not here: the wiring gives it, `linkedOk_eq`.) -/
def hierCheck (C : String → Option (Module × WEnv)) (b : Module) : Bool :=
  Sparkle.IR.RefineCheck.hierBinds b &&
    linkedWF C (checkedOptimize b).body &&
    decide (instNames b.body).Nodup && decide (instNames (checkedOptimize b).body).Nodup &&
    noSelfRead C (checkedOptimize b).body && outsExtracted C b &&
    (b.inputs.map (·.name)).contains "rst"

/-- What `hierCheck` gives. -/
structure HierFacts (C : String → Option (Module × WEnv)) (b : Module) : Prop where
  binds : Sparkle.IR.RefineCheck.hierBinds b = true
  wfO : linkedWF C (checkedOptimize b).body = true
  ndB : (instNames b.body).Nodup
  ndO : (instNames (checkedOptimize b).body).Nodup
  nofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → ∀ child cwe,
    C mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
      c.2 = .ref w → w ∉ instOutWires child.outputs conns
  outs : ∀ w ∈ bodyInstOuts C b.body, w ∈ (Sparkle.IR.HierCheck.openIns b).map (·.name)
  rst : "rst" ∈ b.inputs.map (·.name)

theorem hierCheck_sound {C : String → Option (Module × WEnv)} {b : Module}
    (h : hierCheck C b = true) : HierFacts C b := by
  simp only [hierCheck, Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨hb, hw⟩, hn1⟩, hn2⟩, hs⟩, ho⟩, hr⟩ := h
  exact ⟨hb, hw, hn1, hn2, noSelfRead_sound hs, outsExtracted_sound ho, by simpa using hr⟩

/-- The checker of the sequential / memory route (`machine_ships_hier`):
the common facts and the instance-output widths. -/
def shipsHierCheck (C : String → Option (Module × WEnv)) (b : Module) : Bool :=
  hierCheck C b && instOutWidthsOk C (declWidth b) b.body

theorem shipsHierCheck_sound {C : String → Option (Module × WEnv)} {b : Module}
    (h : shipsHierCheck C b = true) :
    HierFacts C b ∧ instOutWidthsOk C (declWidth b) b.body = true := by
  simp only [shipsHierCheck, Bool.and_eq_true] at h
  exact ⟨hierCheck_sound h.1, h.2⟩

/-! ## The depth boundary's structural facts -/

/-- No instance of `t` in `body`. -/
def noInstOfB (t : String) (body : List Stmt) : Bool :=
  body.all fun st => match st with
    | .inst mn _ _ => mn != t
    | _ => true

theorem noInstOfB_sound {t : String} {body : List Stmt} (h : noInstOfB t body = true) :
    NoInstOf t body := by
  intro mn iname conns hm heq
  have := List.all_eq_true.mp h _ hm
  simp [heq] at this

theorem childMap_some' {ms : List Module} {mn : String} {r : Module × WEnv} :
    childMap ms mn = some r →
      ∃ x, Sparkle.IR.Machine.moduleByName ms mn = some x ∧ r = (x, declWidth x) := by
  unfold childMap
  cases h : Sparkle.IR.Machine.moduleByName ms mn with
  | none => simp
  | some x => intro hr; simp only [Option.map_some, Option.some.injEq] at hr; exact ⟨x, rfl, hr.symm⟩

theorem moduleByName_mem {ms : List Module} {x : String} {c : Module}
    (h : Sparkle.IR.Machine.moduleByName ms x = some c) : c ∈ ms ∧ c.name = x := by
  unfold Sparkle.IR.Machine.moduleByName at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- `ms₂` finds every module of `ms₁` but `t`'s as `ms₁` does, and no module
of `ms₁` instantiates `t`. -/
def extendsAwayB (t : String) (ms₁ ms₂ : List Module) : Bool :=
  ms₁.all (fun c => c.name == t ||
      decide (Sparkle.IR.Machine.moduleByName ms₂ c.name = Sparkle.IR.Machine.moduleByName ms₁ c.name)) &&
    ms₁.all (fun c => noInstOfB t c.body)

theorem extendsAwayB_sound {t : String} {ms₁ ms₂ : List Module}
    (h : extendsAwayB t ms₁ ms₂ = true) : ExtendsAway t (childMap ms₁) (childMap ms₂) := by
  simp only [extendsAwayB, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro x r hx hr
    obtain ⟨c, hc, rfl⟩ := childMap_some' hr
    obtain ⟨hmem, hname⟩ := moduleByName_mem hc
    have h3 := List.all_eq_true.mp h1 c hmem
    rw [hname] at h3
    have hne : (x == t) = false := by simpa using hx
    simp only [hne, Bool.false_or, decide_eq_true_eq] at h3
    show childMap ms₂ x = some (c, declWidth c)
    simp only [childMap, h3, hc, Option.map_some]
  · intro x r hr
    obtain ⟨c, hc, rfl⟩ := childMap_some' hr
    exact noInstOfB_sound (List.all_eq_true.mp h2 c (moduleByName_mem hc).1)

end Tools.ShippingHierPremisesBase
