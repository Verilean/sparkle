import Sparkle.IR.ModuleNames
import Sparkle.Backend.Verilog

namespace Sparkle.IR.ModuleNameCheck
open Sparkle.IR.AST Sparkle.Backend.Verilog

/-- Both definitions and instance targets participate: even an external target
must not normalize to the name of a different internal definition. -/
def namesOf (modules : List Module) : List String := modules.flatMap fun m =>
  m.name :: m.body.filterMap fun st => match st with
    | .inst target _ _ => some target
    | _ => none

/-- Reject invalid emitted names and aliases introduced by normalization.
Repeated uses of the SAME raw name are allowed. -/
def checkNames (names : List String) : Bool := names.all fun a =>
  ModuleNames.legal (sanitizeName a) &&
    names.all fun b => sanitizeName a != sanitizeName b || a == b

/-- Deduplicate repeated uses before the pairwise comparison. -/
def check (modules : List Module) : Bool :=
  checkNames (namesOf modules).eraseDups

/-- Actual definitions, unlike uses, must occur at most once. -/
def checkDesign (d : Design) : Bool :=
  check d.modules && (decide (d.modules.map Module.name).Nodup &&
    (d.modules.map Module.name).contains d.topModule)

theorem checkNames_sound {names : List String} (h : checkNames names = true) :
    (∀ a ∈ names, ModuleNames.legal (sanitizeName a) = true) ∧
    (∀ a ∈ names, ∀ b ∈ names, sanitizeName a = sanitizeName b → a = b) := by
  have ha := List.all_eq_true.mp h
  constructor
  · intro a hm; exact (Bool.and_eq_true_iff.mp (ha a hm)).1
  · intro a ham b hbm he
    have hb := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (ha a ham)).2 b hbm
    simpa [he] using hb

theorem check_sound {modules : List Module} (h : check modules = true) :
    (∀ a ∈ namesOf modules, ModuleNames.legal (sanitizeName a) = true) ∧
    (∀ a ∈ namesOf modules, ∀ b ∈ namesOf modules,
      sanitizeName a = sanitizeName b → a = b) := by
  obtain ⟨hl, hi⟩ := checkNames_sound h
  exact ⟨fun a ha => hl a (List.mem_eraseDups.mpr ha),
    fun a ha b hb => hi a (List.mem_eraseDups.mpr ha) b (List.mem_eraseDups.mpr hb)⟩

theorem definition_mem {modules : List Module} {m : Module} (h : m ∈ modules) :
    m.name ∈ namesOf modules := List.mem_flatMap.mpr ⟨m, h, by simp⟩

theorem reference_mem {modules : List Module} {m : Module} {target inst : String}
    {connections : List (String × Expr)} (hm : m ∈ modules)
    (hs : Stmt.inst target inst connections ∈ m.body) : target ∈ namesOf modules := by
  apply List.mem_flatMap.mpr
  refine ⟨m, hm, List.mem_cons_of_mem _ ?_⟩
  exact List.mem_filterMap.mpr ⟨_, hs, rfl⟩

/-- Within an accepted design, emitted target equality is exactly raw target
equality. The emitter uses sanitizeName for BOTH definitions and references. -/
theorem linkage_iff {modules : List Module} (h : check modules = true)
    {a b : String} (ha : a ∈ namesOf modules) (hb : b ∈ namesOf modules) :
    sanitizeName a = sanitizeName b ↔ a = b :=
  ⟨(check_sound h).2 a ha b hb, congrArg sanitizeName⟩

theorem checkDesign_nodup {d : Design} (h : checkDesign d = true) :
    (d.modules.map fun m => sanitizeName m.name).Nodup := by
  obtain ⟨hc, hd⟩ := Bool.and_eq_true_iff.mp h
  have hn : (d.modules.map Module.name).Nodup := by
    simpa using (Bool.and_eq_true_iff.mp hd).1
  have hi := (check_sound hc).2
  have aux : ∀ names : List String, names.Nodup →
      (∀ a ∈ names, ∀ b ∈ names, sanitizeName a = sanitizeName b → a = b) →
      (names.map sanitizeName).Nodup := by
    intro names hn hi
    induction names with
    | nil => simp
    | cons a rest ih =>
      obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
        exact ha (hi b (by simp [hb]) a (by simp) he ▸ hb)
      · exact ih ht (fun a ha b hb => hi a (by simp [ha]) b (by simp [hb]))
  have hh := aux _ hn (by
    intro a ha b hb
    obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp ha
    obtain ⟨mb, hmb, rfl⟩ := List.mem_map.mp hb
    exact hi _ (definition_mem hma) _ (definition_mem hmb))
  simpa only [List.map_map, Function.comp_def] using hh
theorem checkDesign_top {d : Design} (h : checkDesign d = true) :
    ∃ m ∈ d.modules, m.name = d.topModule := by
  have ht := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
  exact List.mem_map.mp (by simpa using ht)

end Sparkle.IR.ModuleNameCheck
