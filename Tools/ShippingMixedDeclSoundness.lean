import Tools.ShippingMixedPostSoundness
import Tools.ShippingSyntaxSoundness

/-! Names, declaration uniqueness and declaration-derived widths for the
actual mixed frontend, cleanup and checked optimizer. -/
namespace Tools.ShippingMixedDeclSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingMixedEntrySoundness Tools.ShippingTypedPostSoundness
open Tools.ShippingPostSoundness Tools.ShippingTranslateSoundness Tools.ShippingEntrySoundness
open Tools.ShippingDeclWidths Tools.ShippingPrintEntrySoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingPrintSoundness Tools.ShippingSyntaxSoundness
open Tools.ShippingOptSoundness Tools.ShippingSVBridge
open Tools.SVParser.AST Tools.SVParser.EmitAst

/-- Both real cleanup choices preserve ports and only remove wire declarations. -/
theorem post_layout {m m' : Sparkle.IR.AST.Module} (ready : TypedPostReady m)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    m'.inputs = m.inputs ∧ m'.outputs = m.outputs ∧ m'.wires.Sublist m.wires := by
  have hd := dropZeroWidth_typed ready
  have sub : (dropZeroWidthModule m).wires.Sublist m.wires := by
    unfold dropZeroWidthModule
    split
    · exact List.Sublist.refl _
    · exact List.filter_sublist
  rcases post with rfl | rfl
  · exact ⟨hd.2.2.1, hd.2.2.2.1, sub⟩
  · unfold mergeDuplicates
    simp only [hd.2.2.2.2.isAssign, if_true]
    split <;> exact ⟨hd.2.2.1, hd.2.2.2.1, sub⟩

/-- Structural properties of the selected optimized module, independent of
values or a successful evaluator run. -/
theorem declaration_layout {m o : Sparkle.IR.AST.Module} (base : PrintBaseAt outWidth m)
    (ready : TypedPostReady m) (hi : o.inputs = m.inputs) (ho : o.outputs = m.outputs)
    (sub : o.wires.Sublist m.wires) :
    (∀ p ∈ o.wires ++ o.inputs ++ o.outputs, Sparkle.IR.NameHints.DataName p.name) ∧
    (∀ p ∈ o.wires ++ o.inputs ++ o.outputs,
      ∀ q ∈ o.wires ++ o.inputs ++ o.outputs, p.name = q.name → p = q) ∧
    ((o.inputs ++ o.outputs).map Port.name).Nodup ∧ (o.wires.map Port.name).Nodup := by
  obtain ⟨ty, out⟩ := base.output
  have subset : ∀ p ∈ o.wires ++ o.inputs ++
      o.outputs, p ∈ m.wires ∨ p = {name := "out", ty := ty} := by
    intro p hp
    simp only [List.mem_append, hi, ho, out, List.mem_singleton] at hp
    rcases hp with (hp | hp) | hp
    · exact Or.inl (sub.subset hp)
    · exact Or.inl (base.inputWires p hp)
    · exact Or.inr hp
  have noOut : ∀ p ∈ m.wires, p.name ≠ "out" := by
    intro p hp eq
    have h := (base.wireNames p hp).2
    rw [eq] at h
    cases h
  refine ⟨?_, ?_, ?_, ready.wiresNodup.sublist (sub.map _)⟩
  · intro p hp
    rcases subset p hp with hp | rfl
    · exact Or.inl (base.wireNames p hp)
    · exact Or.inr rfl
  · intro p hp q hq eq
    rcases subset p hp with hp | rfl <;> rcases subset q hq with hq | rfl
    · have a := find?_of_nodup ready.wiresNodup hp
      have b := find?_of_nodup ready.wiresNodup hq
      rw [eq, b] at a
      exact (Option.some.inj a).symm
    · exact False.elim (noOut p hp eq)
    · exact False.elim (noOut q hq eq.symm)
    · rfl
  · rw [hi, ho, out, List.map_append, List.nodup_append]
    refine ⟨base.inputNames, by simp, ?_⟩
    intro x hx y hy eq
    have hy : y = "out" := by simpa using hy
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hx
    exact noOut p (base.inputWires p hp) (he.trans (eq.trans hy))

theorem checked_layout {m m' : Sparkle.IR.AST.Module} (base : PrintBaseAt outWidth m)
    (ready : TypedPostReady m) (simple : SimpleStmts m.body)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    let o := checkedOptimize m'
    (∀ p ∈ o.wires ++ o.inputs ++ o.outputs, Sparkle.IR.NameHints.DataName p.name) ∧
    (∀ p ∈ o.wires ++ o.inputs ++ o.outputs,
      ∀ q ∈ o.wires ++ o.inputs ++ o.outputs, p.name = q.name → p = q) ∧
    ((o.inputs ++ o.outputs).map Port.name).Nodup ∧ (o.wires.map Port.name).Nodup := by
  have simple' : SimpleStmts m'.body := by
    have sd : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact sd
    · exact mergeDuplicates_simple _ sd
  obtain ⟨hi, ho, sub⟩ := post_layout ready post
  obtain ⟨hiO, hoO⟩ := checkedOptimize_ports (simpleBody_of m' simple')
  exact declaration_layout base ready (hiO.trans hi) (hoO.trans ho)
    ((checkedOptimize_wires_sublist m').trans sub)

/-- The width environment is read from emitted declarations. Names are legal
and no emitted port/wire declaration is duplicated. This does not yet assert
that every reference or assignment target is declared. -/
structure Declarations (m : Sparkle.IR.AST.Module) (sv : SVModule) : Prop where
  identifiers : ∀ entry ∈ declarationTable sv, Tools.SVParser.ConcreteSyntax.Identifier entry.1
  nodup : ((declarationTable sv).map Prod.fst).Nodup
  widths : astWidths sv = printWidths (m.wires ++ m.inputs ++ m.outputs)

theorem declarations_of_layout {o : Sparkle.IR.AST.Module} {sv : SVModule}
    (names : ∀ p ∈ o.wires ++ o.inputs ++ o.outputs, Sparkle.IR.NameHints.DataName p.name)
    (consistent : ∀ p ∈ o.wires ++ o.inputs ++ o.outputs,
      ∀ q ∈ o.wires ++ o.inputs ++ o.outputs, p.name = q.name → p = q)
    (ports : ((o.inputs ++ o.outputs).map Port.name).Nodup)
    (wires : (o.wires.map Port.name).Nodup)
    (pd : PrintableDecls o)
    (shape : ∀ st ∈ o.body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (ast : emitAstModule o = some sv) : Declarations o sv := by
  have clean : ∀ p ∈ o.wires ++ o.inputs ++
      o.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
    intro p hp
    rcases names p hp with h | h
    · exact sanitizeName_of_clean h.1
    · rw [h]; simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
  have table := declarationTable_emitted pd shape ast
  have visible := visibleDecls_mem consistent
  refine ⟨?_, ?_, astWidths_emitted pd shape clean consistent ast⟩
  · intro entry he
    rw [table] at he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    rw [clean p ((visible p).mp hp)]
    exact dataName_identifier (names p ((visible p).mp hp))
  · rw [table]
    have eq : (irTable (visibleDecls o)).map Prod.fst =
        (visibleDecls o).map Port.name := by
      simp only [irTable, List.map_map]
      apply List.map_congr_left
      intro p hp
      exact clean p ((visible p).mp hp)
    rw [eq]
    exact visibleDecls_nodup ports wires

theorem checked_declarations {m m' : Sparkle.IR.AST.Module} {sv : SVModule}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m) (simple : SimpleStmts m.body)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m))
    (pd : PrintableDecls (checkedOptimize m'))
    (shape : ∀ st ∈ (checkedOptimize m').body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (ast : emitAstModule (checkedOptimize m') = some sv) :
    Declarations (checkedOptimize m') sv := by
  obtain ⟨names, consistent, ports, wires⟩ := checked_layout base ready simple post
  exact declarations_of_layout names consistent ports wires pd shape ast

end Tools.ShippingMixedDeclSoundness
