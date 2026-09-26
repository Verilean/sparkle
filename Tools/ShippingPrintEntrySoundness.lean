import Tools.ShippingPostSoundness
import Tools.ShippingModulePrintSoundness

/-! # Shipping synthesis to whole-module byte rendering

The source fragment and `EnvDefines` boundary are those of the entry theorem.
This module discharges the renderer's declaration and body-shape premises from
that same successful run, including post-processing and both optimizer arms.
It proves AST/string correspondence, not lexical validity or SV evaluation;
those still require a separate connection to `assignsCheck` and SV semantics.
-/

namespace Tools.ShippingPrintEntrySoundness

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Type
open Sparkle.IR.Semantics Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingEntrySoundness Tools.ShippingPostSoundness
open Tools.ShippingModulePrintSoundness
open Tools.ShippingPrintSoundness
open Tools.SVParser.AST Tools.SVParser.EmitAst
open Sparkle.IR.OptCheck

/-- The declaration premises of the whole-module renderer. -/
def PrintableDecls (m : Sparkle.IR.AST.Module) : Prop :=
  m.isPrimitive = false ∧ m.parameters = [] ∧
    ∀ p ∈ m.inputs ++ m.outputs ++ m.wires, PrintableType p.ty

theorem printableType_check (ty : HWType) :
    (match ty with
      | .bit => true | .bitVector n => decide (0 < n) | _ => false) = true ↔ PrintableType ty := by
  cases ty with
  | bit => exact ⟨fun _ => .bit, fun _ => rfl⟩
  | bitVector n =>
    simp only [decide_eq_true_eq]
    exact ⟨fun h => .bits n h, fun h => by cases h; assumption⟩
  | bitVectorDim d => constructor <;> intro h <;> cases h
  | array n t => constructor <;> intro h <;> cases h

theorem printDeclsCheck_iff (m : Sparkle.IR.AST.Module) :
    printDeclsCheck m = true ↔ PrintableDecls m := by
  simp only [printDeclsCheck, PrintableDecls, Bool.and_eq_true_iff,
    Bool.not_eq_true', List.isEmpty_iff, List.all_eq_true]
  constructor
  · rintro ⟨⟨hp, hpar⟩, ht⟩
    exact ⟨hp, hpar, fun p h => (printableType_check p.ty).mp (ht p h)⟩
  · rintro ⟨hp, hpar, ht⟩
    exact ⟨⟨hp, hpar⟩, fun p h => (printableType_check p.ty).mpr (ht p h)⟩

theorem checkedOptimize_printDecls {m : Sparkle.IR.AST.Module}
    (hgate : simpleBody m = true) (hp : PrintableDecls m) :
    PrintableDecls (checkedOptimize m) := by
  unfold checkedOptimize
  simp only [hgate, if_true]
  split
  · rename_i hc
    have hc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).2).1
    rw [(printDeclsCheck_iff m).mpr hp] at hc
    simp only [Bool.not_true, Bool.false_or] at hc
    exact (printDeclsCheck_iff _).mp hc
  · exact hp

theorem postprocess_printDecls {m m' : Sparkle.IR.AST.Module} {n : Nat}
    (hn : 0 < n) (hpr : PostReady m n)
    (hins : ∀ p ∈ m.inputs, p.ty = .bitVector n)
    (hout : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    PrintableDecls m' := by
  obtain ⟨hparams, hprim, hwires, _⟩ := hpr.2.2.2.2.1
  have houtputs := hpr.2.2.2.1 hn
  have hc : allConcrete m = true := by
    unfold allConcrete
    rw [List.all_eq_true]
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · simp [hins p hp, HWType.bitWidth?]
      · rw [houtputs] at hp
        simp only [List.mem_singleton] at hp
        subst p; rfl
    · obtain ⟨k, hk⟩ := hwires p hp
      simp [hk, HWType.bitWidth?]
  have hp : PrintableDecls (dropZeroWidthModule m) := by
    unfold PrintableDecls dropZeroWidthModule
    simp only [hc, Bool.not_true, Bool.false_eq_true, if_false]
    refine ⟨hprim, hparams, ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · rw [hins p hp]; exact .bits n hn
      · rw [houtputs] at hp
        simp only [List.mem_singleton] at hp
        subst p; exact .bits n hn
    · obtain ⟨hp, hpos⟩ := List.mem_filter.mp hp
      obtain ⟨k, hk⟩ := hwires p hp
      rw [hk]
      apply PrintableType.bits
      simp [hk, HWType.bitWidth] at hpos
      omega
  rcases hout with rfl | rfl
  · exact hp
  · have hall : (dropZeroWidthModule m).body.all isAssign = true := by
      rw [(dropZeroWidth_entry m n hn hpr).1, List.all_eq_true]
      intro st hs
      obtain ⟨l, r, rfl, _⟩ := hpr.2.2.1 st hs
      rfl
    unfold mergeDuplicates
    simp only [hall, if_true]
    split <;> exact hp

/-- Actual successful synthesis supplies the renderer's metadata and type
conditions; no `PrintableDecls` premise is required of the caller. -/
theorem synthesized_printFacts {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    PrintableDecls m ∧ simpleBody m = true := by
  obtain ⟨m0, d0, w1, hcore, hpost⟩ := synthesizeCombinational_reads h
  obtain ⟨port, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨env, hev, _, hpr, hins, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  refine ⟨postprocess_printDecls hn hpr ?_ hpost,
    simpleBody_of m (postprocess_facts hn hpr hpost).1⟩
  intro p hp
  obtain ⟨j, hj, hport, hty, _⟩ := hins p hp
  exact hty

/-- Both accepted-optimization and fallback paths preserve the declaration
premises of the shipping renderer, derived from the SAME successful run. -/
theorem printed_printDecls {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) : PrintableDecls (checkedOptimize m) := by
  obtain ⟨hp, hg⟩ := synthesized_printFacts h henv hwf hn
  exact checkedOptimize_printDecls hg hp

/-- The actual emitted bytes render an AST, with declaration and expression
premises derived from synthesis. This does not yet assert SV evaluation. -/
theorem printedModule_render {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    let o := checkedOptimize m
    ∃ sv, emitAstModule o = some sv ∧
      renderModule o.name
        (o.wires.filter fun p => !((o.inputs ++ o.outputs).map (·.name)).contains p.name).length sv
        = some (Sparkle.Backend.Verilog.toVerilog o) := by
  obtain ⟨hp, hg⟩ := synthesized_printFacts h henv hwf hn
  have ho := checkedOptimize_printDecls hg hp
  exact emitModule_render _ ho.1 ho.2.1 ho.2.2 (checkedOptimize_printShape hg)

/-- The two established sides of the shipping-artifact boundary, for one
module: its optimized IR agrees with the source on every input, and its
printed bytes render the emitted SV tree. Deliberately NOT an assertion that
evaluating that tree (or parsing its text) agrees with the source. -/
def FragmentArtifact (m : Sparkle.IR.AST.Module) (names : List Name) (n : Nat)
    (fe : FExpr) : Prop :=
  let o := checkedOptimize m
  ∃ (sv : SVModule) (port : Nat → Option String),
    emitAstModule o = some sv ∧
    renderModule o.name
      (o.wires.filter fun p => !((o.inputs ++ o.outputs).map (·.name)).contains p.name).length sv
      = some (verilogOf m) ∧
    (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
    (∀ j, j < names.length → ∃ w, port j = some w ∧ w ∈ o.inputs.map (·.name)) ∧
    ∀ {dom : Sparkle.Core.Domain.DomainConfig}
      (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv)
      (initial : Env),
      (∀ j w, j < names.length → port j = some w → initial w = ((sigs j).val t).toNat) →
      ∃ env, evalAssigns (declWidth o) mems o.body initial = some env ∧
        env "out" = ((denoteFE n sigs fe).val t).toNat

/-- One application connects the source, the actual optimized module, and
the emitted bytes. Its scope/trust hypotheses are exactly those of the source
entry theorem; no per-circuit semantic certificate is required. -/
theorem compiledFragment_artifact {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) : FragmentArtifact m names n fe := by
  obtain ⟨sv, htree, htext⟩ := printedModule_render h henv hwf hn
  obtain ⟨port, hdist, hex, hsem⟩ := printedModule_fragment h henv hwf hn
  exact ⟨sv, port, htree, htext, hdist, hex, hsem⟩

end Tools.ShippingPrintEntrySoundness
