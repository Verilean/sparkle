import Tools.ShippingDeltaSemantics

/-! The actual compilation endpoint, strengthened to execution and convergence
of complete emitted two-state, zero-delay combinational RTL. The fixed-input
observation model is explicitly `DeltaTrace`; X/Z, physical delay and external
simulator scheduling are outside this theorem, as are unproved DSL branches.
-/
namespace Tools.ShippingExecutionSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.OptCheck
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingEntrySoundness Tools.ShippingTranslateSoundness
open Tools.ShippingOptSoundness Tools.ShippingPrintEntrySoundness
open Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingSVBridge Tools.ShippingDeclWidths
open Tools.ShippingSettledSoundness Tools.ShippingDeltaSemantics

/-- Successful shipping synthesis reaches the same source value after finite
RTL delta settling, from arbitrary bounded internal wire values. Syntax,
declaration uniqueness and binding refer to the very same emitted AST.
No caller supplies an order, a round trace, or a convergence certificate. -/
theorem compiledFragment_execution {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    let o := checkedOptimize m
    ∃ (sv : SVModule) (port : Nat → Option String) (pairs : List CombStep),
      emitAstModule o = some sv ∧
      Tools.SVParser.ConcreteSyntax.Module sv (verilogOf m) ∧
      combItems sv.items = some pairs ∧
      ((declarationTable sv).map Prod.fst).Nodup ∧
      Tools.ShippingNameBinding.AssignmentsBound sv pairs ∧
      (∀ j j' x, port j = some x → port j' = some x → j = j') ∧
      (∀ j x, j < names.length → port j = some x →
        ∃ sp ∈ sv.ports, sp.dir = .input ∧ sp.name = x ∧
          declaredPortWidth sp = some n ∧ sp.isSigned = false) ∧
      (∀ j, j < names.length → ∃ x, port j = some x ∧ x ∈ o.inputs.map (·.name)) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat),
        let initial := inputEnv names.length port (fun j => (sigs j).val t)
        Bounded (fun x => (astWidths sv x).getD 0) initial ∧
        SettlesTo sv pairs initial ((denoteFE n sigs fe).val t).toNat := by
  obtain ⟨sv, port, pairs, ht, _, _, _, hi, hd, hex, hdecl, _, _, hnd,
      hbound, _, hsyntax, hsem⟩ := compiledFragment_settled h henv hwf hn
  have ha := checkedOptimize_order (synthesized_printFacts h henv hwf hn).2
    (Tools.ShippingPostSoundness.synthesized_order h henv hwf hn)
  have hwidth := compiled_astWidths h henv hwf hn ht
  have hc := (forwardCheck_sound (compiled_forwardCheck h henv hwf hn
    (synthesized_names h henv hwf hn))).2
  obtain ⟨sv', pairs', ht', he, hi'⟩ := module_combItems _
    (printed_printDecls h henv hwf hn)
    (checkedOptimize_printShape (synthesized_printFacts h henv hwf hn).2) hc
  rw [ht] at ht'; cases ht'
  rw [hi] at hi'; cases hi'
  rw [← hwidth] at he hc
  have hwe : forwardWidths (checkedOptimize m) = fun x => (astWidths sv x).getD 0 := by
    funext x; rw [hwidth]; rfl
  rw [hwe] at hc
  have hw : ∀ x width, astWidths sv x = some width → (astWidths sv x).getD 0 = width := by
    intro x width hx; simp [hx]
  refine ⟨sv, port, pairs, ht, hsyntax, hi, hnd, hbound, hd, hdecl, hex, ?_⟩
  intro dom sigs t
  obtain ⟨hb, stable, _, _, hobs, hs, _⟩ := hsem sigs t (fun _ _ => 0)
  have hbs := solution_bounded hw hb hs
  refine ⟨hb, stable, hbs, hs, hobs, ?_⟩
  intro seed hseed hframe
  refine ⟨deltaTrace_exists ha hc he hw hseed, ?_⟩
  intro trace htrace k hk
  have heq := deltaTrace_converges ha hc he hw hs hbs hseed hframe htrace k hk
  exact ⟨heq, heq ▸ hobs⟩

end Tools.ShippingExecutionSoundness
