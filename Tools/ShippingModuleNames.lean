import Tools.ShippingDeclWidths

namespace Tools.ShippingModuleNames
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.OptCheck
open Sparkle.Backend.Verilog Sparkle.IR.ModuleNameCheck
open Tools.ShippingEntrySoundness Tools.ShippingTranslateSoundness
open Tools.ShippingPostSoundness Tools.ShippingPrintEntrySoundness
open Tools.SVParser.AST Tools.SVParser.EmitAst

/-- The actual hierarchical return boundary, with no source-fragment premise. -/
theorem validateDesignNames_returns {d result : Design}
    (h : MReturns (validateDesignNames d) result) : result = d ∧ checkDesign result = true := by
  unfold validateDesignNames at h
  split at h
  · rename_i hc
    have he := MReturns.pure h
    exact ⟨he, he ▸ hc⟩
  · exact (MReturns.throw h).elim

theorem hierarchical_names {decl : Name} {d : Design}
    (h : MReturns (synthesizeHierarchical decl) d) : checkDesign d = true := by
  unfold synthesizeHierarchical at h
  obtain ⟨⟨m, child⟩, _, hr⟩ := MReturns.bind h
  exact (validateDesignNames_returns hr).2

theorem hierarchical_parameters_names {decl : Name} {parameters : List (String × Nat)} {d : Design}
    (h : MReturns (synthesizeHierarchicalWithParameters decl parameters) d) : checkDesign d = true := by
  unfold synthesizeHierarchicalWithParameters at h
  obtain ⟨⟨m, child⟩, _, hr⟩ := MReturns.bind h
  exact (validateDesignNames_returns hr).2

/-- Successful hierarchy synthesis cannot introduce a name alias in Verilog.
References to external modules are included in namesOf, too. -/
theorem hierarchical_linkage {decl : Name} {d : Design}
    (h : MReturns (synthesizeHierarchical decl) d) :
    (d.modules.map fun m => Sparkle.Backend.Verilog.sanitizeName m.name).Nodup ∧
    (∀ name ∈ namesOf d.modules, Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName name) = true) ∧
    (∀ a ∈ namesOf d.modules, ∀ b ∈ namesOf d.modules,
      Sparkle.Backend.Verilog.sanitizeName a = Sparkle.Backend.Verilog.sanitizeName b ↔ a = b) := by
  have hc := hierarchical_names h
  have hn := (Bool.and_eq_true_iff.mp hc).1
  exact ⟨checkDesign_nodup hc, (check_sound hn).1,
    fun a ha b hb => linkage_iff hn ha hb⟩

theorem emitted_name {m : Sparkle.IR.AST.Module} {sv : SVModule}
    (h : emitAstModule m = some sv) : sv.name = Sparkle.Backend.Verilog.sanitizeName m.name := by
  unfold emitAstModule at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨ins, _, outs, _, ws, _, bs, _, he⟩ := h
      cases he
      rfl

/-- The AST instance target uses exactly the same normalization as the
module header. No assumptions about the connection expressions are needed. -/
theorem emitted_instance_target {target inst : String} {connections : List (String × Sparkle.IR.AST.Expr)}
    {wof : String → Option Nat} {wires : List Port} {items : List SVModuleItem}
    (h : emitAstStmt wof wires (.inst target inst connections) = some items) :
    ∃ conns, items = [.instantiation (Sparkle.Backend.Verilog.sanitizeName target)
      (Sparkle.Backend.Verilog.sanitizeName inst) conns []] := by
  simp only [emitAstStmt, bind, Option.bind_eq_some_iff] at h
  obtain ⟨conns, _, he⟩ := h
  exact ⟨conns, (Option.some.inj he).symm⟩

/-- An emitted instance can match a definition's emitted name iff its raw
IR target is that definition. This does not assert that external definitions
exist, nor does it prove hierarchical circuit semantics. -/
theorem hierarchical_instance_linkage {decl : Name} {d : Design}
    (h : MReturns (synthesizeHierarchical decl) d)
    {parent callee : Sparkle.IR.AST.Module} {target inst : String}
    {connections : List (String × Sparkle.IR.AST.Expr)}
    (hp : parent ∈ d.modules) (hc : callee ∈ d.modules)
    (hs : Stmt.inst target inst connections ∈ parent.body)
    {sv : SVModule} (he : emitAstModule callee = some sv) :
    Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName target) = true ∧
    (Sparkle.Backend.Verilog.sanitizeName target = sv.name ↔ target = callee.name) := by
  have hn := (Bool.and_eq_true_iff.mp (hierarchical_names h)).1
  have ht := reference_mem hp hs
  refine ⟨(check_sound hn).1 target ht, ?_⟩
  rw [emitted_name he]
  exact linkage_iff hn ht (definition_mem hc)

set_option maxRecDepth 4096 in
theorem checkedOptimize_name (m : Sparkle.IR.AST.Module) :
    (checkedOptimize m).name = m.name := by
  have hn : (Sparkle.IR.Optimize.optimizeModule m).name = m.name := by
    unfold Sparkle.IR.Optimize.optimizeModule
    split
    · rfl
    · rfl
  unfold checkedOptimize
  split
  · dsimp only
    split <;> simp_all
  · exact hn

theorem postprocess_name {m m' : Sparkle.IR.AST.Module} {n : Nat}
    (hn : 0 < n) (hp : PostReady m n)
    (h : m' = Sparkle.IR.ZeroWidth.dropZeroWidthModule m ∨
      m' = Sparkle.IR.RegDedup.mergeDuplicates (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)) :
    m'.name = m.name := by
  have hd : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).name = m.name := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split <;> rfl
  rcases h with rfl | rfl
  · exact hd
  · have ha : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body.all Sparkle.IR.RegDedup.isAssign = true := by
      rw [(dropZeroWidth_entry m n hn hp).1, List.all_eq_true]
      intro st hm
      obtain ⟨l, r, rfl, _⟩ := hp.2.2.1 st hm
      rfl
    unfold Sparkle.IR.RegDedup.mergeDuplicates
    simp only [ha, if_true]
    split <;> exact hd

/-- Lexical module-name validity is a conclusion of the existing source
success theorem, inherited from finishSynth's actual rejection branch. -/
theorem compiled_moduleName {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr} {sv : SVModule}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (ht : emitAstModule (checkedOptimize m) = some sv) :
    sv.name = Sparkle.Backend.Verilog.sanitizeName (checkedOptimize m).name ∧ Sparkle.IR.ModuleNames.legal sv.name = true := by
  have he := emitted_name ht
  refine ⟨he, ?_⟩
  obtain ⟨m0, _, _, hcore, hm⟩ := synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨_, _, _, hpr, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  rw [he, checkedOptimize_name, postprocess_name hn hpr hm]
  exact hpr.2.2.2.2.2.2.2.2

end Tools.ShippingModuleNames
