import Tools.ShippingMixedBindingSoundness

/-! Forward execution of the actual mixed AST. Bounds describe initial wire
values; semantic checks are derived from successful source compilation. -/
namespace Tools.ShippingMixedForwardSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedPrintSoundness
open Tools.ShippingMixedDeclSoundness Tools.ShippingMixedBindingSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingEntrySoundness Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingPrintEntrySoundness Tools.ShippingSVBridge Tools.ShippingDeclWidths
open Tools.ShippingPostSoundness Tools.ShippingControlOptSoundness
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem

/-- The output's separate declaration is included in the execution width map;
all referenced internal widths agree with that map. -/
theorem post_forwardCheck {m m' : Sparkle.IR.AST.Module}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    forwardCheck m' = true := by
  obtain ⟨hi, ho, sub⟩ := post_layout ready post
  obtain ⟨names, consistent, _, _⟩ := declaration_layout base ready hi ho sub
  have clean : ∀ p ∈ m'.wires ++ m'.inputs ++ m'.outputs,
      Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
    intro p hp
    rcases names p hp with h | h
    · exact sanitizeName_of_clean h.1
    · rw [h]; simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
  have typed : TypedStmts (Tools.ShippingEntrySoundness.weOf m') m'.body ∧
      OutputTypedAt outWidth (Tools.ShippingEntrySoundness.weOf m') m'.body := by
    have hd := dropZeroWidth_typed ready
    have out : OutputTypedAt outWidth (Tools.ShippingEntrySoundness.weOf (dropZeroWidthModule m))
        (dropZeroWidthModule m).body := by rw [hd.1, hd.2.1]; exact base.outputTyped
    rcases post with rfl | rfl
    · exact ⟨hd.2.2.2.2, out⟩
    · exact ⟨mergeDuplicates_typed (by rw [hd.2.1]; exact ready.outWidthZero) hd.2.2.2.2,
        mergeDuplicates_output (by rw [hd.2.1]; exact ready.outWidthZero) hd.2.2.2.2 out⟩
  have pd := mixed_post_printDecls base ready post
  have wiresClean : ∀ p ∈ m'.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
    fun p hp => clean p (by simp [hp])
  have facts : ∀ st ∈ m'.body, ∃ l r n, st = .assign l r ∧
      TypedExpr (forwardWidths m') r n ∧
      Sparkle.Backend.Verilog.sanitizeName l = l ∧
      printWidths (m'.wires ++ m'.inputs ++ m'.outputs) l = some n ∧
      (∀ x ∈ Sparkle.IR.Reorder.refsOf r,
        Sparkle.Backend.Verilog.sanitizeName x = x ∧
        printWidths (m'.wires ++ m'.inputs ++ m'.outputs) x = some (forwardWidths m' x) ∧
        Tools.ShippingEntrySoundness.weOf m' x = forwardWidths m' x) := by
    intro st hs
    obtain ⟨l, r, n, eq, ht, hl⟩ := typed.1 st hs
    subst st
    have reads : ∀ x ∈ Sparkle.IR.Reorder.refsOf r,
        Sparkle.Backend.Verilog.sanitizeName x = x ∧
        printWidths (m'.wires ++ m'.inputs ++ m'.outputs) x = some (forwardWidths m' x) ∧
        Tools.ShippingEntrySoundness.weOf m' x = forwardWidths m' x := by
      intro x hx
      obtain ⟨name, width⟩ := printWidths_wire (ht.refs_positive x hx) rfl wiresClean
      have eq : forwardWidths m' x = Tools.ShippingEntrySoundness.weOf m' x := by
        simp only [forwardWidths, width, Option.getD_some]
      exact ⟨name, eq ▸ width, eq.symm⟩
    have rhs := ht.we_congr (fun x hx => (reads x hx).2.2.symm)
    refine ⟨l, r, n, rfl, rhs, ?_, ?_, reads⟩
    · rcases hl with hl | rfl
      · exact (printWidths_wire ht.positive hl wiresClean).1
      · simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
    · rcases hl with hl | rfl
      · exact (printWidths_wire ht.positive hl wiresClean).2
      · have hn := ht.width.symm.trans (typed.2 r hs).width
        obtain ⟨ty, out⟩ := base.output
        have hp : ({name := "out", ty := ty} : Port) ∈ m'.outputs := by rw [ho, out]; simp
        have width := base.outputWidth _ (ho ▸ hp)
        have hw := printWidths_decl (m := m') (p := {name := "out", ty := ty})
          (by simp [hp]) (pd.2.2 _ (by simp [hp])) clean consistent
        rw [width, ← hn] at hw
        exact hw
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro st hs
    obtain ⟨l, r, n, rfl, _, _, _, reads⟩ := facts st hs
    apply List.all_eq_true.mpr
    intro x hx
    exact beq_iff_eq.mpr (reads x hx).2.2
  · apply typedBody_assignsCheck
    · intro st hs
      obtain ⟨l, r, n, eq, ht, _, hw, _⟩ := facts st hs
      have width : forwardWidths m' l = n := by simp only [forwardWidths, hw, Option.getD_some]
      exact ⟨l, r, eq, width ▸ ht⟩
    · intro st hs l r eq
      obtain ⟨l', r', n, eq', ht, name, width, reads⟩ := facts st hs
      cases eq
      cases eq'
      have hw : forwardWidths m' l = n := by simp only [forwardWidths, width, Option.getD_some]
      exact ⟨⟨name, hw ▸ width⟩, fun x hx => ⟨(reads x hx).1, (reads x hx).2.1⟩⟩

/-- The existing guard transfers the arithmetic branch; control modules keep
the postprocessed original. No forward-check certificate is supplied. -/
theorem checked_forwardCheck {m m' : Sparkle.IR.AST.Module}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m) (simple : SimpleStmts m.body)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    forwardCheck (checkedOptimize m') = true := by
  have simple' : SimpleStmts m'.body := by
    have hd : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact hd
    · exact mergeDuplicates_simple _ hd
  have gate := simpleBody_of m' simple'
  by_cases control : HasControl m'.body
  · rw [checkedOptimize_control gate control]
    exact post_forwardCheck base ready post
  · exact printCheck_forward (checkedOptimize_printCheck gate
      (post_printCheck base ready simple' post control))

/-- The SV assignment fold uses the width lookup of the emitted declarations.
This is forward execution, not yet parallel settling. Initial wire bounds are
ordinary two-state initialization conditions, not compiler certificates. -/
def ForwardValue (m : Sparkle.IR.AST.Module) (initial : Env) (mems : MEnv) (expected : Nat) : Prop :=
  SyntaxValue m initial mems expected ∧ forwardCheck (checkedOptimize m) = true ∧
  (Bounded (forwardWidths (checkedOptimize m)) initial →
    ∃ sv pairs result, emitAstModule (checkedOptimize m) = some sv ∧
      combItems sv.items = some pairs ∧
      evalAssignsSV (astWidths sv) mems pairs initial = some result ∧ result "out" = expected)

theorem forward_of_entry {bs m m' initial mems expected}
    (h : RawValueAt outWidth bs m initial mems expected) (positive : PositiveBinders bs)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    ForwardValue m' initial mems expected := by
  have render := rendered_of_entry h positive post
  obtain ⟨_, _, _, ready, simple, _, _, _, base⟩ := h
  have check := checked_forwardCheck (base positive) ready simple post
  refine ⟨⟨render, checked_syntax (base positive) ready simple post⟩, check, ?_⟩
  intro bounds
  obtain ⟨result, sv, run, value, ast, _, decls⟩ := render
  have simple' : SimpleStmts m'.body := by
    have hd : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact hd
    · exact mergeDuplicates_simple _ hd
  have gate := simpleBody_of m' simple'
  have pd := checkedOptimize_printDecls gate (mixed_post_printDecls (base positive) ready post)
  have shape := checkedOptimize_printShape gate
  obtain ⟨reads, checks⟩ := forwardCheck_sound check
  obtain ⟨pairs, result', items, run', svRun⟩ := module_forward pd shape ast checks mems initial bounds
    (fun x n hn => by have := bounds x; simpa only [forwardWidths, hn, Option.getD_some] using this)
  rw [← evalAssigns_widths _ (Tools.ShippingEntrySoundness.weOf (checkedOptimize m')) _ mems shape reads initial] at run'
  rw [run] at run'
  cases run'
  rw [← decls.widths] at svRun
  exact ⟨sv, pairs, result, ast, items, svRun, value⟩

theorem mixed_forward {declName bs body m m'} (source : MixedPreserves declName bs body m)
    (positive : PositiveBinders bs)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    MixedSourcePreserves declName bs body (ForwardValue m') :=
  MixedSourcePreserves.map source (fun _ _ _ h => forward_of_entry h positive post)

theorem synthesizeCombinational_mixed_forward {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        MixedSourcePreserves declName bs body (ForwardValue m) := by
  obtain ⟨raw, design, world, core, post⟩ := synthesizeCombinational_reads hr
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_mixed_sound core
  exact ⟨ci, w1, w2, get, fun bs body old shape =>
    mixed_forward (source bs body old shape) (mixedShape_positive shape) post⟩
/-- Forward execution of the emitted AST observes the actual library Signals. `EnvDefines`
remains the explicit boundary identifying the runtime declaration. -/
theorem forward_source_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {n kb kv : Nat} {bpos vpos : Nat → Nat} {e : Tools.ShippingBoolSourceSoundness.BExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : gatePeel value = none)
    (peel : mixedGatePeel value = some (bs,
      Tools.ShippingBoolSourceSoundness.quoteB dom n
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : Sparkle.Core.Domain.DomainConfig}
        (bools : Nat → Sparkle.Core.Signal.Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      Tools.ShippingMixedSourceBridge.SourceInputs declName bs ids cache (fun j => (bools j).val tick)
        (fun j n => (bits j n).val tick) initial →
      ForwardValue m initial mems (Tools.ShippingMuxLoweringSoundness.encodeBool
        ((Tools.ShippingBoolSourceSoundness.denoteB n (fun j => bools (bpos j))
          (fun j => bits (vpos j) n) e).val tick)) := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinational_mixed_forward hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := by
    simp [certifiedShape?, definition, old]
  have mixedGate := Tools.ShippingMixedSourceBridge.source_gate (d := d)
    (by rw [definition]; exact peel) hn he hb hv
  exact Tools.ShippingMixedSourceBridge.source_signals (source bs _ oldGate mixedGate) hn he hb hv

end Tools.ShippingMixedForwardSoundness
