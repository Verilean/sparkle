import Tools.ShippingMixedPrintSoundness
import Tools.ShippingControlOptSoundness

/-! Declaration binding and concrete syntax for typed mixed modules after
cleanup/checked merging and both branches of the actual checked optimizer. -/
namespace Tools.ShippingMixedBindingSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedPrintSoundness
open Tools.ShippingMixedDeclSoundness Tools.ShippingTypedPostSoundness
open Tools.ShippingTypedExprSoundness Tools.ShippingEntrySoundness
open Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness Tools.ShippingPrintEntrySoundness
open Tools.ShippingDeclWidths Tools.ShippingNameBinding Tools.ShippingSVBridge
open Tools.ShippingSyntaxSoundness Tools.ShippingModuleNames Tools.ShippingPostSoundness
open Tools.ShippingControlOptSoundness
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem

/-- Positive internal widths can only come from a real wire declaration. -/
theorem positive_declared {m : Sparkle.IR.AST.Module} {x : String} (h : 0 < weOf m x) :
    ∃ p ∈ m.wires, p.name = x := by
  unfold Tools.ShippingEntrySoundness.weOf at h
  cases hf : m.wires.find? (fun p => p.name == x) with
  | none => simp [hf] at h
  | some p =>
    exact ⟨p, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- No emitter-check premise: binding follows from the typed IR and its
actual declaration table, including the distinguished output target. -/
theorem typed_bindings {m : Sparkle.IR.AST.Module} {sv : SVModule}
    (pd : PrintableDecls m) (typed : TypedStmts (weOf m) m.body)
    (out : "out" ∈ m.outputs.map Port.name)
    (names : ∀ p ∈ m.wires ++ m.inputs ++ m.outputs, Sparkle.IR.NameHints.DataName p.name)
    (consistent : ∀ p ∈ m.wires ++ m.inputs ++ m.outputs,
      ∀ q ∈ m.wires ++ m.inputs ++ m.outputs, p.name = q.name → p = q)
    (ast : emitAstModule m = some sv) :
    ∃ pairs, combItems sv.items = some pairs ∧ AssignmentsBound sv pairs := by
  have shape : ∀ st ∈ m.body, ∃ l r, st = .assign l r ∧ PrintShape r := by
    intro st hs
    obtain ⟨l, r, n, eq, ht, _⟩ := typed st hs
    exact ⟨l, r, eq, ht.printShape⟩
  have table := declarationTable_emitted pd shape ast
  have declared : ∀ x, (∃ p ∈ m.wires ++ m.inputs ++ m.outputs, p.name = x) →
      Declared sv x ∧ Sparkle.Backend.Verilog.sanitizeName x = x := by
    intro x ⟨p, hp, eq⟩
    subst x
    have clean : Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
      rcases names p hp with h | h
      · exact sanitizeName_of_clean h.1
      · rw [h]; simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
    refine ⟨?_, clean⟩
    refine ⟨(p.name, typeWidth p.ty), ?_, rfl⟩
    rw [table]
    have hv := (visibleDecls_mem consistent p).mpr hp
    simpa only [irTable, clean] using
      List.mem_map_of_mem (f := fun p : Port => (Sparkle.Backend.Verilog.sanitizeName p.name, typeWidth p.ty)) hv
  have internal : ∀ x, 0 < weOf m x → Declared sv x ∧ Sparkle.Backend.Verilog.sanitizeName x = x := by
    intro x hx
    obtain ⟨p, hp, eq⟩ := positive_declared hx
    exact declared x ⟨p, by simp [hp], eq⟩
  have output : Declared sv "out" ∧ Sparkle.Backend.Verilog.sanitizeName "out" = "out" := by
    obtain ⟨p, hp, eq⟩ := List.mem_map.mp out
    exact declared _ ⟨p, by simp [hp], eq⟩
  have left : ∀ l r, Stmt.assign l r ∈ m.body →
      Declared sv l ∧ Sparkle.Backend.Verilog.sanitizeName l = l := by
    intro l r hs
    obtain ⟨l', r', n, eq, ht, hl⟩ := typed _ hs
    cases eq
    rcases hl with hl | rfl
    · exact internal l (by rw [hl]; exact ht.positive)
    · exact output
  obtain ⟨tree, pairs, treeEq, emitted, items⟩ := module_combItems_names m pd shape
    (fun l r hs => (left l r hs).2)
  rw [ast] at treeEq
  cases treeEq
  refine ⟨pairs, items, ?_⟩
  have bindBody : ∀ body pairs, (∀ st ∈ body, st ∈ m.body) →
      emitAssigns (printWidths (m.wires ++ m.inputs ++ m.outputs)) body = some pairs →
      AssignmentsBound sv pairs := by
    intro body
    induction body with
    | nil => intro pairs _ he; simp [emitAssigns] at he; subst pairs; simp [AssignmentsBound]
    | cons st rest ih =>
      intro pairs sub he
      obtain ⟨l, r, n, rfl, ht, _⟩ := typed st (sub st List.mem_cons_self)
      simp only [emitAssigns, bind, Option.bind_eq_some_iff] at he
      obtain ⟨rhs, hr, tail, htail, eq⟩ := he
      cases eq
      have br := emitExpr_bound ht.printShape (fun x hx => by
        have d := internal x (ht.refs_positive x hx)
        rw [d.2]; exact d.1) hr
      intro step hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨(left l r (sub _ List.mem_cons_self)).1, br⟩
      · exact ih tail (fun st hs => sub st (List.mem_cons_of_mem _ hs)) htail step hm
  exact bindBody m.body pairs (fun _ h => h) emitted

/-- A flat typed expression without a control root is in the arithmetic
checker domain. Recursive control expressions cannot hide under flat operands. -/
theorem sized_of_flat {we e n} (h : TypedExpr we e n)
    (simple : simpleRhs e = true) (control : isControlExpr e = false)
    (cast : isCastExpr e = false) :
    Tools.ShippingTranslateSoundness.SizedExpr we e n := by
  cases h with
  | ref x => exact .ref x
  | const v n => exact .const v n
  | @bin op a b n ha hb hs =>
    have refs : ∃ x y, a = .ref x ∧ b = .ref y := by
      cases op <;> cases a <;> cases b <;> simp_all [Tools.ShippingScalarSoundness.Binary.operator, simpleRhs]
    obtain ⟨x, y, rfl, rfl⟩ := refs
    exact .bin op (ha.width ▸ .ref x) (hb.width ▸ .ref y) hs
  | compare hc => cases ‹Operator› <;> simp_all [isUnsignedCompare, isControlExpr, isControlBinOp]
  | signedCompare _ _ hc _ _ => cases ‹Operator› <;> simp_all [isSignedCompare, isControlExpr, isControlBinOp]
  | mux => cases control
  | zext => simp [isCastExpr] at cast
  | trunc => simp [isCastExpr] at cast
  | slice => simp [isCastExpr] at cast
  | cat => simp [isCastExpr] at cast
  | not1 => simp [isCastExpr] at cast

theorem printWidths_decl {m : Sparkle.IR.AST.Module} {p : Port}
    (hp : p ∈ m.wires ++ m.inputs ++ m.outputs)
    (pt : PrintableType p.ty)
    (names : ∀ q ∈ m.wires ++ m.inputs ++ m.outputs, Sparkle.Backend.Verilog.sanitizeName q.name = q.name)
    (consistent : ∀ q ∈ m.wires ++ m.inputs ++ m.outputs,
      ∀ r ∈ m.wires ++ m.inputs ++ m.outputs, q.name = r.name → q = r) :
    printWidths (m.wires ++ m.inputs ++ m.outputs) p.name = some p.ty.bitWidth := by
  unfold printWidths
  cases hf : (m.wires ++ m.inputs ++ m.outputs).find?
      (fun q => Sparkle.Backend.Verilog.sanitizeName q.name == p.name) with
  | none =>
    have hn := List.find?_eq_none.mp hf p hp
    simp [names p hp] at hn
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have eq : q.name = p.name := by simpa [names q hq] using List.find?_some hf
    have eq := consistent q hq p hp eq
    subst q
    simp only [Option.bind_some]
    generalize p.ty = ty at pt ⊢
    cases pt <;> rfl

/-- In the branch without comparison/mux, the existing optimizer guard's
printing premise is derived, including the one-bit output assignment. -/
theorem post_printCheck {m m' : Sparkle.IR.AST.Module}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m) (simple : SimpleStmts m'.body)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m))
    (control : ¬ HasControl m'.body) (castFree : ¬ HasCast m'.body) :
    Sparkle.IR.PrintCheck.moduleCheck m' = true := by
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
  unfold Sparkle.IR.PrintCheck.moduleCheck
  rw [List.all_eq_true]
  intro st hs
  obtain ⟨l, r, n, rfl, ht, hl⟩ := typed.1 st hs
  obtain ⟨l', r', eq, flat⟩ := simple _ hs
  cases eq
  have noControl : isControlExpr r = false := by
    cases hc : isControlExpr r
    · rfl
    · exact False.elim (control ⟨l, r, hs, hc⟩)
  have noCast : isCastExpr r = false := by
    cases hc : isCastExpr r
    · rfl
    · exact False.elim (castFree ⟨l, r, hs, hc⟩)
  have sized := sized_of_flat ht flat noControl noCast
  have wiresClean : ∀ p ∈ m'.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name :=
    fun p hp => clean p (by simp [hp])
  have rhsCheck := printExpr_of_sized sized (fun x hx =>
    printWidths_wire ht.positive (Tools.ShippingSVBridge.SizedExpr.refs_width sized x hx) wiresClean)
  have lhs : Sparkle.Backend.Verilog.sanitizeName l = l ∧
      Sparkle.IR.PrintCheck.widths m' l = some n := by
    rcases hl with hl | rfl
    · exact printWidths_wire ht.positive hl wiresClean
    · have hn := ht.width.symm.trans (typed.2 r hs).width
      obtain ⟨ty, out⟩ := base.output
      have hp : ({name := "out", ty := ty} : Port) ∈ m'.outputs := by rw [ho, out]; simp
      have width := base.outputWidth _ (ho ▸ hp)
      have hw := printWidths_decl (m := m') (p := {name := "out", ty := ty})
        (by simp [hp]) (pd.2.2 _ (by simp [hp])) clean consistent
      rw [width, ← hn] at hw
      exact ⟨by simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq], hw⟩
  simp only [lhs.2, lhs.1, beq_self_eq_true, Bool.true_and, decide_eq_true ht.positive,
    Bool.true_and, rhsCheck]

/-- A concrete grammar derivation and bindings for the same emitted AST. -/
def SyntaxBound (m : Sparkle.IR.AST.Module) (text : String) : Prop :=
  ∃ sv pairs, emitAstModule m = some sv ∧ Declarations m sv ∧
    combItems sv.items = some pairs ∧ AssignmentsBound sv pairs ∧
    Tools.SVParser.ConcreteSyntax.Module sv text

theorem post_name {m m' : Sparkle.IR.AST.Module} (ready : TypedPostReady m)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    m'.name = m.name := by
  have hd : (dropZeroWidthModule m).name = m.name := by unfold dropZeroWidthModule; split <;> rfl
  rcases post with rfl | rfl
  · exact hd
  · unfold mergeDuplicates
    simp only [(dropZeroWidth_typed ready).2.2.2.2.isAssign, if_true]
    split <;> exact hd

theorem post_syntax {m m' : Sparkle.IR.AST.Module}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    SyntaxBound m' (Sparkle.Backend.Verilog.toVerilog m') := by
  obtain ⟨hi, ho, sub⟩ := post_layout ready post
  obtain ⟨names, consistent, ports, wires⟩ := declaration_layout base ready hi ho sub
  have typed : TypedStmts (weOf m') m'.body := by
    have hd := dropZeroWidth_typed ready
    rcases post with rfl | rfl
    · exact hd.2.2.2.2
    · exact mergeDuplicates_typed (by rw [hd.2.1]; exact ready.outWidthZero) hd.2.2.2.2
  have pd := mixed_post_printDecls base ready post
  have shape : ∀ st ∈ m'.body, ∃ l r, st = .assign l r ∧ PrintShape r := by
    intro st hs
    obtain ⟨l, r, n, eq, ht, _⟩ := typed st hs
    exact ⟨l, r, eq, ht.printShape⟩
  obtain ⟨sv, ast, render⟩ := emitModule_render m' pd.1 pd.2.1 pd.2.2 shape
  have decls := declarations_of_layout names consistent ports wires pd shape ast
  obtain ⟨ty, out⟩ := base.output
  obtain ⟨pairs, items, bound⟩ := typed_bindings pd typed (by rw [ho, out]; simp) names consistent ast
  have mn := post_name ready post
  refine ⟨sv, pairs, ast, decls, items, bound, renderModule_syntax render ?_ decls.identifiers items bound⟩
  rw [emitted_name ast, mn]
  exact base.moduleName

/-- Control-bearing mixed modules retain the proved postprocessed AST in the
actual checked optimizer, so the grammar derivation describes `verilogOf`. -/
theorem post_control_syntax {m m' : Sparkle.IR.AST.Module}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m) (simple : SimpleStmts m.body)
    (control : HasControl m.body)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    SyntaxBound (checkedOptimize m') (verilogOf m') := by
  have simple' : SimpleStmts m'.body := by
    have hd : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact hd
    · exact mergeDuplicates_simple _ hd
  have control' : HasControl m'.body := by
    have hd : HasControl (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact control
    rcases post with rfl | rfl
    · exact hd
    · exact mergeDuplicates_hasControl _ (by rw [(dropZeroWidth_typed ready).1]; exact simple) hd
  unfold verilogOf
  rw [checkedOptimize_control (simpleBody_of m' simple') control']
  exact post_syntax base ready post

/-- Full binding and concrete grammar for the real selected module. Both
optimizer retention and acceptance are covered without a caller certificate. -/
theorem checked_syntax {m m' : Sparkle.IR.AST.Module}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m) (simple : SimpleStmts m.body)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    SyntaxBound (checkedOptimize m') (verilogOf m') := by
  have simple' : SimpleStmts m'.body := by
    have hd : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact hd
    · exact mergeDuplicates_simple _ hd
  have gate := simpleBody_of m' simple'
  by_cases control : HasControl m'.body
  · unfold verilogOf
    rw [checkedOptimize_control gate control]
    exact post_syntax base ready post
  · by_cases cast : HasCast m'.body
    · unfold verilogOf
      rw [checkedOptimize_cast gate cast]
      exact post_syntax base ready post
    have check := checkedOptimize_printCheck gate (post_printCheck base ready simple' post control cast)
    have pd := checkedOptimize_printDecls gate (mixed_post_printDecls base ready post)
    have shape := checkedOptimize_printShape gate
    obtain ⟨sv, ast, render⟩ := emitModule_render _ pd.1 pd.2.1 pd.2.2 shape
    have decls := checked_declarations base ready simple post pd shape ast
    have forward := (forwardCheck_sound (printCheck_forward check)).2
    obtain ⟨sv', pairs, ast', emitted, items⟩ := module_combItems _ pd shape forward
    rw [ast] at ast'
    cases ast'
    rw [← decls.widths] at emitted
    have bound := emitAssigns_bound decls.widths shape (fun st hs => List.all_eq_true.mp check st hs) emitted
    refine ⟨sv, pairs, ast, decls, items, bound, renderModule_syntax render ?_ decls.identifiers items bound⟩
    rw [emitted_name ast, checkedOptimize_name, post_name ready post]
    exact base.moduleName


/-- The selected IR value and the actual output text share one emitted AST. -/
def SyntaxValue (m : Sparkle.IR.AST.Module) (initial : Env) (mems : MEnv) (expected : Nat) : Prop :=
  RenderedValue m initial mems expected ∧ SyntaxBound (checkedOptimize m) (verilogOf m)

theorem mixed_syntax {declName bs body m m'} (source : MixedPreserves declName bs body m)
    (positive : PositiveBinders bs)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    MixedSourcePreserves declName bs body (SyntaxValue m') := by
  apply MixedSourcePreserves.map source
  intro initial mems expected h
  have render := rendered_of_entry h positive post
  obtain ⟨_, _, _, ready, simple, _, _, _, base⟩ := h
  exact ⟨render, checked_syntax (base positive) ready simple post⟩

theorem synthesizeCombinational_mixed_syntax {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        MixedSourcePreserves declName bs body (SyntaxValue m) := by
  obtain ⟨raw, design, world, core, post⟩ := synthesizeCombinational_reads hr
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_mixed_sound core
  exact ⟨ci, w1, w2, get, fun bs body old shape =>
    mixed_syntax (source bs body old shape) (mixedShape_positive (shape (fun _ => false))) post⟩
/-- The syntactically valid, bound module observes the actual library Signals. `EnvDefines`
remains the explicit boundary identifying the runtime declaration. -/
theorem syntax_source_of_env {declName : Name} {mctx : Meta.Context}
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
      SyntaxValue m initial mems (Tools.ShippingMuxLoweringSoundness.encodeBool
        ((Tools.ShippingBoolSourceSoundness.denoteB n (fun j => bools (bpos j))
          (fun j => bits (vpos j) n) e).val tick)) := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinational_mixed_syntax hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := by
    simp [certifiedShape?, definition, old]
  have mixedGate := Tools.ShippingMixedSourceBridge.source_gate (d := d)
    (by rw [definition]; exact peel) hn he hb hv
  exact Tools.ShippingMixedSourceBridge.source_signals (source bs _ oldGate mixedGate) hn he hb hv

end Tools.ShippingMixedBindingSoundness
