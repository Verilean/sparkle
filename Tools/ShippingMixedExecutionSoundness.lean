import Tools.ShippingMixedForwardSoundness
import Tools.ShippingDeltaSemantics

/-! Actual mixed shipping compilation to two-state zero-delay RTL settling.
Initial values are bounded by the emitted declarations; no order, checking or
convergence certificate is requested from the caller. -/
namespace Tools.ShippingMixedExecutionSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedPrintSoundness
open Tools.ShippingMixedDeclSoundness Tools.ShippingMixedBindingSoundness
open Tools.ShippingMixedForwardSoundness Tools.ShippingTypedPostSoundness
open Tools.ShippingEntrySoundness Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingPrintEntrySoundness Tools.ShippingSVBridge Tools.ShippingDeclWidths
open Tools.ShippingPostSoundness Tools.ShippingOptSoundness
open Tools.ShippingSettledSoundness Tools.ShippingDeltaSemantics
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem

/-- Order survives both actual postprocessing choices and optimizer selections. -/
theorem checked_order {m m' : Sparkle.IR.AST.Module}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m) (simple : SimpleStmts m.body)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    Acyclic (checkedOptimize m').body := by
  have hd : Acyclic (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact base.order
  have hs : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
  have hp : Acyclic m'.body ∧ SimpleStmts m'.body := by
    rcases post with rfl | rfl
    · exact ⟨hd, hs⟩
    · exact ⟨mergeDuplicates_order hd, mergeDuplicates_simple _ hs⟩
  exact checkedOptimize_order (simpleBody_of m' hp.2) hp.1

/-- Scalar Bool ports have a one-bit output observation too. -/
theorem emitted_bit_output {m : Sparkle.IR.AST.Module} {sv : SVModule} {p : Port}
    (h : emitAstModule m = some sv) (ho : m.outputs = [p]) (ht : p.ty = .bit) :
    declaredOutputWidth sv (Sparkle.Backend.Verilog.sanitizeName p.name) = some 1 := by
  obtain ⟨ins, outs, hi, hs, he⟩ := emitAstModule_ports h
  rw [ho] at hs
  simp [List.mapM_cons, astPort, ht, widthAstOf] at hs
  subst outs
  unfold declaredOutputWidth
  rw [he, List.find?_append]
  have hnone : ins.find? (fun sp => sp.dir == .output &&
      sp.name == Sparkle.Backend.Verilog.sanitizeName p.name) = none := by
    apply List.find?_eq_none.mpr
    intro sp hp
    simp [ports_dir hi sp hp, show (SVPortDir.input == .output) = false from rfl]
  simp [hnone, declaredPortWidth, show (SVPortDir.output == .output) = true from rfl]

theorem checked_output {m m' : Sparkle.IR.AST.Module} {sv : SVModule}
    (base : PrintBaseAt outWidth m) (ready : TypedPostReady m) (simple : SimpleStmts m.body)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m))
    (ast : emitAstModule (checkedOptimize m') = some sv)
    (decls : Declarations (checkedOptimize m') sv) :
    declaredOutputWidth sv "out" = some outWidth ∧ astWidths sv "out" = some outWidth := by
  have simple' : SimpleStmts m'.body := by
    have hs : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact hs
    · exact mergeDuplicates_simple _ hs
  have gate := simpleBody_of m' simple'
  have ho := (checkedOptimize_ports gate).2.trans (post_layout ready post).2.1
  obtain ⟨ty, out⟩ := base.output
  have output : (checkedOptimize m').outputs = [{name := "out", ty := ty}] := ho.trans out
  have rawPort : ({name := "out", ty := ty} : Port) ∈ m.outputs := by rw [out]; simp
  have pt := base.outputs _ rawPort
  have width := base.outputWidth _ rawPort
  have cleanOut : Sparkle.Backend.Verilog.sanitizeName "out" = "out" := by
    simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
  constructor
  · cases pt with
    | bit =>
      change 1 = outWidth at width
      simpa only [cleanOut, width] using emitted_bit_output ast output rfl
    | bits n hn =>
      change n = outWidth at width
      subst n
      simpa only [cleanOut] using emitAstModule_outputWidth ast output rfl hn
  · obtain ⟨names, consistent, _, _⟩ := checked_layout base ready simple post
    rw [decls.widths]
    have hp : ({name := "out", ty := ty} : Port) ∈ (checkedOptimize m').outputs := by rw [output]; simp
    have hw := printWidths_decl (m := checkedOptimize m') (p := {name := "out", ty := ty})
      (by simp [hp]) pt (by
        intro p hp
        rcases names p hp with h | h
        · exact sanitizeName_of_clean h.1
        · rw [h]; exact cleanOut) consistent
    simpa only [width] using hw

/-- The same printed AST has a unique bounded solution and all permitted
parallel delta traces converge to the source output within its assignment count.
Bounds on initialization are explicit two-state input conditions. -/
def ExecutionValue (m : Sparkle.IR.AST.Module) (initial : Env) (mems : MEnv) (expected : Nat) : Prop :=
  SyntaxValue m initial mems expected ∧
  ∃ sv pairs, emitAstModule (checkedOptimize m) = some sv ∧ combItems sv.items = some pairs ∧
    (Bounded (fun x => (astWidths sv x).getD 0) initial →
      ∃ stable, evalAssignsSV (astWidths sv) mems pairs initial = some stable ∧
        observeUnsignedOutput sv stable "out" = some expected ∧
        SVSolution (astWidths sv) pairs initial stable ∧
        (∀ other, Bounded (fun x => (astWidths sv x).getD 0) other →
          SVSolution (astWidths sv) pairs initial other → other = stable) ∧
        SettlesTo sv pairs initial expected)

theorem execution_of_entry {bs m m' initial mems expected}
    (h : RawValueAt outWidth bs m initial mems expected) (positive : PositiveBinders bs)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    ExecutionValue m' initial mems expected := by
  have render := rendered_of_entry h positive post
  obtain ⟨_, _, _, ready, simple, _, _, _, base⟩ := h
  have check := checked_forwardCheck (base positive) ready simple post
  have order := checked_order (base positive) ready simple post
  have syntaxProof := checked_syntax (base positive) ready simple post
  obtain ⟨result, sv, run, value, ast, text, decls⟩ := render
  have simple' : SimpleStmts m'.body := by
    have hd : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact hd
    · exact mergeDuplicates_simple _ hd
  have gate := simpleBody_of m' simple'
  have pd := checkedOptimize_printDecls gate (mixed_post_printDecls (base positive) ready post)
  have shape := checkedOptimize_printShape gate
  obtain ⟨reads, checks⟩ := forwardCheck_sound check
  obtain ⟨sv', pairs, ast', emitted, items⟩ := module_combItems _ pd shape checks
  rw [ast] at ast'
  cases ast'
  have fw : forwardWidths (checkedOptimize m') = fun x => (astWidths sv x).getD 0 := by
    funext x; rw [decls.widths]; rfl
  rw [← decls.widths, fw] at checks
  rw [← decls.widths] at emitted
  have lookup : ∀ x n, astWidths sv x = some n → (astWidths sv x).getD 0 = n := by
    intro x n hx; simp [hx]
  have output := checked_output (base positive) ready simple post ast decls
  refine ⟨⟨⟨result, sv, run, value, ast, text, decls⟩, syntaxProof⟩, sv, pairs, ast, items, ?_⟩
  intro bound
  have allBounds : ∀ x n, astWidths sv x = some n → initial x < 2 ^ n := by
    intro x n hx; simpa only [hx, Option.getD_some] using bound x
  obtain ⟨pairs', stable, items', stableRun, stableBound, stableWidths, solution, unique⟩ :=
    module_settled pd shape ast decls.widths checks order mems initial bound allBounds
  rw [items] at items'
  cases items'
  obtain ⟨pairs'', stable', emitted', irRun, svRun, _, _⟩ :=
    emit_sem_assigns mems _ initial checks bound allBounds
  rw [emitted] at emitted'
  cases emitted'
  rw [stableRun] at svRun
  cases svRun
  rw [← fw] at irRun
  rw [← evalAssigns_widths _ (Tools.ShippingEntrySoundness.weOf (checkedOptimize m')) _ mems shape reads initial] at irRun
  rw [run] at irRun
  cases irRun
  have observed : observeUnsignedOutput sv result "out" = some expected := by
    have b := stableWidths "out" outWidth output.2
    simp only [observeUnsignedOutput, output.1, bind, Option.bind_some]
    rw [Nat.mod_eq_of_lt b, value]
  refine ⟨result, stableRun, observed, solution, ?_, ?_⟩
  · intro other hb hs
    exact unique other hb (fun x n hx => by simpa only [hx, Option.getD_some] using hb x) hs
  · refine ⟨result, stableBound, solution, observed, ?_⟩
    intro seed hseed hframe
    refine ⟨deltaTrace_exists order checks emitted lookup hseed, ?_⟩
    intro trace htrace k hk
    have eq := deltaTrace_converges order checks emitted lookup solution stableBound hseed hframe htrace k hk
    exact ⟨eq, eq ▸ observed⟩

theorem mixed_execution {declName bs body m m'} (source : MixedPreserves declName bs body m)
    (positive : PositiveBinders bs)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    MixedSourcePreserves declName bs body (ExecutionValue m') :=
  MixedSourcePreserves.map source (fun _ _ _ h => execution_of_entry h positive post)

theorem synthesizeCombinational_mixed_execution {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        MixedSourcePreserves declName bs body (ExecutionValue m) := by
  obtain ⟨raw, design, world, core, post⟩ := synthesizeCombinational_reads hr
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_mixed_sound core
  exact ⟨ci, w1, w2, get, fun bs body old shape =>
    mixed_execution (source bs body old shape) (mixedShape_positive (shape (fun _ => false))) post⟩
/-- Finite RTL settling observes the actual library Signals. `EnvDefines`
remains the explicit boundary identifying the runtime declaration. -/
theorem execution_source_of_env {declName : Name} {mctx : Meta.Context}
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
      ExecutionValue m initial mems (Tools.ShippingMuxLoweringSoundness.encodeBool
        ((Tools.ShippingBoolSourceSoundness.denoteB n (fun j => bools (bpos j))
          (fun j => bits (vpos j) n) e).val tick)) := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinational_mixed_execution hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := by
    simp [certifiedShape?, definition, old]
  have mixedGate := Tools.ShippingMixedSourceBridge.source_gate (d := d)
    (by rw [definition]; exact peel) hn he hb hv
  exact Tools.ShippingMixedSourceBridge.source_signals (source bs _ oldGate mixedGate) hn he hb hv

end Tools.ShippingMixedExecutionSoundness
