import Tools.ShippingMixedPostSoundness
import Tools.ShippingMixedSourceBridge
import Tools.ShippingPrintEntrySoundness

/-! Complete shipping module rendering for the mixed source fragment.
This layer proves text/AST rendering equality, separately from identifier,
binding and concurrent-execution obligations. -/
namespace Tools.ShippingMixedPrintSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup
open Tools.ShippingEntrySoundness Tools.ShippingPostSoundness Tools.ShippingTypedPostSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedPostSoundness
open Tools.ShippingPrintEntrySoundness Tools.ShippingModulePrintSoundness Tools.ShippingPrintSoundness
open Tools.SVParser.AST Tools.SVParser.EmitAst

theorem printBase_concrete {m : Sparkle.IR.AST.Module} (h : PrintBase m) : allConcrete m = true := by
  unfold allConcrete
  rw [List.all_eq_true]
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hi | ho
    · have ht := h.inputs p hi
      generalize p.ty = ty at ht ⊢
      cases ht <;> rfl
    · have ht := h.outputs p ho
      generalize p.ty = ty at ht ⊢
      cases ht <;> rfl
  · rcases h.wires p hp with ht | ⟨n, ht⟩ <;> simp [ht, HWType.bitWidth?]

theorem printBase_cleanup {m : Sparkle.IR.AST.Module} (h : PrintBase m) :
    PrintableDecls (dropZeroWidthModule m) := by
  unfold PrintableDecls dropZeroWidthModule
  simp only [printBase_concrete h, Bool.not_true, Bool.false_eq_true, if_false]
  refine ⟨h.primitive, h.parameters, ?_⟩
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hi | ho
    · exact h.inputs p hi
    · exact h.outputs p ho
  · obtain ⟨hp, nz⟩ := List.mem_filter.mp hp
    rcases h.wires p hp with ht | ⟨n, ht⟩
    · rw [ht]; exact .bit
    · rw [ht]; apply PrintableType.bits
      simp [ht, HWType.bitWidth] at nz
      omega

theorem mixed_post_printDecls {m m' : Sparkle.IR.AST.Module}
    (base : PrintBase m) (ready : TypedPostReady m)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    PrintableDecls m' := by
  have hp := printBase_cleanup base
  rcases post with rfl | rfl
  · exact hp
  · have hall := (dropZeroWidth_typed ready).2.2.2.2.isAssign
    unfold mergeDuplicates
    simp only [hall, if_true]
    split <;> exact hp

/-- A successful mixed gate cannot hide a zero-width input binder. -/
theorem mixedBinder_positive {ty n} (h : mixedGateBinderKind? ty = some (.bits n)) : 0 < n := by
  unfold mixedGateBinderKind? at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨k, _, hk⟩ := Option.bind_eq_some_iff.mp h
      split at hk
      · cases hk; assumption
      · cases hk
    · cases h

theorem mixedPeel_positive {value bs body} (h : mixedGatePeel value = some (bs, body)) :
    PositiveBinders bs := by
  induction value generalizing bs body with
  | lam name ty value info ihTy ih =>
    simp only [mixedGatePeel] at h
    split at h
    · rename_i kind rest result hk hr
      cases h
      intro nm n mem
      rcases List.mem_cons.mp mem with eq | mem
      · cases eq; exact mixedBinder_positive hk
      · exact ih hr nm n mem
    · cases h
  | _ => cases h; intro name n mem; cases mem

theorem mixedShape_positive {ci bs body} (h : mixedCertifiedShape? false [] ci = some (bs, body)) :
    PositiveBinders bs := by
  cases ci <;> try cases h
  unfold mixedCertifiedShape? at h
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or, Bool.false_eq_true, if_false] at h
  split at h
  · rename_i binders result peel
    split at h
    · cases h; exact mixedPeel_positive peel
    · cases h
  · cases h

/-- Full printed module equality on the actual postprocessing and checked
optimizer path, alongside the source value. Positivity is a pure source-binder
condition, discharged by `mixedShape_positive` at the real entry. -/
theorem mixed_rendered {declName bs body m m'} (source : MixedPreserves declName bs body m)
    (positive : PositiveBinders bs)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    MixedSourcePreserves declName bs body fun initial mems expected =>
      ∃ result sv, evalAssigns (weOf (checkedOptimize m')) mems (checkedOptimize m').body initial = some result ∧
        result "out" = expected ∧ emitAstModule (checkedOptimize m') = some sv ∧
        renderModule (checkedOptimize m').name
          ((checkedOptimize m').wires.filter fun p =>
            !(((checkedOptimize m').inputs ++ (checkedOptimize m').outputs).map (·.name)).contains p.name).length sv
          = some (verilogOf m') := by
  apply MixedSourcePreserves.map source
  intro initial mems expected h
  obtain ⟨result, run, value, ready, simple, widths, out, bounds, base⟩ := h
  rw [← widths] at run
  have postWidths := typed_postprocess_widths ready post run
  obtain ⟨run', _, inputs, outputs⟩ := typed_postprocess_sound ready post mems initial result run
  have simple' : SimpleStmts m'.body := by
    have sd : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact sd
    · exact mergeDuplicates_simple _ sd
  have gate := simpleBody_of m' simple'
  have pd := checkedOptimize_printDecls gate (mixed_post_printDecls (base positive) ready post)
  obtain ⟨sv, ast, text⟩ := emitModule_render _ pd.1 pd.2.1 pd.2.2 (checkedOptimize_printShape gate)
  obtain ⟨final, finalRun, agrees, _⟩ := checkedOptimize_flat_sound simple'
    (by rw [inputs, postWidths]; exact bounds) run'
  obtain ⟨port, hp, name⟩ := List.mem_map.mp out
  have val := agrees port (outputs ▸ hp)
  rw [name, value] at val
  exact ⟨final, sv, finalRun, val, ast, text⟩

/-- The source value and the complete shipping text describe the same selected
IR module. This rendering relation is not yet the concrete grammar judgment. -/
def RenderedValue (m : Sparkle.IR.AST.Module) (initial : Env) (mems : MEnv) (expected : Nat) : Prop :=
  ∃ result sv, evalAssigns (weOf (checkedOptimize m)) mems (checkedOptimize m).body initial = some result ∧
    result "out" = expected ∧ emitAstModule (checkedOptimize m) = some sv ∧
    renderModule (checkedOptimize m).name
      ((checkedOptimize m).wires.filter fun p =>
        !(((checkedOptimize m).inputs ++ (checkedOptimize m).outputs).map (·.name)).contains p.name).length sv
      = some (verilogOf m)

theorem synthesizeCombinational_mixed_rendered {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        MixedSourcePreserves declName bs body (RenderedValue m) := by
  obtain ⟨raw, design, world, core, post⟩ := synthesizeCombinational_reads hr
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_mixed_sound core
  exact ⟨ci, w1, w2, get, fun bs body old shape =>
    mixed_rendered (source bs body old shape) (mixedShape_positive shape) post⟩

/-- The rendered module observes the actual library Signals. `EnvDefines`
remains the explicit boundary identifying the runtime declaration. -/
theorem rendered_source_of_env {declName : Name} {mctx : Meta.Context}
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
      RenderedValue m initial mems (Tools.ShippingMuxLoweringSoundness.encodeBool
        ((Tools.ShippingBoolSourceSoundness.denoteB n (fun j => bools (bpos j))
          (fun j => bits (vpos j) n) e).val tick)) := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinational_mixed_rendered hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := by
    simp [certifiedShape?, definition, old]
  have mixedGate := Tools.ShippingMixedSourceBridge.source_gate (d := d)
    (by rw [definition]; exact peel) hn he hb hv
  exact Tools.ShippingMixedSourceBridge.source_signals (source bs _ oldGate mixedGate) hn he hb hv

end Tools.ShippingMixedPrintSoundness
