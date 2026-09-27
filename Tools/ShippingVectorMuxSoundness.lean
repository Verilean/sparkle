import Tools.ShippingVectorMuxRecursion
import Tools.ShippingContractEntrySoundness
import Tools.ShippingMixedExecutionSoundness

/-! Entry and backend connection for BitVec mux trees. -/
namespace Tools.ShippingVectorMuxSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedOutputSoundness Tools.ShippingMixedInputSoundness
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMixedBinarySoundness Tools.ShippingMixedRecursion Tools.ShippingTypedPostSoundness
open Tools.ShippingPostSoundness Tools.ShippingCompareLoweringSoundness
open Tools.ShippingModulePrintSoundness Tools.ShippingPrintSoundness

open Tools.ShippingVectorMuxRecursion Tools.ShippingContractEntrySoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedExecutionSoundness
open Tools.ShippingMixedOrderSoundness Tools.ShippingMixedSourceBridge
open Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup Tools.ShippingMixedPrintSoundness

def VectorSourcePreserves (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (observes : Nat → Env → MEnv → Nat → Prop) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits initial (bs.zip ids) a →
    ∀ (dom : Lean.Expr) (n kb kv : Nat) (binp vinp : Nat → FVarId)
      (bvals : Nat → Bool) (vvals : Nat → BitVec n) (e : VExpr),
    0 < n → e.WF kb kv n →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨n, vvals j⟩) →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      quoteV dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e →
    observes n initial mems (evalV n bvals vvals e).toNat

def VectorPreserves (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (m : Sparkle.IR.AST.Module) : Prop :=
  VectorSourcePreserves declName bs body (fun n => RawValueAt n bs m)

theorem VectorSourcePreserves.map {declName bs body P Q}
    (h : VectorSourcePreserves declName bs body P)
    (f : ∀ n initial mems expected, P n initial mems expected → Q n initial mems expected) :
    VectorSourcePreserves declName bs body Q := by
  obtain ⟨ids, nd, len, cache, h⟩ := h
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems a p values dom n kb kv binp vinp bvals vvals e hn he hb hv quote
  exact f n initial mems _ (h bools bits initial mems values dom n kb kv binp vinp bvals vvals e hn he hb hv quote)

theorem synthesizeMixedCertified_vector_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body) (m, d)) :
    VectorPreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, nameLegal⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems a p values dom n kb kv binp vinp bvals vvals e hn he hb hv quote
  have empty := empty_layout (entryCompilerState false cache) declName.toString initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  have leaf := prepare_returns (bs.zip ids) a (bools := bools) (bits := bits) run
  rw [quote] at leaf
  have contract := vector_fuel_contract translateFuelLimit (ctx := p.context) (we := declaredWidths st)
    (mems := mems) (initial := initial) (dom := dom) hn hb hv e he
  have ordered := vector_fuel_orders translateFuelLimit (ctx := p.context) (we := declaredWidths st)
    (mems := mems) (initial := initial) (dom := dom) hn hb hv e he "out" true
  obtain ⟨unique, result, eval, value, out, typed, _⟩ := emitLeaves_from_ports hn contract
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 leaf
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  have outputEq : m.outputs = st.module.outputs.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
  have shape := prepare_shape (bools := bools) (bits := bits) (bs.zip ids) a (by intro p hp; cases hp)
  obtain ⟨wm, ready, printOutputs, outputTyped, outputWidth, order⟩ := emitLeaves_postReady_at hn contract ordered
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 shape.1 shape.2 wireEq bodyEq outputEq leaf
  have ib := prepare_inputBounds (bs.zip ids) a (by intro p hp; cases hp) values
  obtain ⟨w, sm, ty, tr, fresh, ht, hty⟩ := emitLeaves_single leaf
  have frame := contract.frame "out" false true p.state sm w (prepared.1.lookup prepared.2.1) tr
  refine ⟨result, ?_, value, ready, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moduleWidths_finish wireEq unique, bodyEq]; exact eval
  · have simple := frame.simple (by rw [prepared.2.2.1]; intro stmt hs; cases hs)
    intro stmt hs
    rw [bodyEq] at hs
    change stmt ∈ st.module.body.reverse at hs
    rw [List.mem_reverse, ht, emitAssign_body_cons] at hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨"out", .ref w, rfl, rfl⟩
    · exact simple stmt hs
  · rw [wm, moduleWidths_finish wireEq unique]
  · rw [outputEq, List.map_reverse, List.mem_reverse]; exact out
  · intro port hp
    have noSeq := addClockReset_assigns st.module (by
      intro stmt hs
      have hs' : stmt ∈ st.module.finalize.body := List.mem_reverse.mpr hs
      obtain ⟨l, rhs, n, eq, _⟩ := typed stmt hs'
      exact ⟨l, rhs, eq⟩)
    have mi : m.inputs = st.module.inputs.reverse := by rw [hm, noSeq]; rfl
    have hp' : port ∈ p.state.module.inputs := by
      rw [mi, List.mem_reverse, ht, emitAssign_inputs] at hp
      exact frame.inputs ▸ hp
    obtain ⟨decl, bound⟩ := ib port hp'
    rw [wm, declaredWidths_agree unique port (by rw [ht, emitAssign_wires]; exact frame.decls port decl)]
    exact bound
  · intro positive
    have pi := prepare_print (bools := bools) (bits := bits) (bs.zip ids) a
      (by intro port hp; cases hp) (fun name n id hp => positive name n (List.of_mem_zip hp).1)
    have noSeq := addClockReset_assigns st.module (by
      intro stmt hs
      obtain ⟨l, rhs, n, eq, _⟩ := typed stmt (List.mem_reverse.mpr hs)
      exact ⟨l, rhs, eq⟩)
    have mi : m.inputs = st.module.inputs.reverse := by rw [hm, noSeq]; rfl
    have decls := prepare_declarations (bools := bools) (bits := bits) (bs.zip ids) a
      (List.Sublist.refl []) (by intro port hp; cases hp)
    refine ⟨?_, ?_, ?_, printOutputs, ?_, ?_, ?_, ?_, ?_, outputTyped, outputWidth, order, nameLegal⟩
    · rw [hm, noSeq]
      change st.module.isPrimitive = false
      rw [ht]; change sm.module.isPrimitive = false
      rw [frame.primitive]; exact pi.2.2
    · rw [hm, noSeq]
      change st.module.parameters.reverse = []
      rw [ht]; change sm.module.parameters.reverse = []
      rw [frame.parameters, pi.2.1]; rfl
    · intro port hp
      rw [mi, List.mem_reverse, ht, emitAssign_inputs] at hp
      exact pi.1 port (frame.inputs ▸ hp)
    · intro port hp
      rw [wireEq, List.mem_reverse, ht, emitAssign_wires] at hp
      exact frame.scalar shape.1 port hp
    · intro port hp
      rw [wireEq, List.mem_reverse, ht, emitAssign_wires] at hp
      exact (frame.wireNames port hp).elim (decls.2 port) id
    · rw [mi, List.map_reverse]
      apply nodup_reverse
      rw [ht, emitAssign_inputs]
      change (sm.module.inputs.map Port.name).Nodup
      rw [frame.inputs]
      exact prepared.2.1.1.sublist (decls.1.map _)
    · intro port hp
      rw [mi, List.mem_reverse, ht, emitAssign_inputs] at hp
      change port ∈ sm.module.inputs at hp
      rw [frame.inputs] at hp
      rw [wireEq, List.mem_reverse, ht, emitAssign_wires]
      exact frame.decls port (decls.1.subset hp)
    · refine ⟨ty, ?_⟩
      rw [outputEq, ht, emitAssign_outputs]
      change ( {name := "out", ty := ty} :: sm.module.outputs).reverse = _
      rw [frame.outputs, shape.2]; rfl

theorem synthesizeFromConst_vector_sound {logProf declName ci bs body m d}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName [] false true ci) (m, d)) :
    VectorPreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_vector_sound run

/-- The mixed result is tied to the declaration read by this very synthesis
run. As for the old entry, identifying that declaration with a source constant
is the separate `EnvDefines` trust boundary. -/
theorem synthesizeCombinationalCore_vector_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) → VectorPreserves declName bs body m := by
  obtain ⟨logProf, ci, w1, w2, w3, get, run⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape => synthesizeFromConst_vector_sound old shape run.mreturns⟩

theorem vector_execution {declName bs body m m'} (source : VectorPreserves declName bs body m)
    (positive : PositiveBinders bs)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    VectorSourcePreserves declName bs body (fun _ => ExecutionValue m') :=
  VectorSourcePreserves.map source (fun _ _ _ _ h => execution_of_entry h positive post)

theorem synthesizeCombinational_vector_execution {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        VectorSourcePreserves declName bs body (fun _ => ExecutionValue m) := by
  obtain ⟨raw, design, world, core, post⟩ := synthesizeCombinational_reads hr
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_vector_sound core
  exact ⟨ci, w1, w2, get, fun bs body old shape =>
    vector_execution (source bs body old shape) (mixedShape_positive shape) post⟩

open Tools.ShippingMixedGateSoundness Tools.ShippingMuxTypeSoundness
open Sparkle.Core.Domain Sparkle.Core.Signal

def denoteV {dom : DomainConfig} (n : Nat) (bools : Nat → Signal dom Bool)
    (bits : Nat → Signal dom (BitVec n)) : VExpr → Signal dom (BitVec n)
  | .arith e => denoteFE n bits e
  | .mux c a b => Signal.mux (denoteB n bools bits c) (denoteV n bools bits a) (denoteV n bools bits b)

theorem denoteV_val {dom : DomainConfig} (n : Nat) (bools : Nat → Signal dom Bool)
    (bits : Nat → Signal dom (BitVec n)) (tick : Nat) : ∀ e,
    (denoteV n bools bits e).val tick = evalV n (fun j => (bools j).val tick) (fun j => (bits j).val tick) e
  | .arith e => denoteFE_val n bits tick e
  | .mux c a b => by
    simp only [denoteV, library_mux, evalV, denoteB_val, denoteV_val n bools bits tick a,
      denoteV_val n bools bits tick b]

theorem instFVars_quoteV (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr) (n : Nat)
    (binp vinp : Nat → Lean.Expr) : ∀ e,
    instFVars xs d (quoteV dom n binp vinp e) =
      quoteV (instFVars xs d dom) n (fun j => instFVars xs d (binp j))
        (fun j => instFVars xs d (vinp j)) e
  | .arith e => instFVars_quoteF xs d dom n vinp e
  | .mux c a b => by
    show Lean.Expr.app (.app (.app (instFVars xs d _) (instFVars xs d (quoteB dom n binp vinp c)))
      (instFVars xs d (quoteV dom n binp vinp a))) (instFVars xs d (quoteV dom n binp vinp b)) = _
    rw [instFVars_quoteB, instFVars_quoteV, instFVars_quoteV]
    rfl

theorem quoteV_congr {dom : Lean.Expr} {n kb kv : Nat} {binp binp' vinp vinp' : Nat → Lean.Expr}
    (hb : ∀ j, j < kb → binp j = binp' j) (hv : ∀ j, j < kv → vinp j = vinp' j) :
    ∀ e, e.WF kb kv n → quoteV dom n binp vinp e = quoteV dom n binp' vinp' e
  | .arith e, he => quoteF_congr hv e he
  | .mux c a b, ⟨hc, ha, hb'⟩ => by
    simp only [quoteV, quoteB_congr hb hv c hc, quoteV_congr hb hv a ha, quoteV_congr hb hv b hb']

theorem instantiated_quoteV {xs : Array Lean.Expr} {dom : Lean.Expr} {n kb kv : Nat}
    {binp vinp : Nat → Lean.Expr} {bids vids : Nat → FVarId}
    (hb : ∀ j, j < kb → instFVars xs 0 (binp j) = .fvar (bids j))
    (hv : ∀ j, j < kv → instFVars xs 0 (vinp j) = .fvar (vids j))
    (e : VExpr) (he : e.WF kb kv n) :
    instFVars xs 0 (quoteV dom n binp vinp e) =
      quoteV (instFVars xs 0 dom) n (fun j => .fvar (bids j)) (fun j => .fvar (vids j)) e := by
  rw [instFVars_quoteV]
  exact quoteV_congr hb hv e he

theorem source_positions {declName bs dom n kb kv e P} {bpos vpos : Nat → Nat}
    (source : VectorSourcePreserves declName bs
      (quoteV dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) P)
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits initial →
      P n initial mems (evalV n (fun j => bools (bpos j)) (fun j => bits (vpos j) n) e).toNat := by
  obtain ⟨ids, nd, len, cache, source⟩ := source
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems values
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply source (boolValues ids bools) (bitValues ids bits) initial mems values
    (instFVars (ids.map Lean.Expr.fvar).toArray 0 dom)
    n kb kv (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) _ _ e hn he
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bool_lookup (bools := boolValues ids bools) (bits := bitValues ids bits)
      (bs.zip ids) (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hv j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bits_lookup (bools := boolValues ids bools) (bits := bitValues ids bits)
      (bs.zip ids) (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup
  · apply instantiated_quoteV _ _ e he
    · intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
    · intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose

/-- The same theorem observes actual library Signals at any source time.
No equality about the prepared compiler valuation remains a premise. -/
theorem source_signals {declName bs dom n kb kv e P} {bpos vpos : Nat → Nat}
    (source : VectorSourcePreserves declName bs
      (quoteV dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) P)
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : Sparkle.Core.Domain.DomainConfig}
        (bools : Nat → Sparkle.Core.Signal.Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs declName bs ids cache (fun j => (bools j).val tick)
        (fun j n => (bits j n).val tick) initial →
      P n initial mems ((denoteV n (fun j => bools (bpos j)) (fun j => bits (vpos j) n) e).val tick).toNat := by
  obtain ⟨ids, nd, len, cache, source⟩ := source_positions source hn he hb hv
  refine ⟨ids, nd, len, cache, ?_⟩
  intro D bools bits tick initial mems values
  rw [denoteV_val]
  exact source _ _ initial mems values


theorem vectorBody_of_gate {kinds n e}
    (h : gateBody (mixedBitKinds kinds) n e = true) : mixedGateVectorBody kinds n e = true := by
  unfold mixedGateVectorBody
  split
  · simp [gateBody, Lean.Expr.getAppFn, signalBinOpOf] at h
  · exact h

theorem vectorBody_quote {kinds : Array MixedGateBinder} {dom : Lean.Expr} {n kb kv : Nat}
    {binp vinp : Nat → Lean.Expr} (hn : 0 < n)
    (hb : ∀ j, j < kb → mixedGateBoolBody kinds (binp j) = true)
    (hv : ∀ j, j < kv → gateBody (mixedBitKinds kinds) n (vinp j) = true) :
    ∀ e, e.WF kb kv n → mixedGateVectorBody kinds n (quoteV dom n binp vinp e) = true
  | .arith e, he => vectorBody_of_gate (gateBody_inputs hv e he)
  | .mux c a b, ⟨hc, ha, hb'⟩ => by
    change (canonicalNatLitValue? (natE n) == some n &&
      mixedGateBoolBody kinds (quoteB dom n binp vinp c) &&
      mixedGateVectorBody kinds n (quoteV dom n binp vinp a) &&
      mixedGateVectorBody kinds n (quoteV dom n binp vinp b)) = true
    rw [canonicalNatLitValue?_natE, mixedGateBool_quote hn hb hv c hc,
      vectorBody_quote hn hb hv a ha, vectorBody_quote hn hb hv b hb']
    simp

theorem source_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {n kb kv : Nat} {bpos vpos : Nat → Nat} {e : VExpr}
    (peel : mixedGatePeel d.value = some (bs,
      quoteV dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))
    (root : ∃ c a b, e = .mux c a b)
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    mixedCertifiedShape? false [] (.defnInfo d) = some (bs,
      quoteV dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) := by
  have body := vectorBody_quote (dom := dom) (kinds := (bs.map Prod.snd).toArray)
    (binp := fun j => inputExpr bs.length (bpos j))
    (vinp := fun j => inputExpr bs.length (vpos j)) hn (fun j hj => by
    obtain ⟨name, pos⟩ := hb j hj
    change (mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - bpos j) == some .bool) = true
    rw [mixed_kind_at pos]; rfl) (fun j hj => by
    obtain ⟨name, pos⟩ := hv j hj
    exact mixed_bits_at pos) e he
  have accepted : mixedGateVectorRoot (bs.map Prod.snd).toArray
      (quoteV dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) = true := by
    obtain ⟨c, a, b, rfl⟩ := root
    unfold mixedGateVectorRoot mixedGateVectorWidth?
    rw [show quoteV dom n _ _ (.mux c a b) = muxE dom (bitVecE n) _ _ _ from rfl,
      canonicalMuxType?_bitVec]
    simpa only [decide_eq_true hn, Bool.true_and, quoteV] using body
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, accepted, Bool.or_true, if_true]

theorem execution_source_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {n kb kv : Nat} {bpos vpos : Nat → Nat} {e : VExpr}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quoteV dom n
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (bpos j))
        (fun j => Tools.ShippingMixedSourceBridge.inputExpr bs.length (vpos j)) e))
    (root : ∃ c a b, e = .mux c a b)
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
      ExecutionValue m initial mems ((denoteV n (fun j => bools (bpos j))
          (fun j => bits (vpos j) n) e).val tick).toNat := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinational_vector_execution hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have mixedGate := source_gate (d := d)
    (by rw [definition]; exact peel) root hn he hb hv
  exact source_signals (source bs _ oldGate mixedGate) hn he hb hv


end Tools.ShippingVectorMuxSoundness
