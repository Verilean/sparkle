import Tools.ShippingMixedInputSoundness

/-! The shipping mixed entry's complete input walk. Preparation below is a
pure description of the states reached by the actual bindMixedCertifiedInputs;
prepare_returns connects every successful run to that state, not a replacement
compiler or a replay hypothesis. -/
namespace Tools.ShippingMixedEntrySoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingMixedInvariant
open Tools.ShippingMixedOutputSoundness Tools.ShippingMixedInputSoundness
open Tools.ShippingEntrySoundness Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness

structure Setup where
  context : CompilerState
  state : CircuitState
  bools : BoolValuation
  bits : Valuation

def extend (a : Setup) (binder : (Name × MixedGateBinder) × FVarId)
    (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) : Setup :=
  let ((name, kind), id) := binder
  match kind with
  | .domain => a
  | .bool =>
    { context := inputContext a.context id (inputWire a.state name.toString .bit)
      state := inputState a.state name.toString .bit
      bools := fun key => if key = id then some (bools id) else a.bools key
      bits := fun key => if key = id then none else a.bits key }
  | .bits n =>
    { context := inputContext a.context id (inputWire a.state name.toString (.bitVector n))
      state := inputState a.state name.toString (.bitVector n)
      bools := fun key => if key = id then none else a.bools key
      bits := fun key => if key = id then some ⟨n, bits id n⟩ else a.bits key }

def prepare (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    List ((Name × MixedGateBinder) × FVarId) → Setup → Setup
  | [], a => a
  | b :: rest, a => prepare bools bits rest (extend a b bools bits)

/-- The source value at one allocated RTL input port. -/
def InputValue (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) (a : Setup) (binder : (Name × MixedGateBinder) × FVarId) : Prop :=
  match binder.1.2 with
  | .domain => True
  | .bool => initial (inputWire a.state binder.1.1.toString .bit) = encodeBool (bools binder.2)
  | .bits n => initial (inputWire a.state binder.1.1.toString (.bitVector n)) = (bits binder.2 n).toNat

/-- Ordinary admissibility of source input values at their allocated RTL ports. -/
def Admissible (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
    (initial : Env) : List ((Name × MixedGateBinder) × FVarId) → Setup → Prop
  | [], _ => True
  | b :: rest, a => InputValue bools bits initial a b ∧
    Admissible bools bits initial rest (extend a b bools bits)

theorem restrict_ports {ctx ρ β ρ' β' s initial} (h : PortInputs ctx ρ β s initial)
    (hb : ∀ id b, ρ' id = some b → ρ id = some b)
    (hv : ∀ id n (x : BitVec n), β' id = some ⟨n, x⟩ → β id = some ⟨n, x⟩) :
    PortInputs ctx ρ' β' s initial :=
  ⟨fun id b hi => h.bool id b (hb id b hi), fun id n x hi => h.bits id n x (hv id n x hi)⟩

theorem extend_layout {a : Setup} {binder bools bits initial}
    (ports : PortInputs a.context a.bools a.bits a.state initial)
    (wires : WiresOk a.state)
    (value : match binder.1.2 with
      | .domain => True
      | .bool => initial (inputWire a.state binder.1.1.toString .bit) = encodeBool (bools binder.2)
      | .bits n => initial (inputWire a.state binder.1.1.toString (.bitVector n)) = (bits binder.2 n).toNat) :
    let next := extend a binder bools bits
    PortInputs next.context next.bools next.bits next.state initial ∧ WiresOk next.state ∧
      next.state.module.body = a.state.module.body ∧ next.state.translateRecord = a.state.translateRecord := by
  obtain ⟨⟨name, kind⟩, id⟩ := binder
  cases kind with
  | domain => exact ⟨ports, wires, rfl, rfl⟩
  | bool =>
    have restricted : PortInputs a.context a.bools
        (fun key => if key = id then none else a.bits key) a.state initial := by
      apply restrict_ports ports (fun _ _ h => h)
      intro key n x hi
      split at hi
      · cases hi
      · exact hi
    exact ⟨bind_bool_layout (id := id) (β := fun key => if key = id then none else a.bits key) restricted (if_pos rfl) value, input_wiresOk wires,
      input_body _ _ _, input_record _ _ _⟩
  | bits n =>
    have restricted : PortInputs a.context (fun key => if key = id then none else a.bools key)
        a.bits a.state initial := by
      apply restrict_ports ports ?_ (fun _ _ _ h => h)
      intro key b hi
      split at hi
      · cases hi
      · exact hi
    exact ⟨bind_bits_layout (id := id) (ρ := fun key => if key = id then none else a.bools key) _ restricted (if_pos rfl) value, input_wiresOk wires,
      input_body _ _ _, input_record _ _ _⟩

theorem prepare_layout {bools bits initial} (L : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) (ports : PortInputs a.context a.bools a.bits a.state initial)
    (wires : WiresOk a.state) (values : Admissible bools bits initial L a) :
    let final := prepare bools bits L a
    PortInputs final.context final.bools final.bits final.state initial ∧ WiresOk final.state ∧
      final.state.module.body = a.state.module.body ∧ final.state.translateRecord = a.state.translateRecord := by
  induction L generalizing a with
  | nil => exact ⟨ports, wires, rfl, rfl⟩
  | cons binder rest ih =>
    obtain ⟨value, values⟩ := values
    obtain ⟨ports', wires', body, record⟩ := extend_layout (binder := binder) (bools := bools) (bits := bits) ports wires value
    obtain ⟨ports'', wires'', body', record'⟩ := ih _ ports' wires' values
    exact ⟨ports'', wires'', body'.trans body, record'.trans record⟩

/-- Every successful execution of the actual input walk reaches `prepare`.
There are no binder-type inference or handler-correctness premises. -/
theorem prepare_returns {α : Type} {bools bits} (L : List ((Name × MixedGateBinder) × FVarId))
    (a : Setup) {k : CompilerM α} {result : α} {t : CircuitState}
    (hr : Returns (bindMixedCertifiedInputs k L) a.context a.state result t) :
    Returns k (prepare bools bits L a).context (prepare bools bits L a).state result t := by
  induction L generalizing a with
  | nil => exact hr
  | cons binder rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := binder
    cases kind with
    | domain => exact ih a hr
    | bool => exact ih (extend a ((name, .bool), id) bools bits) (bindInputPort_returns hr)
    | bits n => exact ih (extend a ((name, .bits n), id) bools bits) (bindInputPort_returns hr)

/-- The entire real binder walk and output emitter, not just one input node.
Quotation/source-value facts remain explicit until the declaration bridge. -/
theorem bindMixed_emitLeaves_sound {bools bits initial mems ctx s t dom n kb kv cache logProf returned}
    (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup)
    (haCtx : a.context = ctx) (haState : a.state = s)
    {binp vinp : Nat → FVarId} {bvals : Nat → Bool} {vvals : Nat → BitVec n}
    (hn : 0 < n)
    (hb : ∀ j, j < kb → (prepare bools bits L a).bools (binp j) = some (bvals j))
    (hv : ∀ j, j < kv → (prepare bools bits L a).bits (vinp j) = some ⟨n, vvals j⟩)
    (e : BExpr) (he : e.WF kb kv n)
    (ports : PortInputs a.context a.bools a.bits a.state initial)
    (wires : WiresOk a.state) (body : a.state.module.body = []) (record : a.state.translateRecord = {})
    (values : Admissible bools bits initial L a)
    (hr : Returns (bindMixedCertifiedInputs
      (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
        [("out", quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)] none 0) L)
      ctx s returned t) :
    ∃ result, Runs (declaredWidths t) mems initial t result ∧
      result "out" = encodeBool (evalB n bvals vvals e) := by
  rw [← haCtx, ← haState] at hr
  have leaf := prepare_returns L a (bools := bools) (bits := bits) hr
  obtain ⟨p, w, b, r⟩ := prepare_layout L a ports wires values
  obtain ⟨_, result, run, val, _⟩ := emitLeaves_bool_from_ports hn hb hv e he
    (b.trans body) (r.trans record) w p leaf
  exact ⟨result, run, val⟩

/-- Widths read from the actual returned module, including scalar Bool wires. -/
def moduleWidths (m : Sparkle.IR.AST.Module) : WEnv := fun w =>
  ((m.wires.find? (fun p => p.name == w)).map (fun p => p.ty.bitWidth)).getD 0

theorem moduleWidths_finish {m : Sparkle.IR.AST.Module} {s : CircuitState}
    (wires : m.wires = s.module.wires.reverse) (unique : WiresOk s) :
    moduleWidths m = declaredWidths s := by
  funext w
  have eq : m.wires.find? (fun p => p.name == w) = s.module.wires.find? (fun p => p.name == w) := by
    cases hf : s.module.wires.find? (fun p => p.name == w) with
    | none =>
      apply List.find?_eq_none.mpr
      intro p hp
      rw [wires, List.mem_reverse] at hp
      exact List.find?_eq_none.mp hf p hp
    | some p =>
      have hp := List.mem_of_find?_eq_some hf
      have pname : p.name = w := by simpa using List.find?_some hf
      have nd : (m.wires.map (·.name)).Nodup := by
        rw [wires, List.map_reverse]; exact nodup_reverse unique.1
      have hp' : p ∈ m.wires := by rw [wires, List.mem_reverse]; exact hp
      simpa [pname] using find?_of_nodup nd hp'
  unfold moduleWidths declaredWidths
  rw [eq]

/-- No inferred-type premise: this decomposes the actual mixed synthesis run. -/
theorem synthesizeMixedCertified_returns {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body) (m, d)) :
    ∃ ids cache returned st, ids.Nodup ∧ ids.length = bs.length ∧
      Returns (bindMixedCertifiedInputs
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cache logProf
          [("out", instFVars (ids.map Lean.Expr.fvar).toArray 0 body)] none 0) (bs.zip ids))
        (entryCompilerState false cache) (CircuitM.init declName.toString) returned st ∧
      m = (addClockResetIfSequential st.module).finalize ∧ d = st.design ∧
      Sparkle.IR.ModuleNames.legal (Sparkle.Backend.Verilog.sanitizeName m.name) = true := by
  unfold synthesizeMixedCertified at hr
  obtain ⟨ids, _, hr⟩ := MReturns.bind hr
  split at hr
  rotate_left
  · exact (MReturns.throw hr).elim
  rename_i hids
  dsimp only at hr
  obtain ⟨cache, _, hr⟩ := MReturns.bind hr
  obtain ⟨⟨returned, st⟩, run, finish⟩ := MReturns.bind hr
  obtain ⟨hm, hd, name⟩ := finishSynth_returns finish
  exact ⟨ids, cache, returned, st, hids.1, hids.2, MReturns.run run, hm, hd, name⟩

def start (ctx : CompilerState) (name : String) : Setup :=
  ⟨ctx, CircuitM.init name, fun _ => none, fun _ => none⟩

/-- Relational source preservation for the actual mixed entry. As in the old
entry theorem, source meaning is supplied on the instantiated declaration;
it is not a hypothesis about correctness of a compiler subroutine. -/
def MixedPreserves (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits initial (bs.zip ids) a →
    ∀ (dom : Lean.Expr) (n kb kv : Nat) (binp vinp : Nat → FVarId)
      (bvals : Nat → Bool) (vvals : Nat → BitVec n) (e : BExpr),
    0 < n → e.WF kb kv n →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨n, vvals j⟩) →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      quoteB dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e →
    ∃ result, evalAssigns (moduleWidths m) mems m.body initial = some result ∧
      result "out" = encodeBool (evalB n bvals vvals e)

theorem synthesizeMixedCertified_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body) (m, d)) :
    MixedPreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems a p values dom n kb kv binp vinp bvals vvals e hn he hb hv quote
  have empty := empty_layout (entryCompilerState false cache) declName.toString initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  have leaf := prepare_returns (bs.zip ids) a (bools := bools) (bits := bits) run
  rw [quote] at leaf
  obtain ⟨unique, result, eval, value, _⟩ := emitLeaves_bool_from_ports hn hb hv e he
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 leaf
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  refine ⟨result, ?_, value⟩
  rw [moduleWidths_finish wireEq unique, bodyEq]
  exact eval

/-- The actual declaration dispatcher selects this proved input/translation
path. Both gate decisions are pure, checkable conditions on that declaration. -/
theorem synthesizeFromConst_mixed_sound {logProf declName ci bs body m d}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName [] false true ci) (m, d)) :
    MixedPreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_sound run

/-- The mixed result is tied to the declaration read by this very synthesis
run. As for the old entry, identifying that declaration with a source constant
is the separate `EnvDefines` trust boundary. -/
theorem synthesizeCombinationalCore_mixed_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) → MixedPreserves declName bs body m := by
  obtain ⟨logProf, ci, w1, w2, w3, get, run⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape => synthesizeFromConst_mixed_sound old shape run.mreturns⟩

end Tools.ShippingMixedEntrySoundness
