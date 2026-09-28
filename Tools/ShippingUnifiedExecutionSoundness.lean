import Tools.ShippingUnifiedEntrySoundness

/-! Entry and backend connection for the unified mutually recursive source
domain: muxes under arithmetic/comparison parents and vice versa, at either
result sort, through actual synthesis, cleanup, checked optimization and
2-valued RTL execution. -/
namespace Tools.ShippingUnifiedExecutionSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion Tools.ShippingUnifiedProtection
open Tools.ShippingUnifiedEntrySoundness
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedInvariant (Separate)
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingPostSoundness
open Tools.ShippingCompareLoweringSoundness
open Tools.ShippingModulePrintSoundness Tools.ShippingPrintSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedExecutionSoundness
open Tools.ShippingMixedSourceBridge
open Tools.ShippingMixedPrintSoundness (mixedShape_positive)
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingBoolMuxSoundness (boolMuxE)
open Sparkle.IR.ZeroWidth Sparkle.IR.RegDedup

@[simp] theorem pack_width (n : Nat) (s : SType) (x : s.Type n) :
    (pack n s x).kind.width = s.width n := by cases s <;> rfl

/-- Sort-directed acceptance by the unified recognizers. -/
def acceptedAt (kinds : Array MixedGateBinder) (n : Nat) : SType → Lean.Expr → Bool
  | .bool => fun e => unifiedGateBoolBody kinds e
  | .bits => fun e => unifiedGateBitsBody kinds n e

/-- Quoted unified sources are accepted by the new mutually recursive gate. -/
theorem unified_quote_accepted {kinds : Array MixedGateBinder} {dom : Lean.Expr} {n kb kv : Nat}
    {binp vinp : Nat → Lean.Expr} (hn : 0 < n)
    (hb : ∀ j, j < kb → unifiedGateBoolBody kinds (binp j) = true)
    (hv : ∀ j, j < kv → unifiedGateBitsBody kinds n (vinp j) = true) :
    ∀ {s} (e : Term s), e.WF kb kv n →
      acceptedAt kinds n s (quote dom n binp vinp e) = true
  | _, .boolInput j, hj => hb j hj
  | _, .bitsInput j, hj => hv j hj
  | _, .boolLit b, _ => by cases b <;> rfl
  | _, .bitsLit v, hv' => by
    show unifiedGateBitsBody kinds n (quoteF dom n vinp (.lit v)) = true
    change (match bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) with
      | some (w, _) => w == n
      | none => false) = true
    rw [litValue_natE n v hv']
    simp
  | _, .binary op a b, ⟨ha, hb'⟩ => by
    show unifiedGateBitsBody kinds n (binE dom n op (quote dom n binp vinp a)
      (quote dom n binp vinp b)) = true
    have ck := op_checks op dom (quote dom n binp vinp a) (quote dom n binp vinp b) n
    have step : unifiedGateBitsBody kinds n (binE dom n op (quote dom n binp vinp a)
        (quote dom n binp vinp b)) =
        (match signalBinOpOf (binMethod op),
            canonicalSignalBinKinds (binMethod op)
              (binE dom n op (quote dom n binp vinp a) (quote dom n binp vinp b)).getAppArgs,
            canonicalSignalBitVecWidth
              (binE dom n op (quote dom n binp vinp a) (quote dom n binp vinp b)).getAppArgs with
          | some _, some (true, true), some w =>
            w == n && unifiedGateBitsBody kinds n (quote dom n binp vinp a) &&
              unifiedGateBitsBody kinds n (quote dom n binp vinp b)
          | _, _, _ => false) := by
      simp only [binE, mkApp6, mkApp4, mkApp2, mkAppB, mkApp]
      rfl
    have ia : unifiedGateBitsBody kinds n (quote dom n binp vinp a) = true :=
      unified_quote_accepted hn hb hv a ha
    have ib : unifiedGateBitsBody kinds n (quote dom n binp vinp b) = true :=
      unified_quote_accepted hn hb hv b hb'
    rw [step, ck.2.1, ck.2.2.1, ck.2.2.2.1]
    simp [ia, ib]
  | _, .compare le a b, ⟨ha, hb'⟩ => by
    show unifiedGateBoolBody kinds (compareE le dom n (quote dom n binp vinp a)
      (quote dom n binp vinp b)) = true
    have step : unifiedGateBoolBody kinds (compareE le dom n (quote dom n binp vinp a)
        (quote dom n binp vinp b)) =
        (decide (0 < n) && unifiedGateBitsBody kinds n (quote dom n binp vinp a) &&
          unifiedGateBitsBody kinds n (quote dom n binp vinp b)) := by
      cases le <;> simp [compareE, compareName, mkApp2, mkApp3, mkAppB, mkApp,
        unifiedGateBoolBody, isBoolEquality, bitVecEqualityWidth?, canonicalNatLitValue?_natE]
    have ia : unifiedGateBitsBody kinds n (quote dom n binp vinp a) = true :=
      unified_quote_accepted hn hb hv a ha
    have ib : unifiedGateBitsBody kinds n (quote dom n binp vinp b) = true :=
      unified_quote_accepted hn hb hv b hb'
    rw [step, ia, ib]
    simp [hn]
  | _, .boolBinary kind a b, ⟨ha, hb'⟩ => by
    show unifiedGateBoolBody kinds (boolBinE kind dom (quote dom n binp vinp a)
      (quote dom n binp vinp b)) = true
    have gate : unifiedGateBoolBody kinds (boolBinE kind dom (quote dom n binp vinp a)
        (quote dom n binp vinp b)) =
        (unifiedGateBoolBody kinds (quote dom n binp vinp a) &&
          unifiedGateBoolBody kinds (quote dom n binp vinp b)) := by cases kind <;> rfl
    have ia : unifiedGateBoolBody kinds (quote dom n binp vinp a) = true :=
      unified_quote_accepted hn hb hv a ha
    have ib : unifiedGateBoolBody kinds (quote dom n binp vinp b) = true :=
      unified_quote_accepted hn hb hv b hb'
    rw [gate, ia, ib]
    rfl
  | _, .boolNot a, ha => by
    show unifiedGateBoolBody kinds (boolNotE dom (quote dom n binp vinp a)) = true
    exact (unified_quote_accepted hn hb hv a ha :
      unifiedGateBoolBody kinds (quote dom n binp vinp a) = true)
  | _, .boolEq a b, ⟨ha, hb'⟩ => by
    show unifiedGateBoolBody kinds (boolEqE dom (quote dom n binp vinp a)
      (quote dom n binp vinp b)) = true
    have ia : unifiedGateBoolBody kinds (quote dom n binp vinp a) = true :=
      unified_quote_accepted hn hb hv a ha
    have ib : unifiedGateBoolBody kinds (quote dom n binp vinp b) = true :=
      unified_quote_accepted hn hb hv b hb'
    change (unifiedGateBoolBody kinds (quote dom n binp vinp a) &&
      unifiedGateBoolBody kinds (quote dom n binp vinp b)) = true
    rw [ia, ib]
    rfl
  | .bool, .mux c a b, ⟨hc, ha, hb'⟩ => by
    show unifiedGateBoolBody kinds (boolMuxE dom (quote dom n binp vinp c)
      (quote dom n binp vinp a) (quote dom n binp vinp b)) = true
    have ic : unifiedGateBoolBody kinds (quote dom n binp vinp c) = true :=
      unified_quote_accepted hn hb hv c hc
    have ia : unifiedGateBoolBody kinds (quote dom n binp vinp a) = true :=
      unified_quote_accepted hn hb hv a ha
    have ib : unifiedGateBoolBody kinds (quote dom n binp vinp b) = true :=
      unified_quote_accepted hn hb hv b hb'
    change (unifiedGateBoolBody kinds (quote dom n binp vinp c) &&
      unifiedGateBoolBody kinds (quote dom n binp vinp a) &&
      unifiedGateBoolBody kinds (quote dom n binp vinp b)) = true
    rw [ic, ia, ib]
    rfl
  | .bits, .mux c a b, ⟨hc, ha, hb'⟩ => by
    show unifiedGateBitsBody kinds n (muxE dom (bitVecE n) (quote dom n binp vinp c)
      (quote dom n binp vinp a) (quote dom n binp vinp b)) = true
    have ic : unifiedGateBoolBody kinds (quote dom n binp vinp c) = true :=
      unified_quote_accepted hn hb hv c hc
    have ia : unifiedGateBitsBody kinds n (quote dom n binp vinp a) = true :=
      unified_quote_accepted hn hb hv a ha
    have ib : unifiedGateBitsBody kinds n (quote dom n binp vinp b) = true :=
      unified_quote_accepted hn hb hv b hb'
    change (canonicalNatLitValue? (natE n) == some n &&
      unifiedGateBoolBody kinds (quote dom n binp vinp c) &&
      unifiedGateBitsBody kinds n (quote dom n binp vinp a) &&
      unifiedGateBitsBody kinds n (quote dom n binp vinp b)) = true
    rw [canonicalNatLitValue?_natE, ic, ia, ib]
    simp

/-- Root acceptance helpers for the unified gate. -/
theorem root_of_bool {kinds : Array MixedGateBinder} {e : Lean.Expr}
    (body : unifiedGateBoolBody kinds e = true) : unifiedGateRoot kinds e = true := by
  unfold unifiedGateRoot
  rw [body]
  rfl

theorem root_of_top {kinds : Array MixedGateBinder} {n : Nat} {e : Lean.Expr} (hn : 0 < n)
    (mux : canonicalMuxType? e = none)
    (top : gateTopWidth? (mixedBitKinds kinds) e = some n)
    (body : unifiedGateBitsBody kinds n e = true) : unifiedGateRoot kinds e = true := by
  unfold unifiedGateRoot
  rw [mux, top]
  simp [body, hn]

theorem root_of_mux {kinds : Array MixedGateBinder} {n : Nat} {e : Lean.Expr} (hn : 0 < n)
    (mux : canonicalMuxType? e = some (.bitVector n))
    (body : unifiedGateBitsBody kinds n e = true) : unifiedGateRoot kinds e = true := by
  unfold unifiedGateRoot
  rw [mux]
  simp [body, hn]

/-- Root width for every `.bits` constructor, from the same syntactic sources
as the established vector gate. -/
theorem unified_root_accepted {kinds : Array MixedGateBinder} {dom : Lean.Expr} {n kb kv : Nat}
    {binp vinp : Nat → Lean.Expr} (hn : 0 < n)
    (hb : ∀ j, j < kb → unifiedGateBoolBody kinds (binp j) = true)
    (hv : ∀ j, j < kv → unifiedGateBitsBody kinds n (vinp j) = true)
    (hvw : ∀ j, j < kv → gateTopWidth? (mixedBitKinds kinds) (vinp j) = some n)
    (nomux : ∀ j, j < kv → canonicalMuxType? (vinp j) = none)
    {s} (e : Term s) (he : e.WF kb kv n) :
    unifiedGateRoot kinds (quote dom n binp vinp e) = true := by
  cases s with
  | bool =>
    exact root_of_bool (unified_quote_accepted hn hb hv e he)
  | bits =>
    have body : unifiedGateBitsBody kinds n (quote dom n binp vinp e) = true :=
      unified_quote_accepted hn hb hv e he
    cases e with
    | bitsInput j =>
      exact root_of_top hn (nomux j he) (hvw j he)
        (body : unifiedGateBitsBody kinds n (vinp j) = true)
    | bitsLit v =>
      have mux : canonicalMuxType? (quoteF dom n vinp (.lit v)) = none := rfl
      have top : gateTopWidth? (mixedBitKinds kinds) (quoteF dom n vinp (.lit v)) = some n := by
        change ((quoteF dom n vinp (.lit v)).getAppArgs.back?.bind bitVecLitValue?).map (·.1) =
          some n
        change ((some (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v))).bind
          bitVecLitValue?).map (·.1) = some n
        rw [Option.bind_some, litValue_natE n v he]
        rfl
      exact root_of_top hn mux top body
    | binary op a b =>
      have ck := op_checks op dom (quote dom n binp vinp a) (quote dom n binp vinp b) n
      have mux : canonicalMuxType? (binE dom n op (quote dom n binp vinp a)
          (quote dom n binp vinp b)) = none := by
        cases op <;> rfl
      have top : gateTopWidth? (mixedBitKinds kinds) (binE dom n op (quote dom n binp vinp a)
          (quote dom n binp vinp b)) = some n := by
        simp only [gateTopWidth?, ck.1, ck.2.2.2.2.2.2, Bool.false_eq_true, if_false]
        exact ck.2.2.2.1
      exact root_of_top hn mux top body
    | mux c a b =>
      exact root_of_mux hn (canonicalMuxType?_bitVec ..) body

theorem SType_width_pos {n : Nat} (hn : 0 < n) (s : SType) : 0 < s.width n := by
  cases s
  · exact Nat.one_pos
  · exact hn

/-- Bound-variable inputs are accepted at their declared kinds. -/
theorem input_bool_accepted {bs : List (Name × MixedGateBinder)} {j name}
    (pos : bs[j]? = some (name, .bool)) :
    unifiedGateBoolBody (bs.map Prod.snd).toArray (inputExpr bs.length j) = true := by
  change (mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - j) ==
    some MixedGateBinder.bool) = true
  rw [mixed_kind_at pos]
  rfl

theorem input_bits_accepted {bs : List (Name × MixedGateBinder)} {j name n}
    (pos : bs[j]? = some (name, .bits n)) :
    unifiedGateBitsBody (bs.map Prod.snd).toArray n (inputExpr bs.length j) = true := by
  change (mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - j) ==
    some (MixedGateBinder.bits n)) = true
  rw [mixed_kind_at pos]
  simp

theorem input_top_width {bs : List (Name × MixedGateBinder)} {j name n}
    (pos : bs[j]? = some (name, .bits n)) :
    gateTopWidth? (mixedBitKinds (bs.map Prod.snd).toArray) (inputExpr bs.length j) = some n := by
  have h : (gateBVar? (mixedBitKinds (bs.map Prod.snd).toArray) (bs.length - 1 - j) ==
      some (GateBinder.signal n)) = true := mixed_bits_at pos
  have eq := eq_of_beq h
  change (match gateBVar? (mixedBitKinds (bs.map Prod.snd).toArray) (bs.length - 1 - j) with
    | some (.signal n) => some n
    | _ => none) = some n
  rw [eq]

/-- Once the real declaration has been peeled, recognition follows from the
quoted unified source proof. No body-translation success is assumed. -/
theorem term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {n kb kv : Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (peel : mixedGatePeel d.value = some (bs,
      quote dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    mixedCertifiedShape? false [] (.defnInfo d) = some (bs,
      quote dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) := by
  have root := unified_root_accepted (kinds := (bs.map Prod.snd).toArray) (dom := dom) hn
    (fun j hj => (hb j hj).elim fun name pos => input_bool_accepted pos)
    (fun j hj => (hv j hj).elim fun name pos => input_bits_accepted pos)
    (fun j hj => (hv j hj).elim fun name pos => input_top_width pos)
    (fun j hj => rfl) e he
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, if_true]

/-- Relational source preservation for the unified entry: one statement for
both sorts, observing the packed value at the sort's output width. -/
def TermSourcePreserves (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (observes : Nat → Nat → Env → MEnv → Nat → Prop) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits initial (bs.zip ids) a →
    ∀ (dom : Lean.Expr) (n kb kv : Nat) (binp vinp : Nat → FVarId)
      (bvals : Nat → Bool) (vvals : Nat → BitVec n) {srt : SType} (e : Term srt),
    0 < n → e.WF kb kv n →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨n, vvals j⟩) →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      quote dom n (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e →
    observes (srt.width n) n initial mems (pack n srt (eval n bvals vvals e)).toNat

def TermPreserves (declName : Name) (bs : List (Name × MixedGateBinder)) (body : Lean.Expr)
    (m : Sparkle.IR.AST.Module) : Prop :=
  TermSourcePreserves declName bs body (fun outWidth _ => RawValueAt outWidth bs m)

theorem TermSourcePreserves.map {declName bs body P Q}
    (h : TermSourcePreserves declName bs body P)
    (f : ∀ outWidth n initial mems expected, P outWidth n initial mems expected →
      Q outWidth n initial mems expected) :
    TermSourcePreserves declName bs body Q := by
  obtain ⟨ids, nd, len, cache, h⟩ := h
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems a p values dom n kb kv binp vinp bvals vvals srt e hn he hb hv qeq
  exact f _ n initial mems _ (h bools bits initial mems values dom n kb kv binp vinp bvals vvals e hn he hb hv qeq)

theorem synthesizeMixedCertified_term_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body) (m, d)) :
    TermPreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, nameLegal⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro bools bits initial mems a p values dom n kb kv binp vinp bvals vvals srt e hn he hb hv qeq
  have empty := empty_layout (entryCompilerState false cache) declName.toString initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  have leaf := prepare_returns (bs.zip ids) a (bools := bools) (bits := bits) run
  rw [qeq] at leaf
  have separate := prepared.1.separate prepared.2.1
  have hb' : ∀ j, j < kb → inputValues p.bools p.bits (binp j) = some (.bool (bvals j)) :=
    fun j hj => inputValues_bool (hb j hj)
  have hv' : ∀ j, j < kv → inputValues p.bools p.bits (vinp j) = some (.bits n (vvals j)) :=
    fun j hj => inputValues_bits separate (hv j hj)
  have contract := Tools.ShippingUnifiedRecursion.translateExprToWire_contract
    (ctx := p.context) (we := declaredWidths st) (mems := mems) (initial := initial)
    (dom := dom) hn hb' hv' e he
  have ordered := Tools.ShippingUnifiedProtection.translateExprToWire_orders
    (ctx := p.context) (we := declaredWidths st) (mems := mems) (initial := initial)
    (dom := dom) hn hb' hv' e he "out" true
  have positive : 0 < (pack n srt (eval n bvals vvals e)).kind.width := by
    rw [pack_width]
    exact SType_width_pos hn srt
  obtain ⟨unique, result, evalr, value, out, typed, _⟩ := emitLeaves_from_ports positive contract
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 leaf
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  have outputEq : m.outputs = st.module.outputs.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
  have shape := prepare_shape (bools := bools) (bits := bits) (bs.zip ids) a (by intro p hp; cases hp)
  obtain ⟨wm, ready, printOutputs, outputTyped, outputWidth, order⟩ := emitLeaves_postReady_at
    positive contract ordered
    prepared.2.2.1 prepared.2.2.2 prepared.2.1 prepared.1 shape.1 shape.2 wireEq bodyEq outputEq leaf
  have ib := prepare_inputBounds (bs.zip ids) a (by intro p hp; cases hp) values
  obtain ⟨w, sm, ty, tr, fresh, ht, hty⟩ := emitLeaves_single leaf
  have frame := contract.frame "out" false true p.state sm w
    (lookup_of_ports prepared.1 prepared.2.1) tr
  rw [show (pack n srt (eval n bvals vvals e)).kind.width = srt.width n from pack_width ..]
    at outputTyped outputWidth
  refine ⟨result, ?_, value, ready, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moduleWidths_finish wireEq unique, bodyEq]; exact evalr
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
      obtain ⟨l, rhs, k, eq, _⟩ := typed stmt hs'
      exact ⟨l, rhs, eq⟩)
    have mi : m.inputs = st.module.inputs.reverse := by rw [hm, noSeq]; rfl
    have hp' : port ∈ p.state.module.inputs := by
      rw [mi, List.mem_reverse, ht, emitAssign_inputs] at hp
      exact frame.inputs ▸ hp
    obtain ⟨decl, bound⟩ := ib port hp'
    rw [wm, declaredWidths_agree unique port (by rw [ht, emitAssign_wires]; exact frame.decls port decl)]
    exact bound
  · intro positiveBinders
    have pi := prepare_print (bools := bools) (bits := bits) (bs.zip ids) a
      (by intro port hp; cases hp) (fun name k id hp => positiveBinders name k (List.of_mem_zip hp).1)
    have noSeq := addClockReset_assigns st.module (by
      intro stmt hs
      obtain ⟨l, rhs, k, eq, _⟩ := typed stmt (List.mem_reverse.mpr hs)
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
      change ({name := "out", ty := ty} :: sm.module.outputs).reverse = _
      rw [frame.outputs, shape.2]; rfl

theorem synthesizeFromConst_term_sound {logProf declName ci bs body m d}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName [] false true ci) (m, d)) :
    TermPreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_term_sound run

theorem synthesizeCombinationalCore_term_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) → TermPreserves declName bs body m := by
  obtain ⟨logProf, ci, w1, w2, w3, get, run⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape => synthesizeFromConst_term_sound old shape run.mreturns⟩

theorem term_execution {declName bs body m m'} (source : TermPreserves declName bs body m)
    (positive : PositiveBinders bs)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    TermSourcePreserves declName bs body (fun _ _ => ExecutionValue m') :=
  TermSourcePreserves.map source (fun _ _ _ _ _ h => execution_of_entry h positive post)

theorem synthesizeCombinational_term_execution {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        TermSourcePreserves declName bs body (fun _ _ => ExecutionValue m) := by
  obtain ⟨raw, design, world, core, post⟩ := synthesizeCombinational_reads hr
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_term_sound core
  exact ⟨ci, w1, w2, get, fun bs body old shape =>
    term_execution (source bs body old shape) (mixedShape_positive shape) post⟩

theorem instantiated_quote {xs : Array Lean.Expr} {dom : Lean.Expr} {n kb kv : Nat}
    {binp vinp : Nat → Lean.Expr} {bids vids : Nat → FVarId}
    (hb : ∀ j, j < kb → instFVars xs 0 (binp j) = .fvar (bids j))
    (hv : ∀ j, j < kv → instFVars xs 0 (vinp j) = .fvar (vids j))
    {srt : SType} (e : Term srt) (he : e.WF kb kv n) :
    instFVars xs 0 (quote dom n binp vinp e) =
      quote (instFVars xs 0 dom) n (fun j => .fvar (bids j)) (fun j => .fvar (vids j)) e := by
  rw [instFVars_quote]
  exact quote_congr hb hv e he

theorem source_positions {declName bs dom n kb kv P} {bpos vpos : Nat → Nat}
    {srt : SType} {e : Term srt}
    (source : TermSourcePreserves declName bs
      (quote dom n (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) P)
    (hn : 0 < n) (he : e.WF kb kv n)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits n)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits initial →
      P (srt.width n) n initial mems
        (pack n srt (eval n (fun j => bools (bpos j)) (fun j => bits (vpos j) n) e)).toNat := by
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
  · apply instantiated_quote _ _ e he
    · intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
    · intro j hj
      obtain ⟨name, pos⟩ := hv j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose

/-- The same theorem observes actual library Signals at any source time. -/
theorem source_signals {declName bs dom n kb kv P} {bpos vpos : Nat → Nat}
    {srt : SType} {e : Term srt}
    (source : TermSourcePreserves declName bs
      (quote dom n (fun j => inputExpr bs.length (bpos j))
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
      P (srt.width n) n initial mems
        (pack n srt ((Tools.ShippingUnifiedSource.denote n (fun j => bools (bpos j))
          (fun j => bits (vpos j) n) e).val tick)).toNat := by
  obtain ⟨ids, nd, len, cache, source⟩ := source_positions source hn he hb hv
  refine ⟨ids, nd, len, cache, ?_⟩
  intro D bools bits tick initial mems values
  rw [Tools.ShippingUnifiedSource.denote_val]
  exact source _ _ initial mems values

/-- General source-to-RTL execution for the unified mutually recursive
domain, at the real synthesis entry, for either result sort. -/
theorem execution_source_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {n kb kv : Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, design) w')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom n
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
      ExecutionValue m initial mems
        (pack n srt ((Tools.ShippingUnifiedSource.denote n (fun j => bools (bpos j))
          (fun j => bits (vpos j) n) e).val tick)).toNat := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinational_term_execution hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have mixedGate := term_gate (d := d)
    (by rw [definition]; exact peel) hn he hb hv
  exact source_signals (source bs _ oldGate mixedGate) hn he hb hv

end Tools.ShippingUnifiedExecutionSoundness
