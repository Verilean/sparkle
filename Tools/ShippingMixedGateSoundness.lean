import Tools.ShippingMixedEntrySoundness
import Tools.ShippingMuxTypeSoundness

/-! Acceptance of quoted arithmetic and Bool terms by the shipping mixed
syntax gate. These lemmas use no MetaM type-inference premise. -/
namespace Tools.ShippingMixedGateSoundness
open Lean Sparkle.Compiler.Elab Tools.ShippingEntrySoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxTypeSoundness

/-- The real pure instantiator commutes with the whole mixed source syntax. -/
theorem instFVars_quoteB (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr) (n : Nat)
    (binp vinp : Nat → Lean.Expr) : ∀ e,
    instFVars xs d (quoteB dom n binp vinp e) =
      quoteB (instFVars xs d dom) n (fun j => instFVars xs d (binp j))
        (fun j => instFVars xs d (vinp j)) e
  | .inp _ => rfl
  | .lit b => by cases b <;> rfl
  | .compare le a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quoteF dom n vinp a)))
      (instFVars xs d (quoteF dom n vinp b)) = _
    rw [instFVars_quoteF, instFVars_quoteF]
    cases le <;> rfl
  | .boolBin k a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quoteB dom n binp vinp a)))
      (instFVars xs d (quoteB dom n binp vinp b)) = _
    rw [instFVars_quoteB, instFVars_quoteB]
    cases k <;> rfl
  | .boolNot a => by
    show Lean.Expr.app (instFVars xs d _) (instFVars xs d (quoteB dom n binp vinp a)) = _
    rw [instFVars_quoteB]
    rfl
  | .boolEq a b => by
    show Lean.Expr.app (.app (instFVars xs d _) (instFVars xs d (quoteB dom n binp vinp a)))
      (instFVars xs d (quoteB dom n binp vinp b)) = _
    rw [instFVars_quoteB, instFVars_quoteB]
    rfl
  | .mux c a b => by
    show Lean.Expr.app (.app (.app (instFVars xs d _) (instFVars xs d (quoteB dom n binp vinp c)))
      (instFVars xs d (quoteB dom n binp vinp a))) (instFVars xs d (quoteB dom n binp vinp b)) = _
    rw [instFVars_quoteB, instFVars_quoteB, instFVars_quoteB]
    rfl

theorem quoteB_congr {dom : Lean.Expr} {n kb kv : Nat} {binp binp' vinp vinp' : Nat → Lean.Expr}
    (hb : ∀ j, j < kb → binp j = binp' j) (hv : ∀ j, j < kv → vinp j = vinp' j) :
    ∀ e, e.WF kb kv n → quoteB dom n binp vinp e = quoteB dom n binp' vinp' e
  | .inp j, hj => hb j hj
  | .lit _, _ => rfl
  | .compare le a b, ⟨ha, hb'⟩ => by
    simp only [quoteB, quoteF_congr hv a ha, quoteF_congr hv b hb']
  | .boolBin k a b, ⟨ha, hb'⟩ => by
    simp only [quoteB, quoteB_congr hb hv a ha, quoteB_congr hb hv b hb']
  | .boolNot a, ha => by simp only [quoteB, quoteB_congr hb hv a ha]
  | .boolEq a b, ⟨ha, hb'⟩ => by
    simp only [quoteB, quoteB_congr hb hv a ha, quoteB_congr hb hv b hb']
  | .mux c a b, ⟨hc, ha, hb'⟩ => by
    simp only [quoteB, quoteB_congr hb hv c hc, quoteB_congr hb hv a ha, quoteB_congr hb hv b hb']

/-- Source-shape identification reduces to the telescope's input mapping;
no equation about a compiler evaluation is required. -/
theorem instantiated_quoteB {xs : Array Lean.Expr} {dom : Lean.Expr} {n kb kv : Nat}
    {binp vinp : Nat → Lean.Expr} {bids vids : Nat → FVarId}
    (hb : ∀ j, j < kb → instFVars xs 0 (binp j) = .fvar (bids j))
    (hv : ∀ j, j < kv → instFVars xs 0 (vinp j) = .fvar (vids j))
    (e : BExpr) (he : e.WF kb kv n) :
    instFVars xs 0 (quoteB dom n binp vinp e) =
      quoteB (instFVars xs 0 dom) n (fun j => .fvar (bids j)) (fun j => .fvar (vids j)) e := by
  rw [instFVars_quoteB]
  exact quoteB_congr hb hv e he

/-- Arithmetic quotation under an arbitrary scalar input telescope. -/
theorem gateBody_inputs {kinds : Array GateBinder} {dom : Lean.Expr} {n k : Nat}
    {inp : Nat → Lean.Expr} (hi : ∀ j, j < k → gateBody kinds n (inp j) = true) :
    ∀ e, e.WF k n → gateBody kinds n (quoteF dom n inp e) = true
  | .inp j, hj => hi j hj
  | .lit v, hv => by
    show gateBody kinds n (.app (.app _ _) (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v))) = true
    rw [gateBody.eq_2]
    show (if (``Sparkle.Core.Signal.Signal.pure == ``Sparkle.Core.Signal.Signal.pure) = true then
      (match bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE n) (natE v)) with
        | some (w, _) => w == n | none => false) else _) = true
    rw [litValue_natE n v hv]; simp
  | .bin op a b, ⟨ha, hb⟩ => by
    obtain ⟨hfn, hop, hk, hw, -, -, hnp⟩ := op_checks op dom (quoteF dom n inp a) (quoteF dom n inp b) n
    show gateBody kinds n (binE dom n op (quoteF dom n inp a) (quoteF dom n inp b)) = true
    simp only [binE, mkApp6, mkApp4, mkApp2, mkAppB, mkApp] at hfn hk hw ⊢
    rw [gateBody.eq_2, hfn]
    simp only [hnp, Bool.false_eq_true, if_false, hop, hk, hw, beq_self_eq_true, Bool.true_and,
      gateBody_inputs hi a ha, gateBody_inputs hi b hb]

theorem mixed_compare_gate (kinds : Array MixedGateBinder) (dom a b : Lean.Expr)
    (n : Nat) (le : SignalCompareKind) :
    mixedGateBoolBody kinds (compareE le dom n a b) =
      (decide (0 < n) && gateBody (mixedBitKinds kinds) n a && gateBody (mixedBitKinds kinds) n b) := by
  cases le <;> simp [compareE, compareName, mkApp2, mkApp3, mkAppB, mkApp,
    mixedGateBoolBody, isBoolEquality, bitVecEqualityWidth?, canonicalNatLitValue?_natE]

theorem mixedGateBool_quote {kinds : Array MixedGateBinder} {dom : Lean.Expr} {n kb kv : Nat}
    {binp vinp : Nat → Lean.Expr} (hn : 0 < n)
    (hb : ∀ j, j < kb → mixedGateBoolBody kinds (binp j) = true)
    (hv : ∀ j, j < kv → gateBody (mixedBitKinds kinds) n (vinp j) = true) :
    ∀ e, e.WF kb kv n → mixedGateBoolBody kinds (quoteB dom n binp vinp e) = true
  | .inp j, hj => hb j hj
  | .lit b, _ => by cases b <;> rfl
  | .compare le a b, ⟨ha, hb'⟩ => by
    rw [quoteB, mixed_compare_gate, gateBody_inputs hv a ha, gateBody_inputs hv b hb']
    simp [hn]
  | .boolBin kind a b, ⟨ha, hb'⟩ => by
    have gate : mixedGateBoolBody kinds (boolBinE kind dom
        (quoteB dom n binp vinp a) (quoteB dom n binp vinp b)) =
        (mixedGateBoolBody kinds (quoteB dom n binp vinp a) &&
          mixedGateBoolBody kinds (quoteB dom n binp vinp b)) := by cases kind <;> rfl
    rw [quoteB, gate, mixedGateBool_quote hn hb hv a ha, mixedGateBool_quote hn hb hv b hb']
    rfl
  | .boolNot a, ha => by
    change mixedGateBoolBody kinds (quoteB dom n binp vinp a) = true
    exact mixedGateBool_quote hn hb hv a ha
  | .boolEq a b, ⟨ha, hb'⟩ => by
    change (mixedGateBoolBody kinds (quoteB dom n binp vinp a) &&
      mixedGateBoolBody kinds (quoteB dom n binp vinp b)) = true
    rw [mixedGateBool_quote hn hb hv a ha, mixedGateBool_quote hn hb hv b hb']
    rfl
  | .mux c a b, ⟨hc, ha, hb'⟩ => by
    change (mixedGateBoolBody kinds (quoteB dom n binp vinp c) &&
      mixedGateBoolBody kinds (quoteB dom n binp vinp a) &&
      mixedGateBoolBody kinds (quoteB dom n binp vinp b)) = true
    rw [mixedGateBool_quote hn hb hv c hc, mixedGateBool_quote hn hb hv a ha,
      mixedGateBool_quote hn hb hv b hb']
    rfl

/-- Exact scalar binder recognition; Bool and BitVec 1 remain different kinds. -/
theorem mixed_binder_bool (dom : Lean.Expr) :
    mixedGateBinderKind? (mkApp2 (.const ``Sparkle.Core.Signal.Signal []) dom (.const ``Bool [])) = some .bool := rfl

theorem mixed_binder_bits (dom : Lean.Expr) (n : Nat) (hn : 0 < n) :
    mixedGateBinderKind? (sigT dom n) = some (.bits n) := by
  change (canonicalNatLitValue? (natE n)).bind (fun k => if 0 < k then some (MixedGateBinder.bits k) else none) = _
  rw [canonicalNatLitValue?_natE]
  simp [hn]

/-- Once the real declaration has been peeled, recognition follows from the
body's quoted source proof. No body-translation success is assumed by the gate. -/
theorem mixedCertifiedShape_of_quote {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {n kb kv : Nat} {binp vinp : Nat → Lean.Expr} {e : BExpr}
    (peel : mixedGatePeel d.value = some (bs, quoteB dom n binp vinp e)) (hn : 0 < n)
    (hb : ∀ j, j < kb → mixedGateBoolBody (bs.map (·.2)).toArray (binp j) = true)
    (hv : ∀ j, j < kv → gateBody (mixedBitKinds (bs.map (·.2)).toArray) n (vinp j) = true)
    (he : e.WF kb kv n) :
    mixedCertifiedShape? false [] (.defnInfo d) = some (bs, quoteB dom n binp vinp e) := by
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, mixedGateBool_quote hn hb hv e he, if_true]

end Tools.ShippingMixedGateSoundness
