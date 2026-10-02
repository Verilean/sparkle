import Tools.ShippingInstanceLeaf
import Tools.ShippingUnifiedExecutionSoundness

/-! The certified entry for cones over ARBITRARY leaves, in the linked
semantics.

`synthesizeMixedCertified` on a body that is a quoted unified term whose
leaves each bring their own meaning and contract — input binders, instance
calls of linked children, or anything else proved against the contract —
produces a module whose LINKED evaluation (instance statements executed
against the child table) drives `out` with the term's evaluation. -/
namespace Tools.ShippingHierTermSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedEntrySoundness (lookup_of_ports)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingUnifiedExecutionSoundness (pack_width)
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMuxTypeSoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingBoolMuxSoundness (boolMuxE)
open Tools.ShippingMixedInvariant (Separate)

section generic
variable [LinkCtx] [ChildSem]

/-- At the first leaf there is no emitted code or cache record. -/
theorem initial_link {ctx ρ β we mems initial s}
    (body : s.module.body = []) (record : s.translateRecord = {})
    (inputs : Tools.ShippingMixedInvariant.Inputs ctx ρ β we s initial) :
    Inv ctx (inputValues ρ β) we mems initial s initial :=
  ⟨LinkCtx.runs_nil body, Inputs.of_mixed inputs, Records.empty record,
    LinkCtx.typed_nil body⟩

/-- The actual leaf emitter preserves declaration uniqueness. -/
theorem emitLeaves_structure_link {rec ctx inputs we mems initial s t e v cache logProf returned}
    (contract : Contract rec ctx inputs we mems initial e v)
    (lookup : Lookup ctx inputs s) (wires : WiresOk s)
    (hr : Returns (emitLeaves rec cache logProf [("out", e)] none 0) ctx s returned t) :
    DeclGrows s t ∧ WiresOk t := by
  obtain ⟨w, sm, ty, tr, fresh, ht, _⟩ := emitLeaves_single hr
  have frame := contract.frame "out" false true s sm w lookup tr
  have wm := frame.wires wires
  refine ⟨?_, ?_, ?_⟩
  · intro p hp; rw [ht, emitAssign_wires]; exact frame.decls p hp
  · rw [ht, emitAssign_wires]; exact wm.1
  · intro p hp
    rw [ht, emitAssign_wires] at hp
    have hu := wm.2 p hp
    rw [ht, emitAssign_usedNames, addOutput_state]
    simp [Std.HashSet.contains_insert, hu]

/-- A real `emitLeaves` run drives `out` with the leaf contract's value, in
whatever semantic context the contract was proved. -/
theorem emitLeaves_runs_link {ctx inputs we mems initial prior s t e cache logProf returned}
    {v : Value}
    (contract : Contract (fun e hint top named => translateExprToWire e hint top named)
      ctx inputs we mems initial e v)
    (h : Inv ctx inputs we mems initial s prior) (widths : ScalarWidthsAgree we t)
    (hr : Returns (emitLeaves (fun e hint top named => translateExprToWire e hint top named)
      cache logProf [("out", e)] none 0)
      ctx s returned t) :
    ∃ result sm w ty, LinkCtx.Runs we mems initial t result ∧ result "out" = v.toNat ∧
      LinkCtx.Typed we sm ∧
      t = (CircuitM.emitAssign "out" (.ref w) (CircuitM.addOutput "out" ty sm).2).2 := by
  obtain ⟨w, sm, ty, translate, fresh, ht, _⟩ := emitLeaves_single hr
  have wm : ScalarWidthsAgree we sm := by
    intro p hp; apply widths p; rw [ht, emitAssign_wires]; exact hp
  have step := contract.sem "out" false true s sm w prior h wm translate
  obtain ⟨middle, inv, val, frame⟩ := step.execution
  refine ⟨write middle "out" v.toNat, sm, w, ty, ?_, by simp [write], inv.typed, ht⟩
  rw [ht]
  exact LinkCtx.runs_emit (LinkCtx.runs_body (s := sm) rfl inv.runs)
    (by simpa [evalExpr] using congrArg some val)

end generic

/-- A BitVec input leaf at the root (the root-instance family covers it). -/
def isBitsLeaf : {s : SType} → Term s → Bool
  | _, .bitsInput _ _ => true
  | _, _ => false

/-- Sort-directed acceptance by the instance-aware recognizers. -/
def acceptedAtH (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder) :
    SType → Lean.Expr → Bool
  | .bool => fun e => hierGateBoolBody isInst kinds e
  | .bits w => fun e => hierGateBitsBody isInst kinds w e

set_option maxHeartbeats 1000000 in
/-- The instance-aware gate reads a concatenation in the fall-through of its
operator arm, before the instance check. -/
theorem hierGate_concatE (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder) (w : Nat)
    (dom a b : Lean.Expr) (m n : Nat) :
    hierGateBitsBody isInst kinds w (concatE dom m n a b) =
      (match sixArgShape? (concatE dom m n a b) with
       | some (r, ga, gb) =>
         w == r &&
           (match ga with | some m' => hierGateBitsBody isInst kinds m' a | none => true) &&
           (match gb with | some k' => hierGateBitsBody isInst kinds k' b | none => true)
       | none => isInst (concatE dom m n a b) && hierInstSpine isInst kinds (concatE dom m n a b)) := rfl

set_option maxHeartbeats 1000000 in
theorem hierGate_hiE (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder) (w : Nat)
    (dom b : Lean.Expr) (k v n : Nat) :
    hierGateBitsBody isInst kinds w (concatLitHiE dom k v n b) =
      (match sixArgShape? (concatLitHiE dom k v n b) with
       | some (r, ga, gb) =>
         w == r &&
           (match ga with | some m' => hierGateBitsBody isInst kinds m' (litE k v) | none => true) &&
           (match gb with | some k' => hierGateBitsBody isInst kinds k' b | none => true)
       | none => isInst (concatLitHiE dom k v n b) && hierInstSpine isInst kinds (concatLitHiE dom k v n b)) := rfl

set_option maxHeartbeats 1000000 in
theorem hierGate_loE (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder) (w : Nat)
    (dom a : Lean.Expr) (m k v : Nat) :
    hierGateBitsBody isInst kinds w (concatLitLoE dom m k v a) =
      (match sixArgShape? (concatLitLoE dom m k v a) with
       | some (r, ga, gb) =>
         w == r &&
           (match ga with | some m' => hierGateBitsBody isInst kinds m' a | none => true) &&
           (match gb with | some k' => hierGateBitsBody isInst kinds k' (litE k v) | none => true)
       | none => isInst (concatLitLoE dom m k v a) && hierInstSpine isInst kinds (concatLitLoE dom m k v a)) := rfl

set_option maxHeartbeats 1000000 in
theorem hierGate_sliceFE (isInst : Lean.Expr → Bool) (kinds : Array MixedGateBinder) (w : Nat)
    (dom : Lean.Expr) (nm : Lean.Name) (a : Lean.Expr) (ws start len : Nat) :
    hierGateBitsBody isInst kinds w (sliceFE dom nm ws start len a) =
      (match sixArgShape? (sliceFE dom nm ws start len a) with
       | some (r, ga, gb) =>
         w == r &&
           (match ga with
            | some m' => hierGateBitsBody isInst kinds m' (Tools.ShippingUnifiedMeaning.sliceLamE nm ws start len)
            | none => true) &&
           (match gb with | some k' => hierGateBitsBody isInst kinds k' a | none => true)
       | none => isInst (sliceFE dom nm ws start len a) && hierInstSpine isInst kinds (sliceFE dom nm ws start len a)) := rfl

/-- Quoted cones over accepted leaves are accepted by the instance-aware
gate; each operation checks its own width. -/
theorem hier_quote_accepted {isInst : Lean.Expr → Bool} {kinds : Array MixedGateBinder} {dom : Lean.Expr} {kb kv : Nat}
    {vw : Nat → Nat} {binp vinp : Nat → Lean.Expr}
    (hb : ∀ j, j < kb → hierGateBoolBody isInst kinds (binp j) = true)
    (hv : ∀ j, j < kv → hierGateBitsBody isInst kinds (vw j) (vinp j) = true) :
    ∀ {s} (e : Term s), e.WF kb kv vw →
      acceptedAtH isInst kinds s (quote dom binp vinp e) = true
  | _, .boolInput j, hj => hb j hj
  | _, .bitsInput w j, hj => by
    cases hj.2.1
    exact hv j hj.1
  | _, .boolLit b, _ => by cases b <;> rfl
  | _, .bitsLit w v, hv' => by
    show hierGateBitsBody isInst kinds w (quoteF dom w vinp (.lit v)) = true
    change (match bitVecLitValue? (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v)) with
      | some (k, _) => k == w
      | none => false) = true
    rw [litValue_natE w v hv'.1]
    simp
  | _, .bitsNum w v, hv' => by
    show hierGateBitsBody isInst kinds w (numSigE dom w v) = true
    change (match bitVecLitValue? (numLitE w v) with
      | some (k, _) => k == w
      | none => false) = true
    rw [litValue_numLitE w v hv'.1]
    simp
  | _, .binary op (w := w) a b, h => by
    obtain ⟨ha, hb'⟩ := h
    show hierGateBitsBody isInst kinds w (binE dom w op (quote dom binp vinp a)
      (quote dom binp vinp b)) = true
    have ck := op_checks op dom (quote dom binp vinp a) (quote dom binp vinp b) w
    have step : hierGateBitsBody isInst kinds w (binE dom w op (quote dom binp vinp a)
        (quote dom binp vinp b)) =
        (match signalBinOpOf (binMethod op),
            canonicalSignalBinKinds (binMethod op)
              (binE dom w op (quote dom binp vinp a) (quote dom binp vinp b)).getAppArgs,
            canonicalSignalBitVecWidth
              (binE dom w op (quote dom binp vinp a) (quote dom binp vinp b)).getAppArgs with
          | some _, some (true, true), some k =>
            k == w && hierGateBitsBody isInst kinds w (quote dom binp vinp a) &&
              hierGateBitsBody isInst kinds w (quote dom binp vinp b)
          | _, _, _ =>
            match sixArgShape?
                (binE dom w op (quote dom binp vinp a) (quote dom binp vinp b)) with
            | some (r, ga, gb) =>
              w == r &&
                (match ga with | some m => hierGateBitsBody isInst kinds m (quote dom binp vinp a) | none => true) &&
                (match gb with | some k => hierGateBitsBody isInst kinds k (quote dom binp vinp b) | none => true)
            | none =>
              isInst (binE dom w op (quote dom binp vinp a) (quote dom binp vinp b)) &&
                hierInstSpine isInst kinds
                  (binE dom w op (quote dom binp vinp a) (quote dom binp vinp b))) := by
      simp only [binE, mkApp6, mkApp4, mkApp2, mkAppB, mkApp]
      rfl
    have ia : hierGateBitsBody isInst kinds w (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBitsBody isInst kinds w (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    rw [step, ck.2.1, ck.2.2.1, ck.2.2.2.1]
    simp [ia, ib]
  | _, .compare le (w := w) a b, h => by
    obtain ⟨ha, hb'⟩ := h
    show hierGateBoolBody isInst kinds (compareE le dom w (quote dom binp vinp a)
      (quote dom binp vinp b)) = true
    have step : hierGateBoolBody isInst kinds (compareE le dom w (quote dom binp vinp a)
        (quote dom binp vinp b)) =
        (decide (0 < w) && hierGateBitsBody isInst kinds w (quote dom binp vinp a) &&
          hierGateBitsBody isInst kinds w (quote dom binp vinp b)) := by
      cases le <;> simp [compareE, compareName, mkApp2, mkApp3, mkAppB, mkApp,
        hierGateBoolBody, isBoolEquality, bitVecEqualityWidth?, canonicalNatLitValue?_natE]
    have ia : hierGateBitsBody isInst kinds w (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBitsBody isInst kinds w (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    rw [step, ia, ib]
    simp [a.wf_pos ha]
  | _, .boolBinary kind a b, h => by
    obtain ⟨ha, hb'⟩ := h
    show hierGateBoolBody isInst kinds (boolBinE kind dom (quote dom binp vinp a)
      (quote dom binp vinp b)) = true
    have gate : hierGateBoolBody isInst kinds (boolBinE kind dom (quote dom binp vinp a)
        (quote dom binp vinp b)) =
        (hierGateBoolBody isInst kinds (quote dom binp vinp a) &&
          hierGateBoolBody isInst kinds (quote dom binp vinp b)) := by cases kind <;> rfl
    have ia : hierGateBoolBody isInst kinds (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBoolBody isInst kinds (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    rw [gate, ia, ib]
    rfl
  | _, .appCompare le (w := w) a b, h => by
    obtain ⟨ha, hb'⟩ := h
    show hierGateBoolBody isInst kinds (appCompareE le dom w (quote dom binp vinp a)
      (quote dom binp vinp b)) = true
    have step : hierGateBoolBody isInst kinds (appE dom (bitVecE w) (appCompareBodyE le w)
        (quote dom binp vinp a) (quote dom binp vinp b)) =
        (match appBoolBody? (bitVecE w) (appCompareBodyE le w) with
          | some (.compare _ n) =>
            decide (0 < n) && hierGateBitsBody isInst kinds n (quote dom binp vinp a) &&
              hierGateBitsBody isInst kinds n (quote dom binp vinp b)
          | some (.bool _) =>
            hierGateBoolBody isInst kinds (quote dom binp vinp a) && hierGateBoolBody isInst kinds (quote dom binp vinp b)
          | none => false) := rfl
    have ia : hierGateBitsBody isInst kinds w (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBitsBody isInst kinds w (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    rw [appCompareE, step, appBoolBody?_compare]
    simp [ia, ib, a.wf_pos ha]
  | _, .appBool kind a b, h => by
    obtain ⟨ha, hb'⟩ := h
    show hierGateBoolBody isInst kinds (appBoolE kind dom (quote dom binp vinp a)
      (quote dom binp vinp b)) = true
    have gate : hierGateBoolBody isInst kinds (appBoolE kind dom (quote dom binp vinp a)
        (quote dom binp vinp b)) =
        (hierGateBoolBody isInst kinds (quote dom binp vinp a) &&
          hierGateBoolBody isInst kinds (quote dom binp vinp b)) := by cases kind <;> rfl
    have ia : hierGateBoolBody isInst kinds (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBoolBody isInst kinds (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    rw [gate, ia, ib]
    rfl
  | _, .boolNot a, ha => by
    show hierGateBoolBody isInst kinds (boolNotE dom (quote dom binp vinp a)) = true
    exact (hier_quote_accepted hb hv a ha :
      hierGateBoolBody isInst kinds (quote dom binp vinp a) = true)
  | _, .boolEq a b, h => by
    obtain ⟨ha, hb'⟩ := h
    show hierGateBoolBody isInst kinds (boolEqE dom (quote dom binp vinp a)
      (quote dom binp vinp b)) = true
    have ia : hierGateBoolBody isInst kinds (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBoolBody isInst kinds (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    change (hierGateBoolBody isInst kinds (quote dom binp vinp a) &&
      hierGateBoolBody isInst kinds (quote dom binp vinp b)) = true
    rw [ia, ib]
    rfl
  | .bool, .mux c a b, h => by
    obtain ⟨hc, ha, hb'⟩ := h
    show hierGateBoolBody isInst kinds (boolMuxE dom (quote dom binp vinp c)
      (quote dom binp vinp a) (quote dom binp vinp b)) = true
    have ic : hierGateBoolBody isInst kinds (quote dom binp vinp c) = true :=
      hier_quote_accepted hb hv c hc
    have ia : hierGateBoolBody isInst kinds (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBoolBody isInst kinds (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    change (hierGateBoolBody isInst kinds (quote dom binp vinp c) &&
      hierGateBoolBody isInst kinds (quote dom binp vinp a) &&
      hierGateBoolBody isInst kinds (quote dom binp vinp b)) = true
    rw [ic, ia, ib]
    rfl
  | .bits w, .mux c a b, h => by
    obtain ⟨hc, ha, hb'⟩ := h
    show hierGateBitsBody isInst kinds w (muxE dom (bitVecE w) (quote dom binp vinp c)
      (quote dom binp vinp a) (quote dom binp vinp b)) = true
    have ic : hierGateBoolBody isInst kinds (quote dom binp vinp c) = true :=
      hier_quote_accepted hb hv c hc
    have ia : hierGateBitsBody isInst kinds w (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBitsBody isInst kinds w (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    change (canonicalNatLitValue? (natE w) == some w &&
      hierGateBoolBody isInst kinds (quote dom binp vinp c) &&
      hierGateBitsBody isInst kinds w (quote dom binp vinp a) &&
      hierGateBitsBody isInst kinds w (quote dom binp vinp b)) = true
    rw [canonicalNatLitValue?_natE, ic, ia, ib]
    simp
  | _, .setw (w := w) w' a, h => by
    obtain ⟨ha, hpos⟩ := h
    show hierGateBitsBody isInst kinds w' (setwE dom w w' (quote dom binp vinp a)) = true
    have ia : hierGateBitsBody isInst kinds w (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    change (canonicalNatLitValue? (natE w') == some w' &&
      canonicalNatLitValue? (natE w') == some w' &&
      (match canonicalNatLitValue? (natE w), canonicalNatLitValue? (natE w) with
       | some ws, some ws' => ws' == ws && 0 < ws &&
           hierGateBitsBody isInst kinds ws (quote dom binp vinp a)
       | _, _ => false)) = true
    rw [canonicalNatLitValue?_natE, canonicalNatLitValue?_natE]
    simp [ia, a.wf_pos ha]
  | _, .slice nm start len (w := w) a, h => by
    obtain ⟨ha, hlen, hr⟩ := h
    show hierGateBitsBody isInst kinds len (sliceE dom nm w start len (quote dom binp vinp a)) = true
    have ia : hierGateBitsBody isInst kinds w (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    change (canonicalNatLitValue? (natE len) == some len &&
      canonicalNatLitValue? (natE len) == some len &&
      (match canonicalNatLitValue? (natE w), canonicalNatLitValue? (natE w),
          canonicalNatLitValue? (natE start) with
       | some ws, some ws', some st =>
         ws' == ws && 0 < len && decide (st + len ≤ ws) &&
           hierGateBitsBody isInst kinds ws (quote dom binp vinp a)
       | _, _, _ => false)) = true
    rw [canonicalNatLitValue?_natE, canonicalNatLitValue?_natE, canonicalNatLitValue?_natE]
    simp [ia, hlen, hr]
  | _, .concat (m := m) (n := n) a b, h => by
    obtain ⟨ha, hb'⟩ := h
    show hierGateBitsBody isInst kinds (m + n)
      (concatE dom m n (quote dom binp vinp a) (quote dom binp vinp b)) = true
    have ia : hierGateBitsBody isInst kinds m (quote dom binp vinp a) = true :=
      hier_quote_accepted hb hv a ha
    have ib : hierGateBitsBody isInst kinds n (quote dom binp vinp b) = true :=
      hier_quote_accepted hb hv b hb'
    rw [hierGate_concatE, Tools.ShippingUnifiedMeaning.sixArgShape?_concatE dom _ _ (a.wf_pos ha) (b.wf_pos hb')]
    simp [ia, ib]
  | _, .concatLitHi k v (n := n) b, h => by
    obtain ⟨hb', hk, hlt⟩ := h
    show hierGateBitsBody isInst kinds (k + n) (concatLitHiE dom k v n (quote dom binp vinp b)) = true
    have ib : hierGateBitsBody isInst kinds n (quote dom binp vinp b) = true := hier_quote_accepted hb hv b hb'
    rw [hierGate_hiE, Tools.ShippingUnifiedMeaning.sixArgShape?_hiE dom _ hk hlt (b.wf_pos hb')]
    simp [ib]
  | _, .concatLitLo (m := m) a k v, h => by
    obtain ⟨ha, hk, hlt⟩ := h
    show hierGateBitsBody isInst kinds (m + k) (concatLitLoE dom m k v (quote dom binp vinp a)) = true
    have ia : hierGateBitsBody isInst kinds m (quote dom binp vinp a) = true := hier_quote_accepted hb hv a ha
    rw [hierGate_loE, Tools.ShippingUnifiedMeaning.sixArgShape?_loE dom _ hk hlt (a.wf_pos ha)]
    simp [ia]
  | _, .zextMap nm k (n := n) a, h => by
    obtain ⟨ha, hk⟩ := h
    show hierGateBitsBody isInst kinds (k + n) (zextMapE dom nm k n (quote dom binp vinp a)) = true
    have ia : hierGateBitsBody isInst kinds n (quote dom binp vinp a) = true := hier_quote_accepted hb hv a ha
    change (canonicalNatLitValue? (natE (k + n)) == some (k + n) &&
      (match canonicalNatLitValue? (natE n), canonicalNatLitValue? (natE k),
          canonicalNatLitValue? (natE n), canonicalNatLitValue? (natE k),
          canonicalNatLitValue? (natE 0) with
       | some ws, some k', some ws', some kl, some z =>
         0 < ws && 0 < k' && k + n == k' + ws && ws' == ws && kl == k' && z == 0 &&
           hierGateBitsBody isInst kinds ws (quote dom binp vinp a)
       | _, _, _, _, _ => false)) = true
    simp only [canonicalNatLitValue?_natE]
    simp [ia, hk, a.wf_pos ha]
  | _, .sliceF nm start len (w := w) a, h => by
    obtain ⟨ha, hlen, hr⟩ := h
    show hierGateBitsBody isInst kinds len (sliceFE dom nm w start len (quote dom binp vinp a)) = true
    have ia : hierGateBitsBody isInst kinds w (quote dom binp vinp a) = true := hier_quote_accepted hb hv a ha
    rw [hierGate_sliceFE, Tools.ShippingUnifiedMeaning.sixArgShape?_sliceFE dom nm _ hlen hr]
    simp [ia]

/-- A six-argument root (a concatenation, a `<$>` slice): its width is read
from the shape. -/
theorem hroot_of_concat {isInst : Lean.Expr → Bool} {kinds : Array MixedGateBinder}
    {e : Lean.Expr} {r : Nat} {ga gb : Option Nat}
    (cc : sixArgShape? e = some (r, ga, gb))
    (body : hierGateBitsBody isInst kinds r e = true) :
    hierGateRoot isInst kinds e = true := by
  unfold hierGateRoot
  rw [cc]
  simp [body]

/-- Root acceptance helpers for the instance-aware gate. -/
theorem hroot_of_bool {isInst : Lean.Expr → Bool} {kinds : Array MixedGateBinder} {e : Lean.Expr}
    (body : hierGateBoolBody isInst kinds e = true) : hierGateRoot isInst kinds e = true := by
  unfold hierGateRoot
  rw [body]
  rfl

theorem hroot_of_top {isInst : Lean.Expr → Bool} {kinds : Array MixedGateBinder} {n : Nat} {e : Lean.Expr} (hn : 0 < n)
    (mux : canonicalMuxType? e = none)
    (top : gateTopWidth? (mixedBitKinds kinds) e = some n)
    (body : hierGateBitsBody isInst kinds n e = true) : hierGateRoot isInst kinds e = true := by
  unfold hierGateRoot
  rw [mux, top]
  simp [body, hn]

theorem hroot_of_mux {isInst : Lean.Expr → Bool} {kinds : Array MixedGateBinder} {n : Nat} {e : Lean.Expr} (hn : 0 < n)
    (mux : canonicalMuxType? e = some (.bitVector n))
    (body : hierGateBitsBody isInst kinds n e = true) : hierGateRoot isInst kinds e = true := by
  unfold hierGateRoot
  rw [mux]
  simp [body, hn]

theorem hroot_of_setw {isInst : Lean.Expr → Bool} {kinds : Array MixedGateBinder} {n : Nat} {e : Lean.Expr} (hn : 0 < n)
    (mux : canonicalMuxType? e = none)
    (top : gateTopWidth? (mixedBitKinds kinds) e = none)
    (swtop : canonicalSetWidthTop? e = some n)
    (body : hierGateBitsBody isInst kinds n e = true) : hierGateRoot isInst kinds e = true := by
  unfold hierGateRoot
  rw [mux, top, swtop]
  simp [body, hn]

set_option maxHeartbeats 1000000 in
/-- Root width for every non-leaf `.bits` constructor, from the same
syntactic sources as the established vector gate. A bare leaf root is the
instance-root family's business. -/
theorem hier_root_accepted {isInst : Lean.Expr → Bool} {kinds : Array MixedGateBinder} {dom : Lean.Expr} {kb kv : Nat}
    {vw : Nat → Nat} {binp vinp : Nat → Lean.Expr}
    (hb : ∀ j, j < kb → hierGateBoolBody isInst kinds (binp j) = true)
    (hv : ∀ j, j < kv → hierGateBitsBody isInst kinds (vw j) (vinp j) = true)
    :
    ∀ {s} (e : Term s), e.WF kb kv vw → isBitsLeaf e = false →
      hierGateRoot isInst kinds (quote dom binp vinp e) = true
  | .bool, e, he, _ => hroot_of_bool (hier_quote_accepted hb hv e he)
  | _, .bitsInput w j, he, hl => by cases hl
  | _, .bitsLit w v, he, _ => by
    have body : hierGateBitsBody isInst kinds w (quoteF dom w vinp (.lit v)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.bitsLit w v) he
    have mux : canonicalMuxType? (quoteF dom w vinp (.lit v)) = none := rfl
    have top : gateTopWidth? (mixedBitKinds kinds) (quoteF dom w vinp (.lit v)) = some w := by
      change ((quoteF dom w vinp (.lit v)).getAppArgs.back?.bind bitVecLitValue?).map (·.1) =
        some w
      change ((some (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v))).bind
        bitVecLitValue?).map (·.1) = some w
      rw [Option.bind_some, litValue_natE w v he.1]
      rfl
    exact hroot_of_top he.2 mux top body
  | _, .bitsNum w v, he, _ => by
    have body : hierGateBitsBody isInst kinds w (numSigE dom w v) = true :=
      hier_quote_accepted (dom := dom) hb hv (.bitsNum w v) he
    have mux : canonicalMuxType? (numSigE dom w v) = none := rfl
    have top : gateTopWidth? (mixedBitKinds kinds) (numSigE dom w v) = some w := by
      change ((numSigE dom w v).getAppArgs.back?.bind bitVecLitValue?).map (·.1) =
        some w
      change ((some (numLitE w v)).bind
        bitVecLitValue?).map (·.1) = some w
      rw [Option.bind_some, litValue_numLitE w v he.1]
      rfl
    exact hroot_of_top he.2 mux top body
  | _, .binary op (w := w) a b, he, _ => by
    have body : hierGateBitsBody isInst kinds w (binE dom w op (quote dom binp vinp a)
        (quote dom binp vinp b)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.binary op a b) he
    obtain ⟨ha, hb'⟩ := he
    have hn : 0 < w := a.wf_pos ha
    have ck := op_checks op dom (quote dom binp vinp a) (quote dom binp vinp b) w
    have mux : canonicalMuxType? (binE dom w op (quote dom binp vinp a)
        (quote dom binp vinp b)) = none := by
      cases op <;> rfl
    have top : gateTopWidth? (mixedBitKinds kinds) (binE dom w op (quote dom binp vinp a)
        (quote dom binp vinp b)) = some w := by
      simp only [gateTopWidth?, ck.1, ck.2.2.2.2.2.2, Bool.false_eq_true, if_false]
      exact ck.2.2.2.1
    exact hroot_of_top hn mux top body
  | .bits w, .mux c a b, he, _ => by
    have body : hierGateBitsBody isInst kinds w (muxE dom (bitVecE w) (quote dom binp vinp c)
        (quote dom binp vinp a) (quote dom binp vinp b)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.mux c a b) he
    obtain ⟨hc, ha, hb'⟩ := he
    exact hroot_of_mux (a.wf_pos ha) (canonicalMuxType?_bitVec ..) body
  | _, .setw (w := w) w' a, he, _ => by
    have body : hierGateBitsBody isInst kinds w' (setwE dom w w' (quote dom binp vinp a)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.setw w' a) he
    obtain ⟨ha, hpos⟩ := he
    have mux : canonicalMuxType? (setwE dom w w' (quote dom binp vinp a)) = none := rfl
    have top : gateTopWidth? (mixedBitKinds kinds)
        (setwE dom w w' (quote dom binp vinp a)) = none := rfl
    have swtop : canonicalSetWidthTop? (setwE dom w w' (quote dom binp vinp a)) = some w' := by
      unfold canonicalSetWidthTop?
      rw [Tools.ShippingUnifiedRecursion.canonicalSetWidth?_setwE dom _ (a.wf_pos ha) hpos]
    exact hroot_of_setw hpos mux top swtop body
  | _, .slice nm start len (w := w) a, he, _ => by
    have body : hierGateBitsBody isInst kinds len (sliceE dom nm w start len (quote dom binp vinp a)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.slice nm start len a) he
    obtain ⟨ha, hlen, hr⟩ := he
    exact hroot_of_setw hlen (Tools.ShippingUnifiedExecutionSoundness.sliceE_noMux ..) (Tools.ShippingUnifiedExecutionSoundness.sliceE_noTop ..)
      (Tools.ShippingUnifiedExecutionSoundness.sliceE_top dom nm _ hlen hr) body
  | _, .concat (m := m) (n := n) a b, he, _ => by
    have body : hierGateBitsBody isInst kinds (m + n)
        (concatE dom m n (quote dom binp vinp a) (quote dom binp vinp b)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.concat a b) he
    obtain ⟨ha, hb'⟩ := he
    exact hroot_of_concat (Tools.ShippingUnifiedMeaning.sixArgShape?_concatE dom _ _
      (a.wf_pos ha) (b.wf_pos hb')) body
  | _, .concatLitHi k v (n := n) b, he, _ => by
    have body : hierGateBitsBody isInst kinds (k + n) (concatLitHiE dom k v n (quote dom binp vinp b)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.concatLitHi k v b) he
    obtain ⟨hb', hk, hlt⟩ := he
    exact hroot_of_concat (Tools.ShippingUnifiedMeaning.sixArgShape?_hiE dom _ hk hlt (b.wf_pos hb')) body
  | _, .concatLitLo (m := m) a k v, he, _ => by
    have body : hierGateBitsBody isInst kinds (m + k) (concatLitLoE dom m k v (quote dom binp vinp a)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.concatLitLo a k v) he
    obtain ⟨ha, hk, hlt⟩ := he
    exact hroot_of_concat (Tools.ShippingUnifiedMeaning.sixArgShape?_loE dom _ hk hlt (a.wf_pos ha)) body
  | _, .zextMap nm k (n := n) a, he, _ => by
    have body : hierGateBitsBody isInst kinds (k + n) (zextMapE dom nm k n (quote dom binp vinp a)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.zextMap nm k a) he
    obtain ⟨ha, hk⟩ := he
    exact hroot_of_setw (Nat.add_pos_left hk n) (Tools.ShippingUnifiedExecutionSoundness.zextMapE_noMux ..) (Tools.ShippingUnifiedExecutionSoundness.zextMapE_noTop ..)
      (Tools.ShippingUnifiedExecutionSoundness.zextMapE_top dom nm _ hk (a.wf_pos ha)) body
  | _, .sliceF nm start len (w := w) a, he, _ => by
    have body : hierGateBitsBody isInst kinds len (sliceFE dom nm w start len (quote dom binp vinp a)) = true :=
      hier_quote_accepted (dom := dom) hb hv (.sliceF nm start len a) he
    obtain ⟨ha, hlen, hr⟩ := he
    exact hroot_of_concat (Tools.ShippingUnifiedMeaning.sixArgShape?_sliceFE dom nm _ hlen hr) body

/-- Once the real declaration has been peeled, recognition of a cone over
accepted leaves follows — AT the given designation predicate. -/
theorem hier_cone_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bE vE : Nat → Lean.Expr}
    {srt : SType} {e : Term srt} {isInst : Lean.Expr → Bool}
    (peel : mixedGatePeel d.value = some (bs, quote dom bE vE e))
    (he : e.WF kb kv vw) (hroot : isBitsLeaf e = false)
    (hscalar : mixedGateResultScalar d.type = true)
    (hb : ∀ j, j < kb → hierGateBoolBody isInst (bs.map Prod.snd).toArray (bE j) = true)
    (hv : ∀ j, j < kv →
      hierGateBitsBody isInst (bs.map Prod.snd).toArray (vw j) (vE j) = true) :
    mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, quote dom bE vE e) := by
  have root := hier_root_accepted (kinds := (bs.map Prod.snd).toArray) (dom := dom)
    hb hv e he hroot
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, hscalar, Bool.and_self, Bool.or_true,
    Bool.true_or, if_true]

/-- A pipeline root — a designated call over binders and nested designated
calls — is recognized AT the given designation predicate. -/
theorem hier_instRoot_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} {isInst : Lean.Expr → Bool}
    (peel : mixedGatePeel d.value = some (bs, body))
    (hroot : hierInstRoot isInst (bs.map Prod.snd).toArray body = true)
    (hscalar : mixedGateResultScalar d.type = true) :
    mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, body) := by
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, hroot, hscalar, Bool.and_self, Bool.or_true,
    Bool.true_or, if_true]

/-- The linked value observed at `out`. -/
def HierValue (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (m : Sparkle.IR.AST.Module) (initial : Env) (mems : MEnv) (expected : Nat) : Prop :=
  ∃ result, evalAssignsH (moduleWidths m) children mems m.body initial = some result ∧
    result "out" = expected

/-- Every instance statement of the module is an instance of a linked child,
WIDTH-LINKED against the module's own declarations. -/
def InstsLinked (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (m : Sparkle.IR.AST.Module) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ m.body →
    ∃ child cwe, children mn = some (child, cwe) ∧ Linked m child conns

/-- A leaf's meaning, with the child semantics explicit. -/
def LeafMeaning (C : ChildSem) (inputs : FVarId → Option Value) (e : Lean.Expr)
    (v : Value) : Prop :=
  @Meaning C inputs e v

/-- A leaf's contract at every width environment and fuel, in the linked
semantic context of `children`. -/
def LeafContract (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (C : ChildSem)
    (ctx : CompilerState) (inputs : FVarId → Option Value) (mems : MEnv) (initial : Env)
    (e : Lean.Expr) (v : Value) : Prop :=
  ∀ (we : WEnv) (fuel : Nat),
    @Contract (hierLink children).toLinkCtx C (translateFuelFix translateStep fuel)
      ctx inputs we mems initial e v

/-- Linked source preservation for a cone over arbitrary leaves: whenever the
quoted body's leaves carry their meanings and contracts, the compiled
module's linked evaluation observes the term's evaluation at `out`. -/
def HierConePreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (C : ChildSem)
      (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) (mems : MEnv),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits initial (bs.zip ids) a →
    Separate p.bools p.bits ∧
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (bE vE : Nat → Lean.Expr)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (w : Nat) → BitVec w)
      {srt : SType} (e : Term srt),
    e.WF kb kv vw →
    (∀ j, j < kb → LeafMeaning C (inputValues p.bools p.bits) (bE j) (.bool (bvals j))) →
    (∀ j, j < kv → LeafMeaning C (inputValues p.bools p.bits) (vE j)
      (.bits (vw j) (vvals j (vw j)))) →
    (∀ j, j < kb → LeafContract children C p.context (inputValues p.bools p.bits)
      mems initial (bE j) (.bool (bvals j))) →
    (∀ j, j < kv → LeafContract children C p.context (inputValues p.bools p.bits)
      mems initial (vE j) (.bits (vw j) (vvals j (vw j)))) →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body = quote dom bE vE e →
    HierValue children m initial mems (pack srt (eval bvals vvals e)).toNat ∧
      InstsLinked children m

theorem synthesizeMixedCertified_hierCone_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    HierConePreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro children C bools bits initial mems a p values
  have empty := empty_layout (entryCompilerState false cache) declName.toString initial
  have prepared := prepare_layout (bs.zip ids) a empty.1 empty.2 values
  refine ⟨prepared.1.separate prepared.2.1, ?_⟩
  intro dom kb kv vw bE vE bvals vvals srt e he hbM hvM hbC hvC qeq
  letI : HierCtx := hierLink children
  letI : ChildSem := C
  have leaf := prepare_returns (bs.zip ids) a (bools := bools) (bits := bits) run
  rw [qeq] at leaf
  have contract : Contract (fun e hint top named => translateExprToWire e hint top named)
      p.context (inputValues p.bools p.bits) (declaredWidths st) mems initial
      (quote dom bE vE e) (pack srt (eval bvals vvals e)) :=
    fuel_contract_leaves translateFuelLimit hbM hvM
      (fun j hj fuel => hbC j hj (declaredWidths st) fuel)
      (fun j hj fuel => hvC j hj (declaredWidths st) fuel) e he
  obtain ⟨growth, finalWires⟩ := emitLeaves_structure_link contract
    (lookup_of_ports prepared.1 prepared.2.1) prepared.2.1 leaf
  have widths := declaredWidths_agree finalWires
  have inv0 : Inv p.context (inputValues p.bools p.bits) (declaredWidths st) mems initial
      p.state initial :=
    initial_link prepared.2.2.1 prepared.2.2.2 (prepared.1.inputs prepared.2.1 growth widths)
  obtain ⟨result, sm, wOut, ty, evalr, value, typedSm, ht⟩ :=
    emitLeaves_runs_link contract inv0 widths leaf
  have wireEq : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have bodyEq : m.body = st.module.finalize.body := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).1]
  refine ⟨⟨result, ?_, value⟩, ?_⟩
  · rw [moduleWidths_finish wireEq finalWires, bodyEq]
    exact evalr
  · intro mn iname conns hmem
    have hmem' : Stmt.inst mn iname conns ∈ st.module.body := by
      rw [bodyEq] at hmem
      exact List.mem_reverse.mp hmem
    rw [ht, emitAssign_body_cons] at hmem'
    rcases List.mem_cons.mp hmem' with hbad | hmem'
    · cases hbad
    · obtain ⟨child, cwe, hc, hl⟩ := HierCtx.typed_linked typedSm hmem'
      refine ⟨child, cwe, hc, hl.mono ?_ ?_⟩
      · intro q hq
        rw [wireEq, List.mem_reverse, ht, emitAssign_wires]
        exact hq
      · intro q hq
        rw [hm]
        show q ∈ (addClockResetIfSequential st.module).inputs.reverse
        rw [List.mem_reverse]
        exact (addClockReset_facts st.module).2.2.2 q (by rw [ht]; exact hq)

/-- The declaration dispatcher selects the proved cone path. -/
theorem synthesizeFromConst_hierCone_sound {logProf declName ci bs body m d}
    {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    HierConePreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_hierCone_sound run

/-- The cone result is tied to the declaration and the environment THIS run
read: the gate holds at `instancePredicate envR` for the run's own `getEnv`. -/
theorem synthesizeCombinationalCore_hierCone_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w') :
    ∃ (ci : ConstantInfo) (envR : Environment) (w1 w2 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci
          (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body) →
        HierConePreserves declName bs body m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    Tools.ShippingEntrySoundness.synthesizeCombinationalCore_reads hr
  exact ⟨ci, envR, w1, w2, w5, w6, get, henv, fun _ _ old shape =>
    synthesizeFromConst_hierCone_sound old shape (Tools.ShippingEntrySoundness.entry_kept shape run).mreturns⟩

/-- The cone entry endpoint under the run's environment boundaries: a
declaration whose value peels to a quoted term over accepted leaves — the
leaf acceptance holding at the run's own designation predicate — compiles
to a module with the linked-cone guarantee. -/
theorem hierCone_entry_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bE vE : Nat → Lean.Expr}
    {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (env : Tools.ShippingEntrySoundness.EnvDefines mctx mref cctx cref declName value)
    (old : ∀ dv : DefinitionVal, dv.value = value →
      certifiedShape? false [] (.defnInfo dv) = none)
    (hscalar : ∀ dv : DefinitionVal, dv.value = value →
      mixedGateResultScalar dv.type = true)
    (peel : mixedGatePeel value = some (bs, quote dom bE vE e))
    (he : e.WF kb kv vw) (hroot : isBitsLeaf e = false)
    (leaves : ∀ wE envR wE',
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE envR wE' →
      (∀ j, j < kb → hierGateBoolBody (Sparkle.Compiler.Elab.instancePredicate envR)
        (bs.map Prod.snd).toArray (bE j) = true) ∧
      (∀ j, j < kv → hierGateBitsBody (Sparkle.Compiler.Elab.instancePredicate envR)
        (bs.map Prod.snd).toArray (vw j) (vE j) = true)) :
    HierConePreserves declName bs (quote dom bE vE e) m := by
  obtain ⟨ci, envR, w1, w2, w5, w6, get, henv, sel⟩ :=
    synthesizeCombinationalCore_hierCone_sound hr
  obtain ⟨dv, rfl, hval⟩ := env w1 ci w2 get
  obtain ⟨hb, hv⟩ := leaves _ _ _ henv
  have shape := hier_cone_gate (d := dv) (by rw [hval]; exact peel) he hroot
    (hscalar dv hval) hb hv
  exact sel bs _ (old dv hval) shape

/-- The pipeline-root entry endpoint: a declaration whose whole body is a
designated call over binders and nested designated calls — recognized at the
run's own predicate — compiles to a module with the linked-cone guarantee
(instantiate it at the one-leaf term whose leaf is the call). -/
theorem hierRoot_entry_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, d) w')
    (env : Tools.ShippingEntrySoundness.EnvDefines mctx mref cctx cref declName value)
    (old : ∀ dv : DefinitionVal, dv.value = value →
      certifiedShape? false [] (.defnInfo dv) = none)
    (hscalar : ∀ dv : DefinitionVal, dv.value = value →
      mixedGateResultScalar dv.type = true)
    (peel : mixedGatePeel value = some (bs, body))
    (root : ∀ wE envR wE',
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref wE envR wE' →
      hierInstRoot (Sparkle.Compiler.Elab.instancePredicate envR)
        (bs.map Prod.snd).toArray body = true) :
    HierConePreserves declName bs body m := by
  obtain ⟨ci, envR, w1, w2, w5, w6, get, henv, sel⟩ :=
    synthesizeCombinationalCore_hierCone_sound hr
  obtain ⟨dv, rfl, hval⟩ := env w1 ci w2 get
  have shape := hier_instRoot_gate (d := dv) (by rw [hval]; exact peel)
    (root _ _ _ henv) (hscalar dv hval)
  exact sel bs _ (old dv hval) shape

end Tools.ShippingHierTermSoundness
