import Tools.ShippingGateConeBoolNot

variable {tenv : Lean.Environment}

/-! # The Bool binary node of the cone at world level (worker N, round 7)

WRITTEN, NOT BUILT.

A canonical Bool operator `boolBinE kind dom a b` (`&&&` / `|||` / `^^^` on
`Signal dom Bool`) is routed to the validated-cache wrapper around
`translateBoolBinary` (both operands, one Bool wire and its assign).

* `boolBin_freshAt`: the text of the built `boolBin_shape` / `boolBin_fresh`
  over the operand runs' own facts (`ChildAt`).
* `boolBin_missW`: a run of `translateBoolBinary` with its worlds (the
  pattern of `signalCompare_missW`).
* **`boolBin_contractW`** (through `cachedW_contract`).
* `cfragC3` (NEW; earlier fragments unchanged) = `cfragC2` + `boolBinary`,
  **`fuel_contractWC3`**. -/
namespace Tools.ShippingGateParentRun
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTypedExprSoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx
open Tools.ShippingHierarchySoundness
open Tools.ShippingChildInv (RefLaws InvV J KeepsC Res
  cacheLookupValidated_keepsC recordTranslation_keepsC makeWire_keepsC emitAssign_keepsC)
open Tools.ShippingCacheCoherentRun (SubMap sub_trans sub_refl)

set_option linter.unusedSectionVars false

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

section generic
variable [LinkCtx] [ChildSem]

/-- **The Bool binary lowering over `ChildAt`s** (the text of the built
`boolBin_shape` / `boolBin_fresh`, with the operand facts of ONE run each). -/
theorem boolBin_freshAt {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {s sa sb t : CircuitState} {a b w hint : String}
    {named : Bool} {kind : SignalBoolBinKind}
    (x y : Bool)
    (ca : ChildAt ctx inputs we mems initial s sa a (.bool x))
    (cb : ChildAt ctx inputs we mems initial sa sb b (.bool y))
    (re : Tools.ShippingTranslateSoundness.Returns
      (emitBoolResult (.op (signalBoolBinOp kind) [.ref a, .ref b]) hint named) ctx sb w t) :
    (Lookup ctx inputs s → Frame s t ∧ s.usedNames.contains w = false) ∧
    (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
      Outcome ctx inputs we mems initial prior s t w (.bool (boolBinValue kind x y))) := by
  refine ⟨fun lookup => ?_, fun prior h widths => ?_⟩
  · have fa := ca.frame lookup
    have fb := cb.frame (lookup.transfer fa)
    obtain ⟨fe, fresh⟩ :=
      Tools.ShippingMixedRecursion.emit_bool_frame (by cases kind <;> rfl) re
    refine ⟨(fa.trans fb).trans fe, ?_⟩
    cases hu : s.usedNames.contains w
    · rfl
    · have := fb.used w (fa.used w hu); simp [fresh] at this
  · have fa := ca.frame (Lookup.ofInputs h.inputs)
    have fb := cb.frame ((Lookup.ofInputs h.inputs).transfer fa)
    have fe := (Tools.ShippingMixedRecursion.emit_bool_frame (by cases kind <;> rfl) re).1
    have aout := ca.sem prior h ((fb.decls.trans fe.decls).widths widths)
    obtain ⟨va', ia, av, af⟩ := aout.execution
    have bout := cb.sem va' ia (fe.decls.widths widths)
    obtain ⟨vb', ib, bv, bf⟩ := bout.execution
    have step := emit_bool_outcome ib
      (Tools.ShippingMixedRecursion.typed_bool_bin kind a b aout.width bout.width)
      (Tools.ShippingMixedRecursion.bool_bin_rhs kind we vb' a b x y
        ((bf a aout.used).trans av) bv aout.width bout.width)
      widths re
    obtain ⟨result, inv, val, frame⟩ := step.execution
    exact ⟨step.used, step.width, fun z hz => step.grows z (fb.used z (fa.used z hz)),
      result, inv, val, fun z hz => (frame z (fb.used z (fa.used z hz))).trans
        ((bf z (fa.used z hz)).trans (af z hz))⟩

/-- **A run of the Bool binary lowering, with its worlds** (the pattern of
`signalCompare_missW`). -/
theorem boolBin_missW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {ae be : Lean.Expr} {kind : SignalBoolBinKind}
    (x y : Bool)
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae (.bool x))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      be (.bool y))
    {hint : String} {named : Bool} {s sm : CircuitState} {w : String}
    {wa wb : Void IO.RealWorld}
    (hwa0 : InvV L wa) (hda0 : L.dval wa = D)
    (miss : RunsC (translateBoolBinary (translateFuelFix (translateStep tenv) fuel) kind ae be
      hint named) ctx s mctx mref cctx cref wa (w, sm) wb) :
    InvV L wb ∧ L.dval wb = D ∧ (SubMap (L.val wb) mF →
      (Lookup ctx inputs s → Frame s sm ∧ s.usedNames.contains w = false) ∧
      (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we sm →
        Outcome ctx inputs we mems initial prior s sm w (.bool (boolBinValue kind x y)))) := by
  unfold translateBoolBinary at miss
  obtain ⟨a, sa, wa1, ra, rest⟩ := RunsC.bind miss
  obtain ⟨b, sb, wb1, rb, re⟩ := RunsC.bind rest
  obtain ⟨hwa1, hda1, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa0 hda0 ra
  obtain ⟨hwb1, hdb1, hsab⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa1 hda1 rb
  have reR := runsCReturns re
  have reE : RunsC (emitBoolResult (.op (signalBoolBinOp kind) [.ref a, .ref b]) hint named)
      ctx sb mctx mref cctx cref wb1 (w, sm) wb := re
  unfold emitBoolResult at reE
  obtain ⟨r1, s1, wq, rm, rest2⟩ := RunsC.bind reE
  obtain ⟨u, s2, wq2, rem, fin⟩ := RunsC.bind rest2
  obtain ⟨-, hwq⟩ := RunsC.pure fin
  obtain ⟨hwm, hdm, hs1⟩ :=
    keepsW L (fun L' => makeWire_keepsC L' D hint .bit named) hwb1 hdb1 rm
  obtain ⟨hwq', hdq', hs2⟩ :=
    keepsW L (fun L' => emitAssign_keepsC L' D r1 (.op (signalBoolBinOp kind) [.ref a, .ref b]))
      hwm hdm rem
  rw [← hwq] at hwq' hdq' hs2
  refine ⟨hwq', hdq', fun hsub => ?_⟩
  have subB : SubMap (L.val wb1) mF := sub_trans hs1 (sub_trans hs2 hsub)
  have subA : SubMap (L.val wa1) mF := sub_trans hsab subB
  have caAt := ca.atRun hwa0 hda0 subA ra
  have cbAt := cb.atRun hwa1 hda1 subB rb
  exact boolBin_freshAt x y caAt cbAt reR

/-- **The world-indexed contract of a canonical Bool binary node**, from those
of its operands. -/
theorem boolBin_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom ae be : Lean.Expr}
    (kind : SignalBoolBinKind) (a b : Bool)
    (meaning : Meaning inputs (boolBinE kind dom ae be) (.bool (boolBinValue kind a b)))
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae (.bool a))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      be (.bool b)) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      (boolBinE kind dom ae be) (.bool (boolBinValue kind a b)) := by
  refine cachedW_contract (tenv := tenv) L fuel
    (lower := translateBoolUncachedWith (translateFuelFix (translateStep tenv) fuel)
      (fun e h t n => Sparkle.Compiler.Elab.Rec.translateExprToWireImpl
        (fun e h t n => translateFuelFix (translateStep tenv) fuel e h t n) e h t n))
    meaning (fun hint top named => ?_) ?_
  · rw [Tools.ShippingMixedRecursion.boolBin_step]
    exact translateFallback_bool _ _ hint top named (by cases kind <;> rfl)
  · intro mctx cctx hint top named s sm w wa wb hwa hda miss
    rw [Tools.ShippingMixedRecursion.translateBoolUncachedWith_boolBin] at miss
    exact boolBin_missW (tenv := tenv) L hD fuel a b ca cb hwa hda miss

/-! ## The fragment with Bool binary operators, and its fuel induction -/

/-- The cone nodes walked at world level: `cfragC2` plus `boolBinary`.
(Earlier fragments are unchanged.) -/
def cfragC3 : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .bitsNum _ _ => true
  | _, .binary _ a b => cfragC3 a && cfragC3 b
  | _, .compare _ a b => cfragC3 a && cfragC3 b
  | _, .boolNot a => cfragC3 a
  | _, .boolBinary _ a b => cfragC3 a && cfragC3 b
  | _, _ => false

/-- **The fuel induction at world level over `cfragC3`** (the text of
`fuel_contractWC2` with the `boolBinary` case of the built
`fuel_contract_leaves`). -/
theorem fuel_contractWC3 (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    (mF : Std.HashMap Lean.Name Res) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (vE j) (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → cfragC3 e = true →
      ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
        (quote dom bE vE e) (pack s (eval bools bits e)) := by
  induction fuel with
  | zero =>
    intro s e _ _
    exact ContractW.zero
  | succ fuel ih =>
    intro s e he hf
    change ContractW L mF D (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel)) _ _ _ _ _ _ _
    cases e with
    | boolInput j => exact hbC j he (fuel + 1)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact hvC j hj (fuel + 1)
    | boolLit b =>
      exact ContractW.ofContract (rec := translateStepWith (translateFallback tenv)
        (translateFuelFix (translateStep tenv) fuel)) (bool_literal_contract b)
    | bitsLit w v =>
      obtain ⟨hval, hpos⟩ := he
      exact ContractW.ofContract (rec := translateStepWith (translateFallback tenv)
        (translateFuelFix (translateStep tenv) fuel)) (bits_literal_contract hpos hval)
    | bitsNum w v =>
      obtain ⟨hval, hpos⟩ := he
      exact ContractW.ofContract (rec := translateStepWith (translateFallback tenv)
        (translateFuelFix (translateStep tenv) fuel)) (num_literal_contract hpos hval)
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC3, Bool.and_eq_true] at hf
      have hn : 0 < w := a.wf_pos ha
      have ck := op_checks op dom (quote dom bE vE a) (quote dom bE vE b) w
      have ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems
          initial
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 2]!)
          (.bits w (eval bools bits a)) := by
        rw [ck.2.2.2.2.1]; exact ih a ha hf.1
      have cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems
          initial
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 1]!)
          (.bits w (eval bools bits b)) := by
        rw [ck.2.2.2.2.2.1]; exact ih b hb' hf.2
      exact binary_contractW L hD fuel op _ _ hn ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1
        (meaning_quote_leaves hb hv (.binary op a b) ⟨ha, hb'⟩) ca cb
    | compare op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC3, Bool.and_eq_true] at hf
      exact compare_contractW L hD fuel _ _ (a.wf_pos ha)
        (meaning_quote_leaves hb hv (.compare op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | boolNot a =>
      simp only [cfragC3] at hf
      exact boolNot_contractW L hD fuel _ (meaning_quote_leaves hb hv (.boolNot a) he)
        (ih a he hf) (ih (.boolLit false) trivial rfl)
    | boolBinary op a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC3, Bool.and_eq_true] at hf
      exact boolBin_contractW L hD fuel op _ _
        (meaning_quote_leaves hb hv (.boolBinary op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | _ => simp [cfragC3] at hf

end generic

end Tools.ShippingGateParentRun
