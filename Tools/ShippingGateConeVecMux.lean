import Tools.ShippingGateConeMux

variable {tenv : Lean.Environment}

/-! # The bit-vector mux node of the cone at world level (worker N, round 7)

WRITTEN, NOT BUILT.

A canonical bit-vector mux `muxE dom (bitVecE n) c a b` is routed by the step
to the validated-cache wrapper around `translateVectorMuxUncachedWith rec n`
(`vector_step`), which on the node IS `translateMuxWith rec (pure (.bitVector n))`
(`vectorMuxUncached_muxE`); `muxPure_missW` gives the miss.

* `vecMux_freshAt`: the text of the built `vector_shape` / `vector_fresh` over
  `ChildAt`s.
* **`vecMux_contractW`** (through `cachedW_contract`).
* `cfragC6` (NEW; earlier fragments unchanged) = `cfragC5` with `mux` at
  every sort, **`fuel_contractWC6`**. -/
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

/-- **The bit-vector mux lowering over `ChildAt`s** (the text of the built
`vector_shape` / `vector_fresh`, with the operand facts of ONE run each). -/
theorem vecMux_freshAt {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {s sc sa sb t : CircuitState} {cw aw bw w hint : String}
    {named : Bool} {n : Nat}
    (c : Bool) (a b : BitVec n) (hn : 0 < n)
    (cc : ChildAt ctx inputs we mems initial s sc cw (.bool c))
    (ca : ChildAt ctx inputs we mems initial sc sa aw (.bits n a))
    (cb : ChildAt ctx inputs we mems initial sa sb bw (.bits n b))
    (re : Tools.ShippingTranslateSoundness.Returns
      (emitMuxResult cw aw bw hint named (.bitVector n)) ctx sb w t) :
    (Lookup ctx inputs s → Frame s t ∧ s.usedNames.contains w = false) ∧
    (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
      Outcome ctx inputs we mems initial prior s t w (.bits n (if c then a else b))) := by
  refine ⟨fun lookup => ?_, fun prior h widths => ?_⟩
  · have fc := cc.frame lookup
    have fa := ca.frame (lookup.transfer fc)
    have fb := cb.frame ((lookup.transfer fc).transfer fa)
    obtain ⟨fe, fresh⟩ := Tools.ShippingVectorMuxRecursion.emit_vector_frame re
    refine ⟨((fc.trans fa).trans fb).trans fe, ?_⟩
    cases hu : s.usedNames.contains w
    · rfl
    · have := fb.used w (fa.used w (fc.used w hu)); simp [fresh] at this
  · have lookup := Lookup.ofInputs h.inputs
    have fc := cc.frame lookup
    have fa := ca.frame (lookup.transfer fc)
    have fb := cb.frame ((lookup.transfer fc).transfer fa)
    have fe := (Tools.ShippingVectorMuxRecursion.emit_vector_frame re).1
    have cout := cc.sem prior h (((fa.decls.trans fb.decls).trans fe.decls).widths widths)
    obtain ⟨vc', ic, cv, cf⟩ := cout.execution
    have aout := ca.sem vc' ic ((fb.decls.trans fe.decls).widths widths)
    obtain ⟨va', ia, av, af⟩ := aout.execution
    have bout := cb.sem va' ia (fe.decls.widths widths)
    obtain ⟨vb', ib, bv, bf⟩ := bout.execution
    have cv' : vb' cw = encodeBool c :=
      (bf cw (fa.used cw cout.used)).trans ((af cw cout.used).trans cv)
    have av' : vb' aw = a.toNat := (bf aw aout.used).trans av
    have wc : we cw = 1 := cout.width
    have wa : we aw = n := aout.width
    have wb : we bw = n := bout.width
    have step := emit_vector_outcome (x := if c then a else b) ib
      (.mux (wc ▸ TypedExpr.ref (we := we) cw (by rw [wc]; decide))
        (wa ▸ TypedExpr.ref (we := we) aw (by rw [wa]; exact hn))
        (wb ▸ TypedExpr.ref (we := we) bw (by rw [wb]; exact hn)))
      (by cases c <;> simp [evalExpr, evalList, evalOp, cv', av', bv, encodeBool]) widths re
    obtain ⟨result, inv, val, frame⟩ := step.execution
    have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
      fun z hz => fb.used z (fa.used z (fc.used z hz))
    exact ⟨step.used, step.width, fun z hz => step.grows z (mono z hz), result, inv, val,
      fun z hz => (frame z (mono z hz)).trans ((bf z (fa.used z (fc.used z hz))).trans
        ((af z (fc.used z hz)).trans (cf z hz)))⟩

/-- **The world-indexed contract of a canonical bit-vector mux**, from those
of its three operands. The step routes it to the validated-cache wrapper
around `translateVectorMuxUncachedWith` (`vector_step`), which IS
`translateMuxWith rec (pure (.bitVector n))` on the node
(`vectorMuxUncached_muxE`). -/
theorem vecMux_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom ce ae be : Lean.Expr} {n : Nat}
    (c : Bool) (a b : BitVec n) (hn : 0 < n)
    (meaning : Meaning inputs (muxE dom (bitVecE n) ce ae be) (.bits n (if c then a else b)))
    (cc : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ce (.bool c))
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae (.bits n a))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      be (.bits n b)) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      (muxE dom (bitVecE n) ce ae be) (.bits n (if c then a else b)) := by
  refine cachedW_contract (tenv := tenv) L fuel
    (lower := translateVectorMuxUncachedWith (translateFuelFix (translateStep tenv) fuel) n)
    meaning (fun hint top named =>
      Tools.ShippingVectorMuxRecursion.vector_step (tenv := tenv)
        (translateFuelFix (translateStep tenv) fuel) dom ce ae be n hint top named) ?_
  intro mctx cctx hint top named s sm w wa wb hwa hda miss
  rw [Tools.ShippingVectorMuxRecursion.vectorMuxUncached_muxE] at miss
  obtain ⟨hwb, hdb, facts⟩ := muxPure_missW (tenv := tenv) L hD fuel cc ca cb hwa hda miss
  refine ⟨hwb, hdb, fun hsub => ?_⟩
  obtain ⟨cw, aw, bw, sc, sa, sb, ccAt, caAt, cbAt, reR⟩ := facts hsub
  exact vecMux_freshAt c a b hn ccAt caAt cbAt reR

/-! ## The fragment with muxes at every sort, and its fuel induction -/

/-- The cone nodes walked at world level: `cfragC5` with `mux` at EVERY sort
(Bool and bit-vector).
(Earlier fragments are unchanged.) -/
def cfragC6 : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .bitsNum _ _ => true
  | _, .binary _ a b => cfragC6 a && cfragC6 b
  | _, .compare _ a b => cfragC6 a && cfragC6 b
  | _, .boolNot a => cfragC6 a
  | _, .boolBinary _ a b => cfragC6 a && cfragC6 b
  | _, .boolEq a b => cfragC6 a && cfragC6 b
  | _, .mux c a b => cfragC6 c && (cfragC6 a && cfragC6 b)
  | _, _ => false

/-- **The fuel induction at world level over `cfragC6`** (the text of
`fuel_contractWC5` with the bit-vector `mux` case of the built
`fuel_contract_leaves`). -/
theorem fuel_contractWC6 (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    (mF : Std.HashMap Lean.Name Res) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (vE j) (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → cfragC6 e = true →
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
      simp only [cfragC6, Bool.and_eq_true] at hf
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
      simp only [cfragC6, Bool.and_eq_true] at hf
      exact compare_contractW L hD fuel _ _ (a.wf_pos ha)
        (meaning_quote_leaves hb hv (.compare op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | boolNot a =>
      simp only [cfragC6] at hf
      exact boolNot_contractW L hD fuel _ (meaning_quote_leaves hb hv (.boolNot a) he)
        (ih a he hf) (ih (.boolLit false) trivial rfl)
    | boolBinary op a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC6, Bool.and_eq_true] at hf
      exact boolBin_contractW L hD fuel op _ _
        (meaning_quote_leaves hb hv (.boolBinary op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC6, Bool.and_eq_true] at hf
      exact boolEq_contractW L hD fuel _ _
        (meaning_quote_leaves hb hv (.boolEq a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | mux c a b =>
      simp only [cfragC6, Bool.and_eq_true] at hf
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        exact boolMux_contractW L hD fuel _ _ _
          (meaning_quote_leaves hb hv (.mux c a b) ⟨hc, ha, hb'⟩)
          (ih c hc hf.1) (ih a ha hf.2.1) (ih b hb' hf.2.2)
      | bits w =>
        exact vecMux_contractW L hD fuel _ _ _ (a.wf_pos ha)
          (meaning_quote_leaves hb hv (.mux c a b) ⟨hc, ha, hb'⟩)
          (ih c hc hf.1) (ih a ha hf.2.1) (ih b hb' hf.2.2)
    | _ => simp [cfragC6] at hf

end generic

end Tools.ShippingGateParentRun
