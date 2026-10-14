import Tools.ShippingGateConeBoolBin

variable {tenv : Lean.Environment}

/-! # The Bool equality node of the cone at world level (worker N, round 7)

WRITTEN, NOT BUILT.

A canonical Bool equality `boolEqE dom a b` (`Signal.beq` at `Bool`) is
routed to the validated-cache wrapper around `translateSignalCompare .eq`
(the Bool operands at width one). `signalCompare_missW` (with the values
`BitVec.ofNat 1 (encodeBool _)`) gives the miss; `cachedW_contract` the rest.

* **`boolEq_contractW`**.
* `cfragC4` (NEW; earlier fragments unchanged) = `cfragC3` + `boolEq`,
  **`fuel_contractWC4`**. -/
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

/-- **The world-indexed contract of a canonical Bool equality**, from those of
its operands. -/
theorem boolEq_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom ae be : Lean.Expr}
    (a b : Bool)
    (meaning : Meaning inputs (boolEqE dom ae be) (.bool (a == b)))
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae (.bool a))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      be (.bool b)) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      (boolEqE dom ae be) (.bool (a == b)) := by
  refine cachedW_contract (tenv := tenv) L fuel
    (lower := translateBoolUncachedWith (translateFuelFix (translateStep tenv) fuel)
      (fun e h t n => Sparkle.Compiler.Elab.Rec.translateExprToWireImpl
        (fun e h t n => translateFuelFix (translateStep tenv) fuel e h t n) e h t n))
    meaning (fun hint top named => ?_) ?_
  · rw [Tools.ShippingMixedRecursion.boolEq_step]
    exact translateFallback_bool _ _ hint top named rfl
  · intro mctx cctx hint top named s sm w wa wb hwa hda miss
    change RunsC (translateSignalCompare (translateFuelFix (translateStep tenv) fuel) .eq ae be
      hint named) ctx s mctx mref cctx cref wa (w, sm) wb at miss
    have val : compareValue .eq (BitVec.ofNat 1 (encodeBool a)) (BitVec.ofNat 1 (encodeBool b)) =
        (a == b) := by
      cases a <;> cases b <;> rfl
    rw [← val]
    exact signalCompare_missW (tenv := tenv) (n := 1) (va := .bool a) (vb := .bool b) L hD fuel
      (BitVec.ofNat 1 (encodeBool a)) (BitVec.ofNat 1 (encodeBool b)) (by decide) (by cases a <;> rfl)
      rfl (by cases b <;> rfl) rfl ca cb hwa hda miss

/-! ## The fragment with Bool equality, and its fuel induction -/

/-- The cone nodes walked at world level: `cfragC3` plus `boolEq`.
(Earlier fragments are unchanged.) -/
def cfragC4 : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .bitsNum _ _ => true
  | _, .binary _ a b => cfragC4 a && cfragC4 b
  | _, .compare _ a b => cfragC4 a && cfragC4 b
  | _, .boolNot a => cfragC4 a
  | _, .boolBinary _ a b => cfragC4 a && cfragC4 b
  | _, .boolEq a b => cfragC4 a && cfragC4 b
  | _, _ => false

/-- **The fuel induction at world level over `cfragC4`** (the text of
`fuel_contractWC3` with the `boolEq` case of the built
`fuel_contract_leaves`). -/
theorem fuel_contractWC4 (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    (mF : Std.HashMap Lean.Name Res) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (vE j) (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → cfragC4 e = true →
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
      simp only [cfragC4, Bool.and_eq_true] at hf
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
      simp only [cfragC4, Bool.and_eq_true] at hf
      exact compare_contractW L hD fuel _ _ (a.wf_pos ha)
        (meaning_quote_leaves hb hv (.compare op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | boolNot a =>
      simp only [cfragC4] at hf
      exact boolNot_contractW L hD fuel _ (meaning_quote_leaves hb hv (.boolNot a) he)
        (ih a he hf) (ih (.boolLit false) trivial rfl)
    | boolBinary op a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC4, Bool.and_eq_true] at hf
      exact boolBin_contractW L hD fuel op _ _
        (meaning_quote_leaves hb hv (.boolBinary op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC4, Bool.and_eq_true] at hf
      exact boolEq_contractW L hD fuel _ _
        (meaning_quote_leaves hb hv (.boolEq a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | _ => simp [cfragC4] at hf

end generic

end Tools.ShippingGateParentRun
