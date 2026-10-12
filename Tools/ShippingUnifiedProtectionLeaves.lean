import Tools.ShippingUnifiedProtection

/-! # Protection and order of the quoted fragment over ARBITRARY leaves

`fuel_protects` and `fuel_orders` (`Tools/ShippingUnifiedProtection.lean`)
are stated for terms whose leaves are input binders
(`quote dom (fun j => .fvar (bi j)) (fun j => .fvar (vi j)) e`). The contract
has a leaf-generic form (`fuel_contract_leaves`); protection and order did
not, so a term over a legacy leaf (a call the inline arm lowers) had a
contract but no order statement — and the entry's output statement
(`emitLeaves_postReady_at`) needs the order.

**Proved here** (`fuel_protects_leaves`, `fuel_orders_leaves`): the same two
inductions over a term with arbitrary leaf expressions, each leaf bringing
its meaning, its contract (at every fuel and environment), its protection
and — for the order — its order, at every fuel, hint and name flag.

The proof texts are the two certified proofs, generated from them by the
substitutions: the binder leaves → `bE vE`; `meaning_quote` →
`meaning_quote_leaves`; `fuel_contract` → `fuel_contract_leaves` with the
leaves' contracts; `fuel_protects` → `fuel_protects_leaves`; the two input
cases → the leaves' hypotheses. No other step was changed.

**NOT proved here**: anything about a leaf. The legacy leaves' facts are in
`Tools/ShippingLegacySemOrder.lean`. -/
namespace Tools.ShippingUnifiedProtection
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Reorder
open Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTranslationOrder
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingScalarSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires binary_returns core_binary_returns)
open Tools.ShippingMixedRecursion (emit_bool_frame compare_step boolBin_step boolEq_step
  boolNot_step translateBoolUncachedWith_boolBin translateBoolBinary_returns)
open Tools.ShippingMixedInvariant (translateStep_fvar_returns)
open Tools.ShippingVectorMuxRecursion (emit_vector_frame vector_step vectorMuxUncached_muxE emit_vector_order)
open Tools.ShippingMixedOrderSoundness (emit_bool_order)

/-- Protection along the fuel recursion, over arbitrary leaves. -/
theorem fuel_protects_leaves (fuel : Nat) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ (fuel : Nat) (we : WEnv) (mems : MEnv) (initial : Env),
      Contract (translateFuelFix translateStep fuel) ctx inputs we mems initial
        (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ (fuel : Nat) (we : WEnv) (mems : MEnv) (initial : Env),
      Contract (translateFuelFix translateStep fuel) ctx inputs we mems initial
        (vE j) (.bits (vw j) (bits j (vw j))))
    (hbP : ∀ j, j < kb → ∀ (fuel : Nat) (hint : String) (named : Bool),
      ActionProtect (translateFuelFix translateStep fuel (bE j) hint false named) ctx inputs)
    (hvP : ∀ j, j < kv → ∀ (fuel : Nat) (hint : String) (named : Bool),
      ActionProtect (translateFuelFix translateStep fuel (vE j) hint false named) ctx inputs) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → ∀ hint named,
      ActionProtect (translateFuelFix translateStep fuel
        (quote dom bE vE e) hint false named) ctx inputs := by
  induction fuel with
  | zero =>
    intro s e he hint named s' w t p hr lookup hp
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro s e he hint named
    have fc : ∀ {s' : SType} (e' : Term s'), e'.WF kb kv vw →
        Contract (translateFuelFix translateStep fuel) ctx inputs (fun _ => 0) (fun _ _ => 0)
          (fun _ => 0) (quote dom bE vE e')
          (pack s' (eval bools bits e')) :=
      fun e' he' => fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) e' he'
    change ActionProtect (translateStepWith translateFallback
      (translateFuelFix translateStep fuel) _ hint false named) _ _
    cases e with
    | boolInput j => exact hbP j he (fuel + 1) hint named
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact hvP j hj (fuel + 1) hint named
    | boolLit b => exact bool_literal_protect b
    | bitsLit w v => exact bits_literal_protect he.1
    | bitsNum w v => exact num_literal_protect he.1
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      have ck := op_checks op dom (quote dom bE vE a)
        (quote dom bE vE b) w
      have ca : Child (translateFuelFix translateStep fuel) ctx inputs (fun _ => 0) (fun _ _ => 0) (fun _ => 0)
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 2]!)
          "op_a" (pack (.bits w) (eval bools bits a)) := by
        rw [ck.2.2.2.2.1]
        exact ((fc a ha).child "op_a")
      have cb : Child (translateFuelFix translateStep fuel) ctx inputs (fun _ => 0) (fun _ _ => 0) (fun _ => 0)
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 1]!)
          "op_b" (pack (.bits w) (eval bools bits b)) := by
        rw [ck.2.2.2.2.2.1]
        exact ((fc b hb').child "op_b")
      have pa : ActionProtect (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 2]!)
          "op_a" false false) ctx inputs := by
        rw [ck.2.2.2.2.1]
        exact ih a ha "op_a" false
      have pb : ActionProtect (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 1]!)
          "op_b" false false) ctx inputs := by
        rw [ck.2.2.2.2.2.1]
        exact ih b hb' "op_b" false
      exact binary_step_protect op ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1
        (meaning_quote_leaves hb hv (.binary op a b) ⟨ha, hb'⟩) ca cb pa pb
    | compare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (compareE le dom w (quote dom bE vE a)
          (quote dom bE vE b)) hint false named) ctx inputs
      rw [compare_step, translateFallback_bool _ _ hint false named (by cases le <;> rfl)]
      have meaning : Meaning inputs
          (compareE le dom w (quote dom bE vE a)
            (quote dom bE vE b))
          (pack .bool (eval bools bits (.compare le a b))) :=
        meaning_quote_leaves hb hv (.compare le a b) ⟨ha, hb'⟩
      apply cached_protect meaning
      show ActionProtect (translateBoolUncachedWith _ _ _ hint false named) ctx inputs
      rw [Tools.ShippingCompareLoweringSoundness.translateBoolUncachedWith_compare]
      exact compare_protect ((fc a ha).child "a")
        ((fc b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | boolBinary kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolBinE kind dom (quote dom bE vE a)
          (quote dom bE vE b)) hint false named) ctx inputs
      rw [boolBin_step, translateFallback_bool _ _ hint false named (by cases kind <;> rfl)]
      have meaning : Meaning inputs
          (boolBinE kind dom (quote dom bE vE a)
            (quote dom bE vE b))
          (pack .bool (eval bools bits (.boolBinary kind a b))) :=
        meaning_quote_leaves hb hv (.boolBinary kind a b) ⟨ha, hb'⟩
      apply cached_protect meaning
      show ActionProtect (translateBoolUncachedWith _ _ _ hint false named) ctx inputs
      rw [translateBoolUncachedWith_boolBin]
      exact boolBin_protect ((fc a ha).child "a")
        ((fc b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | appCompare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (appCompareE le dom w (quote dom bE vE a)
          (quote dom bE vE b)) hint false named) ctx inputs
      rw [appCompare_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appCompareE _ _ _ _ _)]
      have meaning : Meaning inputs
          (appCompareE le dom w (quote dom bE vE a)
            (quote dom bE vE b))
          (pack .bool (eval bools bits (.appCompare le a b))) :=
        meaning_quote_leaves hb hv (.appCompare le a b) ⟨ha, hb'⟩
      apply cached_protect meaning
      show ActionProtect (translateBoolUncachedWith _ _ _ hint false named) ctx inputs
      rw [translateBoolUncachedWith_appCompare]
      exact appCompare_protect ((fc a ha).child "app_arg")
        ((fc b hb').child "app_arg")
        (ih a ha "app_arg" false) (ih b hb' "app_arg" false)
    | appBool kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (appBoolE kind dom (quote dom bE vE a)
          (quote dom bE vE b)) hint false named) ctx inputs
      rw [appBool_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appBoolE _ _ _ _)]
      have meaning : Meaning inputs
          (appBoolE kind dom (quote dom bE vE a)
            (quote dom bE vE b))
          (pack .bool (eval bools bits (.appBool kind a b))) :=
        meaning_quote_leaves hb hv (.appBool kind a b) ⟨ha, hb'⟩
      apply cached_protect meaning
      show ActionProtect (translateBoolUncachedWith _ _ _ hint false named) ctx inputs
      rw [translateBoolUncachedWith_appBool]
      exact appBool_protect ((fc a ha).child "app_arg")
        ((fc b hb').child "app_arg")
        (ih a ha "app_arg" false) (ih b hb' "app_arg" false)
    | appBool2 f a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (appBool2E f dom (quote dom bE vE a)
          (quote dom bE vE b)) hint false named) ctx inputs
      rw [appBool2_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appBool2E _ _ _ _)]
      have meaning : Meaning inputs
          (appBool2E f dom (quote dom bE vE a)
            (quote dom bE vE b))
          (pack .bool (eval bools bits (.appBool2 f a b))) :=
        meaning_quote_leaves hb hv (.appBool2 f a b) ⟨ha, hb'⟩
      apply cached_protect meaning
      show ActionProtect (translateBoolUncachedWith _ _ _ hint false named) ctx inputs
      rw [translateBoolUncachedWith_appBool2]
      exact appBool2_protect ((fc a ha).child "app_arg")
        ((fc b hb').child "app_arg")
        (ih a ha "app_arg" false) (ih b hb' "app_arg" false)
    | boolNot a =>
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolNotE dom (quote dom bE vE a))
        hint false named) ctx inputs
      rw [boolNot_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_protect (meaning_quote_leaves hb hv (.boolNot a) he)
      show ActionProtect (translateSignalCompare (translateFuelFix translateStep fuel) .eq
        (quote dom bE vE a)
        (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
          (.const ``Bool.false [])) hint named) ctx inputs
      exact compare_protect ((fc a he).child "a")
        ((fc (.boolLit false) trivial).child "b")
        (ih a he "a" false) (ih (.boolLit false) trivial "b" false)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolEqE dom (quote dom bE vE a)
          (quote dom bE vE b)) hint false named) ctx inputs
      rw [boolEq_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_protect (meaning_quote_leaves hb hv (.boolEq a b) ⟨ha, hb'⟩)
      show ActionProtect (translateSignalCompare (translateFuelFix translateStep fuel) .eq
        (quote dom bE vE a)
        (quote dom bE vE b) hint named) ctx inputs
      exact compare_protect ((fc a ha).child "a")
        ((fc b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        show ActionProtect (translateStepWith translateFallback
          (translateFuelFix translateStep fuel)
          (boolMuxE dom (quote dom bE vE c)
            (quote dom bE vE a)
            (quote dom bE vE b)) hint false named) ctx inputs
        rw [boolMux_step, translateFallback_bool _ _ hint false named rfl]
        apply cached_protect (meaning_quote_leaves hb hv (.mux c a b) ⟨hc, ha, hb'⟩)
        show ActionProtect (translateMuxWith (translateFuelFix translateStep fuel) (pure .bit)
          _ _ _ hint named) ctx inputs
        exact muxWith_protect _ rfl ((fc c hc).child "mux_cond")
          ((fc a ha).child "mux_then")
          ((fc b hb').child "mux_else")
          (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)
      | bits w =>
        show ActionProtect (translateStepWith translateFallback
          (translateFuelFix translateStep fuel)
          (muxE dom (bitVecE w) (quote dom bE vE c)
            (quote dom bE vE a)
            (quote dom bE vE b)) hint false named) ctx inputs
        rw [vector_step]
        have meaning : Meaning inputs
            (muxE dom (bitVecE w) (quote dom bE vE c)
              (quote dom bE vE a)
              (quote dom bE vE b))
            (pack (.bits w) (eval bools bits (.mux c a b))) :=
          meaning_quote_leaves hb hv (.mux c a b) ⟨hc, ha, hb'⟩
        apply cached_protect meaning
        show ActionProtect (translateVectorMuxUncachedWith (translateFuelFix translateStep fuel) w
          (muxE dom (bitVecE w) (quote dom bE vE c)
            (quote dom bE vE a)
            (quote dom bE vE b)) hint false named) ctx inputs
        rw [vectorMuxUncached_muxE]
        exact muxWith_protect _ rfl ((fc c hc).child "mux_cond")
          ((fc a ha).child "mux_then")
          ((fc b hb').child "mux_else")
          (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)
    | setw w' a =>
      rename_i w
      obtain ⟨ha, hpos⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (setwE dom w w' (quote dom bE vE a))
        hint false named) ctx inputs
      rw [setw_step _ _ _ _ _ (a.wf_pos ha) hpos]
      apply cached_protect (meaning_quote_leaves hb hv (.setw w' a) ⟨ha, hpos⟩)
      show ActionProtect (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) w w'
        (setwE dom w w' (quote dom bE vE a))
        hint false named) ctx inputs
      rw [setwUncached_setwE]
      exact setw_protect ((fc a ha).child "s") (ih a ha "s" false)
    | slice nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (sliceE dom nm w start len (quote dom bE vE a))
        hint false named) ctx inputs
      rw [slice_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply cached_protect (meaning_quote_leaves hb hv (.slice nm start len a) ⟨ha, hlen, hr⟩)
      show ActionProtect (translateSliceUncachedWith (translateFuelFix translateStep fuel)
        start len
        (sliceE dom nm w start len (quote dom bE vE a))
        hint false named) ctx inputs
      rw [sliceUncached_sliceE]
      exact slice_protect ((fc a ha).child "s") (ih a ha "s" false)
    | concat a b =>
      rename_i m n
      have hab := he
      obtain ⟨ha, hb'⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (concatE dom m n (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs
      rw [concat_step _ _ _ _ _ _ _ _ _ (a.wf_pos ha) (b.wf_pos hb')]
      apply cached_protect (meaning_quote_leaves hb hv (.concat a b) hab)
      show ActionProtect (translateConcatUncachedWith (translateFuelFix translateStep fuel) m n
        (concatE dom m n (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs
      rw [concatUncached_concatE]
      exact concat_protect ((fc a ha).child "concat_hi").action
        ((fc b hb').child "concat_lo").action
        (ih a ha "concat_hi" false) (ih b hb' "concat_lo" false)
    | concatLitHi k v b =>
      rename_i n
      have hall := he
      obtain ⟨hb', hk, hlt⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (concatLitHiE dom k v n (quote dom bE vE b))
        hint false named) ctx inputs
      rw [concatLitHi_step _ _ _ _ _ _ _ _ _ hk hlt (b.wf_pos hb')]
      apply cached_protect (meaning_quote_leaves hb hv (.concatLitHi k v b) hall)
      show ActionProtect (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        true k v n (concatLitHiE dom k v n (quote dom bE vE b))
        hint false named) ctx inputs
      rw [concatLitUncached_hiE]
      exact concat_protect (concatConst_spec hk hlt) ((fc b hb').child "concat_lo").action
        concatConst_protect (ih b hb' "concat_lo" false)
    | concatLitLo a k v =>
      rename_i m
      have hall := he
      obtain ⟨ha, hk, hlt⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (concatLitLoE dom m k v (quote dom bE vE a))
        hint false named) ctx inputs
      rw [concatLitLo_step _ _ _ _ _ _ _ _ _ hk hlt (a.wf_pos ha)]
      apply cached_protect (meaning_quote_leaves hb hv (.concatLitLo a k v) hall)
      show ActionProtect (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        false k v m (concatLitLoE dom m k v (quote dom bE vE a))
        hint false named) ctx inputs
      rw [concatLitUncached_loE]
      exact concat_protect ((fc a ha).child "concat_hi").action (concatConst_spec hk hlt)
        (ih a ha "concat_hi" false) concatConst_protect
    | zextMap nm k a =>
      rename_i n
      have hall := he
      obtain ⟨ha, hk⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (zextMapE dom nm k n (quote dom bE vE a))
        hint false named) ctx inputs
      rw [zextMap_step _ _ _ _ _ _ _ _ _ hk (a.wf_pos ha)]
      apply cached_protect (meaning_quote_leaves hb hv (.zextMap nm k a) hall)
      show ActionProtect (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) n
        (k + n) (zextMapE dom nm k n (quote dom bE vE a))
        hint false named) ctx inputs
      rw [setwUncached_zextMapE]
      exact setw_protect ((fc a ha).child "s") (ih a ha "s" false)
    | sliceF nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      show ActionProtect (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (sliceFE dom nm w start len (quote dom bE vE a))
        hint false named) ctx inputs
      rw [sliceF_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply cached_protect (meaning_quote_leaves hb hv (.sliceF nm start len a) ⟨ha, hlen, hr⟩)
      show ActionProtect (translateSliceFUncachedWith (translateFuelFix translateStep fuel)
        start len (sliceFE dom nm w start len (quote dom bE vE a))
        hint false named) ctx inputs
      rw [sliceFUncached_sliceFE]
      exact slice_protect ((fc a ha).child "a") (ih a ha "a" false)

/-- Order along the fuel recursion, over arbitrary leaves. -/
theorem fuel_orders_leaves (fuel : Nat) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ (fuel : Nat) (we : WEnv) (mems : MEnv) (initial : Env),
      Contract (translateFuelFix translateStep fuel) ctx inputs we mems initial
        (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ (fuel : Nat) (we : WEnv) (mems : MEnv) (initial : Env),
      Contract (translateFuelFix translateStep fuel) ctx inputs we mems initial
        (vE j) (.bits (vw j) (bits j (vw j))))
    (hbP : ∀ j, j < kb → ∀ (fuel : Nat) (hint : String) (named : Bool),
      ActionProtect (translateFuelFix translateStep fuel (bE j) hint false named) ctx inputs)
    (hvP : ∀ j, j < kv → ∀ (fuel : Nat) (hint : String) (named : Bool),
      ActionProtect (translateFuelFix translateStep fuel (vE j) hint false named) ctx inputs)
    (hbO : ∀ j, j < kb → ∀ (fuel : Nat) (hint : String) (named : Bool),
      ActionOrder (translateFuelFix translateStep fuel (bE j) hint false named)
        ctx inputs we mems initial)
    (hvO : ∀ j, j < kv → ∀ (fuel : Nat) (hint : String) (named : Bool),
      ActionOrder (translateFuelFix translateStep fuel (vE j) hint false named)
        ctx inputs we mems initial) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → ∀ hint named,
      ActionOrder (translateFuelFix translateStep fuel
        (quote dom bE vE e) hint false named)
        ctx inputs we mems initial := by
  induction fuel with
  | zero =>
    intro s e he hint named s' t w prior hr h widths order
    exact (Returns.throw hr).elim
  | succ fuel ih =>
    intro s e he hint named
    change ActionOrder (translateStepWith translateFallback
      (translateFuelFix translateStep fuel) _ hint false named) _ _ _ _ _
    cases e with
    | boolInput j => exact hbO j he (fuel + 1) hint named
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact hvO j hj (fuel + 1) hint named
    | boolLit b => exact bool_literal_order b
    | bitsLit w v => exact bits_literal_order he.1
    | bitsNum w v => exact num_literal_order he.1
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      have ck := op_checks op dom (quote dom bE vE a)
        (quote dom bE vE b) w
      have ca : Child (translateFuelFix translateStep fuel) ctx inputs we mems initial
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 2]!)
          "op_a" (.bits w (eval bools bits a)) := by
        rw [ck.2.2.2.2.1]
        exact ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "op_a")
      have cb : Child (translateFuelFix translateStep fuel) ctx inputs we mems initial
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 1]!)
          "op_b" (.bits w (eval bools bits b)) := by
        rw [ck.2.2.2.2.2.1]
        exact ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "op_b")
      have pa : ActionProtect (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 2]!)
          "op_a" false false) ctx inputs := by
        rw [ck.2.2.2.2.1]
        exact fuel_protects_leaves fuel hb hv hbC hvC hbP hvP a ha "op_a" false
      have pb : ActionProtect (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 1]!)
          "op_b" false false) ctx inputs := by
        rw [ck.2.2.2.2.2.1]
        exact fuel_protects_leaves fuel hb hv hbC hvC hbP hvP b hb' "op_b" false
      have oa : ActionOrder (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 2]!)
          "op_a" false false) ctx inputs we mems initial := by
        rw [ck.2.2.2.2.1]
        exact ih a ha "op_a" false
      have ob : ActionOrder (translateFuelFix translateStep fuel
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 1]!)
          "op_b" false false) ctx inputs we mems initial := by
        rw [ck.2.2.2.2.2.1]
        exact ih b hb' "op_b" false
      exact binary_step_order op ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1 ca cb pa pb oa ob
    | compare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (compareE le dom w (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [compare_step, translateFallback_bool _ _ hint false named (by cases le <;> rfl)]
      apply cached_order
      show ActionOrder (translateBoolUncachedWith _ _ _ hint false named) _ _ _ _ _
      rw [Tools.ShippingCompareLoweringSoundness.translateBoolUncachedWith_compare]
      exact compare_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "a")
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | boolBinary kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolBinE kind dom (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [boolBin_step, translateFallback_bool _ _ hint false named (by cases kind <;> rfl)]
      apply cached_order
      show ActionOrder (translateBoolUncachedWith _ _ _ hint false named) _ _ _ _ _
      rw [translateBoolUncachedWith_boolBin]
      exact boolBin_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "a")
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | appCompare le a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (appCompareE le dom w (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [appCompare_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appCompareE _ _ _ _ _)]
      apply cached_order
      show ActionOrder (translateBoolUncachedWith _ _ _ hint false named) _ _ _ _ _
      rw [translateBoolUncachedWith_appCompare]
      exact appCompare_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "app_arg")
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "app_arg")
        (ih a ha "app_arg" false) (ih b hb' "app_arg" false)
    | appBool kind a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (appBoolE kind dom (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [appBool_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appBoolE _ _ _ _)]
      apply cached_order
      show ActionOrder (translateBoolUncachedWith _ _ _ hint false named) _ _ _ _ _
      rw [translateBoolUncachedWith_appBool]
      exact appBool_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "app_arg")
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "app_arg")
        (ih a ha "app_arg" false) (ih b hb' "app_arg" false)
    | appBool2 f a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (appBool2E f dom (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [appBool2_step, translateFallback_bool _ _ hint false named
        (isBoolControl_appBool2E _ _ _ _)]
      apply cached_order
      show ActionOrder (translateBoolUncachedWith _ _ _ hint false named) _ _ _ _ _
      rw [translateBoolUncachedWith_appBool2]
      exact appBool2_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "app_arg")
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "app_arg")
        (ih a ha "app_arg" false) (ih b hb' "app_arg" false)
    | boolNot a =>
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolNotE dom (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [boolNot_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_order
      show ActionOrder (translateSignalCompare (translateFuelFix translateStep fuel) .eq
        (quote dom bE vE a)
        (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
          (.const ``Bool.false [])) hint named) _ _ _ _ _
      exact compare_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a he).child "a")
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) (.boolLit false) trivial).child "b")
        (ih a he "a" false) (ih (.boolLit false) trivial "b" false)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (boolEqE dom (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [boolEq_step, translateFallback_bool _ _ hint false named rfl]
      apply cached_order
      show ActionOrder (translateSignalCompare (translateFuelFix translateStep fuel) .eq
        (quote dom bE vE a)
        (quote dom bE vE b) hint named) _ _ _ _ _
      exact compare_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "a")
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "b")
        (ih a ha "a" false) (ih b hb' "b" false)
    | mux c a b =>
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        show ActionOrder (translateStepWith translateFallback
          (translateFuelFix translateStep fuel)
          (boolMuxE dom (quote dom bE vE c)
            (quote dom bE vE a)
            (quote dom bE vE b))
          hint false named) ctx inputs we mems initial
        rw [boolMux_step, translateFallback_bool _ _ hint false named rfl]
        apply cached_order
        show ActionOrder (translateMuxWith (translateFuelFix translateStep fuel) (pure .bit)
          _ _ _ hint named) _ _ _ _ _
        exact mux_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) c hc).child "mux_cond")
          ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "mux_then")
          ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "mux_else")
          (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)
      | bits w =>
        show ActionOrder (translateStepWith translateFallback
          (translateFuelFix translateStep fuel)
          (muxE dom (bitVecE w) (quote dom bE vE c)
            (quote dom bE vE a)
            (quote dom bE vE b))
          hint false named) ctx inputs we mems initial
        rw [vector_step]
        apply cached_order
        show ActionOrder (translateVectorMuxUncachedWith (translateFuelFix translateStep fuel) w
          (muxE dom (bitVecE w) (quote dom bE vE c)
            (quote dom bE vE a)
            (quote dom bE vE b)) hint false named)
          ctx inputs we mems initial
        rw [vectorMuxUncached_muxE]
        exact vector_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) c hc).child "mux_cond")
          ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "mux_then")
          ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "mux_else")
          (ih c hc "mux_cond" false) (ih a ha "mux_then" false) (ih b hb' "mux_else" false)
    | setw w' a =>
      rename_i w
      obtain ⟨ha, hpos⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (setwE dom w w' (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [setw_step _ _ _ _ _ (a.wf_pos ha) hpos]
      apply cached_order
      show ActionOrder (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) w w'
        (setwE dom w w' (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [setwUncached_setwE]
      exact setw_order hpos ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "s") (ih a ha "s" false)
    | slice nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (sliceE dom nm w start len (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [slice_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply cached_order
      show ActionOrder (translateSliceUncachedWith (translateFuelFix translateStep fuel)
        start len
        (sliceE dom nm w start len (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [sliceUncached_sliceE]
      exact slice_order hlen ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "s") (ih a ha "s" false)
    | concat a b =>
      rename_i m n
      obtain ⟨ha, hb'⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (concatE dom m n (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [concat_step _ _ _ _ _ _ _ _ _ (a.wf_pos ha) (b.wf_pos hb')]
      apply cached_order
      show ActionOrder (translateConcatUncachedWith (translateFuelFix translateStep fuel) m n
        (concatE dom m n (quote dom bE vE a)
          (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [concatUncached_concatE]
      exact concat_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "concat_hi").action
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "concat_lo").action
        (fuel_protects_leaves fuel hb hv hbC hvC hbP hvP a ha "concat_hi" false)
        (fuel_protects_leaves fuel hb hv hbC hvC hbP hvP b hb' "concat_lo" false)
        (ih a ha "concat_hi" false) (ih b hb' "concat_lo" false)
    | concatLitHi k v b =>
      rename_i n
      obtain ⟨hb', hk, hlt⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (concatLitHiE dom k v n (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [concatLitHi_step _ _ _ _ _ _ _ _ _ hk hlt (b.wf_pos hb')]
      apply cached_order
      show ActionOrder (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        true k v n (concatLitHiE dom k v n (quote dom bE vE b))
        hint false named) ctx inputs we mems initial
      rw [concatLitUncached_hiE]
      exact concat_order (concatConst_spec hk hlt)
        ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) b hb').child "concat_lo").action
        concatConst_protect (fuel_protects_leaves fuel hb hv hbC hvC hbP hvP b hb' "concat_lo" false)
        concatConst_order (ih b hb' "concat_lo" false)
    | concatLitLo a k v =>
      rename_i m
      obtain ⟨ha, hk, hlt⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (concatLitLoE dom m k v (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [concatLitLo_step _ _ _ _ _ _ _ _ _ hk hlt (a.wf_pos ha)]
      apply cached_order
      show ActionOrder (translateConcatLitUncachedWith (translateFuelFix translateStep fuel)
        false k v m (concatLitLoE dom m k v (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [concatLitUncached_loE]
      exact concat_order ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "concat_hi").action
        (concatConst_spec hk hlt)
        (fuel_protects_leaves fuel hb hv hbC hvC hbP hvP a ha "concat_hi" false) concatConst_protect
        (ih a ha "concat_hi" false) concatConst_order
    | zextMap nm k a =>
      rename_i n
      obtain ⟨ha, hk⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (zextMapE dom nm k n (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [zextMap_step _ _ _ _ _ _ _ _ _ hk (a.wf_pos ha)]
      apply cached_order
      show ActionOrder (translateSetWidthUncachedWith (translateFuelFix translateStep fuel) n
        (k + n) (zextMapE dom nm k n (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [setwUncached_zextMapE]
      exact setw_order (by omega) ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "s") (ih a ha "s" false)
    | sliceF nm start len a =>
      rename_i w
      obtain ⟨ha, hlen, hr⟩ := he
      show ActionOrder (translateStepWith translateFallback
        (translateFuelFix translateStep fuel)
        (sliceFE dom nm w start len (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [sliceF_step _ _ _ _ _ _ _ _ _ _ hlen hr]
      apply cached_order
      show ActionOrder (translateSliceFUncachedWith (translateFuelFix translateStep fuel)
        start len (sliceFE dom nm w start len (quote dom bE vE a))
        hint false named) ctx inputs we mems initial
      rw [sliceFUncached_sliceFE]
      exact slice_order hlen ((fuel_contract_leaves fuel hb hv (fun j hj f => hbC j hj f _ _ _) (fun j hj f => hvC j hj f _ _ _) a ha).child "a") (ih a ha "a" false)

end Tools.ShippingUnifiedProtection
