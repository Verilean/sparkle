import Tools.ShippingGateConeW

variable {tenv : Lean.Environment}

/-! # The comparison node of the cone at world level (worker N, round 6)

WRITTEN, NOT BUILT.

`binary_contractW` (round 3) walks a canonical binary node with its worlds.
Here the same for a canonical comparison `compareE le dom n a b`
(`Signal.ult` / `ule` / `slt` / `sle` / `beq` at `BitVec n`), whose route is
NOT the core: the step hands it to the fallback's Bool arm
(`compare_step`, `translateFallback_bool`), i.e. the validated-cache wrapper
`translateControlCachedWith` around `translateSignalCompare` (both operands,
then one Bool wire and its assign).

* `controlCached_runsW`: the wrapper, world by world — a validated hit, or the
  lowering from an invariant world at the same depth followed by the record.
* `compare_freshAt`: the text of the built `compare_shape` / `compare_fresh`
  over the operand runs' own facts (`ChildAt`).
* **`compare_contractW`**: the world-indexed contract of a comparison node from
  those of its operands.
* `cfragC` (a NEW fragment; `cfrag` and every statement over it are
  unchanged): `cfrag` plus `compare`. **`fuel_contractWC`**: the fuel
  induction of `fuel_contractW` over `cfragC`.

The cone result `HierConePreservesK` (over `cfrag`) is NOT restated over
`cfragC` here. -/
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

/-! ## The validated-cache wrapper, world by world -/

/-- **`translateControlCachedWith`, with its worlds** (the decomposition of
the built `translateControlCachedWith_returns`): a validated hit, or the
lowering from an invariant world at depth `D` and then the record. -/
theorem controlCached_runsW (L : RefLaws mref cref) {D : Nat} {lower : TranslateFn}
    {e : Lean.Expr} {hint : String} {top named : Bool} {ctx : CompilerState}
    {s t : CircuitState} {w : String} {w0 w1 : Void IO.RealWorld}
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D)
    (h : RunsC (translateControlCachedWith lower e hint top named) ctx s
      mctx mref cctx cref w0 (w, t) w1) :
    Tools.ShippingTranslateSoundness.Returns (cacheLookupValidated e) ctx s (some w) t ∨
      ∃ (sm : CircuitState) (wa wb : Void IO.RealWorld), InvV L wa ∧ L.dval wa = D ∧
        RunsC (lower e hint top named) ctx s mctx mref cctx cref wa (w, sm) wb ∧
        RunsC (recordTranslation e w (!named && !e.isFVar && !top)) ctx sm
          mctx mref cctx cref wb ((), t) w1 := by
  unfold translateControlCachedWith at h
  dsimp only at h
  split at h
  · obtain ⟨hit, sh, wh, hc, h2⟩ := RunsC.bind h
    have hs := (cacheLookupValidated_returns (runsCReturns hc)).1
    obtain ⟨hwh, hdh, -⟩ := keepsW L (fun L' => cacheLookupValidated_keepsC L' D e) hw0 hd0 hc
    subst hs
    split at h2
    · obtain ⟨hp, -⟩ := RunsC.pure h2
      obtain ⟨hw', ht'⟩ := Prod.mk.inj hp
      subst hw' ht'
      exact Or.inl (runsCReturns hc)
    · obtain ⟨r, sm, wa', hl, h3⟩ := RunsC.bind h2
      obtain ⟨u, sr, wr, hrec, h4⟩ := RunsC.bind h3
      obtain ⟨hp, hw1⟩ := RunsC.pure h4
      obtain ⟨hw', ht'⟩ := Prod.mk.inj hp
      subst hw' ht' hw1
      cases u
      exact Or.inr ⟨sm, wh, wa', hwh, hdh, hl, hrec⟩
  · obtain ⟨r, sm, wa', hl, h3⟩ := RunsC.bind h
    obtain ⟨u, sr, wr, hrec, h4⟩ := RunsC.bind h3
    obtain ⟨hp, hw1⟩ := RunsC.pure h4
    obtain ⟨hw', ht'⟩ := Prod.mk.inj hp
    subst hw' ht' hw1
    cases u
    exact Or.inr ⟨sm, w0, wa', hw0, hd0, hl, hrec⟩

section generic
variable [LinkCtx] [ChildSem]

/-! ## The comparison lowering over the operand runs' own facts -/

/-- **The comparison lowering over `ChildAt`s** (the text of the built
`compare_shape` / `compare_fresh`, with the operand facts of ONE run each). -/
theorem compare_freshAt {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {s sa sb t : CircuitState} {a b w hint : String}
    {named : Bool} {le : SignalCompareKind} {n : Nat} {va vb : Value}
    (x y : BitVec n) (hn : 0 < n)
    (hva : va.toNat = x.toNat) (hwa : va.kind.width = n)
    (hvb : vb.toNat = y.toNat) (hwb : vb.kind.width = n)
    (ca : ChildAt ctx inputs we mems initial s sa a va)
    (cb : ChildAt ctx inputs we mems initial sa sb b vb)
    (re : Tools.ShippingTranslateSoundness.Returns (emitCompareResult le a b hint named)
      ctx sb w t) :
    (Lookup ctx inputs s → Frame s t ∧ s.usedNames.contains w = false) ∧
    (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
      Outcome ctx inputs we mems initial prior s t w (.bool (compareValue le x y))) := by
  refine ⟨fun lookup => ?_, fun prior h widths => ?_⟩
  · have fa := ca.frame lookup
    have fb := cb.frame (lookup.transfer fa)
    obtain ⟨fe, fresh⟩ := Tools.ShippingMixedRecursion.emit_bool_frame (by cases le <;> rfl) re
    refine ⟨(fa.trans fb).trans fe, ?_⟩
    cases hu : s.usedNames.contains w
    · rfl
    · have := fb.used w (fa.used w hu); simp [fresh] at this
  · have fa := ca.frame (Lookup.ofInputs h.inputs)
    have fb := cb.frame ((Lookup.ofInputs h.inputs).transfer fa)
    have fe := (Tools.ShippingMixedRecursion.emit_bool_frame (by cases le <;> rfl) re).1
    have aout := ca.sem prior h ((fb.decls.trans fe.decls).widths widths)
    obtain ⟨va', ia, av, af⟩ := aout.execution
    have bout := cb.sem va' ia (fe.decls.widths widths)
    obtain ⟨vb', ib, bv, bf⟩ := bout.execution
    have wa : we a = n := by rw [aout.width, hwa]
    have wb : we b = n := by rw [bout.width, hwb]
    have av2 : vb' a = x.toNat := by rw [(bf a aout.used).trans av, hva]
    have bv2 : vb' b = y.toNat := by rw [bv, hvb]
    have step := emit_bool_outcome ib (typed_compare_refs le hn wa wb)
      (compare_rhs_correct le x y we vb' a b av2 bv2 wa wb) widths re
    obtain ⟨result, inv, val, frame⟩ := step.execution
    exact ⟨step.used, step.width, fun z hz => step.grows z (fb.used z (fa.used z hz)),
      result, inv, val, fun z hz => (frame z (fb.used z (fa.used z hz))).trans
        ((bf z (fa.used z hz)).trans (af z hz))⟩

/-! ## The comparison node at world level -/

/-- **The world-indexed contract of a canonical comparison node**, from those
of its operands. -/
theorem compare_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom ae be : Lean.Expr} {n : Nat}
    {le : SignalCompareKind}
    (x y : BitVec n) (hn : 0 < n)
    (meaning : Meaning inputs (compareE le dom n ae be) (.bool (compareValue le x y)))
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae (.bits n x))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      be (.bits n y)) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      (compareE le dom n ae be) (.bool (compareValue le x y)) := by
  have step : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String)
      (top named : Bool) (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
      InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
      RunsC (translateFuelFix (translateStep tenv) (fuel + 1) (compareE le dom n ae be)
        hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 →
      (Lookup ctx inputs s → Frame s t) ∧
        (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
          Outcome ctx inputs we mems initial prior s t w (.bool (compareValue le x y))) := by
    intro mctx cctx hint top named s t w w0 w1 hw0 hd0 hsub hr
    change RunsC (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel) (compareE le dom n ae be) hint top named) ctx s
      mctx mref cctx cref w0 (w, t) w1 at hr
    rw [Tools.ShippingMixedRecursion.compare_step,
      translateFallback_bool (translateFuelFix (translateStep tenv) fuel)
        (compareE le dom n ae be) hint top named (by cases le <;> rfl)] at hr
    rcases controlCached_runsW L hw0 hd0 hr with hit | ⟨sm, wa, wb, hwa, hda, miss, record⟩
    · -- a validated hit: the recorded wire, the state unchanged
      have ht := (cacheLookupValidated_returns hit).1
      refine ⟨fun _ => ?_, fun prior h _ => hit_outcome h meaning hit⟩
      rw [ht]
      exact Frame.refl _
    · -- a miss: both operands, one Bool wire and its assign, the record
      rw [translateBoolUncachedWith_compare] at miss
      unfold translateSignalCompare at miss
      obtain ⟨a, sa, wa1, ra, rest⟩ := RunsC.bind miss
      obtain ⟨b, sb, wb1, rb, re⟩ := RunsC.bind rest
      obtain ⟨hwa1, hda1, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa hda ra
      obtain ⟨hwb1, hdb1, hsab⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa1 hda1 rb
      have reE : RunsC (emitBoolResult (.op (signalCompareOp le) [.ref a, .ref b]) hint named)
          ctx sb mctx mref cctx cref wb1 (w, sm) wb := re
      unfold emitBoolResult at reE
      obtain ⟨r1, s1, wq, rm, rest2⟩ := RunsC.bind reE
      obtain ⟨u, s2, wq2, rem, fin⟩ := RunsC.bind rest2
      obtain ⟨-, hwq⟩ := RunsC.pure fin
      obtain ⟨hwm, hdm, hs1⟩ :=
        keepsW L (fun L' => makeWire_keepsC L' D hint .bit named) hwb1 hdb1 rm
      obtain ⟨hwq', hdq', hs2⟩ :=
        keepsW L (fun L' => emitAssign_keepsC L' D r1 (.op (signalCompareOp le) [.ref a, .ref b]))
          hwm hdm rem
      rw [← hwq] at hwq' hdq' hs2
      obtain ⟨-, -, hsr⟩ :=
        keepsW L (fun L' => recordTranslation_keepsC L' D (compareE le dom n ae be) w
          (!named && !(compareE le dom n ae be).isFVar && !top)) hwq' hdq' record
      have subB : SubMap (L.val wb1) mF := sub_trans hs1 (sub_trans hs2 (sub_trans hsr hsub))
      have subA : SubMap (L.val wa1) mF := sub_trans hsab subB
      have caAt := ca.atRun hwa hda subA ra
      have cbAt := cb.atRun hwa1 hda1 subB rb
      have shape := compare_freshAt (le := le) x y hn rfl rfl rfl rfl caAt cbAt (runsCReturns re)
      have recordR := runsCReturns record
      refine ⟨fun lookup => ?_, fun prior h widths => ?_⟩
      · obtain ⟨fr, fresh⟩ := shape.1 lookup
        exact fr.record_new fresh recordR
      · have hs := recordTranslation_returns recordR
        have wm : ScalarWidthsAgree we sm := by
          intro p hp; apply widths p; rw [hs]; exact hp
        have st := shape.2 prior h wm
        obtain ⟨result, inv, val, frame⟩ := st.execution
        refine ⟨?_, st.width, ?_, result,
          inv.record meaning st.used val st.width recordR, val, frame⟩
        · rw [hs]; exact st.used
        · rw [hs]; exact st.grows
  exact ⟨fun mctx cctx hint top named s t w w0 w1 lookup hw hd hsub hr =>
      (step mctx cctx hint top named s t w w0 w1 hw hd hsub hr).1 lookup,
    fun mctx cctx hint top named s t w prior w0 w1 h widths hw hd hsub hr =>
      (step mctx cctx hint top named s t w w0 w1 hw hd hsub hr).2 prior h widths⟩

/-! ## The fragment with comparisons, and its fuel induction -/

/-- The cone nodes walked at world level, with comparisons: `cfrag` plus
`compare`. (`cfrag` itself is unchanged.) -/
def cfragC : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .bitsNum _ _ => true
  | _, .binary _ a b => cfragC a && cfragC b
  | _, .compare _ a b => cfragC a && cfragC b
  | _, _ => false

/-- **The fuel induction at world level over `cfragC`** (the text of
`fuel_contractW` with the comparison case of the built
`fuel_contract_leaves`). -/
theorem fuel_contractWC (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    (mF : Std.HashMap Lean.Name Res) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (vE j) (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → cfragC e = true →
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
      simp only [cfragC, Bool.and_eq_true] at hf
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
      simp only [cfragC, Bool.and_eq_true] at hf
      exact compare_contractW L hD fuel _ _ (a.wf_pos ha)
        (meaning_quote_leaves hb hv (.compare op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | _ => simp [cfragC] at hf

end generic

end Tools.ShippingGateParentRun
