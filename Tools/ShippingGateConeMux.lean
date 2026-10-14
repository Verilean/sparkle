import Tools.ShippingGateConeBoolEq

variable {tenv : Lean.Environment}

/-! # The Bool mux node of the cone at world level (worker N, round 7)

WRITTEN, NOT BUILT.

A canonical Bool mux `boolMuxE dom c a b` (`Signal.mux` at `Bool`) is routed
to the validated-cache wrapper around `translateMuxWith rec (pure .bit)`
(condition, then, else; the result type query `pure .bit`; one wire and its
`mux` assign).

* `muxPure_missW`: a run of `translateMuxWith rec (pure ty)` with its worlds,
  for ANY result type `ty` (also used by the bit-vector mux): the invariant
  and the depth are kept, and once the final cache is in `mF` the three
  operands' `ContractW`s give `ChildAt`s of their own runs and the emission is
  a `Returns` of `emitMuxResult`.
* `boolMux_freshAt`: the text of the built `mux_shape` / `mux_fresh` over
  `ChildAt`s.
* **`boolMux_contractW`** (through `cachedW_contract`).
* `stBool`, `cfragC5` (NEW; earlier fragments unchanged) = `cfragC4` + `mux`
  at sort `bool`, **`fuel_contractWC5`**. -/
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

/-- Whether a sort is `bool` (the Bool mux is in `cfragC5`, the bit-vector mux
is not). -/
def stBool : SType → Bool
  | .bool => true
  | .bits _ => false

section generic
variable [LinkCtx] [ChildSem]

/-- **A run of the mux lowering with a constant result type, with its
worlds**: the three operands, the type query `pure ty`, one wire and its
`mux` assign keep the invariant and the depth; once the final cache is in
`mF`, the operands' `ContractW`s apply to their own runs. -/
theorem muxPure_missW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {ty : Sparkle.IR.Type.HWType} {ce ae be : Lean.Expr} {vc va vb : Value}
    (cc : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ce vc)
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae va)
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      be vb)
    {hint : String} {named : Bool} {s sm : CircuitState} {w : String}
    {wa wb : Void IO.RealWorld}
    (hwa0 : InvV L wa) (hda0 : L.dval wa = D)
    (miss : RunsC (translateMuxWith (translateFuelFix (translateStep tenv) fuel) (pure ty)
      ce ae be hint named) ctx s mctx mref cctx cref wa (w, sm) wb) :
    InvV L wb ∧ L.dval wb = D ∧ (SubMap (L.val wb) mF →
      ∃ (cw aw bw : String) (sc sa sb : CircuitState),
        ChildAt ctx inputs we mems initial s sc cw vc ∧
        ChildAt ctx inputs we mems initial sc sa aw va ∧
        ChildAt ctx inputs we mems initial sa sb bw vb ∧
        Tools.ShippingTranslateSoundness.Returns (emitMuxResult cw aw bw hint named ty)
          ctx sb w sm) := by
  unfold translateMuxWith at miss
  obtain ⟨cw, sc, wc1, rc, rest⟩ := RunsC.bind miss
  obtain ⟨aw, sa, wa1, ra, rest1⟩ := RunsC.bind rest
  obtain ⟨bw, sb, wb1, rb, rest2⟩ := RunsC.bind rest1
  obtain ⟨ty', sq, wq, rq, re⟩ := RunsC.bind rest2
  obtain ⟨hq, hwq⟩ := RunsC.pure rq
  obtain ⟨hty, hsq⟩ := Prod.mk.inj hq
  rw [hty, hsq, hwq] at re
  obtain ⟨hwc1, hdc1, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa0 hda0 rc
  obtain ⟨hwa1, hda1, hsca⟩ := fuel_runsW (tenv := tenv) L hD fuel hwc1 hdc1 ra
  obtain ⟨hwb1, hdb1, hsab⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa1 hda1 rb
  have reR := runsCReturns re
  unfold emitMuxResult at re
  obtain ⟨r1, s1, wm, rm, rest3⟩ := RunsC.bind re
  obtain ⟨u, s2, wq2, rem, fin⟩ := RunsC.bind rest3
  obtain ⟨-, hwq2⟩ := RunsC.pure fin
  obtain ⟨hwm, hdm, hs1⟩ :=
    keepsW L (fun L' => makeWire_keepsC L' D hint ty named) hwb1 hdb1 rm
  obtain ⟨hwq', hdq', hs2⟩ :=
    keepsW L (fun L' => emitAssign_keepsC L' D r1 (.op .mux [.ref cw, .ref aw, .ref bw]))
      hwm hdm rem
  rw [← hwq2] at hwq' hdq' hs2
  refine ⟨hwq', hdq', fun hsub => ?_⟩
  have subB : SubMap (L.val wb1) mF := sub_trans hs1 (sub_trans hs2 hsub)
  have subA : SubMap (L.val wa1) mF := sub_trans hsab subB
  have subC : SubMap (L.val wc1) mF := sub_trans hsca subA
  exact ⟨cw, aw, bw, sc, sa, sb, cc.atRun hwa0 hda0 subC rc, ca.atRun hwc1 hdc1 subA ra,
    cb.atRun hwa1 hda1 subB rb, reR⟩

/-- **The Bool mux lowering over `ChildAt`s** (the text of the built
`mux_shape` / `mux_fresh`, with the operand facts of ONE run each). -/
theorem boolMux_freshAt {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {s sc sa sb t : CircuitState} {cw aw bw w hint : String}
    {named : Bool}
    (c a b : Bool)
    (cc : ChildAt ctx inputs we mems initial s sc cw (.bool c))
    (ca : ChildAt ctx inputs we mems initial sc sa aw (.bool a))
    (cb : ChildAt ctx inputs we mems initial sa sb bw (.bool b))
    (re : Tools.ShippingTranslateSoundness.Returns (emitMuxResult cw aw bw hint named .bit)
      ctx sb w t) :
    (Lookup ctx inputs s → Frame s t ∧ s.usedNames.contains w = false) ∧
    (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
      Outcome ctx inputs we mems initial prior s t w (.bool (if c then a else b))) := by
  refine ⟨fun lookup => ?_, fun prior h widths => ?_⟩
  · have fc := cc.frame lookup
    have fa := ca.frame (lookup.transfer fc)
    have fb := cb.frame ((lookup.transfer fc).transfer fa)
    obtain ⟨fe, fresh⟩ := Tools.ShippingMixedRecursion.emit_bool_frame rfl re
    refine ⟨((fc.trans fa).trans fb).trans fe, ?_⟩
    cases hu : s.usedNames.contains w
    · rfl
    · have := fb.used w (fa.used w (fc.used w hu)); simp [fresh] at this
  · have lookup := Lookup.ofInputs h.inputs
    have fc := cc.frame lookup
    have fa := ca.frame (lookup.transfer fc)
    have fb := cb.frame ((lookup.transfer fc).transfer fa)
    have fe := (Tools.ShippingMixedRecursion.emit_bool_frame rfl re).1
    have cout := cc.sem prior h (((fa.decls.trans fb.decls).trans fe.decls).widths widths)
    obtain ⟨vc', ic, cv, cf⟩ := cout.execution
    have aout := ca.sem vc' ic ((fb.decls.trans fe.decls).widths widths)
    obtain ⟨va', ia, av, af⟩ := aout.execution
    have bout := cb.sem va' ia (fe.decls.widths widths)
    obtain ⟨vb', ib, bv, bf⟩ := bout.execution
    have cv' : vb' cw = encodeBool c :=
      (bf cw (fa.used cw cout.used)).trans ((af cw cout.used).trans cv)
    have av' : vb' aw = encodeBool a := (bf aw aout.used).trans av
    have wc : we cw = 1 := cout.width
    have wa : we aw = 1 := aout.width
    have wb : we bw = 1 := bout.width
    have step := emit_bool_outcome ib
      (.mux (wc ▸ TypedExpr.ref (we := we) cw (by rw [wc]; decide))
        (wa ▸ TypedExpr.ref (we := we) aw (by rw [wa]; decide))
        (wb ▸ TypedExpr.ref (we := we) bw (by rw [wb]; decide)))
      (bool_mux_rhs we vb' cw aw bw c a b cv' av' bv) widths re
    obtain ⟨result, inv, val, frame⟩ := step.execution
    have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
      fun z hz => fb.used z (fa.used z (fc.used z hz))
    exact ⟨step.used, step.width, fun z hz => step.grows z (mono z hz), result, inv, val,
      fun z hz => (frame z (mono z hz)).trans ((bf z (fa.used z (fc.used z hz))).trans
        ((af z (fc.used z hz)).trans (cf z hz)))⟩

/-- **The world-indexed contract of a canonical Bool mux**, from those of its
three operands. -/
theorem boolMux_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom ce ae be : Lean.Expr}
    (c a b : Bool)
    (meaning : Meaning inputs (boolMuxE dom ce ae be) (.bool (if c then a else b)))
    (cc : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ce (.bool c))
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae (.bool a))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      be (.bool b)) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      (boolMuxE dom ce ae be) (.bool (if c then a else b)) := by
  refine cachedW_contract (tenv := tenv) L fuel
    (lower := translateBoolUncachedWith (translateFuelFix (translateStep tenv) fuel)
      (fun e h t n => Sparkle.Compiler.Elab.Rec.translateExprToWireImpl
        (fun e h t n => translateFuelFix (translateStep tenv) fuel e h t n) e h t n))
    meaning (fun hint top named => ?_) ?_
  · rw [Tools.ShippingBoolMuxSoundness.boolMux_step]
    exact translateFallback_bool _ _ hint top named rfl
  · intro mctx cctx hint top named s sm w wa wb hwa hda miss
    change RunsC (translateMuxWith (translateFuelFix (translateStep tenv) fuel) (pure .bit)
      ce ae be hint named) ctx s mctx mref cctx cref wa (w, sm) wb at miss
    obtain ⟨hwb, hdb, facts⟩ := muxPure_missW (tenv := tenv) L hD fuel cc ca cb hwa hda miss
    refine ⟨hwb, hdb, fun hsub => ?_⟩
    obtain ⟨cw, aw, bw, sc, sa, sb, ccAt, caAt, cbAt, reR⟩ := facts hsub
    exact boolMux_freshAt c a b ccAt caAt cbAt reR

/-! ## The fragment with Bool muxes, and its fuel induction -/

/-- The cone nodes walked at world level: `cfragC4` plus `mux` at sort `bool`
(a `mux` at a bit-vector sort is NOT in it).
(Earlier fragments are unchanged.) -/
def cfragC5 : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .bitsNum _ _ => true
  | _, .binary _ a b => cfragC5 a && cfragC5 b
  | _, .compare _ a b => cfragC5 a && cfragC5 b
  | _, .boolNot a => cfragC5 a
  | _, .boolBinary _ a b => cfragC5 a && cfragC5 b
  | _, .boolEq a b => cfragC5 a && cfragC5 b
  | s, .mux c a b => stBool s && (cfragC5 c && (cfragC5 a && cfragC5 b))
  | _, _ => false

/-- **The fuel induction at world level over `cfragC5`** (the text of
`fuel_contractWC4` with the Bool `mux` case of the built
`fuel_contract_leaves`). -/
theorem fuel_contractWC5 (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    (mF : Std.HashMap Lean.Name Res) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (vE j) (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → cfragC5 e = true →
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
      simp only [cfragC5, Bool.and_eq_true] at hf
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
      simp only [cfragC5, Bool.and_eq_true] at hf
      exact compare_contractW L hD fuel _ _ (a.wf_pos ha)
        (meaning_quote_leaves hb hv (.compare op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | boolNot a =>
      simp only [cfragC5] at hf
      exact boolNot_contractW L hD fuel _ (meaning_quote_leaves hb hv (.boolNot a) he)
        (ih a he hf) (ih (.boolLit false) trivial rfl)
    | boolBinary op a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC5, Bool.and_eq_true] at hf
      exact boolBin_contractW L hD fuel op _ _
        (meaning_quote_leaves hb hv (.boolBinary op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | boolEq a b =>
      obtain ⟨ha, hb'⟩ := he
      simp only [cfragC5, Bool.and_eq_true] at hf
      exact boolEq_contractW L hD fuel _ _
        (meaning_quote_leaves hb hv (.boolEq a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | mux c a b =>
      simp only [cfragC5, Bool.and_eq_true] at hf
      obtain ⟨hc, ha, hb'⟩ := he
      cases s with
      | bool =>
        exact boolMux_contractW L hD fuel _ _ _
          (meaning_quote_leaves hb hv (.mux c a b) ⟨hc, ha, hb'⟩)
          (ih c hc hf.2.1) (ih a ha hf.2.2.1) (ih b hb' hf.2.2.2)
      | bits w => simp [stBool] at hf
    | _ => simp [cfragC5] at hf

end generic

end Tools.ShippingGateParentRun
