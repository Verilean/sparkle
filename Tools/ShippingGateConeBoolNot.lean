import Tools.ShippingGateConeCompare

variable {tenv : Lean.Environment}

/-! # Validated-cache cone nodes at world level; `boolNot` (worker N, round 7)

WRITTEN, NOT BUILT.

Every Bool cone node (`boolNot`, `boolBinary`, `boolEq`, Bool `mux`) and the
bit-vector `mux` is routed by the step to the fallback, i.e. to the
validated-cache wrapper `translateControlCachedWith lower` (a hit, or `lower`
then the record). `compare_contractW` (round 6) did the wrapper inline; here
it is factored once:

* **`cachedW_contract`**: the world-indexed contract of a node whose step IS
  `translateControlCachedWith lower`, from a world-level fact about a run of
  `lower` (it keeps the invariant and the depth, and — once its final cache is
  in `mF` — has the frame, freshness and the outcome). The hit and the
  record are handled here (the text of `compare_contractW`).
* **`signalCompare_missW`**: that world-level fact for the comparison lowering
  `translateSignalCompare` (both operands, one Bool wire and its assign) from
  the operands' `ContractW`s, over any operand values encoding bit vectors
  (the text of `compare_contractW`'s miss branch). `boolNot` and `boolEq` are
  lowered by it (`!a` is `a == false`).
* **`boolNot_contractW`**: the canonical `~~~a` / `!a` node.
* `cfragC2` (a NEW fragment; `cfragC` and every statement over it are
  unchanged): `cfragC` plus `boolNot`. **`fuel_contractWC2`**: the fuel
  induction over `cfragC2`. -/
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

/-! ## A node under the validated-cache wrapper -/

/-- **The world-indexed contract of a node whose step is the validated-cache
wrapper around `lower`**: a validated hit reuses the recorded wire; a miss
runs `lower` (which keeps the invariant and the depth and, ending in a world
whose cache is in `mF`, has the frame, freshness and the outcome) and then
records. -/
theorem cachedW_contract (L : RefLaws mref cref) {D : Nat} (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value} {lower : TranslateFn}
    (meaning : Meaning inputs e v)
    (hstep : ∀ (hint : String) (top named : Bool),
      translateStepWith (translateFallback tenv) (translateFuelFix (translateStep tenv) fuel) e
        hint top named = translateControlCachedWith lower e hint top named)
    (node : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String)
      (top named : Bool) (s sm : CircuitState) (w : String) (wa wb : Void IO.RealWorld),
      InvV L wa → L.dval wa = D →
      RunsC (lower e hint top named) ctx s mctx mref cctx cref wa (w, sm) wb →
      InvV L wb ∧ L.dval wb = D ∧ (SubMap (L.val wb) mF →
        (Lookup ctx inputs s → Frame s sm ∧ s.usedNames.contains w = false) ∧
        (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we sm →
          Outcome ctx inputs we mems initial prior s sm w v))) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      e v := by
  have step : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String)
      (top named : Bool) (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
      InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
      RunsC (translateFuelFix (translateStep tenv) (fuel + 1) e hint top named) ctx s
        mctx mref cctx cref w0 (w, t) w1 →
      (Lookup ctx inputs s → Frame s t) ∧
        (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
          Outcome ctx inputs we mems initial prior s t w v) := by
    intro mctx cctx hint top named s t w w0 w1 hw0 hd0 hsub hr
    change RunsC (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel) e hint top named) ctx s
      mctx mref cctx cref w0 (w, t) w1 at hr
    rw [hstep] at hr
    rcases controlCached_runsW L hw0 hd0 hr with hit | ⟨sm, wa, wb, hwa, hda, miss, record⟩
    · -- a validated hit: the recorded wire, the state unchanged
      have ht := (cacheLookupValidated_returns hit).1
      refine ⟨fun _ => ?_, fun prior h _ => hit_outcome h meaning hit⟩
      rw [ht]
      exact Frame.refl _
    · -- a miss: the lowering, then the record
      obtain ⟨hwb, hdb, facts⟩ := node mctx cctx hint top named s sm w wa wb hwa hda miss
      obtain ⟨-, -, hsr⟩ :=
        keepsW L (fun L' => recordTranslation_keepsC L' D e w (!named && !e.isFVar && !top))
          hwb hdb record
      have shape := facts (sub_trans hsr hsub)
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

/-! ## The comparison lowering at world level -/

/-- **A run of the comparison lowering, with its worlds**: both operands, one
Bool wire and its assign keep the invariant and the depth; once the final
cache is in `mF`, the operands' `ContractW`s apply to their own runs and the
lowering has the frame, freshness and the outcome (the text of
`compare_contractW`'s miss branch, for any operand values encoding `x`, `y`). -/
theorem signalCompare_missW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {ae be : Lean.Expr} {le : SignalCompareKind}
    {n : Nat} {va vb : Value}
    (x y : BitVec n) (hn : 0 < n)
    (hva : va.toNat = x.toNat) (hwa : va.kind.width = n)
    (hvb : vb.toNat = y.toNat) (hwb : vb.kind.width = n)
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae va)
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      be vb)
    {hint : String} {named : Bool} {s sm : CircuitState} {w : String}
    {wa wb : Void IO.RealWorld}
    (hwa0 : InvV L wa) (hda0 : L.dval wa = D)
    (miss : RunsC (translateSignalCompare (translateFuelFix (translateStep tenv) fuel) le ae be
      hint named) ctx s mctx mref cctx cref wa (w, sm) wb) :
    InvV L wb ∧ L.dval wb = D ∧ (SubMap (L.val wb) mF →
      (Lookup ctx inputs s → Frame s sm ∧ s.usedNames.contains w = false) ∧
      (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we sm →
        Outcome ctx inputs we mems initial prior s sm w (.bool (compareValue le x y)))) := by
  unfold translateSignalCompare at miss
  obtain ⟨a, sa, wa1, ra, rest⟩ := RunsC.bind miss
  obtain ⟨b, sb, wb1, rb, re⟩ := RunsC.bind rest
  obtain ⟨hwa1, hda1, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa0 hda0 ra
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
  refine ⟨hwq', hdq', fun hsub => ?_⟩
  have subB : SubMap (L.val wb1) mF := sub_trans hs1 (sub_trans hs2 hsub)
  have subA : SubMap (L.val wa1) mF := sub_trans hsab subB
  have caAt := ca.atRun hwa0 hda0 subA ra
  have cbAt := cb.atRun hwa1 hda1 subB rb
  exact compare_freshAt (le := le) x y hn hva hwa hvb hwb caAt cbAt (runsCReturns re)

/-! ## `boolNot` -/

/-- **The world-indexed contract of a canonical Bool negation**, from those of
its operand and of the literal `false` it is compared with. -/
theorem boolNot_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom ae : Lean.Expr}
    (a : Bool)
    (meaning : Meaning inputs (boolNotE dom ae) (.bool (!a)))
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      ae (.bool a))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
        (.const ``Bool.false [])) (.bool false)) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      (boolNotE dom ae) (.bool (!a)) := by
  refine cachedW_contract (tenv := tenv) L fuel
    (lower := translateBoolUncachedWith (translateFuelFix (translateStep tenv) fuel)
      (fun e h t n => Sparkle.Compiler.Elab.Rec.translateExprToWireImpl
        (fun e h t n => translateFuelFix (translateStep tenv) fuel e h t n) e h t n))
    meaning (fun hint top named => ?_) ?_
  · rw [Tools.ShippingMixedRecursion.boolNot_step]
    exact translateFallback_bool _ _ hint top named rfl
  · intro mctx cctx hint top named s sm w wa wb hwa hda miss
    change RunsC (translateSignalCompare (translateFuelFix (translateStep tenv) fuel) .eq ae
      (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
        (.const ``Bool.false [])) hint named) ctx s mctx mref cctx cref wa (w, sm) wb at miss
    have val : compareValue .eq (BitVec.ofNat 1 (encodeBool a)) (0#1) = !a := by
      cases a <;> rfl
    rw [← val]
    exact signalCompare_missW (tenv := tenv) (n := 1) (va := .bool a) (vb := .bool false) L hD fuel
      (BitVec.ofNat 1 (encodeBool a)) (0#1) (by decide) (by cases a <;> rfl)
      rfl rfl rfl ca cb hwa hda miss

/-! ## The fragment with `boolNot`, and its fuel induction -/

/-- The cone nodes walked at world level: `cfragC` plus `boolNot`.
(`cfrag` and `cfragC` are unchanged.) -/
def cfragC2 : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .bitsNum _ _ => true
  | _, .binary _ a b => cfragC2 a && cfragC2 b
  | _, .compare _ a b => cfragC2 a && cfragC2 b
  | _, .boolNot a => cfragC2 a
  | _, _ => false

/-- **The fuel induction at world level over `cfragC2`** (the text of
`fuel_contractWC` with the `boolNot` case of the built
`fuel_contract_leaves`). -/
theorem fuel_contractWC2 (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    (mF : Std.HashMap Lean.Name Res) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (vE j) (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → cfragC2 e = true →
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
      simp only [cfragC2, Bool.and_eq_true] at hf
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
      simp only [cfragC2, Bool.and_eq_true] at hf
      exact compare_contractW L hD fuel _ _ (a.wf_pos ha)
        (meaning_quote_leaves hb hv (.compare op a b) ⟨ha, hb'⟩) (ih a ha hf.1) (ih b hb' hf.2)
    | boolNot a =>
      simp only [cfragC2] at hf
      exact boolNot_contractW L hD fuel _ (meaning_quote_leaves hb hv (.boolNot a) he)
        (ih a he hf) (ih (.boolLit false) trivial rfl)
    | _ => simp [cfragC2] at hf

end generic

end Tools.ShippingGateParentRun
