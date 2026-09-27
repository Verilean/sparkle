import Tools.ShippingBoolLiteralSoundness

/-! Bool-result mux lowering through the shipping translator. The three child
simulations remain explicit. The mux node, type selection and both cache
branches are proved without an opaque handler or a type oracle. -/
namespace Tools.ShippingBoolMuxSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMuxRecursionSoundness Tools.ShippingMuxTypeSoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingBoolLiteralSoundness

def boolMuxE (dom c a b : Lean.Expr) := muxE dom (.const ``Bool []) c a b

theorem boolMux_uncached (rec legacy : TranslateFn) (dom c a b : Lean.Expr)
    (hint : String) (top named : Bool) :
    translateBoolUncachedWith rec legacy (boolMuxE dom c a b) hint top named =
      translateMuxWith rec (pure .bit) c a b hint named := rfl

theorem boolMux_step (rec : TranslateFn) (dom c a b : Lean.Expr)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (boolMuxE dom c a b) hint top named =
      translateFallback rec (boolMuxE dom c a b) hint top named := by
  have shape : translateCoreShape (boolMuxE dom c a b) = false := rfl
  have core : translateCore rec (boolMuxE dom c a b) hint top named = pure none := rfl
  simp [translateStepWith, shape, core]
  rfl

theorem bool_mux_rhs (we : WEnv) (env : Env) (cw aw bw : String) (c a b : Bool)
    (hc : env cw = encodeBool c) (ha : env aw = encodeBool a) (hb : env bw = encodeBool b) :
    evalExpr we env (.op .mux [.ref cw, .ref aw, .ref bw]) =
      some (encodeBool (if c then a else b)) := by
  cases c <;> simp [evalExpr, evalList, evalOp, encodeBool, hc, ha, hb]

theorem emitBoolMux_correct {ρ β we mems initial prior s s' ctx}
    {cw aw bw hint w : String} {named : Bool} (c a b : Bool)
    (hr : Returns (emitMuxResult cw aw bw hint named .bit) ctx s w s')
    (hp : Runs we mems initial s prior) (hrec : BoolRecordOk ρ β we s prior)
    (hbody : TypedBody we s)
    (hc : prior cw = encodeBool c) (ha : prior aw = encodeBool a) (hb : prior bw = encodeBool b)
    (wc : we cw = 1) (wa : we aw = 1) (wb : we bw = 1) (hw : ScalarWidthsAgree we s') :
    BoolStep ρ β we mems initial prior s s' w (if c then a else b) :=
  emitBoolResult_correct hr hp hrec hbody
    (.mux (wc ▸ TypedExpr.ref (we := we) cw (by omega))
      (wa ▸ TypedExpr.ref (we := we) aw (by omega))
      (wb ▸ TypedExpr.ref (we := we) bw (by omega)))
    (bool_mux_rhs we prior cw aw bw c a b hc ha hb) hw

/-- Compose the three children with the real mux sequence. Preservation of
earlier child values follows from their reserved-wire frame conditions. -/
theorem translateBoolMux_correct {ρ β we mems initial prior s s' ctx}
    {rec : TranslateFn} {ce ae be : Lean.Expr} {hint w : String} {named : Bool}
    (c a b : Bool) (good : CircuitState → Env → Prop)
    (hc : ChildSpec rec ctx we mems initial good ce "mux_cond" 1 (encodeBool c))
    (ha : ChildSpec rec ctx we mems initial good ae "mux_then" 1 (encodeBool a))
    (hb : ChildSpec rec ctx we mems initial good be "mux_else" 1 (encodeBool b))
    (hg : good s prior) (hp : Runs we mems initial s prior)
    (ht : ∀ st env, good st env → TypedBody we st)
    (hrec : ∀ st env, good st env → BoolRecordOk ρ β we st env)
    (hw : ScalarWidthsAgree we s')
    (hr : Returns (translateMuxWith rec (pure .bit) ce ae be hint named) ctx s w s') :
    BoolStep ρ β we mems initial prior s s' w (if c then a else b) := by
  obtain ⟨cw, aw, bw, sc, sa, sb, sq, ty, rc, ra, rb, rq, re⟩ := translateMuxWith_returns hr
  obtain ⟨hty, hsq⟩ := Returns.pure rq
  subst ty sq
  obtain ⟨vc, gc, ec, uc, wc, cv, mc, fc⟩ := hc s sc cw prior hg hp rc
  obtain ⟨va, ga, ea, ua, wa, av, ma, fa⟩ := ha sc sa aw vc gc ec ra
  obtain ⟨vb, gb, eb, ub, wb, bv, mb, fb⟩ := hb sa sb bw va ga ea rb
  have cv' : vb cw = encodeBool c := (fb cw (ma cw uc)).trans ((fa cw uc).trans cv)
  have av' : vb aw = encodeBool a := (fb aw ua).trans av
  have step := emitBoolMux_correct c a b re eb (hrec sb vb gb) (ht sb vb gb) cv' av' bv wc wa wb hw
  have mono : ∀ z, s.usedNames.contains z = true → sb.usedNames.contains z = true :=
    fun z hz => mb z (ma z (mc z hz))
  have fresh : s.usedNames.contains w = false := by
    cases hu : s.usedNames.contains w
    · rfl
    · have := mono w hu; simp [step.fresh] at this
  obtain ⟨result, er, cr, vr, fr⟩ := step.execution
  exact ⟨fresh, step.width, step.typed, step.used,
    fun z hz => step.grows z (mono z hz), result, er, cr, vr,
    fun z hz => (fr z (mono z hz)).trans ((fb z (ma z (mc z hz))).trans
      ((fa z (mc z hz)).trans (fc z hz)))⟩

theorem translateFallback_boolMux_correct {ρ β we mems initial prior s s' ctx}
    {rec : TranslateFn} {dom ce ae be : Lean.Expr} {hint w : String} {top named : Bool}
    (c a b : Bool) (good : CircuitState → Env → Prop)
    (dc : BoolDenotes ρ β ce c) (da : BoolDenotes ρ β ae a) (db : BoolDenotes ρ β be b)
    (hc : ChildSpec rec ctx we mems initial good ce "mux_cond" 1 (encodeBool c))
    (ha : ChildSpec rec ctx we mems initial good ae "mux_then" 1 (encodeBool a))
    (hb : ChildSpec rec ctx we mems initial good be "mux_else" 1 (encodeBool b))
    (hg : good s prior) (hp : Runs we mems initial s prior)
    (ht : ∀ st env, good st env → TypedBody we st)
    (hrec : ∀ st env, good st env → BoolRecordOk ρ β we st env)
    (hw : ScalarWidthsAgree we s')
    (hr : Returns (translateFallback rec (boolMuxE dom ce ae be) hint top named) ctx s w s') :
    BoolOutcome ρ β we mems initial prior s s' w (if c then a else b) := by
  have hd := BoolDenotes.quoteMux dom ce ae be dc da db
  rw [translateFallback_bool rec _ hint top named rfl] at hr
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · obtain ⟨hs, hu, hv, hw'⟩ := validatedBoolHit_correct (hrec s prior hg) hd hit
    subst s'
    exact ⟨ht s prior hg, hu, hw', fun _ h => h, prior, hp, hrec s prior hg, hv, fun _ _ => rfl⟩
  · rw [boolMux_uncached] at miss
    have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sm := by intro p h; apply hw p; rw [hs]; exact h
    have step := translateBoolMux_correct c a b good hc ha hb hg hp ht hrec wm miss
    obtain ⟨result, er, cr, vr, fr⟩ := step.execution
    refine ⟨?_, ?_, step.width, ?_, result, ?_,
      recordTranslation_bool cr hd step.used vr step.width record, vr, fr⟩
    · rw [hs]; exact step.typed
    · rw [hs]; exact step.used
    · rw [hs]; exact step.grows
    · rw [hs]; exact er

/-- The actual translator's Bool mux step. Child simulations are for its
smaller fuel budget; closing those hypotheses by induction remains separate. -/
theorem translateExprToWire_boolMux_correct {ρ β we mems initial prior s s' ctx}
    {dom ce ae be : Lean.Expr} {hint w : String} {top named : Bool}
    (c a b : Bool) (good : CircuitState → Env → Prop)
    (dc : BoolDenotes ρ β ce c) (da : BoolDenotes ρ β ae a) (db : BoolDenotes ρ β be b)
    (hc : ChildSpec (translateFuelFix translateStep (translateFuelLimit - 1)) ctx we mems initial good
      ce "mux_cond" 1 (encodeBool c))
    (ha : ChildSpec (translateFuelFix translateStep (translateFuelLimit - 1)) ctx we mems initial good
      ae "mux_then" 1 (encodeBool a))
    (hb : ChildSpec (translateFuelFix translateStep (translateFuelLimit - 1)) ctx we mems initial good
      be "mux_else" 1 (encodeBool b))
    (hg : good s prior) (hp : Runs we mems initial s prior)
    (ht : ∀ st env, good st env → TypedBody we st)
    (hrec : ∀ st env, good st env → BoolRecordOk ρ β we st env)
    (hw : ScalarWidthsAgree we s')
    (hr : Returns (translateExprToWire (boolMuxE dom ce ae be) hint top named) ctx s w s') :
    BoolOutcome ρ β we mems initial prior s s' w (if c then a else b) := by
  change Returns (translateStepWith translateFallback (translateFuelFix translateStep (translateFuelLimit - 1))
    (boolMuxE dom ce ae be) hint top named) ctx s w s' at hr
  rw [boolMux_step] at hr
  exact translateFallback_boolMux_correct c a b good dc da db hc ha hb hg hp ht hrec hw hr

end Tools.ShippingBoolMuxSoundness
