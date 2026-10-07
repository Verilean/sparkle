import Tools.ShippingCompareLoweringSoundness

/-! Literal Bool translation through the real fuel-bounded translator.
No recursive-child or legacy-handler hypothesis is needed for this leaf.
Initial invariants and agreement with final declaration widths remain explicit. -/
namespace Tools.ShippingBoolLiteralSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingBoolSourceSoundness Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMuxRecursionSoundness Tools.ShippingCompareLoweringSoundness

def literalE (dom : Lean.Expr) (b : Bool) : Lean.Expr :=
  mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) dom (.const ``Bool [])
    (.const (boolName b) [])

theorem literal_core (rec : TranslateFn) (dom : Lean.Expr) (b : Bool)
    (hint : String) (top named : Bool) :
    translateCore rec (literalE dom b) hint top named = pure none := by cases b <;> rfl

theorem literal_uncached (rec legacy : TranslateFn) (dom : Lean.Expr) (b : Bool)
    (hint : String) (top named : Bool) :
    translateBoolUncachedWith rec legacy (literalE dom b) hint top named =
      emitBoolLiteral b hint named := by cases b <;> rfl

theorem emitBoolLiteral_correct {ρ β we mems initial prior s s' ctx hint w named}
    (b : Bool) (hr : Returns (emitBoolLiteral b hint named) ctx s w s')
    (hp : Runs we mems initial s prior) (hc : BoolRecordOk ρ β we s prior)
    (ht : TypedBody we s) (hw : ScalarWidthsAgree we s') :
    BoolStep ρ β we mems initial prior s s' w b := by
  apply emitBoolResult_correct hr hp hc ht (.const _ 1 (by decide)) ?_ hw
  have he := evalExpr_const_lt we prior (encodeBool b) 1 (encodeBool_lt b)
  cases b <;> simpa [encodeBool] using he

/-- A cache-compatible result: allocation may be fresh or a previously recorded
wire, but execution, typing and all reserved values are preserved. -/
structure BoolOutcome (ρ : BoolValuation) (β : Valuation) (we : WEnv) (mems : MEnv)
    (initial prior : Env) (s s' : CircuitState) (w : String) (value : Bool) : Prop where
  typed : TypedBody we s'
  used : s'.usedNames.contains w = true
  width : we w = 1
  grows : ∀ z, s.usedNames.contains z = true → s'.usedNames.contains z = true
  execution : ∃ result, Runs we mems initial s' result ∧ BoolRecordOk ρ β we s' result ∧
    result w = encodeBool value ∧
    (∀ z, s.usedNames.contains z = true → result z = prior z)

theorem literal_hit {ρ β we mems initial prior s s' ctx dom w b}
    (hp : Runs we mems initial s prior) (hc : BoolRecordOk ρ β we s prior)
    (ht : TypedBody we s)
    (hr : Returns (cacheLookupValidated (literalE dom b)) ctx s (some w) s') :
    BoolOutcome ρ β we mems initial prior s s' w b := by
  obtain ⟨hs, hu, hv, hw⟩ := validatedBoolHit_correct hc (BoolDenotes.quotePure dom b) hr
  subst s'
  exact ⟨ht, hu, hw, fun _ h => h, prior, hp, hc, hv, fun _ _ => rfl⟩

theorem translateFallback_literal_correct {ρ β we mems initial prior s s' ctx dom w hint top named}
    (rec : TranslateFn) (b : Bool)
    (hp : Runs we mems initial s prior) (hc : BoolRecordOk ρ β we s prior)
    (ht : TypedBody we s) (hw : ScalarWidthsAgree we s')
    (hr : Returns (translateFallback rec (literalE dom b) hint top named) ctx s w s') :
    BoolOutcome ρ β we mems initial prior s s' w b := by
  rw [translateFallback_bool rec _ hint top named (by cases b <;> rfl)] at hr
  rcases translateControlCachedWith_returns hr with hit | ⟨sm, miss, record⟩
  · exact literal_hit hp hc ht hit
  · rw [literal_uncached] at miss
    have hs := recordTranslation_returns record
    have wm : ScalarWidthsAgree we sm := by intro p h; apply hw p; rw [hs]; exact h
    have step := emitBoolLiteral_correct b miss hp hc ht wm
    obtain ⟨result, er, cr, vr, fr⟩ := step.execution
    refine ⟨?_, ?_, step.width, ?_, result, ?_,
      recordTranslation_bool cr (BoolDenotes.quotePure dom b) step.used vr step.width record, vr, fr⟩
    · rw [hs]; exact step.typed
    · rw [hs]; exact step.used
    · rw [hs]; exact step.grows
    · rw [hs]; exact er

/-- Both the outer core cache and the fallback cache are covered. The recursive
entry is arbitrary because literal translation never calls it. -/
theorem translateStep_literal_correct {ρ β we mems initial prior s s' ctx dom w hint top named}
    (rec : TranslateFn) (b : Bool)
    (hp : Runs we mems initial s prior) (hc : BoolRecordOk ρ β we s prior)
    (ht : TypedBody we s) (hw : ScalarWidthsAgree we s')
    (hr : Returns (translateStepWith translateFallback rec (literalE dom b) hint top named) ctx s w s') :
    BoolOutcome ρ β we mems initial prior s s' w b := by
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, rh, hr⟩ := Returns.bind hr
    have hs := (cacheLookupValidated_returns rh).1
    subst sh
    split at hr
    · obtain ⟨hw', hs'⟩ := Returns.pure hr
      subst w s'
      exact literal_hit hp hc ht rh
    · rw [literal_core] at hr
      obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
      obtain ⟨hv, hs⟩ := Returns.pure rv
      subst v sc
      exact translateFallback_literal_correct rec b hp hc ht hw hr
  · rw [literal_core] at hr
    obtain ⟨v, sc, rv, hr⟩ := Returns.bind hr
    obtain ⟨hv, hs⟩ := Returns.pure rv
    subst v sc
    exact translateFallback_literal_correct rec b hp hc ht hw hr

/-- The actual shipping translator on a library Bool literal. Unlike a node
composition theorem, this needs no recursive translation hypothesis. -/
theorem translateExprToWire_literal_correct {ρ β we mems initial prior s s' ctx dom w hint top named}
    (b : Bool)
    (hp : Runs we mems initial s prior) (hc : BoolRecordOk ρ β we s prior)
    (ht : TypedBody we s) (hw : ScalarWidthsAgree we s')
    (hr : Returns (translateExprToWire (literalE dom b) hint top named) ctx s w s') :
    BoolOutcome ρ β we mems initial prior s s' w b := by
  change Returns (translateStepWith translateFallback
    (translateFuelFix translateStep (translateFuelLimit - 1)) (literalE dom b) hint top named) ctx s w s' at hr
  exact translateStep_literal_correct _ b hp hc ht hw hr

end Tools.ShippingBoolLiteralSoundness
