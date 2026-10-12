import Tools.ShippingLegacySemContract
import Tools.ShippingUnifiedProtectionLeaves

/-! # Protection and order on the combined domain

`legacy_translate_contract` (`Tools/ShippingLegacySemContract.lean`) gives the
certified `Contract` on `LegacyDom` — input binders, certified nodes over
leaves of the domain, legacy inline arms. The entry's output statement needs
two more facts about the translation of the leaf, which the certified
fragment proves next to its contract (`Tools/ShippingUnifiedProtection.lean`):

* `ActionProtect` — a run never returns, nor declares, a name protected in
  its start state;
* `ActionOrder` — a run keeps the order invariant of the emitted statements
  (`OrderInv`).

**Proved here**, by induction on the derivation of `LegacyDom`, in the form
the certified fragment has them (every fuel, every hint and name flag,
`isTopLevel = false`):

* `legacy_fuel_protect`, `legacy_fuel_order`;
* `legacy_translate_protect`, `legacy_translate_order` — the shipping
  translator; the second is the `ordered` argument of
  `emitLeaves_postReady_at` / `harness_sound_at`.

Cases: an input binder by `input_protect` / `input_order`; a certified node
by the leaf-generic inductions (`fuel_protects_leaves`,
`fuel_orders_leaves`), the leaves' contracts from `legacy_fuel_contract` and
their protection / order from the induction hypothesis; a legacy inline arm
directly — the step on such a call IS a run of the translator on an
unfolding of the call, from the same state to the same state, with the same
wire (`ReachesUnfold`, the premise of `LegacyDom.inline`), so both facts are the
unfolding's, one fuel below. The inline attempt adds no statement and no
name of its own.

Stated at the default link context and child semantics (as
`Tools/ShippingUnifiedProtection.lean` and the certified entry are).

**NOT proved here**: `ReachesUnfold` and the unfoldings' membership stay the
premises carried by `LegacyDom.inline`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedProtection

/-- One step on a call the core declines is the fallback, for a run. -/
theorem step_run_fallback {rec : TranslateFn} {e : Lean.Expr} (nc : NotCore e)
    {hint : String} {top named : Bool} {ctx : CompilerState} {s t : CircuitState} {w : String}
    (hr : Returns (translateStepWith translateFallback rec e hint top named) ctx s w t) :
    Returns (translateFallback rec e hint top named) ctx s w t := by
  rw [step_eq_fallback rec e hint top named nc.shape (nc.core rec hint top named)] at hr
  exact hr

/-- **Protection on the combined domain, at every fuel.** -/
theorem legacy_fuel_protect {ctx : CompilerState} {inputs : FVarId → Option Value}
    {e : Lean.Expr} {v : Value} (h : LegacyDom ctx inputs e v) :
    ∀ (fuel : Nat) (hint : String) (named : Bool),
      ActionProtect (translateFuelFix translateStep fuel e hint false named) ctx inputs := by
  induction h with
  | input hi =>
    intro fuel hint named
    cases fuel with
    | zero =>
      intro s w t p hr lookup hp
      exact (Returns.throw hr).elim
    | succ fuel =>
      show ActionProtect (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (.fvar _) hint false named) ctx inputs
      exact input_protect hi
  | cert t wf mb mv db dv ihb ihv =>
    intro fuel hint named
    exact fuel_protects_leaves fuel mb mv
      (fun j hj f _ _ _ => legacy_fuel_contract (db j hj) f)
      (fun j hj f _ _ _ => legacy_fuel_contract (dv j hj) f)
      ihb ihv t wf hint named
  | inline nc reach _ ih =>
    intro fuel hint named
    cases fuel with
    | zero =>
      intro s w t p hr lookup hp
      exact (Returns.throw hr).elim
    | succ fuel =>
      intro s w t p hr lookup hp
      have hstep : Returns (translateStepWith translateFallback
          (translateFuelFix translateStep fuel) _ hint false named) ctx s w t := hr
      have hfb := step_run_fallback nc hstep
      obtain ⟨e', hU, htr⟩ := reach _ hint false named s t w hfb
      exact ih e' hU fuel hint named s w t p htr lookup hp

/-- **Order on the combined domain, at every fuel.** -/
theorem legacy_fuel_order {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value}
    (h : LegacyDom ctx inputs e v) :
    ∀ (fuel : Nat) (hint : String) (named : Bool),
      ActionOrder (translateFuelFix translateStep fuel e hint false named)
        ctx inputs we mems initial := by
  induction h with
  | input hi =>
    intro fuel hint named
    cases fuel with
    | zero =>
      intro s t w prior hr hinv widths order
      exact (Returns.throw hr).elim
    | succ fuel =>
      show ActionOrder (translateStepWith translateFallback (translateFuelFix translateStep fuel)
        (.fvar _) hint false named) ctx inputs we mems initial
      exact input_order hi
  | cert t wf mb mv db dv ihb ihv =>
    intro fuel hint named
    exact fuel_orders_leaves fuel mb mv
      (fun j hj f _ _ _ => legacy_fuel_contract (db j hj) f)
      (fun j hj f _ _ _ => legacy_fuel_contract (dv j hj) f)
      (fun j hj => legacy_fuel_protect (db j hj))
      (fun j hj => legacy_fuel_protect (dv j hj))
      ihb ihv t wf hint named
  | inline nc reach _ ih =>
    intro fuel hint named
    cases fuel with
    | zero =>
      intro s t w prior hr hinv widths order
      exact (Returns.throw hr).elim
    | succ fuel =>
      intro s t w prior hr hinv widths order
      have hstep : Returns (translateStepWith translateFallback
          (translateFuelFix translateStep fuel) _ hint false named) ctx s w t := hr
      have hfb := step_run_fallback nc hstep
      obtain ⟨e', hU, htr⟩ := reach _ hint false named s t w hfb
      exact ih e' hU fuel hint named s t w prior htr hinv widths order

/-- **The shipping translator protects, on the combined domain.** -/
theorem legacy_translate_protect {ctx : CompilerState} {inputs : FVarId → Option Value}
    {e : Lean.Expr} {v : Value} (h : LegacyDom ctx inputs e v) (hint : String) (named : Bool) :
    ActionProtect (translateExprToWire e hint false named) ctx inputs :=
  legacy_fuel_protect h translateFuelLimit hint named

/-- **The shipping translator keeps the order, on the combined domain** — the
order-invariant analogue of `legacy_translate_contract`. -/
theorem legacy_translate_order {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value}
    (h : LegacyDom ctx inputs e v) (hint : String) (named : Bool) :
    ActionOrder (translateExprToWire e hint false named) ctx inputs we mems initial :=
  legacy_fuel_order h translateFuelLimit hint named

end Tools.ShippingLegacySem
