import Tools.ShippingLegacySemLeafHandled

/-! # A beta-redex leaf whose reduction is an input variable: a wire-through

The census (rounds 19–20, `Tests/Compiler/LegacyArmCensusTest.lean`): of the
90 Signal-valued definitions of the examined IP modules for which the
shipping entry RETURNS through the legacy arm, 45 are structure field
projection functions (`SHA256Out.done`, `RxOut.dmac`, …). `openRecordInputs`
opens the record parameter into its Signal fields, and the leaf handed to the
translator is the projection function applied to the rebuilt record:

```
(fun dom self => self.i) dom ⟨dom, x₁, …, xₖ⟩        -- head: a lambda
```

**What the translator does with it** (`Sparkle/Compiler/Elab.lean`):

| Stage | Lines | Here |
|---|---|---|
| the core declines (`translateCoreShape`, `translateCore`: head not a constant, not a variable) | 8149–8180 | `notCore_of_lamHead` |
| `translateFallback`: `fallbackKind = .other` (premise: a closed computation on the leaf) | 8750–8791 | `fallback_eq_arm` |
| `translateInstanceOrFallback`: head not a constant → the shim, NO environment read | 8638–8679 | `arm_to_shim_lam` |
| the shim: `isNamed = true` → not cacheable → the body | 7914–7950 | `legacyShim_returns` |
| the body's prefix: trace, call counter, limit, tick | 6853–6900 | as `pre_plain` |
| not a variable; head not a constant: both name-guarded blocks skipped | 6903, 6965, 7011 | the `match`es reduce on the lambda head |
| `let isBetaRedex := e.isApp && e.getAppFn.isLambda` — TRUE: the body replaces `e` by `withTransparency .reducible (whnf e)` | 7606–7609 | the ORACLE: premise `WhnfIsVar e x` |
| the `match` on the result: `.fvar fvarId` → `CompilerM.lookupVar fvarId`; a hit returns the wire, a miss throws `Unbound variable` | 7738–7744 | `lookupVar_returns` |

So a successful run returns the wire bound for the variable and leaves the
builder state: a WIRE-THROUGH of one input.

**Proved here**

* `impl_betaRedex` — the body on `.app f a` with a lambda head and
  `WhnfIsVar (.app f a) x`: `visible ctx s.sourceBindings x = some w ∧ t = s`.
* `betaRedex_step` — the same from one step of the translator at the entry's
  flags (`isTopLevel = false`, `isNamed = true`).
* `handlerCase_wire` — the arm as a `HandlerCase` with NO sub-expression: for
  `inputs x = some v`, frame and outcome are the input binder's
  (`input_contract`'s two proofs, with the run fact above in place of
  `translateStep_fvar_returns`), the order statement likewise.
* `leafDom_betaWire` — the leaf is in `LeafDom … hint true` at the input's
  value.

**Premises, classified**

| Premise | Class |
|---|---|
| `(Expr.app f a).getAppFn = .lam n ty b bi` | closed computation on the leaf |
| `fallbackKind (.app f a) = .other` | closed computation on the leaf (the compiler's own function; observed by the census: all 45 are `other`) |
| `WhnfIsVar (.app f a) x`: every successful `withTransparency .reducible (whnf leaf)` returns `.fvar x` | ORACLE (reflection through `whnf`; same class as `hunfE`); observed by the evidence line |
| `inputs x = some v` | a fact of the prepared setup (proved per declaration from `prepare`) |

That the variable is FOUND (`lookupVar` hits) is not a premise: it follows
from `inputs x = some v` through the invariant (`h.inputs.lookup`), exactly as
for an input leaf. No `Meta` context is needed: the post-`whnf` variable arm
(7738–7744) does not read the local context (unlike the pre-`whnf` one,
`impl_fvar`).

**Program shapes EXPECTED** (the prefix and the `whnf` test are OBSERVED in
`pre_plain`; the rest is not):

```
B0  (prefix)                                               -- k0 … k4 of `pre_plain`
B1  match e with | .fvar _ => … | _ => REST                -- e = .app f a: reduces
    REST: let fn := e.getAppFn; …
          match fn with | .const instName _ => … | _ => J₂ -- after `rw [hfnL]`: reduces
    J₂:   match fn with | .const name _ => … | _ => J₃     -- reduces
B2  J₃ = getCompilerState >>= fun varMap =>
         if (!hasMappedFvar || isBetaRedex) = true
         then (liftMetaM (withTransparency .reducible (whnf e)) >>= K) else (pure e >>= K)
B3  K e' = let fn := e'.getAppFn; match e' with … | .fvar fvarId => V fvarId | …
B4  V x = CompilerM.lookupVar x >>= fun r =>
          match r with | some w => pure w
                       | none => getCompilerState >>= fun st => liftMetaM (throwError …)
```
-/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingMixedBinarySoundness (Frame)
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedProtection
open Tools.ShippingBindingsSoundness (visible)

/-- **The oracle premise of the beta branch**: every successful reducible
`whnf` of `e` returns the variable `x`. -/
def WhnfIsVar (e : Lean.Expr) (x : FVarId) : Prop :=
  ∀ e' : Lean.Expr,
    MReturns (Lean.Meta.withTransparency Lean.Meta.TransparencyMode.reducible
      (Lean.Meta.whnf e)) e' →
    e' = Lean.Expr.fvar x

/-- The body's `whnf` test when the beta-redex flag is `true`. -/
theorem betaTest (h : Bool) : (!h || true) = true := by
  cases h <;> rfl

/-- The taken branch of an `if` whose condition holds. -/
theorem returns_ite_pos {α : Type} {c : Prop} [Decidable c] {a b : CompilerM α}
    {ctx : CompilerState} {s t : CircuitState} {r : α}
    (h : Returns (if c then a else b) ctx s r t) (hc : c) : Returns a ctx s r t := by
  rw [if_pos hc] at h
  exact h

/-- The core declines an application whose head is a lambda. -/
theorem notCore_of_lamHead {f a : Lean.Expr} {n : Name} {ty b : Lean.Expr} {bi : BinderInfo}
    (hfnL : (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi) :
    NotCore (Lean.Expr.app f a) where
  shape := by
    first
      | (unfold translateCoreShape
         rw [hfnL]
         first | done | rfl)
      | simp only [translateCoreShape, hfnL]
      | simp [translateCoreShape, hfnL]
  core := fun rec hint top named => by
    first
      | simp only [translateCore, hfnL]
      | (unfold translateCore
         simp only [hfnL])
      | (unfold translateCore
         rw [hfnL])
      | simp [translateCore, hfnL]

/-- For a lambda head the instance arm hands the expression to the caching
shim directly (no environment read). -/
theorem arm_to_shim_lam {rec : TranslateFn} {f a : Lean.Expr} {n : Name} {ty b : Lean.Expr}
    {bi : BinderInfo} {hint : String} {top named : Bool} {ctx : CompilerState}
    {s t : CircuitState} {w : String}
    (hfnL : (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (tr : Returns (translateInstanceOrFallback rec (Lean.Expr.app f a) hint top named)
      ctx s w t) :
    Returns (Rec.translateExprToWireCached (fun e h t n => rec e h t n) (Lean.Expr.app f a)
      hint top named) ctx s w t := by
  unfold translateInstanceOrFallback at tr
  rw [hfnL] at tr
  first
    | exact tr
    | (simp only [] at tr
       exact tr)
    | (dsimp only at tr
       exact tr)

set_option maxHeartbeats 2000000 in
/-- **The body on a beta-redex whose reducible `whnf` is the variable `x`**:
the wire bound for `x`, the builder state unchanged. -/
theorem impl_betaRedex {rec : TranslateFn} {ctx : CompilerState} {f a : Lean.Expr} {n : Name}
    {ty b : Lean.Expr} {bi : BinderInfo} {x : FVarId} {hint : String} {top named : Bool}
    {s t : CircuitState} {w : String}
    (hfnL : (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hwhnf : WhnfIsVar (Lean.Expr.app f a) x)
    (h : Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) (Lean.Expr.app f a)
      hint top named) ctx s w t) :
    visible ctx s.sourceBindings x = some w ∧ t = s := by
  unfold Rec.translateExprToWireImpl at h
  -- B0: the trace, the call counter, the limit, the tick (as `pre_plain`)
  have k0 := returns_trace_then h
  obtain ⟨callN, s1, h1, k1⟩ := Returns.bind k0
  rw [Returns.liftMetaM h1] at k1
  obtain ⟨limit, s2, h2, k2⟩ := Returns.bind k1
  rw [Returns.liftMetaM h2] at k2
  rcases returns_ite k2 with ⟨_, ka⟩ | ⟨_, k3⟩
  · obtain ⟨u, s3, hthrow, _⟩ := Returns.bind ka
    exact (returns_throw hthrow).elim
  have k4 := returns_ite_lift_then k3
  -- B1: an application, its head a lambda
  rw [hfnL] at k4
  -- B2: the context read, then the `whnf` test: a beta-redex
  obtain ⟨c0, s8, hread, k8⟩ := Returns.bind k4
  obtain ⟨hc0, hs8⟩ := Returns.read hread
  rw [hc0, hs8] at k8
  have kthen := returns_ite_pos k8 (betaTest _)
  obtain ⟨e', s9, hw, k9⟩ := Returns.bind kthen
  obtain ⟨hm, hs9⟩ := returns_liftMetaM hw
  have he' : e' = Lean.Expr.fvar x := hwhnf e' hm
  rw [he', hs9] at k9
  -- B3 / B4: the result is a variable; the lookup
  obtain ⟨r, s10, hlook, k10⟩ := Returns.bind k9
  obtain ⟨hr, hs10⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns hlook
  rw [hs10] at k10
  cases r with
  | some wn =>
    obtain ⟨hw', ht⟩ := Returns.pure k10
    refine ⟨?_, ht⟩
    rw [hw']
    exact hr.symm
  | none =>
    obtain ⟨st, s11, _, k11⟩ := Returns.bind k10
    first
      | exact (returns_throw k11).elim
      | (obtain ⟨u3, s12, hth, _⟩ := Returns.bind k11
         exact (returns_throw hth).elim)

/-- **One step of the translator on such a leaf, at the entry's flags.** -/
theorem betaRedex_step {rec : TranslateFn} {ctx : CompilerState} {f a : Lean.Expr} {n : Name}
    {ty b : Lean.Expr} {bi : BinderInfo} {x : FVarId} {hint : String}
    {s t : CircuitState} {w : String}
    (hfnL : (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hkind : fallbackKind (Lean.Expr.app f a) = .other)
    (hwhnf : WhnfIsVar (Lean.Expr.app f a) x)
    (hr : Returns (translateStepWith translateFallback rec (Lean.Expr.app f a) hint false true)
      ctx s w t) :
    visible ctx s.sourceBindings x = some w ∧ t = s := by
  have h1 := step_run_fallback (notCore_of_lamHead hfnL) hr
  rw [fallback_eq_arm rec (Lean.Expr.app f a) hint false true hkind] at h1
  have h2 := arm_to_shim_lam hfnL h1
  have hnc : (!true && !(Lean.Expr.app f a).isFVar && !false) = false := rfl
  rcases legacyShim_returns h2 with hbody | ⟨hc, _, _⟩
  · exact impl_betaRedex hfnL hwhnf hbody
  · exact absurd (hnc.symm.trans hc) (by decide)

/-- **The wire-through arm is a handler case** (no sub-expression). -/
theorem handlerCase_wire {ctx : CompilerState} {inputs : FVarId → Option Value}
    {hint : String} {f a : Lean.Expr} {n : Name} {ty b : Lean.Expr} {bi : BinderInfo}
    {x : FVarId} {v : Value}
    (hfnL : (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hkind : fallbackKind (Lean.Expr.app f a) = .other)
    (hwhnf : WhnfIsVar (Lean.Expr.app f a) x)
    (hi : inputs x = some v) :
    HandlerCase ctx inputs hint true (Lean.Expr.app f a) v (fun _ _ _ _ => False) where
  spec := by
    intro fuel we mems initial _
    constructor
    · intro s t w lookup hr
      have hstep : Returns (translateStepWith translateFallback
          (translateFuelFix translateStep fuel) (Lean.Expr.app f a) hint false true)
          ctx s w t := hr
      obtain ⟨_, ht⟩ := betaRedex_step hfnL hkind hwhnf hstep
      rw [ht]
      exact Frame.refl s
    · intro s t w prior h widths hr
      have hstep : Returns (translateStepWith translateFallback
          (translateFuelFix translateStep fuel) (Lean.Expr.app f a) hint false true)
          ctx s w t := hr
      obtain ⟨hv, ht⟩ := betaRedex_step hfnL hkind hwhnf hstep
      obtain ⟨z, bound, used, val, width⟩ := h.inputs.lookup x v hi
      have hz : z = w := Option.some.inj (bound.symm.trans hv)
      rw [ht, ← hz]
      exact ⟨used, width, fun _ hz => hz, prior, h, val, fun _ _ => rfl⟩
  order := by
    intro fuel we mems initial _ _ s t w prior hr h widths order
    have hstep : Returns (translateStepWith translateFallback
        (translateFuelFix translateStep fuel) (Lean.Expr.app f a) hint false true)
        ctx s w t := hr
    rw [(betaRedex_step hfnL hkind hwhnf hstep).2]
    exact order

/-- **A beta-redex leaf whose reduction is an input variable is in the leaf
domain, at the input's value.** -/
theorem leafDom_betaWire {ctx : CompilerState} {inputs : FVarId → Option Value}
    {hint : String} {f a : Lean.Expr} {n : Name} {ty b : Lean.Expr} {bi : BinderInfo}
    {x : FVarId} {v : Value}
    (hfnL : (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hkind : fallbackKind (Lean.Expr.app f a) = .other)
    (hwhnf : WhnfIsVar (Lean.Expr.app f a) x)
    (hi : inputs x = some v) :
    LeafDom ctx inputs hint true (Lean.Expr.app f a) v :=
  LeafDom.handled (fun _ _ _ _ => False) (handlerCase_wire hfnL hkind hwhnf hi)
    (fun _ _ _ _ h => h.elim)

end Tools.ShippingLegacySem
