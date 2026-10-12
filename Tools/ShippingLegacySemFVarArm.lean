import Tools.ShippingLegacySemSteps2

/-! # What the legacy body does on a free variable (`Rec.translateExprToWireImpl` on `.fvar id`)

Question of round 15: is the third outcome of `useDbl_output`
(`InputSkipped`: the leaf emitted with NO input port bound) refutable from
`Returns` alone, because "the translation of an unmapped variable throws"?

**Answer: no.** The body's variable arm (`Sparkle/Compiler/Elab.lean`, "0.
Handle free variables first") does NOT simply throw on a variable that the
context's `varMap` does not bind. In order:

1. `CompilerM.lookupVar` — the context's `varMap`, THEN the builder state's
   `sourceBindings` (`visible ctx s.sourceBindings id`). A hit returns the
   wire; the builder state is untouched.
2. on a miss it reads the `Meta` local context: if the variable has a VALUE
   there (a `let` variable), the arm translates the value (zeta), through the
   recursive translator;
3. otherwise it runs `try Lean.Meta.reduce e catch _ => pure e`; if the
   oracle's result differs from the variable, the arm translates THAT;
4. only otherwise it throws `Unbound variable`.

**Proved here** (`impl_fvar`): a successful run of the body on `.fvar id` is
one of the three non-throwing cases — a `lookupVar` hit with the state
unchanged, or a successful run of the recursive translator (same hint and
flags, same states, same wire) on SOME expression `val` (case 2: what the
local-context read returned), or on some `reduced` with
`(reduced != .fvar id) = true` (case 3: what the `reduce` oracle returned).

So "a successful translation of a variable leaf implies the variable is
mapped" is FALSE as a statement about `Returns`; what holds is the
disjunction above. To exclude cases 2 and 3 for a telescope variable one
needs (a) the run in its `Meta` context all the way down to this arm
(`RunsIn` through the whole translator — the local-context read must be the
telescope's, where the variable is a `cdecl` without value) and (b) a
Meta-library premise: `reduce` on a `cdecl` variable returns it.

**And the leaf of `useDbl` is not a variable.** It is the call `dbl x`. With
no port bound, the body's test `hasMappedFvar` (`Expr.find?`, kernel-opaque
— not provably `false` even for an empty `varMap`) is false at run time, and
the body then replaces the expression by `whnf e` — an oracle's result that
nothing relates to `dbl x` — and continues on THAT (`pre_plain`'s premise
`HasMappedFVar` is exactly what keeps the proved walk away from this branch).
Whether the run then reaches this arm, and whether it returns, is not
derivable; the compiled evidence in
`Tests/Compiler/LegacySemInstanceTest.lean` (`SKIPPED-INPUT EVIDENCE`) runs
that very leaf translation without a bound port and logs what happens.

`InputSkipped` therefore stays in the conclusion of `useDbl_output`.

**Program shape EXPECTED at each inversion.** The prefix is OBSERVED (it is
`pre_plain`'s, `Tools/ShippingLegacySemPre.lean`): trace; call counter;
limit; `if callN > limit` (throws); the profile tick. Then, NOT observed:

```
F0  match Expr.fvar id with | .fvar fvarId => ARM | _ => …     (reduces at the next inversion)
F1  ARM = CompilerM.lookupVar id >>= fun r =>
            match r with | some w => pure w | none => MISS     (bind; `cases r`)
F2  MISS = CompilerM.liftMetaM (local-context read) >>= fun inlinedVal =>
            match inlinedVal with | some val => Z val | none => R   (bind; `cases`)
F3  Z val = liftMetaM visited.get >>= fun visited =>
            (if visited.contains … then liftMetaM (throwError …) >>= fun _ => P else P)
            P = liftMetaM (insert) >>= fun _ => rec val hint top named >>= fun r =>
                liftMetaM (erase) >>= fun _ => pure r
F4  R = liftMetaM visited.get >>= fun visited =>
            (if … then liftMetaM (throwError …) >>= fun _ => Q else Q)
            Q = liftMetaM (insert) >>= fun _ => liftMetaM (try reduce …) >>= fun reduced =>
                liftMetaM (erase) >>= fun _ =>
                if (reduced != e) = true then (rec reduced hint top named >>= fun r => pure r)
                else liftMetaM (inferType …) >>= fun ty => liftMetaM (ppExpr …) >>= fun tyPP =>
                     liftMetaM (user name) >>= fun userName => getCompilerState >>= fun st =>
                     liftMetaM (throwError …)        (possibly `>>= fun _ => <join point of the rest>`)
```
-/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

set_option maxHeartbeats 2000000 in
/-- **The body on a free variable**: a `lookupVar` hit, or the recursive
translator's run on a local-context value, or on a changed result of the
`reduce` oracle. (The fourth case, the `Unbound variable` error, has no
successful run.) -/
theorem impl_fvar {rec : TranslateFn} {ctx : CompilerState} {id : FVarId} {hint : String}
    {top named : Bool} {s t : CircuitState} {w : String}
    (h : Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) (Lean.Expr.fvar id)
      hint top named) ctx s w t) :
    (Tools.ShippingBindingsSoundness.visible ctx s.sourceBindings id = some w ∧ t = s) ∨
    (∃ val : Lean.Expr, Returns (rec val hint top named) ctx s w t) ∨
    (∃ reduced : Lean.Expr, (reduced != Lean.Expr.fvar id) = true ∧
      Returns (rec reduced hint top named) ctx s w t) := by
  unfold Rec.translateExprToWireImpl at h
  -- the trace, the call counter, the limit (as `pre_plain`)
  have k0 := returns_trace_then h
  obtain ⟨callN, s1, h1, k1⟩ := Returns.bind k0
  rw [Returns.liftMetaM h1] at k1
  obtain ⟨limit, s2, h2, k2⟩ := Returns.bind k1
  rw [Returns.liftMetaM h2] at k2
  rcases returns_ite k2 with ⟨_, ka⟩ | ⟨_, k3⟩
  · obtain ⟨u, s3, hthrow, _⟩ := Returns.bind ka
    exact (returns_throw hthrow).elim
  -- the profile tick
  have k4 := returns_ite_lift_then k3
  -- F0 / F1: the variable arm; the lookup
  obtain ⟨r, s5, hlook, k5⟩ := Returns.bind k4
  obtain ⟨hr, hs5⟩ := Tools.ShippingTranslateSoundness.lookupVar_returns hlook
  rw [hs5] at k5
  cases r with
  | some wn =>
    obtain ⟨hw, ht⟩ := Returns.pure k5
    refine Or.inl ⟨?_, ht⟩
    rw [hw]
    exact hr.symm
  | none =>
    refine Or.inr ?_
    -- F2: the local-context read
    obtain ⟨iv, s6, hiv, k6⟩ := Returns.bind k5
    rw [Returns.liftMetaM hiv] at k6
    cases iv with
    | some val =>
      -- F3: zeta
      refine Or.inl ⟨val, ?_⟩
      obtain ⟨vis, s7, hvis, k7⟩ := Returns.bind k6
      rw [Returns.liftMetaM hvis] at k7
      have k8 := returns_ite_lift_then k7
      obtain ⟨u1, s9, hmod, k9⟩ := Returns.bind k8
      rw [Returns.liftMetaM hmod] at k9
      obtain ⟨r1, s10, hrec, k10⟩ := Returns.bind k9
      obtain ⟨u2, s11, hmod2, k11⟩ := Returns.bind k10
      rw [Returns.liftMetaM hmod2] at k11
      obtain ⟨hr1, ht⟩ := Returns.pure k11
      rw [hr1, ht]
      exact hrec
    | none =>
      -- F4: the `reduce` oracle
      refine Or.inr ?_
      obtain ⟨vis, s7, hvis, k7⟩ := Returns.bind k6
      rw [Returns.liftMetaM hvis] at k7
      have k8 := returns_ite_lift_then k7
      obtain ⟨u1, s9, hmod, k9⟩ := Returns.bind k8
      rw [Returns.liftMetaM hmod] at k9
      obtain ⟨reduced, s10, hred, k10⟩ := Returns.bind k9
      rw [Returns.liftMetaM hred] at k10
      obtain ⟨u2, s11, hmod2, k11⟩ := Returns.bind k10
      rw [Returns.liftMetaM hmod2] at k11
      rcases returns_ite k11 with ⟨hne, k12⟩ | ⟨_, k12⟩
      · -- the recursive call is the arm's last statement: no bind after it
        exact ⟨reduced, hne, k12⟩
      · -- the `Unbound variable` error: no run
        obtain ⟨ty, s12, _, k13⟩ := Returns.bind k12
        obtain ⟨tyPP, s13, _, k14⟩ := Returns.bind k13
        obtain ⟨un, s14, _, k15⟩ := Returns.bind k14
        obtain ⟨st, s15, _, k16⟩ := Returns.bind k15
        -- (the error is the arm's last statement but not the body's: the
        -- elaborator may have appended the join point of the rest to it)
        first
          | exact (returns_throw k16).elim
          | (obtain ⟨u3, s16, hth, _⟩ := Returns.bind k16
             exact (returns_throw hth).elim)

end Tools.ShippingLegacySem
