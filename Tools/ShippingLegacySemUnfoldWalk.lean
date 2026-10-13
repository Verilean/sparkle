import Tools.ShippingLegacySemUnfold
import Tools.ShippingLegacySemSteps

variable {tenv : Lean.Environment}

/-! # `handleDefinitionUnfold` on a plain head, walked

**Proved** (`unfoldSpec_plain`): `UnfoldSpec rec ctx e name` from
`PlainHead name` — for a head that is neither tagged nor a structure
projection in the environment the run reads, a successful run of
`Rec.handleDefinitionUnfold` returning `some w` has an `UnfoldOutcome`
(`Tools/ShippingLegacySemUnfold.lean`): the inline attempt's wire, or the
attempt returned none and left the state (the sub-module path).

The walk stops at the attempt: `inline_tail` needs only that the handler
returns the attempt's wire when there is one. The sub-module synthesis, the
argument translations and the instance emission after a failed attempt are
not entered.

**Expected elaborated shape** of `Rec.handleDefinitionUnfold tr e name args
hint named` (NOT observed), join points inlined by `dsimp only`:

```
CompilerM.liftMetaM (try … catch _ => pure false) >>= fun isValidDef =>
if (!isValidDef) = true then pure none else
CompilerM.liftMetaM getEnv >>= fun env =>
if isHardwareModule env name = true then (debug hook …; REST) else REST
  where REST =
match env.getProjectionStructureName? name with
| some structName => … (the projection branch; ends in `pure none`)
| none =>
  if isHardwareModule env name = true then (tagged: sub-module directly) else
  Lean.isTracingEnabledFor cls >>= fun b =>
  if b = true then Lean.addTrace cls msg >>= fun _ => TAIL else TAIL
    where TAIL =
  Rec.tryInlineUnfold … e hint named >>= fun q =>
  match q with
  | (some w, _) => pure (some w)
  | (none, lastFail) => (try … catch …) >>= fun subResult? => …
```

(Round 6: no `dsimp` — the join points are NOT inlined; each `have __do_jp`
is instantiated by the unifier when the next inversion lemma is applied.)

Steps, in order, each a place the build can stop: (1) the validity bind;
(2) `split` on `!isValidDef` — the `then` branch returns `none`, not
`some w`; (3) the environment bind and `PlainHead`; (4) the two tag tests and
the projection test rewritten and reduced; (5) the two trace actions
(`Tools/ShippingLegacySemTrace.lean`); (6) `inline_tail`, whose side goal is
that the `match` on `(some w', _)` IS `pure (some w')` (`rfl`). -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

set_option maxHeartbeats 1000000 in
/-- **`Rec.handleDefinitionUnfold` on a plain head.** -/
theorem unfoldSpec_plain {rec : TranslateFn} {ctx : CompilerState} {e : Lean.Expr}
    {name : Name} (hplain : PlainHead tenv name) : UnfoldSpec rec ctx e name := by
  intro hint named s t w h
  unfold Rec.handleDefinitionUnfold at h
  -- No `dsimp` / `simp` / `split` on the handler (the first build ran out of
  -- simp steps there): every step is an inversion lemma, and the unifier
  -- does the zeta / beta / matcher reduction it needs at the head.
  -- (1) is the declaration a definition? (an oracle)
  obtain ⟨valid, s1, hv, k1⟩ := Returns.bind h
  rw [Returns.liftMetaM hv] at k1
  -- (2) not a definition: `none` is returned, not `some w`
  rcases returns_ite k1 with ⟨_, ka⟩ | ⟨_, kb⟩
  · exact absurd (Returns.pure ka).1 (by intro hh; cases hh)
  -- (3) the environment
  obtain ⟨env, s2, henv, k2⟩ := Returns.bind kb
  obtain ⟨henvM, hs2⟩ := returns_liftMetaM henv
  rw [hs2] at k2
  obtain ⟨hnotTag, hproj⟩ := hplain.2 env henvM
  -- (4a) the debug hook of a tagged head
  rcases returns_ite k2 with ⟨hc, _⟩ | ⟨_, k3⟩
  · rw [hnotTag] at hc
    cases hc
  -- (4b) not a projection; (4c) not opted into a sub-module
  rw [hproj] at k3
  rcases returns_ite k3 with ⟨hc, _⟩ | ⟨_, k4⟩
  · rw [hnotTag] at hc
    cases hc
  -- (5) the trace of the inline branch
  have k5 := returns_trace_then k4
  -- (6) the attempt, and its wire returned
  refine inline_tail ?_ k5
  intro w' q2
  rfl

end Tools.ShippingLegacySem
