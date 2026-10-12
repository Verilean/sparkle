import Tools.ShippingLegacySemBinder
import Tools.ShippingLegacySemThrows

/-! # The legacy binder walk on one `bits n` binder, WITHOUT the skipped outcome

`bindInputsLegacy_one` (`Tools/ShippingLegacySemBinder.lean`) has two
outcomes: the certified walk, or the binder skipped. The skip is created at
ONE place (`Sparkle/Compiler/Elab.lean`, `bindInputsLegacy`, lines 2135–2138):

```
let isHWArg ← try
  let _ ← inferHWTypeFromSignal binderType
  pure true
catch _ => pure false
```

`isHWArg = false` needs the handler to run, and the handler runs only on an
exception that the `try`'s body threw and that `Core.tryCatch` hands over
(not an interrupt, not a runtime exception). The body is the oracle followed
by `pure true`; `pure` does not fail. So the skip needs a CATCHABLE failure
of `inferHWTypeFromSignal binderType`.

**Defined here**: `InfersNoCatch T` — every failing run of
`inferHWTypeFromSignal T` (from any compiler context and builder state) ends
in an interrupt or a runtime exception. A premise about ONE oracle call on
ONE type, of the same class as `InfersBits T n` (which speaks of its
returning runs): together they say what the oracle does on `T`. It is stated
with "no catchable failure" and not "never fails" because the latter is
false of some worlds (an interrupt, the heartbeat limit) and is more than
the walk needs: `Core.tryCatch` rethrows those two kinds without running the
handler.

**Proved here**: `bindInputsLegacy_one_bound` — with `InfersNoCatch d0.type`
added to the premises of `bindInputsLegacy_one`, a successful run of the
legacy walk IS a run of the certified walk over
`[((d0.userName, .bits n), id)]`. No second outcome.

Between "the oracle returned" and "the port is bound" there is no further
step that could skip: after `isHWArg = true` the walk calls the oracle a
second time (line 2140; a returning run, so `InfersBits` gives its result;
a failing run is not a successful run of the walk) and then `bindInputPort`
unconditionally (line 2141).

The proof is `bindInputsLegacy_one_raw`'s (built), with step S4 inverted by
`returns_tryCatch_throws` (`Tools/ShippingLegacySemThrows.lean`) and the
`else` branch of S5 closed by `isHWArg = true`. Program shapes: as listed in
`Tools/ShippingLegacySemBinder.lean` (S0–S6), all observed there. -/
namespace Tools.ShippingLegacySem
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- The hardware-type oracle has no CATCHABLE failure on `T`: every failing
run ends in an interrupt or a runtime exception (which `try … catch` does not
catch). -/
def InfersNoCatch (T : Lean.Expr) : Prop :=
  ∀ (ctx : CompilerState) (s : CircuitState) (ex : Exception),
    Throws (inferHWTypeFromSignal T) ctx s ex → (ex.isInterrupt || ex.isRuntime) = true

/-- **The legacy walk on one variable, the skip excluded**, the variable given by an equation on
`xs[0]` (so that the proof never rewrites the program's own `xs[0].fvarId!`). -/
theorem bindInputsLegacy_one_bound_raw {xs : Array Lean.Expr} {id : FVarId} {d0 : LocalDecl}
    {n : Nat} {mctx : Meta.Context} {k : CompilerM String} {ctx : CompilerState}
    {s t : CircuitState} {r : String}
    (hsz : xs.size = 1)
    (hx : ∀ h : 0 < xs.size, (xs[0]'h).fvarId! = id)
    (hfind : mctx.lctx.find? id = some d0)
    (hsig : SignalTestFrame d0.type) (hinf : InfersBits d0.type n)
    (hnt : InfersNoCatch d0.type)
    (hrun : RunsIn (bindInputsLegacy [] false xs 0 k) mctx ctx s r t) :
    Returns (bindMixedCertifiedInputs k [((d0.userName, MixedGateBinder.bits n), id)])
      ctx s r t := by
  -- (no `rw [hsz]` on these goals: `rw` closes a goal it can prove by `rfl`,
  -- and the next tactic would then find no goal)
  have h0 : 0 < xs.size := by
    first | omega | exact Nat.lt_of_lt_of_eq Nat.zero_lt_one hsz.symm
  have hle : xs.size ≤ 0 + 1 := by
    first | omega | exact Nat.le_of_eq hsz
  -- S0
  first
    | unfold bindInputsLegacy at hrun
    | rw [bindInputsLegacy] at hrun
  have a1 := RunsIn.dite_pos hrun h0
  -- S1: the declaration, read from the context
  obtain ⟨decl, s1, hd, a2⟩ := RunsIn.bind a1
  obtain ⟨hdm, hs1⟩ := RunsIn.liftMetaM hd
  have hde : decl = d0 := getDecl_runsIn_find (hx h0) hfind hdm
  rw [hs1] at a2
  rw [hde] at a2
  -- from here on the context is not read: `Returns`
  have b0 := RunsIn.returns a2
  -- S2: no parameter; the Signal test
  first
    | (obtain ⟨sg, s2, hsg, b1⟩ := Returns.bind b0)
    | (simp only [List.find?, Option.map] at b0
       obtain ⟨sg, s2, hsg, b1⟩ := Returns.bind b0)
  have hs2 : s2 = s := hsig ctx s s2 sg hsg
  rw [hs2] at b1
  -- S3: not symbolic
  rcases returns_if b1 with ⟨hsym, _⟩ | ⟨_, b2⟩
  · exact absurd (show false = true from hsym) Bool.false_ne_true
  -- S4: the `try` around the type oracle. Its body returned `true` from the
  -- same state; its handler did not run: that needs a CATCHABLE failure of
  -- `inferHWTypeFromSignal ty >>= fun _ => pure true`, i.e. of the oracle
  -- (`pure` does not fail), which `hnt` excludes
  obtain ⟨hwb, s3, htry, b3⟩ := Returns.bind b2
  have hs3 : s3 = s ∧ hwb = true := by
    rcases returns_tryCatch_throws htry with hbody | ⟨ex, hthrow, hcatch, _⟩
    · obtain ⟨hw0, s4, hi0, hp0⟩ := Returns.bind hbody
      obtain ⟨_, hs4⟩ := hinf ctx s s4 hw0 hi0
      rw [hs4] at hp0
      obtain ⟨hb, hs⟩ := Returns.pure hp0
      exact ⟨hs, hb⟩
    · rcases Throws.bind hthrow with hinfer | ⟨a0, s4, _, hpure⟩
      · exact absurd (hnt ctx s ex hinfer) hcatch
      · exact (Throws.pure hpure).elim
  rw [hs3.1] at b3
  -- S5: `isHWArg` is `true`
  rcases returns_if b3 with ⟨_, c1⟩ | ⟨hF, _⟩
  · -- the port is bound
    obtain ⟨hw1, s5, hi1, c2⟩ := Returns.bind c1
    obtain ⟨hw1eq, hs5⟩ := hinf ctx s s5 hw1 hi1
    rw [hs5] at c2
    rw [hw1eq] at c2
    -- S6
    have c3 := bindInputPort_done_returns c2 hle
    have c4 := bindInputPort_congr_id (hx h0) c3
    rw [bindMixed_one_bits]
    exact c4
  · -- the skip branch: excluded
    exact absurd hs3.2 hF

/-- **The legacy binder walk on one `bits n` binder.** In a context whose
local context declares `id` as `d0`, a successful run of the legacy walk over
`#[.fvar id]` is a run of the certified walk over
`[((d0.userName, .bits n), id)]` — when the type oracle has no catchable
failure on the binder's type (`InfersNoCatch`), so that the walk's `try`
cannot yield `false`. -/
theorem bindInputsLegacy_one_bound {id : FVarId} {d0 : LocalDecl} {n : Nat} {mctx : Meta.Context}
    {k : CompilerM String} {ctx : CompilerState} {s t : CircuitState} {r : String}
    (hfind : mctx.lctx.find? id = some d0)
    (hsig : SignalTestFrame d0.type) (hinf : InfersBits d0.type n)
    (hnt : InfersNoCatch d0.type)
    (hrun : RunsIn (bindInputsLegacy [] false #[Lean.Expr.fvar id] 0 k) mctx ctx s r t) :
    Returns (bindMixedCertifiedInputs k [((d0.userName, MixedGateBinder.bits n), id)])
      ctx s r t := by
  have hsz : (#[Lean.Expr.fvar id] : Array Lean.Expr).size = 1 := by
    first | rfl | simp
  have hx : ∀ h : 0 < (#[Lean.Expr.fvar id] : Array Lean.Expr).size,
      ((#[Lean.Expr.fvar id] : Array Lean.Expr)[0]'h).fvarId! = id := by
    intro h
    first | rfl | simp [Lean.Expr.fvarId!] | (simp; rfl)
  exact bindInputsLegacy_one_bound_raw hsz hx hfind hsig hinf hnt hrun

end Tools.ShippingLegacySem
