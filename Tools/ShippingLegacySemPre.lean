import Tools.ShippingLegacySemSteps2
import Tools.ShippingLegacySemBody

/-! # The body's prefix, walked: `Rec.translateExprToWireImpl` → `Rec.translateExprToWireApp`

**Proved** (`pre_plain`): for an APPLICATION `.app f a` whose head is the
constant `name`, with

* `ImplName name` — `name` fails every name test of the body's inline arms
  (the early operator interception: `signalBinOpOf name = none`, not
  `HAppend.hAppend`; then `OfNat.ofNat`, `Bool.true` / `false`, `OfNat.mk`,
  the wrapper names and suffixes, `Signal.pure` / `lit`, `bundle2`,
  `Signal.map`, `ite` / `dite`, `Decidable.rec` / `casesOn`, `Prod.rec` /
  `casesOn`, `Seq.seq`, `Functor.map`);
* `HasMappedFVar ctx (.app f a)` — the expression contains a free variable
  that the context's `varMap` binds. This is EXACTLY the test the body
  computes before its `whnf` step (`e.find? …`, the same function), as a
  proposition about `e` and `ctx`: when it holds (and the head is not a
  lambda, which a constant head is not), the body does NOT `whnf` the
  expression and goes on with the expression itself. Without it the body
  replaces `e` by an oracle's result, and nothing relates the two;

a successful run of the body on the expression is a successful run of
`Rec.translateExprToWireApp` on the SAME expression, same hint and name flag,
same states, same wire. This is the hypothesis `hpre` of `bodyOutcome_plain`.

No `dsimp` / `simp` / `split` on the program (it is about a thousand lines
with join points): inversion lemmas only.

**Elaborated shape** — OBSERVED from the first build's goal (the nest of join
points is written inline here; the `whnf` test is an `if` whose branches each
bind the expression and call the continuation):

```
trace[…];                                             -- returns_trace_then
liftMetaM (callCounter.modifyGet …) >>= fun callN =>
liftMetaM (… limit …) >>= fun limit =>
if callN > limit then (liftMetaM (throwError …) >>= …) else
if (callN % 10000 == 0) = true then (liftMetaM (… tick …) >>= fun _ => REST) else REST
REST:
match e with | .fvar id => … | _ =>                   -- e = .app f a: reduces
let fn := e.getAppFn; let args := e.getAppArgs;
match fn with | .const instName _ =>                  -- after `rw [hfn]`: reduces
    (match signalBinOpOf instName with | some op => … | _ => J₁)      -- conv whnf, rw
    J₁: match (if instName == ``HAppend.hAppend then … else none) with
        | some (i₁, i₂) => … | _ => J₂                                 -- conv whnf, rw
  | _ => J₂
J₂: match fn with | .const name _ =>
      fourteen `if guard then … else …` on the name                    -- returns_ite each
    | _ => J₃
J₃: getCompilerState >>= fun varMap =>
    if (!hasMappedFvar || isBetaRedex) = true then (liftMetaM (whnf e) >>= K) else (pure e >>= K)
    K: fun e => let fn := e.getAppFn;
    match e with | .app .. => (match fn with | .const _ _ => translateExprToWireApp … | _ => …) | …
```
-/
namespace Tools.ShippingLegacySem
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- **The body's `whnf` test, as a proposition**: some sub-expression of `e`
is a free variable bound in the context's `varMap` — the value the body
computes as `hasMappedFvar`. -/
def HasMappedFVar (ctx : CompilerState) (e : Lean.Expr) : Prop :=
  (e.find? (fun sub =>
    match sub with
    | .fvar fid => ctx.varMap.any (fun (vid, _) => vid == fid)
    | _ => false)).isSome = true

/-- The name tests of the body's inline arms, failing. -/
structure ImplName (name : Name) : Prop where
  binOp : signalBinOpOf name = none
  hAppend : (name == ``HAppend.hAppend) = false
  ofNat : (name == ``OfNat.ofNat) = false
  boolTrue : (name == ``Bool.true) = false
  boolFalse : (name == ``Bool.false) = false
  ofNatMk : (name == ``OfNat.mk) = false
  sigMk : (name == ``Sparkle.Core.Signal.Signal.mk) = false
  sigVal : (name == ``Sparkle.Core.Signal.Signal.val) = false
  bvOfFin : (name == ``BitVec.ofFin) = false
  finMk : (name == ``Fin.mk) = false
  bvOfNat : (name == ``BitVec.ofNat) = false
  bvToNat : (name == ``BitVec.toNat) = false
  sufOfFin : name.toString.endsWith ".ofFin" = false
  sufOfNat : name.toString.endsWith ".ofNat" = false
  sufToNat : name.toString.endsWith ".toNat" = false
  sigPure : (name == ``Sparkle.Core.Signal.Signal.pure) = false
  sigLit : (name == ``Sparkle.Core.Signal.Signal.lit) = false
  bundle2 : (name == ``Sparkle.Core.Signal.bundle2) = false
  sigMap : (name == ``Sparkle.Core.Signal.Signal.map) = false
  notIte : (name == ``ite) = false
  notDite : (name == ``dite) = false
  decRec : (name == ``Decidable.rec) = false
  decCases : (name == ``Decidable.casesOn) = false
  prodRec : (name == ``Prod.rec) = false
  prodCases : (name == ``Prod.casesOn) = false
  seq : (name == ``Seq.seq) = false
  fmap : (name == ``Functor.map) = false

set_option maxHeartbeats 2000000 in
/-- **The body's prefix on a plain application.** -/
theorem pre_plain {rec : TranslateFn} {ctx : CompilerState} {f a : Lean.Expr} {name : Name}
    {us : List Level} (hfn : (Lean.Expr.app f a).getAppFn = .const name us)
    (hi : ImplName name) (hmap : HasMappedFVar ctx (.app f a))
    (hint : String) (top named : Bool) (s t : CircuitState) (w : String)
    (h : Returns (Rec.translateExprToWireImpl (fun e h t n => rec e h t n) (.app f a) hint top
      named) ctx s w t) :
    Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) (.app f a) hint named)
      ctx s w t := by
  unfold Rec.translateExprToWireImpl at h
  -- the trace, the call counter, the limit
  have k0 := returns_trace_then h
  obtain ⟨callN, s1, h1, k1⟩ := Returns.bind k0
  rw [Returns.liftMetaM h1] at k1
  obtain ⟨limit, s2, h2, k2⟩ := Returns.bind k1
  rw [Returns.liftMetaM h2] at k2
  -- over the limit: an error, no run
  rcases returns_ite k2 with ⟨_, ka⟩ | ⟨_, k3⟩
  · obtain ⟨u, s3, hthrow, _⟩ := Returns.bind ka
    exact (returns_throw hthrow).elim
  -- the profile tick
  have k4 := returns_ite_lift_then k3
  -- the expression is an application, not a variable; its head is `name`
  rw [hfn] at k4
  -- The early operator interception is two `match`es on an `Option` whose
  -- discriminants mention the head's name only AFTER the `match` on the head
  -- is reduced (the name is bound by that `match`). `whnf` on the program
  -- alone reduces its head that far — and no further: it stops at the stuck
  -- `match` — and the discriminant is then rewritten to `none`.
  -- (`returns_optCases` did not unify with the auxiliary matcher: first build.)
  conv at k4 => arg 1; whnf
  rw [hi.binOp] at k4
  conv at k4 => arg 1; whnf
  rw [hi.hAppend, if_neg Bool.false_ne_true] at k4
  -- the fourteen name-guarded inline arms
  rcases returns_ite k4 with ⟨hc, _⟩ | ⟨_, g1⟩
  · exact absurd hc (by
      simp only [hi.ofNat, Bool.false_and, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g1 with ⟨hc, _⟩ | ⟨_, g2⟩
  · exact absurd hc (by simp only [hi.boolTrue, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g2 with ⟨hc, _⟩ | ⟨_, g3⟩
  · exact absurd hc (by simp only [hi.boolFalse, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g3 with ⟨hc, _⟩ | ⟨_, g4⟩
  · exact absurd hc (by
      simp only [hi.ofNatMk, Bool.false_and, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g4 with ⟨hc, _⟩ | ⟨_, g5⟩
  · exact absurd hc (by
      simp only [hi.sigMk, hi.sigVal, hi.bvOfFin, hi.finMk, hi.bvOfNat, hi.bvToNat,
        hi.sufOfFin, hi.sufOfNat, hi.sufToNat, Bool.or_self, Bool.false_or, Bool.or_false,
        Bool.false_and, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g5 with ⟨hc, _⟩ | ⟨_, g6⟩
  · exact absurd hc (by
      simp only [hi.sigPure, hi.sigLit, Bool.or_self, Bool.false_and, Bool.false_eq_true,
        not_false_eq_true])
  rcases returns_ite g6 with ⟨hc, _⟩ | ⟨_, g7⟩
  · exact absurd hc (by
      simp only [hi.bundle2, Bool.false_and, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g7 with ⟨hc, _⟩ | ⟨_, g8⟩
  · exact absurd hc (by
      simp only [hi.sigMap, Bool.false_and, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g8 with ⟨hc, _⟩ | ⟨_, g9⟩
  · exact absurd hc (by
      simp only [hi.notIte, hi.notDite, Bool.or_self, Bool.false_eq_true,
        not_false_eq_true])
  rcases returns_ite g9 with ⟨hc, _⟩ | ⟨_, g10⟩
  · exact absurd hc (by
      simp only [hi.decRec, hi.decCases, Bool.or_self, Bool.false_eq_true,
        not_false_eq_true])
  rcases returns_ite g10 with ⟨hc, _⟩ | ⟨_, g11⟩
  · exact absurd hc (by
      simp only [hi.prodRec, hi.prodCases, Bool.or_self, Bool.false_eq_true,
        not_false_eq_true])
  rcases returns_ite g11 with ⟨hc, _⟩ | ⟨_, g12⟩
  · exact absurd hc (by
      simp only [hi.seq, Bool.false_and, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g12 with ⟨hc, _⟩ | ⟨_, g13⟩
  · exact absurd hc (by
      simp only [hi.seq, Bool.false_and, Bool.false_eq_true, not_false_eq_true])
  rcases returns_ite g13 with ⟨hc, _⟩ | ⟨_, g14⟩
  · exact absurd hc (by
      simp only [hi.fmap, Bool.false_and, Bool.false_eq_true, not_false_eq_true])
  -- the context read, then the `whnf` test (an `if` whose two branches bind
  -- the expression and continue): a mapped variable, no beta-redex
  obtain ⟨c0, s8, hread, k8⟩ := Returns.bind g14
  obtain ⟨hc0, hs8⟩ := Returns.read hread
  rw [hc0, hs8] at k8
  rcases returns_ite k8 with ⟨hc, _⟩ | ⟨_, kelse⟩
  · exact absurd hc (guard_not hmap (by first | rfl | (rw [hfn]; rfl)))
  obtain ⟨e', s9, hp, k9⟩ := Returns.bind kelse
  obtain ⟨he', hs9⟩ := Returns.pure hp
  rw [he', hs9] at k9
  -- The continuation applied to the expression itself (second build: `k9` is
  -- an un-reduced `(fun e => have fn := e.getAppFn; match e with …) (f.app a)`,
  -- so `hfn` has nothing to rewrite yet). Reduce the HEAD of the program: the
  -- beta step, the `have`, the `match` on the application; it stops at the
  -- inner `match` on `(f.app a).getAppFn`, which `hfn` then turns into the
  -- constant. What is left is `Rec.translateExprToWireApp` on the expression,
  -- with the translator eta-expanded once more (`fun e h t n => (fun e h t n
  -- => rec e h t n) e h t n`), which is the goal's by eta.
  conv at k9 => arg 1; whnf
  rw [hfn] at k9
  show Returns (Rec.translateExprToWireApp (fun e h t n => rec e h t n) (Lean.Expr.app f a) hint
    named) ctx s w t
  exact k9

end Tools.ShippingLegacySem
