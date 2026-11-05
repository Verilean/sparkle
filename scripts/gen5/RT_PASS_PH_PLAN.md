# RT pass_ph plan (`sparkle-rt-pass-ph`, parent `sparkle-gen5-dg-readertrace`)

base: par/rt-pass-total-b 2df5d4d7. Status: plan + decision request; no Lean written. Conditional / intermediate: `pass_ph` is NOT proved.

## 0. Finding (blocks the fixed statement)

The fixed statement (`0e16378b:Tools/ShippingGen5ReaderTraceInlineCompose.lean` 8-24) is
`PassPh env := DeclValuePh env -> RecRulePhU env -> forall isUser e, NoPh e -> BvarLt 0 e -> NoPh (pass ..) /\ BvarLt 0 (pass ..)`
with no other hypothesis. In this investigation no route was found to prove it from those two hypotheses alone, because `pass` reaches core externs/opaques that have no content in the logic:

| call in MachRecUnfold (2df5d4d7) | reached from | extern / opaque | agreement hypothesis that would be needed |
|---|---|---|---|
| `Expr.instantiateLevelParams` | `iota` (_sparseCasesOn, rec arms), `reduceMatcher?`, `unfoldCall?` | `Expr.replace` (`lean_replace_expr`) | `ReplaceAgrees` (U-1, `0e16378b:Tools/Assume/AbbrevExtern.lean:73`) |
| `Expr.beta` (`v.beta args`, `f.beta args` in `headBetaM`) | `unfoldCall?`, `headBetaM` | `betaRev` (core `partial def`) + externs `instantiate`/`instantiateRange` | not covered: U-2 `HeadBetaAgrees0` is about `Expr.headBeta` on `NoPh/BvarLt 0` inputs; `Expr.beta f args` with args needs the same family (a `betaRev`-with-args agreement or a preservation law) |
| `Expr.instantiate1` (`b.instantiate1 v'`, `alt`/`rest` none) | `passStep` letE arm, `listLit?` letE arm | extern | `Inst1Agrees` (T1L-51, `Tools/ShippingLetsExternSpec.lean:121`, already in the ledger) |
| `Expr.instantiate` via `mkAppN`/`extract` | none (structural) | - | none |

So any proof needs these as theorem hypotheses. That changes the fixed statement (PassPh would take ReplaceAgrees / Inst1Agrees / a beta agreement), or adds new T1 laws. Both are outside what I may do (no new law / no statement change without user approval). Also `ReplaceAgrees`, `HeadBetaAgrees0`, `AbbrevS1`, `Direct2`, `InlineP1` are not in this base (they live in the rt-inline-compose lineage, `0e16378b`); the base has `Inst1Agrees`/`LiftAgrees` only.

(This is "no route found", not a proof of impossibility. It is a reading of the definitions: the externs are `opaque` and a preservation claim about them is not derivable without a spec.)

## 1. Decomposition (what would be proved once the hypotheses are settled)

Hypotheses H := DeclValuePh, RecRulePhU, plus agreement set A (above). `G e := NoPh e = true /\ BvarLt 0 e = true`; most lemmas generalise to `BvarLt L`.

* `headBeta`-style: `beta_good : G f -> (forall a in args, G a) -> G (f.beta args)` (needs A_beta). `headBetaM_good : G e -> headBetaM n e = .ok e' -> G e'` (induction on fuel; `.error` branch vacuous).
* `ilp_good : G e -> G (e.instantiateLevelParams ps ls)` (needs ReplaceAgrees; rnc_ph2 generalisation from `RT_RECRULE_FREEZE.md` section 4).
* `rec_arm_goodU` (RT_RECRULE_FREEZE 1.2, scratch exists in bab003d9's freeze text).
* `ctorApp_good : G e -> ctorApp? .. e = some (cv, fs) -> forall f in fs, G f` (`natLitE` is closed NoPh).
* `iota_good : G e -> iota env nl fuel e = some(.ok r) -> G r`, by fuel induction. `stuck` (none) and `.error` are vacuous; fuel 0 returns `stuck`.
* `reduceMatcher?_good`, `reduceHead_good` (fuel 0 -> stuck; letE arm keeps `v`, rebuilds with `b'` under BvarLt (L+1)).
* `betaAll_good` / `betaSpine_good` (mutual, by the `(fuel, sizeOf, k)` measure; fuel 0 re-entry -> `.error`).
* `listLit?_good : result elements are G` (zeta step uses Inst1Agrees + inst1Spec_* lemmas; zipIdx builds `natLitE`).
* `evalNode?_good` (returns subterm `a`/`b`, `mkListLit`, `xs.headD d`).
* `unfoldCall?_good` (DeclValuePh on the `_sunfold` value, ilp_good, beta_good, reduceHead_good, betaAll_good).
* `relevantClosure`: pure Bool, never changes the expression; no preservation lemma needed (it only selects whether `pass` is called). `relevant` likewise.
* `passM` memo invariant: every `(k, v)` in the memo satisfies `G k -> G v`; `passM/passStep/passSpine` jointly by the same measure; `pass_ph` follows from `passWith` with empty memo.

Estimated size when unblocked: one new file, ~15 lemmas, 500-800 lines.

## 2. Fuel-exhausted branches

`pass` / `passWith` return `Except String Expr`. On fuel exhaustion they return `.error msg` (never a silent cut). `PassPh` as stated applies `NoPh`/`BvarLt` to `pass ...` which is an `Except`, not an `Expr` (the 0e16378b statement was written against the partial `pass : Expr`). So the fixed statement does not typecheck against 2df5d4d7's `pass` (`Except String Expr`) unless a coercion/match is added (e.g. "on `.ok r`, G r"; `.error` vacuous). This is a second reason the statement needs a decision; the sensible repair is `forall r, pass .. = .ok r -> G r` (fuel-exhausted `.error` is vacuous; stuck steps leave the term unchanged and are covered by the lemmas above).

## 3. RecRulePhU placement

Defined only in `Tools/ShippingGen5PassPh.lean` as a hypothesis (statement copied from 0e16378b); not registered in `Tools/Assume/`. Registration and ledger counting (FG +1 vs extension of N1-a) remain the reviewer's decision (RT_RECRULE_FREEZE section 5).

## 4. Decision requested (see also `RT_PASS_PH_DECISION.md`)

1. Allow `PassPh` to carry the agreement hypotheses (ReplaceAgrees, Inst1Agrees, a beta agreement) - ledger: ReplaceAgrees/HeadBetaAgrees0 are already candidates in the inline-compose lineage; the beta-with-args agreement is new (T1 +1 candidate, not counted).
2. Change the result shape to `pass .. = .ok r -> G r`.
3. Re-base on the inline-compose lineage (or merge it) so `ReplaceAgrees` exists.

Ledger: FG 94 / T1 54 (this unit FG -0 +0 / T1 -0 +0); nothing registered or counted.
