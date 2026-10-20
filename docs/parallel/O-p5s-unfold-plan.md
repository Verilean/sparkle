# Plan: discharging the unfolding branch of `p5s` without a law about opaque code

> **Reviewer corrections (review a230f9d1) — binding over the text below.**
> 1. p5p1 shows only that the BACKWARD reading (declared ⇐ inlined) fails on selected TYPES. It does NOT show
>    that a real parent + child run reaches all premises of `LocalStruct.p5s`; "counterexample to the run theorem"
>    is NOT claimed until a concrete actual-run alias / folded-width probe exists.
> 2. "`passF 0` = old `partial`" is a RUNTIME COMPATIBILITY argument (same body by source review), not a kernel
>    equivalence proof and not a total runtime guarantee; that boundary stays OPEN.
> 3. Structural `replaceNoCache` vs the cached extern `Expr.replace`: agreement and performance need their own
>    evidence; OPEN (the "≡ extensionally" line below is an expectation, not a fact).
> 4. G3 / `readSkel` acceptance restriction is NOT authorized for production ("every well-typed hardware type
>    satisfies it" is unproved, esp. dependent / parameterized types). New exclusion guards (G1/G2) are NOT adopted
>    as behaviour-preserving because expected module classification makes them redundant: candidate lemmas take
>    the environment facts as EXPLICIT premises (localisation) instead.
> 5. Authorized now: ISOLATED candidate first increment U1c + U3 + L2 + U5a, no production switch, starting with
>    forward single-Signal result-kind preservation on `forallE` types. No new trusted laws; no refusal fallback
>    as acceptance proof. Gate-check discharge and `Tests.AllTests` take precedence over widening candidate scope.

Planning worker O-UNFOLD, branch `par/o-unfold`, base `13f4b393`. SOURCE REVIEW ONLY: nothing here was built,
no Lean was run. Sketch: `docs/parallel/sketch/InlTypeCand.lean` (not built, not registered).

Ruling this round: nothing is added to `RefLaws` (Tools/ShippingChildInv.lean 333) or to any trust or
allowed-premise list. That excludes `envGet`/`envFrame`, `InstAgree` and any `passM`/`relevantClosure`
"unfold law".

## 0. What actually blocks `p5s` (corrections to the C record)

`LocalStruct.p5s` (Tools/ShippingEnvLocal.lean) says: when the run unfolds,
`declOuts? (structEnv envR) (userInliner envR dD.type) = some o → declOuts? (structEnv envR) dD.type = some o`.
`userInliner` (Elab.lean 3387) on a type is
`inlFoldNat (inlAbbrevs env 4 X)`, with `X = rounds 64 e1` if `relevantClosure …` and `X = e1` otherwise, where
`e1 = inl e` (`inlineDefs`).

| piece | in the logic | does `p5s` need an equation for it? |
|---|---|---|
| `MachRecUnfold.relevantClosure` (MachRecUnfold.lean 283) | `partial def`. Its inner `go` already recurses structurally on `fuel` (100000), so `partial` can be dropped with no change in behaviour. But it reads `Expr.getUsedConstants` = `foldConsts`, which is `@[implemented_by] opaque` (Lean/Util/FoldConsts.lean 51), so even a total version has no computable value | **No.** It only picks between two branches. A proof does `cases h : relevantClosure …` and handles both branches |
| `MachRecUnfold.passM` / `pass` (243, 273) | `partial def` | **Yes, but only on the input shape.** We need `pass env _ _ (.forallE …) = .forallE …`, which is the trivial arm `\| e => pure e` after an empty-memo lookup |
| `==` on `Expr` in `rounds` and `inlAbbrevs` | `opaque Expr.eqv` (Expr.lean 809) | **No.** Case-split on the Bool. Both outcomes are handled, using induction where needed (`rounds k e = e` when `pass e = e` and `inl e = e`) |
| `Expr.replace` in `inlAbbrevs` (3376) | `replaceImpl`, `@[extern "lean_replace_expr"] opaque` (Util/ReplaceExpr.lean 16) | **Yes, unavoidably.** Nothing is known about its result. This blocker was MISSED in the C record (B-readerinv.md §3 already had it for P5) |
| `Expr.headBeta` (in `inlAbbrevs`) | a `def`. It calls `partial betaRev` only when the head is a lambda | No, on `.forallE` inputs: `isHeadBetaTargetFn false (.forallE …) = false` |
| `inlineDefs`, `inlFoldNat`, `inlSpine`, `inlMap` | total `def`s | equations exist. `inlineDefs` returns a `.forallE` input unchanged (it never descends into a `forallE`) |

So the caller's premise that "the unfolding branch needs an equation for `relevantClosure`/`passM`" is
half right. `relevantClosure` is a red herring. `passM` is needed only for its trivial arm. `replaceImpl` is
the hard blocker.

**Second finding: `p5s` as stated is FALSE on accepted inputs.** *(Integrator probe p5p1, 2026-10-19, exit 0, at
13f4b393+fb5ffe0b: `declOuts? (structEnv env) ty` vs `declOuts? (structEnv env) (userInliner env ty)` on the full
declaration types — `fAlias : … → Pair` (abbrev of a product): declared `none`, inlined `some`; `fSum` over
`BitVec (4+4)`: declared `none`, inlined `some`; control `fPlain` (product written out): both `some`. Evidence on
the reading functions only; that a parent with such a child reaches the unfolding branch was not run.)* Take a child whose result type is written
with an alias, e.g. `abbrev Pair := Signal dom (BitVec 8) × Signal dom Bool` and `f : Signal dom (BitVec 8) → Pair`
(`circuit do` body). The inlined type reads `some (some Prod.mk, [out_0, out_1])`, but the declared type reads
`none` (`machOuts?` meets `.const Pair []`, and `userStructure? Pair = none`). A width written as `BitVec (4+4)` behaves
the same way, because `inlFoldNat` folds the sum and `canonicalNatLitValue?` only accepts literals. The `inlAbbrevs`
pass exists precisely to make such types read (TODO 1401). So **no compiler change can make the present
`p5s` field provable for every run.** The field has to be restated in the direction that is true:

* **forward** (`p5sF`): if the declared type reads `o`, the inlined type reads `o`. P5At
  (ShippingCallWidthsChildReal.lean 147) already has this direction for result kinds.

The consumer (`structRes_of_declOuts`, StructRes.lean) then needs the declared reading, and it gets it from
the parent's reading of `instRes ty args`, read backwards (§2, ISC).

**Third finding: no environment-free theorem exists without guards.** In an abstract `envR`,
`userAbbrev? envR BitVec` (or `Bool`, `Nat`, `instOfNatNat`) may be `some`, and `userStructure? envR Signal`
may be `some`. Either can change a successful reading, e.g. `Bool` aliased to `BitVec 1` changes `.bool` into `.bits 1`.
Two ways to rule this out:

* environment facts as premises: localisation, not elimination;
* env-free exclusion guards that are redundant in every real environment. These are constants of
  `Init`/`Sparkle`, so `inlUserModule` is already false for them. This is the guard route G1/G2 below.

## 1. Options

Common notation: `fwd` = `declOuts? senv ty = some o → declOuts? senv (userInliner env ty) = some o`.

### (a) Total `relevantClosure` / `passM` (fuel; on exhaustion, exactly the old code)

* `relevantClosure`: drop `partial`. Output is identical (same body), and the equation comes by `unfold`. **Gain: none**,
  because its value is opaque through `foldConsts` and it is not needed. Not recommended: it only creates drift.
* `passM` → `passF : Nat → Expr → StateM (HashMap Expr Expr) Expr`, with `passF 0 e = passM e` (the ORIGINAL
  partial def) and `passF (n+1)` = the body of `passM` with its recursive calls going to `passF n` (sketch U1a).
  *Output identity on all inputs*: at runtime a compiled `partial def` is its body. By induction on `n`,
  `passF n e s = passM e s`, with the same memo operations in the same order. Fuel exhaustion runs the old code, so
  the result is identical even there. (A fuel version that returns `e` at 0 would NOT be identical. Rejected.)
  *Equations*: `passF (n+1) e = …` by `unfold`/`simp only [passF]`. For `.forallE`, add
  `Std.HashMap.getElem?_empty`, which needs only `BEq`/`Hashable` (v4.32.1 Std/Data/HashMap/Lemmas.lean 256),
  important because `BEq Expr` is the opaque `eqv`.
* **Alone, (a) does not discharge `p5s`**: `inlAbbrevs` still goes through `replaceImpl`. With the additions
  below, (a) becomes (a′).

### (a′) RECOMMENDED: the inliner's type path gets equations (passF + structural replace on `.forallE` + guards)

Compiler change (new file + small Elab hunks; prepared as a patch, applied to production only after a ruling):

1. `passT := (passF … passDepth e).run' {}` replaces `MachRecUnfold.pass` in `userInliner.rounds`.
2. `abbrevStep env e := if e.isForall then e.replaceNoCache f else e.replace f` in `inlAbbrevs`
   (`replaceNoCache` is a structural `def`, ReplaceExpr.lean 23). Values keep the cached extern `replace`, so no
   DAG blow-up on unfolded values (memory note "inliner pass compile time"). Types are small trees.
3. **G1** `userAbbrev?` excludes `[BitVec, Bool, Nat, instOfNatNat]`.
4. **G2** `userStructure?` excludes `[Sparkle.Core.Signal.Signal, HAdd.hAdd, HSub.hSub]` (Signal: so NS holds
   in every environment; HAdd/HSub: the `inlFoldNat` corner where the result head itself is a foldable sum).
5. (P5S increment only, optional) **G3** `instSignatureS?` also requires `readSkel ci.type`: no loose bvar at a
   reading position of the result body (head of the result body, Prod components' heads, width literals). Every
   well-typed hardware type satisfies it. It makes the converse-substitution premise's side condition derivable.

*Acceptance / output identity* (a source argument, not a proof; the old code is opaque, so no proof is possible):

* passF ≡ passM by construction (above);
* `replaceNoCache f e` ≡ `replace f e` extensionally (the extern is the cached form of the same traversal);
* G1/G2/G3 never fire in a real environment: G1/G2 because those constants come from `Init`/`Sparkle`, so
  `inlUserModule` is already false; G3 by typing.

Evidence to collect: the fixed-list small shadow (U2: old copies vs patched, every declaration of a fixed list,
values AND types, plus `entryConst`), and a compile-time check (Fp12MulHWTest ≈ 23 s baseline, the Keccak sponge).
**No input is refused.** The guards only make the code ignore names that real environments never treat as user
abbreviations or structures.

*Proof churn*: `userInliner` is never unfolded in Tools/Tests (grep: 0 sites). `userAbbrev?` is never mentioned.
`userStructure?` is never unfolded. `instSignatureS?` (G3 only) needs `instSignatureS?_some` re-proved. Drift: the
OldEqV snapshot / `oldeqv_drift.py` must record the Elab change deliberately (ruling 2026-10-16).

Exact statements (the candidate names are proposals; after the switch, the production names via `rfl`):

```lean
-- U3 (pure Expr facts)
theorem inlineDefs_forall : inlineDefs defs projs inlineDepth (.forallE n d b bi) inlineBudget =
    some (.forallE n d b bi, inlineBudget)
theorem passT_forall : passT env natLit? isUser (.forallE n d b bi) = .forallE n d b bi
theorem rounds_forall (hf : e.isForall = true) : userInliner.rounds env … k e = e   -- case split on `==`
theorem headBeta_forall (hf : e.isForall = true) : e.headBeta = e
theorem inlAbbrevs_forall_inv (P : Expr → Prop) (hstep : ∀ x, x.isForall → P x → P (x.replaceNoCache (abbrevFn env)))
    (hf : e.isForall) (h : P e) : P (inlAbbrevs env n e)                          -- induction on n, case split on `==`
-- U4 (the core; no environment premise once G1/G2 are in)
theorem resKind_userInliner (hf : ty.isForall = true) (h : machResultKind? ty = some k) :
    machResultKind? (userInliner env ty) = some k                                -- L2
theorem declOuts_userInliner (hf : ty.isForall = true) (h : declOuts? (structEnv env) ty = some o) :
    declOuts? (structEnv env) (userInliner env ty) = some o                      -- L1
```

L1's structure case needs `userAbbrev? env S = none` for the result head `S`. That follows from
`(structEnv env).fields S = some _`: `userStructure?` gives `env.find? S = some (.inductInfo _)`, and `userAbbrev?`
only accepts `.defnInfo`. No premise is needed.

Consumers:

```lean
-- P5At (ShippingCallWidthsChildReal 147) for callees with ≥ 1 binder:
def ResDeclFAt (c) (res) : Prop := ∀ … ci dD, RunsTo (getConstInfo c) … ci … → ci = .defnInfo dD →
  machResultKind? dD.type = some res ∧ dD.type.isForall = true         -- ResDeclAt + arity (same class)
theorem p5At_of_resDeclF : ResDeclFAt mref cref c res → P5At mref cref c res
-- P5S: restated forward, and the consumer rewired
structure InstSubstC : Prop where   -- converse reading through instantiate1; same extern boundary as InstSubst
  outsC : ∀ senv b a o, readSkel b = true → machOuts? senv (b.instantiate1 a) = some o → machOuts? senv b = some o
theorem structResAt_of_partsF (IS : InstSubst) (ISC : InstSubstC)
    (DR : DeclTypeReadAt mref cref envP c) (FA : FieldsAt mref cref envP c) :
    StructResAt mref cref (structEnv envP) c          -- no NS (G2), no P5S, for calls with ≥ 1 argument
```

*Proof of `structResAt_of_partsF`, entry `k`, call with args `a :: as`.*

1. `instRes` needs a `forallE` for each argument (`instRes_cons_forall`; any other head gives `none`), so `ty` is a `forallE`.
2. `DR` gives `ty = dD.type`.
3. The parent's `machOuts? senvP resTy = some (some ctor, fields)` goes back through `instRes` by `ISC`, giving the declared reading. `readSkel ty` comes from G3 via `instSignatureS?_some`.
4. `FA` / `outs_congr` move that reading from `senvP` to `senvC`.
5. **L1** carries it to the inlined type.
6. `Option.some.inj` against the child's reading gives `fields = outs`.

For `args = []`: `resTy = ty`, and the declared reading is immediate. It is covered when `ty` is a `forallE`
(only implicit binders); otherwise it is the residue below.

Premise accounting, (a′):

| premise | after (a′) | kind |
|---|---|---|
| `P5At c res` (one-Signal callees) | gone for callees whose type is a `forallE`; `ResDeclAt` gains `isForall` (same class: declared-type read) | ELIMINATED (arity ≥ 1); RENAMED into ResDeclAt for the arity bit |
| `P5SAt` / `LocalStruct.p5s` | gone for calls with ≥ 1 argument (or `forallE` types) | ELIMINATED there; kept as `P5S0` (`¬ dD.type.isForall`) for zero-binder callees: LOCALISED |
| `NS` (`userStructure? envP Signal = none`) | provable for every environment (G2) | ELIMINATED |
| `InstSubstC` | NEW, same extern boundary as `InstSubst` (`instantiate1`); provable for the model `inst1M` (ShippingInstSubstModel), so ELIMINATED for `instResM`, like IS | RENAMED into the open IS boundary (production) |
| `typeAgree`/`DR`, `fieldsAgree`/`FA` | unchanged | open (envGet/envFrame not added) |
| RefLaws / trust lists | unchanged | — |

Effort: compiler patch ~80 lines (new file `Sparkle/Compiler/MachRecUnfoldF.lean` for passF/passT/abbrevStep +
4 Elab hunks); proofs ~500–800 lines (U3 the bulk: `replaceNoCache`/`inlFoldNat` reading lemmas by structural
induction); consumers ~200 lines. Risk: moderate in the proofs (the shape of the `rounds` auxiliary, structural
recursion through `Array.mapM` in passF, see sketch `-- UNSURE`), low for acceptance.

### (b) Checked certificate (translation validation)

* **(b1) Closure certificate for `relevantClosure`** (the compiler records the closure; a total checker validates it
  against the witnessed constants): sound, but **pointless**, because no proof needs `relevantClosure`'s value (§0).
* **(b2) Output-list certificate at the entry**: `entryConst` unfolds only if
  `outsKeep projs ci (inl ci.type)` = "declared reads `none`, or the inlined reading equals the declared one". The run fact
  `entryConst … ≠ ci` then *contains* `p5sF` (all arities, no inliner equations, no G1/G2). A check in the `p5s`
  direction would refuse alias-typed children that are accepted today: narrowing, rejected. For `outsKeep` itself, a
  failure falls back to `ci` (the child takes the legacy route), so output changes on any input where the check fails.
  The claim that it never fails in a real environment is the very fact (a′) proves (modulo guards); in (b2) it is only
  argued. Cost: `entryConst` is unfolded at 10 sites (`entryConst_cases`, `gates_miss_of_entryConst`, `entryConst_mixed`,
  `EntryDefines.*`, …), and every `MachineDefines` generator's `decide` path is touched. Still needs ISC and NS. **Fallback** if U3
  stalls; it also covers zero-binder callees.
* **(b3) Width check in the IR closing** (`instStmtG`, MachineInstG.lean 26, today checks field NAMES only): the
  closing would also check every connected field's width against the transition input. `ChildLinkStruct` would then follow
  from the parent's successful run, with no p5s/IS/DR/FA at all. But it is a refusal guard on the certified route
  (parents with mismatching widths fall back to legacy), the kind ruled against on 2026-10-19 ("provenance, not refusal
  guard"). Not recommended without an explicit ruling.

### (c) Only the witnessed run (no equation)

`MachineDefines c sc` pins `machineShape?` of the entry constant to a reflected `sc`, so the INLINED side is known
concretely (`sc.layout.outs`). The declared side, though, lives in the abstract `envP`/`envR`. No run fact relates
`dD.type` to `userInliner envR dD.type`, because `userInliner` is pure and has no `RunsTo`. So (c) cannot discharge
`p5s`. What it can do is make `p5s` **unnecessary on generated endpoints**: `TagObl … (.field _)` (ShippingCallWidthsTagObl)
is `ChildLinkStructEx (kidOuts k) nm e.2.2` with `nm = d.shape.instFields[k]` and `e` concrete in a reflected parent.
With `kidOuts k = sc.layout.outs` (the existing `Struct`/hkid boundary), it is `SelOut sc.layout.outs nm w`, decidable.
This is "Way 1" (CallWidthsEntryExampleTest) per entry tag. It is honest coverage per declaration, NOT a general
discharge, and it does not change the general theorem's premises. Optional parallel unit U7.

### (d) Other

* (d1) `envGet`/`envFrame`, `InstAgree`, an unfold law for `passM`: excluded by the ruling.
* (d2) Record the unfolding's type in the entry/cache: a recorded value is not a run fact unless behaviour depends
  on it, and if it does, that is (b2).
* (d3) Stop inlining types (`inlinedConst` keeps `d.type`): changes which children read (aliases), so acceptance
  narrows. Rejected.
* (d4) Change the type path only (`inlinedConst` with a separate type inliner): changes the `entryConst` signature, with
  churn across 61 files. (a′) gets the same effect inside `userInliner` by dispatching on `isForall`.

## 2. Recommendation

**(a′)**, in two increments, with the production switch gated by a ruling. Until then everything runs against a
**candidate copy** in Tools (the precedent is reader candidate `machineShapeF`), so production is unchanged. Rationale:
it is the only option that PROVES the type-preservation fact the reviewer asked for ("prove type/result-kind
preservation or keep P5 explicit", 2026-10-18). It adds no law, changes no acceptance, and costs zero proof churn in
existing files. It also discharges `P5At` (one-Signal callees) along with `p5s`. (b2) is the fallback if U3's Expr
lemmas prove too costly.

Residue after (a′), stated precisely:

* zero-binder callees, whose type is not a `forallE`. On app types, `inlineDefs` and `passM` do real work, and
  `userDefinition?`/`isRec` see library names, so more guards plus the general passF lemmas would be needed;
* `InstSubst` + `InstSubstC` (one extern boundary; model-eliminated);
* `typeAgree`/`fieldsAgree` (environment agreement; unchanged).

## 3. Units (parallel workers author; the integrator builds serially, 3 GiB, swap 0, `-j 1`)

**Minimum first vertical increment = U1c + U3(part) + U4-L2 + U5a**: `P5At` discharged for `forallE` callees against the
candidate inliner, end to end, with no production change.

| unit | content | files | depends | production change |
|---|---|---|---|---|
| U1 | candidate defs: `passF`/`passT`/`passDepth`, `inlLibConsts`, `userAbbrevC?`, `abbrevStep`, `inlAbbrevsC`, `userInlinerC` (sketch) | `Tools/ShippingInlCand.lean` (new); production patch `docs/parallel/patches/inl-total.patch` (new compiler file `Sparkle/Compiler/MachRecUnfoldF.lean` + Elab hunks: `rounds` → `passT`, `inlAbbrevs` → `abbrevStep`, G1 in `userAbbrev?`, G2 in `userStructure?`, G3 separate hunk) | — | patch only (not applied) |
| U2 | fixed-list shadow: verbatim OLD copies (`oldUserInliner`, old `inlAbbrevs`/`passM` are already `partial`, fine in a test) vs candidate, every declaration of the regression list (15 tests of rg1, MemNameCollision*, struct-child tests, Keccak sponge), on `ci.value` AND `ci.type`, plus `entryConst` equality; asserting `run_cmd` (throws on difference); timing of Fp12MulHWTest/Keccak | `Tests/Compiler/InlCandShadowTest.lean` | U1 | none |
| U3 | Expr facts: `inlineDefs_forall`, `passT_forall`, `rounds_forall`, `headBeta_forall`, `replaceNoCache` forall-spine/body lemmas, `inlAbbrevs_forall_inv`, `inlFoldNat` on canonical literals and on `Signal`/`Prod`/structure heads (`inlNatSum?` = none unless HAdd/HSub head) | `Tools/ShippingInlTypeFacts.lean` | U1 | none |
| U4 | L2 `resKind_userInlinerC`; L1 `declOuts_userInlinerC` (G2-free form with `hNS`/`hSum` first, then without them under G2) | `Tools/ShippingInlTypeReads.lean` | U3 | none |
| U5a | `ResDeclFAt`, `p5At_of_resDeclF` (candidate form `P5AtC` over `userInlinerC`), `childLink_real` variant without `P5` | `Tools/ShippingP5Forall.lean` | U4 | none |
| U5b | `InstSubstC`, `readSkel`, `structResAt_of_partsF`, `LocalStructF` (no `p5s`) + `childLinkStruct_realLF`; old theorems kept | `Tools/ShippingCallWidthsStructResF.lean` | U4, U6 | none |
| U6 | `readSkel` (Bool), `instSubstCM` (ISC for the model `inst1M`), `instResM` converse | `Tools/ShippingInstSubstModelC.lean` | — | none |
| U7 (optional) | `.field` `TagObl` by `decide` from reflected `sc` (Way 1 per tag) for collision/struct parents | test file | — | none |
| SW | after ruling: apply `inl-total.patch`; `userInliner_eq_cand : userInliner = userInlinerC` by `rfl` (or retarget names); OldEqV drift record; rerun U2 + rg1 + affected Tools targets | Elab.lean, MachRecUnfoldF.lean | U1–U5 | YES (ruling) |

Parallelism: U1 ∥ U6 first. Then U2 ∥ U3. Then U4. Then U5a ∥ U5b. U7 is independent.

Build order for the integrator: U1 + U6 → U3 → U4 → U5a (increment 1 closes here) → U2 (shadow, evidence for SW) →
U5b → SW.

Reporting per unit: SHA, command, exit, `#print axioms` (expected `[propext, Classical.choice, Quot.sound]`), and the
premise table above updated with what was actually built. Keep "source argument" (output identity) separate from
"built evidence" (U2 shadow) and from the runtime bridge (O1–O4 unchanged).
