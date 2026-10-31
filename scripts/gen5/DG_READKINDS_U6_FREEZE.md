# DG-READKINDS U6 freeze (Issue sparkle-gen5-dg-readkinds; base 29b6c56e on 4ac00d24, branch kjob/g5rk-r6)

Extends `DG_READKINDS_FREEZE.md`, `DG_READKINDS_U5_FREEZE_REV3.md`, `DG_READKINDS_U5_FREEZE_REV3_1.md`. Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU6.lean` and `Tests/Gen5/ReadKindsU6Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, `Tools/Prototype/DGenProv.lean`; no new TRUSTED boundary, law,
FG/guarantee change; FG not reduced; `GenWF` not strengthened.

Wording: "not supplied / this survey found no route" describes this survey, not impossibility. A "mutant" is a rejection by signature/defeq of a changed
statement, not a semantic counterexample. A result resting on a named premise is **conditional = intermediate**, never counted as a supply.

## 0. Record correction (docs/header only, committed first as 29b6c56e)

Clean build `rk5v-4ac00d24` (exit 0, 756 jobs, scoped approved at 4ac00d24). `ReadKindsU5Check` actual counts, summary lines excluded:
TYPE = 10 comparisons (7 theorems + 2 definitions + 1 comparator positive control); MUTANT = 7. Earlier 11 / 8 counted summary lines.

## 1. What was read (read-only)

`Tools/ShippingMachineCommand.lean:440-541` (`readMachine`, `Read` at `:390`), `Tools/Prototype/DGenProv.lean` (whole; `readMachine_run`, `ReadConcl`, `GenEntry`),
`Tools/ShippingGen5RunReads.lean:38-73` (`RunReadsAt`), `Tools/ShippingEntryReadsLinked.lean:245-270` (`envAt`, `getEnv_value`, `getConstInfo_value`),
`Tools/ShippingEnvSnapshot.lean:36-96` (`EnvFrame`, `GetEnvFrame`, `envFrame_getConstInfo`), `Tools/ShippingGen5Env.lean` (`ReadsAt`, E1-E6),
`Tools/ShippingGen5ReadKinds.lean:725` (`RootFacts`), `Tools/ShippingGen5ReadKindsU5.lean` (U5), grep of `Tools/` for `unq`, `Expr.equal` theorems.

New fact found by this survey (it was not in the rev3/rev3.1 text): **`Tools.Prototype.DGenProv.readMachine_run` already walks `readMachine`** and proves, from
ONE run `RunsTo (readMachine declName allowGate) … w r w'`:
```lean
theorem Tools.Prototype.DGenProv.readMachine_run {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Tools.ShippingMachineCommand.Read} {w' : Void IO.RealWorld}
    (h : Tools.ShippingEntrySoundness.RunsTo (Tools.ShippingMachineCommand.readMachine declName allowGate) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ReadConcl ci env r
-- ReadConcl ci env r := r.entry = GenEntry ci env ∧ machineShape? false [] (GenEntry ci env) (structEnv env) = some r.shape
-- GenEntry ci env   := entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)
```
Inside its proof the walk passes the peel (`hp`), the value (`hv`), the float (`eb = rootFloat entryBody`) and `machRoot … eb []` (`hm`), but exports none of them
(`Read` has no `entryBody` field). So the earlier statement "`readMachine`'s `entryBody` is a local `let`, no source" was too strong for the **existence** of a tie; the walk
is the source (below, U6a/U6d).

## 2. Supplier table

Notation: `E` an entry `ConstantInfo`, `RunsTo` the in-tree run relation. "closed" = closed by existing theorems (named) possibly under the stated named premises; the premises are in the
last column and are NOT supplied.

| row | statement | existing suppliers (full names) | result | premises not supplied |
|---|---|---|---|---|
| T1 | `RootFactsAt (r.entry)` for a `readMachine` run `r` | `Tools.Prototype.DGenProv.readMachine_run`, `Tools.ShippingGen5ReadKindsU5.rootFactsAt_of_machineShape` | **closed (U6a)**; says `r.entry` has a peel/float witness, not which `entryBody` `readMachine` used | the run `hrun` itself (a hypothesis, as in DGenProv) |
| T2 | tie to the body `readMachine` itself used: `∃ body, RootFactsTie (GenEntry ci env) body` and `r.rootLets/sel?/hasOuter` are `machRoot` of that `body` | `readMachine_run` walk (technique and the case structure), `rootFacts_of_peel`, `RootFactsTie` | **route found; closes by repeating the walk of `readMachine_run` with `hp`/`hv`/`hm`/`hx_eb` kept in the conclusion (U6d)**; no new lemma about a `partial` def is needed because the hypotheses come from `generalize … = o` in the walk, not from unfolding `rootFloat`/`mixedGatePeel` | `hrun` |
| T3 | `Read` fields beyond `rootLets/sel?/hasOuter` (`srcDom`, `dom`, `bposL`, …) as functions of `body` | same walk | **not in this unit** (more cases; not needed for the tie of the root) | `hrun` |
| E1 | `r.entry` = the `RunReadsAt` entry (`hentry`) | `readMachine_run`; `Tools.ShippingEntryReadsLinked.getEnv_value`/`getConstInfo_value`; `Tools.ShippingEnvSnapshot.envFrame_getConstInfo` | **conditional (U6b)**, under `hg` and `hw` below; no unconditional route found: `RunReadsAt` has no world relation to the `readMachine` run | `hg : GetEnvFrame mctx mref cctx cref` (existing SR2h named premise about the opaque `ST.Ref.get`; NOT proved); `hw : envAt cref w = envAt cref w1` (the `readMachine` start world agrees with the chain world of `getConstInfo X`); `declName = X` |
| E2 | `envR = envR'` | `getEnv_value`, `GetEnvFrame` | **conditional**, inside U6b (`RunReadsAt` header lists it as not claimed) | `hg` |
| E3 | `r.shape = shape` (the `RunReadsAt` shape) | `readMachine_run`, E1, E2, `RunReadsAt.shapeEq` | **conditional**, inside U6b | `hg`, `hw`, `declName = X` |
| Q1 | hq: body-is-quotation from `readMachine`'s `q.equal shape.body` | none: `Expr.equal` is `opaque` (`Tools/ShippingCacheSoundness.lean:15-45`), no `Expr.equal a b = true → a = b` theorem in `Tools/` (grep) | **not supplied / route not found** | = B1 (a law, not adopted) |
| Q2 | hq from `unq c shape.body = some whole` | `unq` is `partial` (`ShippingMachineCommand.lean:93`); `Tools.Prototype.DGenProv` only carries `unq … = o` as `generalize`; no theorem relates `unq` to `readN`/`readTot` | **not supplied / route not found** | B2/B4 |
| Q3 | hq from `readN` success | `readN_sound` + `machine_body_of_readN` (U3) | conditional on `hread : readN cfg k body = some r` (coverage question itself) | `hread` |
| Q4 | hq per declaration with endpoint | `f.machine_body` by `Eq.refl` (`ShippingNoPortsCommand.lean:127`) | per declaration only | the endpoint command |
| Q5 | `ShapeDecomp` / `RunReadsAt` body field | `ShippingShapeDecomp.ShapeDecomp` (fields `peel outsEq binders slots layoutOuts lets`), `RunReadsAt` | no body field in either | — |

Not closed by this survey (rows Q1, Q2, rest of T3, E1's premises): **未供給 / この調査で経路未発見**. Nothing here is a claim of impossibility.
No row of this table is a real-run tie, reader coverage, or an FG supply.

## 3. Implementation (new file; each item is a theorem with a complete type)

Imports: `Tools.Prototype.DGenProv`, `Tools.ShippingGen5ReadKindsU5`, `Tools.ShippingGen5RunReads`, `Tools.ShippingEnvSnapshot`, `Tools.ShippingEntryReadsLinked`.
Namespace `Tools.ShippingGen5ReadKindsU6`; `open Lean Meta Sparkle.Compiler.Elab Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.Prototype.DGenProv Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5 Tools.ShippingEntryReadsLinked (envAt getEnv_value getConstInfo_value) Tools.ShippingEnvSnapshot`.
Variables are bound in each statement (no `variable`).

```lean
/-- U6a (T1). -/
theorem readMachine_rootFactsAt {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    RootFactsAt r.entry

/-- The statement of U6d: what a `readMachine` run says about the root `body` it used. -/
def ReadRoot (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ReadConcl ci env r ∧
  ∃ body : Lean.Expr, RootFactsTie (GenEntry ci env) body ∧
    r.rootLets = (machRoot (structEnv env).proj body []).1.length ∧
    r.sel? = (machRoot (structEnv env).proj body []).2.1 ∧
    r.hasOuter = (machRoot (structEnv env).proj body []).2.2.1.isSome

/-- U6d (T2): same chain as `readMachine_run`, with the root body recorded. -/
theorem readMachine_root {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ReadRoot ci env r

/-- U6b (E1-E3), CONDITIONAL (intermediate). The three runs are those of `RunReadsAt.chain`, written out. -/
theorem readMachine_agrees_runReads {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {w1 w2 w3 w5 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (hget : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5)
    (hshape : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape)
    (hX : declName = X) (hg : GetEnvFrame mctx mref cctx cref) (hw : envAt cref w = envAt cref w1) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧ r.shape = shape
```
`hg`, `hw`, `hX` are hypotheses; nothing in this Issue supplies them. U6b is stated with the chain pieces and not with `RunReadsAt` because `RunReadsAt.chain`
hides `w1` in an `∃`, so the premise `hw` could not be named on it.

Proof routes (not yet tested): U6a = `obtain ⟨ci, env, w1, w2, he, hc, hent, hsh⟩ := readMachine_run hrun; rw [hent]; exact rootFactsAt_of_machineShape hsh`.
U6d = the proof of `readMachine_run` repeated with `ReadConcl` replaced by `ReadRoot` and `⟨rfl, hs⟩` replaced by `⟨⟨rfl, hs⟩, eb, ⟨entryV, bsIn, entryBody, hv, ⟨hp, hx_eb⟩⟩, rfl, rfl, rfl⟩`
(the only change; copied into the new file because `readMachine_run`'s proof cannot be reused from outside). Risk: the earlier walk needed care for memory (`DGenProv` header: p1-p6
exit 1/0/1/1/1/137); if U6d does not build in this Issue it is recorded as "route found, not built", not as closed.
U6b = `readMachine_run`, `getEnv_value` ×3, `envFrame_getConstInfo X hg`, `hg`, `getConstInfo_value`, `Option.some.inj`.

## 4. Check plan (`Tests/Gen5/ReadKindsU6Check.lean`)

* TYPE: each theorem above (U6a, U6d if built, U6b) and the def `ReadRoot` against independently written `Exp…` statements, same reducible comparator
  `Tests.Gen3.ExpectedType`; one positive control (comparator accepts a copy). The count printed is the number of comparisons excluding the summary line.
* MUTANT (signature/defeq rejection only, not semantic counterexamples): U6b without `hg`; U6b without `hw`; U6b with `envR'` in place of `envR` in the entry; `ReadRoot` with `r.rootLets` replaced by `r.nIn`;
  U6a with `RootFactsAt ci` for an unrelated `ci`. Count = the number actually rejected.
* CLOSURE: explicit-value scan reused from `ReadKindsCheck`/`ReadKindsU5Check` from each theorem; must not reach `T1Hyp`/`T1HypND` (name, raw proj, rec/casesOn/recOn) or `Laws`; reaching `Lean.Expr.equal/eqv`
  only through the program `readMachine`/`machineShape?` is logged as a fact (as in U5); unknown constant = fail. `GetEnvFrame` is a hypothesis in U6b's type and must appear in the statement, not in any value.
* AXIOMS: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`axiom`/`native_decide`.
* Log: a STATUS line listing what is NOT supplied: `hentry` unconditional, hq (Q1, Q2), `Read` fields of T3, real run, coverage, FG.

## 5. Not claimed
`hentry` supplied (U6b is conditional on `hg`, `hw`, `hX`); `GetEnvFrame` or `hw` supplied; hq supplied; reader coverage; real-run tie; FG, M5, DG-COVER completion.
`RootFactsAt r.entry` (U6a) is existence from the peel, as in U5; it is not a statement about which body `readMachine` used (that is U6d). Build: `kjob lake build` one target at a time in the pod; after Lean commits the Issue stays `doing` (clean build is the coder's).
