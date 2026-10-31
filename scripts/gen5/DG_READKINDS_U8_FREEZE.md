# DG-READKINDS U8 freeze (Issue sparkle-gen5-dg-readkinds; base 5212b42f = 8bed2e00 + header-only commit, branch kjob/g5rk-r11) — DESIGN ONLY, no Lean yet

Extends `DG_READKINDS_FREEZE.md`, `..._U5_FREEZE_REV3_1.md`, `..._U6_FREEZE.md`, `..._U7_FREEZE.md`. Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU8.lean`, `Tests/Gen5/ReadKindsU8Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, `Tools/Prototype/DGenProv.lean`, `Tools/ShippingGen5Env.lean`, `Tools/ShippingEntrySoundness.lean`;
no new TRUSTED boundary / law / axiom; FG not reduced; `GenWF` not strengthened; no sorry / native_decide.

Wording: "not supplied / this survey found no route" describes this survey, not impossibility. A "mutant" is a rejection by signature/defeq of a changed
statement, not a semantic counterexample. A result resting on a named premise (`hall`) is **conditional = intermediate**, never counted as a supply.
Nothing below is a real-run tie, reader coverage, or an FG supply; the Issue stays open.

`open` context for every statement below: `Lean Meta`, `Sparkle.Compiler.Elab`, `Tools.ShippingEntrySoundness` (`RunsTo`), `Tools.ShippingMachineCommand`, `Tools.ShippingMachineEntry` (`MachineDefines`),
`Tools.Prototype.DGenProv` (`GenEntry`, `ReadConcl`, `readMachine_run`), `Tools.ShippingGen5ReadKindsU6` (`ReadRoot`, `readMachine_root`), `Tools.ShippingGen5ReadKindsU7` (`ReadFields`, `readMachine_fields`),
`Tools.ShippingGen5Env` (`ReadsAt`, `ci_of_readsAt`, `envR_of_readsAt`, `machineDefines_of_readsAll`). Binders of every theorem are fully explicit (no `variable`):
`{mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}`.

## 1. U8a — one run gives `ReadRoot` and `ReadFields` for the same `ci` / `env` / `w1` / `w2`

Problem (U7 §6 addendum): `readMachine_root` and `readMachine_fields` each return their own `∃ ci env w1 w2`. A plain `∧` of the two theorems would assert two witness tuples.
Route chosen: **prove the witnesses equal**, from the fact that a `RunsTo` is an equation of an `EST.Out.ok` value of one function at one world (the rest of the walk is not repeated).

U8a-0 (determinism of a run; a lemma, no new law — `RunsTo m … w a w'` unfolds to `m mctx mref cctx cref w = EST.Out.ok a w'`, so two runs from the same `w` give the same output by `Eq.trans` + constructor injectivity):
```lean
theorem runsTo_det {α : Type} {m : MetaM α} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {a b : α} {w' w'' : Void IO.RealWorld}
    (h1 : RunsTo m mctx mref cctx cref w a w') (h2 : RunsTo m mctx mref cctx cref w b w'') :
    a = b ∧ w' = w''
```
U8a (the combined theorem):
```lean
theorem readMachine_rootFields {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ReadRoot ci env r ∧ ReadFields ci env r
```
`ReadRoot ci env r` already contains `ReadConcl ci env r` as its first conjunct, so `ReadConcl` is present for the same `ci`/`env`.
Proof route: obtain the two witness tuples from `readMachine_root h` and `readMachine_fields h`; `runsTo_det` on the two `getEnv` runs (same `w`) gives `env = env'`, `w1 = w1'`; then on the two
`getConstInfo declName` runs (same `w1`) gives `ci = ci'`, `w2 = w2'`; `subst`. The conclusion is therefore about ONE tuple, not two existence claims joined by `∧`.
Not claimed: that this is "the same walk" syntactically (two walks are run; their results are proved to agree).

## 2. U8d (new closable row found by this survey) — the gate-miss conjuncts of `MachineDefines`

`MachineDefines` (`Tools/ShippingMachineEntry.lean:2345`) concludes `certifiedShape? … = none ∧ mixedCertifiedShape? … = none ∧ machineShape? … = some shape`. `ReadConcl` contains only the third.
`readMachine` (`Tools/ShippingMachineCommand.lean:440`) throws when `!allowGate && ((certifiedShape? false [] entry).isSome || (mixedCertifiedShape? false [] entry (instancePredicate env)).isSome)`,
so a successful run with `allowGate = false` records the first two. This needs only the prefix of the walk (`getEnv`, `getConstInfo`, `unless levelParams.isEmpty`, the gate `if`); the rest of the run is not walked.
```lean
theorem readMachine_gates {declName : Lean.Name}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName false) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      certifiedShape? false [] (GenEntry ci env) = none ∧
      mixedCertifiedShape? false [] (GenEntry ci env) (instancePredicate env) = none
```
(`GenEntry ci env` is by definition `entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)`, the `entry` of the source.)

## 3. U8e (CONDITIONAL, intermediate) — `MachineDefines` of `r.shape` from a run and the DG-ENV premise

```lean
/-- CONDITIONAL on `hall` (DG-ENV C0, supplied nowhere): the reader run on `declName` (with `allowGate = false`) defines
`MachineDefines … declName r.shape`. `hX` does not appear: `MachineDefines` quantifies over `getConstInfo declName` for the same `declName`. -/
theorem machineDefines_of_readMachine {declName : Lean.Name}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName false) mctx mref cctx cref w r w')
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u) :
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName r.shape
```
Proof route: `readMachine_gates hrun` (gate facts at `ci`, `env`) and `readMachine_run hrun` (`ReadConcl`), identified by `runsTo_det` on the `getEnv` / `getConstInfo` runs;
`ci_of_readsAt` (`env₀.find? declName = some ci`) at `hall w1`; `envR_of_readsAt` at `hall w` (the three derived arguments of `env` equal those of `env₀`);
rewrite the gate and shape facts to `env₀`; `Tools.ShippingGen5Env.machineDefines_of_readsAll` (E6). Premises left: `hall` (no theorem here supplies it), the run `hrun` (real-run tie not supplied).
`hall` is a premise this survey found no supplier for (DG-ENV C0: agent g5env-r4, U1 in progress); nothing here shows it unprovable.

## 4. U8b — where `hX : declName = X` comes from in the actual consumers (survey result)

* Consumer `MachineDefines mctx mref cctx cref c shape` (used by `T1Hyp.defines` G3-SHAPE, `StepStmt`, `MemParentStmt`, `LeafStmt` in `scripts/gen2/GEN2_DEFS.lean.txt`): the statement itself
  quantifies over `RunsTo (getConstInfo c)` with the same `c`. A reader run `readMachine c` therefore needs no extra `hX`: U8e states `declName` once. `hX` is **removed by the statement** here (rfl), not by a run.
* Consumer `readMachine_agrees_runReads` / `_of_readsAt` (`RunReadsAt`, `Tools/ShippingGen5RunReads.lean:38-73`): `X` is the target of `synthesizeCombinationalCore X`; `declName` is the argument of `readMachine`.
  This survey found no theorem relating the two runs; they are related only if the reader is invoked on the declaration being synthesized — that is the **real-run tie** (the call site in
  `generateCore`/`Tools/ShippingMachineCommand.lean:2511` is not modelled by any `RunsTo` hypothesis in `Tools/`). **Not supplied / this survey found no route.** `hX` stays a premise there.
* `StoredFromRead d r := d.shape = r.shape` (`Tools/Prototype/DGenProv.lean:264`) links the kernel-checked stored `d` to the run's `r`; it needs `dataE` reflection, **not supplied**.

## 5. U8c — what U5-U8 conclusions remove from the reader-bridge premises (names and full types)

Reader-bridge target (GENERAL_SPEC §5 M5): production reader successful read → `MachineDefines` (T1Hyp.defines) / `GateDefines`, `body_eq`. "closed" = proved unconditionally in a built file after U8 review; "cond." = conditional on a named premise; blank = this survey found no route.

| # | consumer premise (real name, type) | provided by (real name) | status after U8 | still missing |
|---|---|---|---|---|
| 1 | `T1Hyp.defines : ∀ c, Reach c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx → MachineDefines mctx mref cctx cref c q.d.shape` | `machineDefines_of_readMachine` (U8e) with `hrun`, `hall`, and `StoredFromRead q.d r` | cond. on `hall`, `hrun`, `hstore` | `hall` = DG-ENV C0 (g5env-r4 U1 in progress); `hrun` = real-run tie (not supplied); `hstore` (DGenProv:266) not supplied |
| 2 | `MachineDefines` conjunct 3: `machineShape? false [] (entryConst … ci … envR) (structEnv envR') = some shape` | `ReadConcl` (`readMachine_run`, DGenProv:119) at `structEnv env`; transported to `envR, envR'` only through `hall` (E5) | cond. on `hall` | `hall` |
| 3 | `MachineDefines` conjuncts 1-2: `certifiedShape? … = none`, `mixedCertifiedShape? … = none` | `readMachine_gates` (U8d), `allowGate = false` | closed for the run's own `ci`/`env` (U8d); transport to `envR` via `hall` | `hall` |
| 4 | `GateDefines mctx mref cctx cref c bs body` (`Tools/ShippingGateDefines.lean:72`; needs `mixedCertifiedShape? … = some (bs, body)`) | none: `readMachine` computes no `mixedCertifiedShape?` value; `allowGate = true` only skips the guard | **未供給 / この調査で経路未発見** | gate-route reader (`mixedCertifiedShape?`) walk |
| 5 | `Read` fields `rootLets sel? hasOuter` / `nDecl nIn tuple ctor? outNames bposL vposL vwL` / `dom`-existence | `ReadRoot` (U6d `readMachine_root`), `ReadFields` (U7a `readMachine_fields`), jointly `readMachine_rootFields` (U8a) | closed (one tuple) | — |
| 6 | `Read` fields `srcDom`, `ls`, `outs`, `nexts` | none | **未供給 / この調査で経路未発見** (`partial` `unq`, `typed … : MetaM`, 4-way `srcDom` branch) | route walks/`RunsTo`-for-`mapM` lemma |
| 7 | `RootFactsAt r.entry` | `readMachine_rootFactsAt` (U6a) | closed | — |
| 8 | `hX : declName = X` of `readMachine_agrees_runReads(_of_readsAt)` | for the `MachineDefines` consumer: removed by statement (§4); for `RunReadsAt` consumer: none | cond./未供給 per consumer | real-run tie |
| 9 | `GetEnvFrame`, `hw`, `hall` | none (`ReadsAt` E1-E6 are lemmas about them, not suppliers) | **未供給** = DG-ENV C0 | g5env-r4 |
| 10 | `GenFacts.body_eq : d.shape.body = quote … d.packed` (hq: `readMachine` guard `q.equal shape.body`) | none | Q1 needs `Lean.Expr.equal_sound` = new TRUSTED law, **not adopted**; Q2 (`partial unq`) no route; Q3 via `readN_sound`+`machine_body_of_readN` conditional on `hread` (coverage) | user decision (Q1), coverage (Q3) |
| 11 | reader coverage (`readN cfg k body = some r` for production bodies), FG | none | 未供給 | M5 / DG-COVER |

Rows 1-3 are the only ones U8 changes (row 3 closed for the run's own env, rows 1-2 conditional). Counting rule for the Check/report: rows are counted once per row number above; "closed" rows = 5, 7 (+ row 3 partly); "cond." = 1, 2, 8; "未供給" = 4, 6, 9, 10, 11.

## 6. Check plan (`Tests/Gen5/ReadKindsU8Check.lean`)

* TYPE: independently written `Exp…` statements (from this document, not copied from the Lean) vs `runsTo_det`, `readMachine_rootFields`, `readMachine_gates`, `machineDefines_of_readMachine`;
  same reducible comparator `Tests.Gen3.ExpectedType`; positive control (comparator accepts a copy).
* MUTANT (signature/defeq rejection only, not semantic counterexamples), single change each, each counted as actually rejected:
  `readMachine_rootFields` without `ReadRoot` conjunct; without `ReadFields` conjunct; with two independent `∃` tuples (the rejected plain-conjunction form) — i.e. `(∃ ci env w1 w2, … ∧ ReadRoot) ∧ (∃ ci env w1 w2, … ∧ ReadFields)`;
  `readMachine_gates` with `allowGate` generalized (`declName false` → arbitrary `allowGate`); with `isSome` instead of `none`; without the mixed conjunct;
  `machineDefines_of_readMachine` without `hall`; with `allowGate` free; conclusion `r.shape` replaced by an arbitrary `shape`; `runsTo_det` with `w' = w''` dropped.
* CONJUNCT COUNT: the number of top-level conjuncts of each Expected conclusion and of each conclusion-dropping mutant (auxiliary; not a proof that a mutant is a single change).
* CLOSURE: explicit-value scan as in `ReadKindsU7Check`; `T1Hyp`/`T1HypND`/`Laws` not reached; unknown constant = fail.
* AXIOMS: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
* STATUS line lists NOT supplied: `hall` / DG-ENV C0, `GetEnvFrame`, real-run tie (`hrun`, `hX` for `RunReadsAt`), `hstore`, `GateDefines`, `srcDom`, `ls/outs/nexts`, hq (Q1 `Expr.equal_sound` not adopted; Q2; Q3 `hread`), coverage, FG.

## 7. Risks / plan if something does not build
* `readMachine_gates` unfolds only the prefix; if the `if` guard elaborates with a `Decidable` instance form `runs_dcases` does not match, the fallback is the walk of `readMachine_run` with the gate fact added (heavier; recorded as "route found, not built" if it fails).
* `machineDefines_of_readMachine` rewriting `GenEntry ci env` to `env₀`-arguments may need `show`/`unfold GenEntry`; the Check's independent Expected is the arbiter; any difference is reported, not patched into the Expected.
* If the combined U8e does not build it is recorded as "route found, not built", not as closed.

## 8. Not claimed
`hall` / DG-ENV C0 supplied; real-run tie; `hstore`; `GateDefines`; `srcDom`, `ls`, `outs`, `nexts`; hq; `Expr.equal_sound` (not added); reader coverage; FG, M5, DG-COVER, DG-READKINDS completion.
After Lean commits the Issue stays `doing` (clean build is the coder's).

## 9. Implementation status (appended after the Lean commit; the freeze statements above are unchanged)
Implemented as frozen in `Tools/ShippingGen5ReadKindsU8.lean`: `runsTo_det` (thin alias of `Tools.ShippingStRefCorrespondence.runsTo_det`, not re-proved), `readMachine_rootFields`, `readMachine_gates`,
`machineDefines_of_readMachine` (conditional on `hall`). Pod build of `Tests.Gen5.ReadKindsU8Check` exit 0; the clean issue-linked build is the coder's.
§5 table status sync: rows 3 (own `ci`/`env`) and 5 closed in the built statement sense above; rows 1, 2 conditional on `hall` (row 1 also `hrun`, `hstore`); rows 4, 6, 9, 10, 11 unchanged (not supplied / no route found in this survey); rows 7 unchanged; row 8 as in §4.
