# DG-READKINDS U10 freeze (Issue sparkle-gen5-dg-readkinds; base a04a7a8e = 730dbea5 + header sync, branch kjob/g5rk-r15) — DESIGN ONLY, no Lean yet

Extends `DG_READKINDS_FREEZE.md` and the U5–U9 freezes. Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU10.lean`, `Tests/Gen5/ReadKindsU10Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, any built file;
no new TRUSTED boundary / law / axiom; FG not reduced; `GenWF` not strengthened; no sorry / native_decide; hq (`Expr.equal` soundness) not adopted.

Wording: "未供給 / この調査で経路未発見" describes this survey (what was read and grepped in the branches named below), not impossibility or non-derivability.
A "mutant" is a rejection by signature/defeq of a changed statement, not a semantic counterexample. A result resting on a named premise is
**conditional = intermediate**, never a supply. Nothing below is reader coverage or an FG supply; the Issue stays open.

## 0. Where the approved parts live (finding of this survey — affects what can be implemented)

The parts named in the task are on sibling branches that all fork from `d0ddc50b` and are NOT ancestors of this branch (`git merge-base --is-ancestor` negative; `git branch --contains` lists only the branch itself and, for Cover, `kjob/g5rt-r1/r2`):

| part | branch (head used for reading) | file(s) | in this base? |
|---|---|---|---|
| DG-ENV U1 `EnvFrameEnd` (pure/bind/get/set/modify/modifyGet/getEnv, `readsAt_endW`) | `kjob/g5env-r9` | `Tools/ShippingGen5EnvFrame.lean` | **no** |
| DG-ENV U2 (B′ IO lift, C: metaGet…constInfo) | same | `Tools/ShippingGen5EnvFrame2.lean` | **no** |
| DG-ENV U3 (per-field aggregation, `CellPrem`) | same | `Tools/ShippingGen5EnvFrame3.lean` | **no** |
| DG-COVER Cover5 (`shapeAgree_of_fuel_run` …), Cover6 (`FReachC`) | `kjob/g5cv-r13` | `Tools/ShippingGen5Cover5.lean`, `Cover6.lean` | **no** |
| DG-DATAOF (`dataOfFrom`/`dataOfAt`, dims) | `kjob/g5do-r6` | `Tools/ShippingGen5DataOf*.lean` | **no** |
| DG-ENV E1–E6, `MachineDefinesR`, `TQ` | base | `Tools/ShippingGen5Env.lean`, `EnvR.lean`, `EnvQ.lean` | yes |
| DG-RUNREADS `RunReadsAt` | base | `Tools/ShippingGen5RunReads.lean` | yes |
| `EnvFrame`, `GetEnvFrame`, `envFrame_getConstInfo` (premise form) | base | `Tools/ShippingEnvSnapshot.lean` | yes |
| READKINDS U5–U9 | base | `Tools/ShippingGen5ReadKindsU5..U9.lean` | yes |

Consequence: this unit imports only base files. A row whose supplier is on a sibling branch is marked "supplier on `<branch>`, not importable from this base without integrating that branch";
integration (merge / cherry-pick across Issues) is not done by this Issue and is a question for the reviewer/user, not an assumption (§5).
Owner Issues: DG-ENV = `sparkle-gen5-dg-env`; DG-COVER = `sparkle-gen5-dg-cover`; DG-DATAOF = `sparkle-gen5-dg-dataof`; DG-RUNREADS = `sparkle-gen5-dg-runreads`;
reader trace = `sparkle-gen5-dg-readertrace`. Rows owned there are not re-implemented here.

## 1. Survey: the remaining rows

| row | real name and full type | supplier found | owner | status after this survey |
|---|---|---|---|---|
| **hR** (U9c) | `∀ w1 w2 w3, RunsTo (getConstInfo X) … w1 ci w2 → RunsTo getEnv … w2 envR w3 → RunsTo getEnv … w3 envR′ w5 → ReadsAt env₀ cref w1 ∧ ReadsAt env₀ cref w2 ∧ ReadsAt env₀ cref w3` | the w2, w3 conjuncts: base `envFrame_getConstInfo X hg`, `GetEnvFrame` (premise) with E3 `ReadsAt.of_frame`. (On `kjob/g5env-r9` the corresponding `EnvFrameEnd` rows `envFrameEnd_constInfo` (needs `ReadWorld cref`, `ReadWorld mref`) and `envFrameEnd_getEnv` (needs `ReadWorld cref`) are proved; they are in `endW` form, a different statement from `EnvFrame`; the bridge `EnvFrameEnd → EnvFrame` was not looked for/found in this survey.) The w1 conjunct: none | DG-ENV | **w2, w3 reduce to w1 + `GetEnvFrame` (U10a, implementable in base)**. **w1 (the world after `coreHead`): 未供給 / この調査で経路未発見**: `coreHead` (`Tools/ShippingEntryReadsLinked.lean:62`) starts with `IO.getEnv`, `IO.eprintln`, `IO.FS.Handle.mk`; `ioEnv` is one of the 13 class-D constructors that DG-ENV U3 §3 records as having no premise name / no route |
| **h1** (U9c) | `∀ env v1, RunsTo getEnv … w env v1 → ReadsAt env₀ cref v1` | base `GetEnvFrame` + E3 | DG-ENV | reduces to `h0` + `GetEnvFrame` (U10b, base) |
| **h0** (U9c) | `ReadsAt env₀ cref w` | base E1 `readsAt_self cref w : ReadsAt (envAt cref w) cref w` | DG-ENV | supplied **for `env₀ := envAt cref w`** (the `readMachine` start world). It is NOT supplied for an `env₀` shared with the synthesis run (next row) |
| **env tie between the two runs** | `env₀` of the `readMachine` run = `env₀` of the synthesis run (`ws`); i.e. an agreement of `envAt cref w` and `envAt cref ws` on the constants and the three env-derived entry arguments | none | DG-ENV C0 (`sparkle-gen5-dg-env`) | 未供給 / この調査で経路未発見. DG-ENV U3 §6 lists C0 (generic, all worlds) as open: 13 class-D rows, `Diag`, telescopes, callbacks, and `CellPrem` at the runtime. The two runs' relative order is not an input of any base theorem |
| **hall** | `∀ u, ReadsAt env₀ cref u` | none | DG-ENV C0 | 未供給 (as U9 §0) |
| **run existence** | ∃ a `readMachine` run and a synthesis run (`RunReadsAt` instance) for the same `X`, and `declName = X` | `RunReadsAt` is produced by DG-RUNREADS RR3 `runReads_of_run` from a synthesis run, `JQ`/cache at its start, `MachineDefines`, `MachineClosesAtA`; no producer of the run itself | DG-RUNREADS / DG-CLOSINGRUN (`sparkle-gen5-dg-closingrun`) | 未供給 / この調査で経路未発見 (existence of the runs is a premise of every consumer) |
| **hag** (U9b) | `ReflExprAgree := ∀ e, reflExpr e = reflExprS e` (`DGenStored2.lean:646`) | none: `reflExpr` is a `partial def`; only the finite sample check `reflExpr_samples` | none named (`DGenStored2`, DGEN stored) | 未供給 / この調査で経路未発見. Not a READKINDS row |
| **ShapeDenotes / hK** (U9b) | `ShapeDenotes (dataShapeE r.shape b lay) d.shape := evShape (dataShapeE r.shape b lay) = some d.shape` | none: the link “the stored constant's declared value is `dataE r` and the value `d` it defines is what `evShape` reads” is not formulated (`DGenStored2.lean:652-656`) | none named | 未供給 / この調査で経路未発見. Not closable from `ReadsAt`/`RunReadsAt`/`dataE_run` (U9a only exposes the three reflected pieces of the Expr) |
| **coverage** `dataOfAt … = some d` | DG-DATAOF freeze §11.2 rows 1–6, 8 | `kjob/g5do-r6`: dims lemmas only | DG-DATAOF / DG-COVER | 未供給 (rows 1,2,3,4,5,6,8 open per its own §11.4; supplier on a sibling branch) |
| **ShapeAgree (state side)** | Cover5 `shapeAgree_of_fuel_run`, `shapeAgree_of_production` (conditional on `hbr`) | `kjob/g5cv-r13` | DG-COVER | supplier on a sibling branch, conditional on `ShapeFuelBridge` text `hbr`; row 6b needs `d.shape = sp`, not connected to U9 |
| **reader trace** `FReachC` | Cover6 | `kjob/g5cv-r13` | DG-COVER / `sparkle-gen5-dg-readertrace` | “nothing connects any `readF` call to `FReachC`” (its own header); not a READKINDS row |
| hq / FG | — | — | — | hq not adopted (trust boundary); FG not supplied |

## 2. First unit to implement: **U10 = {U10a, U10b, U10c}**, base-only, law-free
Reason: it is the only line among the open rows that closes with base files only (every other closable line needs a sibling-branch file or is a premise of the runtime). It turns three of the five named-world `ReadsAt` facts of U9c (`h1`, and the `w2`, `w3` conjuncts of `hR`) into the one existing premise `GetEnvFrame` plus the world after `coreHead`, so that the list DG-ENV C0 must deliver for U9c shrinks to: `ReadsAt` at `w`'s `env₀`-tie to the synthesis run, and `ReadsAt env₀` at the post-`coreHead` world. Nothing is claimed about those two.
`open`: `Lean Meta`, `Sparkle.Compiler.Elab`, `Tools.ShippingEntrySoundness` (`RunsTo`), `Tools.ShippingGen5Env` (`ReadsAt`, `ReadsAt.of_frame`), `Tools.ShippingEnvSnapshot` (`GetEnvFrame`, `envFrame_getConstInfo`), `Tools.ShippingGen5ReadKindsU9`.
Binders are fully explicit (no `variable`): `{mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}`.

### U10a — hR from the post-`coreHead` world and `GetEnvFrame`
```lean
theorem hR_of_w1 {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {w5 : Void IO.RealWorld}
    {env₀ : Lean.Environment}
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1) :
    ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3
```
Route: `ReadsAt.of_frame (envFrame_getConstInfo X hg) hget (hw1 …)` for `w2`; `ReadsAt.of_frame hg henv h2` for `w3` (`GetEnvFrame` is by definition `EnvFrame getEnv`). Premises: `hg` (existing, named, base; not a new premise), `hw1`.

### U10b — h1 from h0 and `GetEnvFrame`
```lean
theorem h1_of_h0 {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {env₀ : Lean.Environment} {w : Void IO.RealWorld}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w) :
    ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref v1
```
Route: `ReadsAt.of_frame hg hrun h0`.

### U10c — U9c with `h1`/`hR` replaced by `hg` and `hw1`
```lean
theorem readMachine_agrees_runReads_framed {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1)
    (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape
```
Route: `readMachine_agrees_runReads_at hrun R h0 (h1_of_h0 hg h0) (hR_of_w1 hg hw1) hX`. Conditional (intermediate): `hg`, `h0`, `hw1`, the two runs and `hX` remain premises.
Note on `h0`/`hw1` and `env₀`: `h0` with `env₀ := envAt cref w` is E1 (`readsAt_self`); `hw1` then asserts that the post-`coreHead` world of the synthesis run agrees with that `env₀`, which is the env-tie row of §1 (not supplied).

## 3. Rows not implemented in U10 (stay 未供給 / この調査で経路未発見)
hw1 (post-`coreHead` world; `ioEnv` class D), env tie between the two runs / C0, `hall`, run existence, `hag`, `ShapeDenotes`/`hK`, `d.ok`, coverage (`dataOfAt = some`), `ShapeAgree` connection, reader trace, hq, FG. `envR = envR′` and `ci ∈ envR` are still not derived.
Rows with a supplier on a sibling branch (DG-ENV `EnvFrameEnd`, DG-COVER Cover5/6, DG-DATAOF) are not duplicated here.

## 4. Check plan (`Tests/Gen5/ReadKindsU10Check.lean`)
Written from this document, not from the Lean statement.
1. TYPE: `Exp…` statements for U10a/b/c written independently, same reducible comparator `Tests.Gen3.ExpectedType`; positive control (separately written copy accepted).
2. MUTANTS (well-typed single changes only; signature/defeq rejection, not semantic counterexamples): U10a drop the `w3` conjunct / drop the `w2` conjunct / replace `hg` by none is ill-typed (not counted) so use: swap the premise `hw1` for `ReadsAt env₀ cref w2` (well-typed) ; U10b conclusion `ReadsAt env₀ cref v1` → `ReadsAt env₀ cref w` ; U10c drop `hX` / drop `h0` / drop the `r.shape = shape` conjunct.
3. COUNT: conjunct counts as an auxiliary necessary condition only.
4. CLOSURE (`reach2` as in the U9 Check, defined in the new Check): root itself tested against the forbid set; unknown constant fails; negatives for an unknown root, a helper whose VALUE mentions an unknown name, an existing helper whose TYPE only mentions an unknown name, each asserting the intended name; clean control; bad fixtures inside `withoutModifyingEnv`. `GetEnvFrame` is recorded as a FACT (premise use), not forbidden; forbid set = `forbidConsts` minus `Expr.equal`/`eqv` as in U8/U9.
5. AXIOMS: `propext` / `Classical.choice` / `Quot.sound` only. No sorry.
Counts are reported as real numbers with the partition and the counting rule. Before commit, the Check is built on the committed tree itself.

## 5. Questions for the reviewer (no assumption made)
(a) Base integration: should a later unit import `Tools.ShippingGen5EnvFrame*` (U1–U3) so that `GetEnvFrame` itself is discharged from `ReadWorld cref` via `envFrameEnd_getEnv`? That needs a bridge `EnvFrameEnd → EnvFrame` (not found in this survey) and a base containing those files; this Issue does not merge or cherry-pick across Issues on its own.
(b) U10 as scoped (base-only, three short theorems) is acceptable as the first unit?

## 6. Not claimed
`hw1`, env tie / C0 / `hall`, `CellPrem`, existence of the runs, `envR = envR′`, `ci ∈ envR`, `hag`, `hK`, `GateDefines`, `srcDom`, `ls`/`outs`/`nexts`, hq, coverage, FG, M5. The Issue stays open.
