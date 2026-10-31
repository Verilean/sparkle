# DG-READKINDS U9 freeze (Issue sparkle-gen5-dg-readkinds; base f86cbdd7 + 7370be6f (Check/comment sync), branch kjob/g5rk-r13) — DESIGN ONLY, no Lean yet

Extends `DG_READKINDS_FREEZE.md` and the U5–U8 freezes. Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU9.lean`, `Tests/Gen5/ReadKindsU9Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, `Tools/Prototype/*`, `Tools/ShippingGen5Env*.lean`, `Tools/ShippingGen5RunReads.lean`;
no new TRUSTED boundary / law / axiom; FG not reduced; `GenWF` not strengthened; no sorry / native_decide.

Wording: "not supplied / this survey found no route" describes this survey (what was read and grepped), not impossibility. A "mutant" is a rejection by
signature/defeq of a changed statement, not a semantic counterexample. A result resting on a named premise is **conditional = intermediate**, never a supply.
Nothing below is reader coverage or an FG supply; the Issue stays open.

`open` context: `Lean Meta`, `Sparkle.Compiler.Elab`, `Tools.ShippingEntrySoundness` (`RunsTo`), `Tools.ShippingMachineCommand` (`readMachine`, `dataE`, `dataPure`, `dataShapeE`, `layoutE`),
`Tools.ShippingMachineEntry`, `Tools.Prototype.DGenProv` (`GenEntry`, `StoredFromRead`, `readMachine_run`), `Tools.Prototype.DGenStored2` (`ReflExprAgree`, `ShapeDenotes`, `storedFromRead_of_kernelRead`),
`Tools.ShippingEntrySoundness.reflExpr`, `Tools.ShippingGen5Env` (`ReadsAt`, `ci_of_readsAt`, `envR_of_readsAt`), `Tools.ShippingGen5RunReads` (`RunReadsAt`).
Binders of every theorem are fully explicit (no `variable`): `{mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}`.

## 0. Survey: the remaining rows (this survey read the files named; "not found" = this survey found no supplier/route)

| row | real name and full type | existing supplier (file) | status after this survey |
|---|---|---|---|
| **hstore** | `Tools.Prototype.DGenProv.StoredFromRead (d : MachineData) (r : Read) : Prop := d.shape = r.shape` | `Tools.Prototype.DGenStored2.storedFromRead_of_kernelRead (hag : ReflExprAgree) (d) (r) (b lay : Lean.Expr) (hb : reflExpr r.shape.body = .ok b) (hl : layoutE r.shape.layout = some lay) (hK : ShapeDenotes (dataShapeE r.shape b lay) d.shape) : StoredFromRead d r` | open premises: `hag` (`reflExpr` is a `partial def`; only a finite sample check exists), `hK` (stored constant ↔ declared `Expr`: `generateCore` calls `addDef … (← dataE r)`; the link from the added declaration's value to the kernel-evaluated `d` is not formulated; this survey found no route), `hb`/`hl` (success of `reflExpr`/`layoutE` — **U9a/U9b below replace `hb`/`hl` by "the `dataE r` run succeeded"**) |
| **hrun** (tie to a real synthesis run) | `RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6` (`Tools/ShippingGen5RunReads.lean:42`) with `chain` (getConstInfo X from w1, getEnv from w2, getEnv from w3) and `shapeEq` | `Tools.ShippingGen5ReadKindsU7.readMachine_agrees_runReads_of_readsAt` (needs `hall : ∀ u, ReadsAt env₀ cref u` and takes `hget henv henv' hshape` as separate hypotheses) | conditional on `hall` over EVERY world. **U9c below needs `ReadsAt` only at the named worlds of the two runs** (the shape of `MachineDefinesR`), takes `R : RunReadsAt …` directly. The runs themselves (that a `readMachine` run and a synthesis run exist at all, and `declName = X`) are premises of the consumer, not produced here |
| hall | `∀ u, ReadsAt env₀ cref u` (U9c: the named-world `ReadsAt` premises) | DG-ENV C0: `GetEnvFrame` / `EnvFrame` / `EnvSnapshot` are PREMISES (`Tools/ShippingEnvSnapshot.lean`); no supplier | NOT supplied (DG-ENV C0). The world `w'` returned by `getEnv` is an abstract `Void` token; `envAt cref w' = envAt cref w` is not derivable without `GetEnvFrame` |
| hq | `Expr.equal` soundness law (Q1); readN coverage (Q3) | none | Q1: trust boundary, not adopted. Q3: not supplied |
| coverage / FG | — | — | not supplied |

First unit to implement: **U9c** (hrun with named-world `ReadsAt`). Reason: it is the only row whose consumer is the real synthesis run (`RunReadsAt`), it turns the all-world `hall` into five explicit world facts that DG-ENV C0 must deliver (so C0's required content becomes a finite list), and it is law-free and short. U9a/U9b (hstore piece) follow in the same file: they close only the `hb`/`hl` part of hstore; `hag` and `hK` stay open.

## 1. U9a — a successful `dataE r` run exposes the three reflected pieces
```lean
theorem dataE_run {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (h : RunsTo (dataE r) mctx mref cctx cref w e w') :
    ∃ body dom lay : Lean.Expr,
      reflExpr r.shape.body = .ok body ∧ reflExpr r.dom = .ok dom ∧
      layoutE r.shape.layout = some lay ∧ e = dataPure r body dom lay
```
Route: `unfold dataE`, `RunsTo.bind` twice, `rcases` on the `Except` / `Option` with `throwError_not_runs` for the failure branches, `RunsTo.pure_eq`. No premise.

## 2. U9b — hstore with `hb`/`hl` replaced by the success of the `dataE` run
```lean
theorem storedFromRead_of_dataE_run (hag : Tools.Prototype.DGenStored2.ReflExprAgree)
    {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (hrun : RunsTo (dataE r) mctx mref cctx cref w e w') (d : MachineData) :
    ∃ body lay : Lean.Expr, reflExpr r.shape.body = .ok body ∧ layoutE r.shape.layout = some lay ∧
      (Tools.Prototype.DGenStored2.ShapeDenotes (dataShapeE r.shape body lay) d.shape →
        Tools.Prototype.DGenProv.StoredFromRead d r)
```
Route: `dataE_run`, then `storedFromRead_of_kernelRead hag d r body lay hb hl`. **Conditional (intermediate)** on `hag` and on the denotation hypothesis in the conclusion (`hK`); neither is supplied. `hb`/`hl` are no longer separate premises, they follow from "the `dataE r` run succeeded" (the run `generateCore` performs before `addDef`; that the run exists is a premise of the consumer).

## 3. U9c — hrun: a `readMachine` run and a `RunReadsAt` run see the same entry and shape (named-world `ReadsAt`)
```lean
theorem readMachine_agrees_runReads_at {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h1 : ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref v1)
    (hR : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3)
    (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape
```
Route: as `readMachine_agrees_runReads_of_readsAt` (U7), with `R.chain` / `R.shapeEq` destructured for `hget henv henv' hshape` and the five `ReadsAt` facts taken from `h0`, `h1` (at the `readMachine` run's own `getEnv`-end world; `h1` quantifies over the run's possible end world, so it is a fact about that run) and `hR`. The `getConstInfo` read of `readMachine` happens at the world `v1` that `h1` covers.
Premises remaining: the five named-world `ReadsAt env₀` facts (DG-ENV C0), the two runs, `hX`. Not claimed: that the two runs exist, `envR = envR'`, `ci ∈ envR`, gates agreement, `hall`.

## 4. Check plan (`Tests/Gen5/ReadKindsU9Check.lean`)
Written from this document, not from the Lean statement.
1. TYPE: `Exp…` statements for U9a/b/c written independently, same reducible comparator `Tests.Gen3.ExpectedType`; positive control (a separately written copy is accepted).
2. MUTANTS (well-typed single changes only; ill-typed ones are not counted; signature/defeq rejection, not a semantic counterexample): U9a drop the `layoutE` conjunct / drop `e = dataPure …`; U9b drop `hag` / swap `StoredFromRead d r` for `StoredFromRead d r'` is ill-typed (not counted) so use: drop the `ShapeDenotes` antecedent; U9c drop `hX` / drop `h1` (premise) / `r.shape = shape` → `r.entry = …` only.
3. COUNT: conjunct counts as an auxiliary necessary condition (kept as in U7/U8 Checks; stated as auxiliary).
4. CLOSURE (improved common walker `reach2`, defined in the new Check, the shared `reach` unchanged): the root itself is tested against the forbid set; unknown-constant negatives: (i) a root that is an unknown name, (ii) a helper whose VALUE mentions an unknown name, (iii) an existing helper whose TYPE only mentions an unknown name; each asserted to report exactly the intended name; a clean control reports no unknown; the bad fixtures are built inside `withoutModifyingEnv`. Forbid set = `forbidConsts` minus `Expr.equal`/`eqv` as in U8 (that exclusion is not a supply of a soundness law); `ReflExprAgree` use in U9b is recorded as a FACT, not forbidden.
5. AXIOMS: `propext` / `Classical.choice` / `Quot.sound` only. No sorry.
Counts are reported as real numbers with the partition and the counting rule.

## 5. Risks
`dataE` peeling may need `generalize` on the `Except` (`reflExpr` is a `partial def`; only `Eq` reasoning on its output is used, never unfolding). If U9a does not close, U9b/U9c are independent and are committed alone; a non-closing row stays "not supplied".

## 6. Not claimed
`hag`, `hK`, `hall`/DG-ENV C0, existence of the runs, `GateDefines`, `srcDom`, `ls`/`outs`/`nexts`, hq (Q1 not adopted; Q3), coverage, FG, M5.
