# DG-READKINDS U11 freeze (Issue sparkle-gen5-dg-readkinds; base b73244c3 = U10 approved 1045325e + header sync, branch kjob/g5rk-r17) — DESIGN ONLY, no Lean yet

Extends `DG_READKINDS_FREEZE.md` and the U5–U10 freezes. Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU11.lean`, `Tests/Gen5/ReadKindsU11Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, any built file; no new TRUSTED boundary / law / axiom;
FG not reduced; `GenWF` not strengthened; no sorry / native_decide; hq not adopted.

Wording: "未供給 / この調査で経路未発見" describes this survey (what was read and grepped in this branch), not impossibility or non-derivability.
A "mutant" is a rejection by signature/defeq of a changed statement, not a semantic counterexample. A result resting on a named premise is
**conditional = intermediate**, never a supply. Nothing below is reader coverage, C0, or an FG supply; the Issue stays open.

## 1. Survey of the remaining rows (this branch only)

| row | status after this survey |
|---|---|
| U9a `dataE_run_exposes…`, U9b `storedFromRead_of_dataE_run` | already implemented in `Tools/ShippingGen5ReadKindsU9.lean` (U9 freeze §7); nothing to do. Their residual premises are `hag` (`ReflExprAgree`) and `hK` (`ShapeDenotes …`): 未供給 / この調査で経路未発見 (U10 freeze §1), not READKINDS rows |
| U10 premise **hg** `GetEnvFrame mctx mref cctx cref` | **closes to a cell-level premise from an existing base lemma**: `Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps {mctx mref cctx cref} (hk : ReadKeeps cref) : GetEnvFrame mctx mref cctx cref` (`Tools/ShippingStRefCorrespondence.lean:75`, axioms propext/Classical.choice/Quot.sound, built in unit SR2i). `ReadKeeps cref := ∀ w, readOf cref (getW cref w) = readOf cref w` is itself a PREMISE about the opaque `ST.Ref.get` (not proved of the runtime). Also `ReadWorld.readKeeps : ReadWorld r → ReadKeeps r`. So U11 replaces the premise `hg` (a statement about `getEnv`) by `hk` (a statement about the single cell `cref`); it is a change of premise, not a supply |
| U10 premise **hw1** (`ReadsAt env₀ cref w1` at the world after `coreHead`, for all matching triples) | 未供給 / この調査で経路未発見. `coreHead` (`Tools/ShippingEntryReadsLinked.lean:62`) begins with `IO.getEnv`, `IO.eprintln`, `Handle.mk/putStrLn` (class D in DG-ENV terms; owner `sparkle-gen5-dg-env`), then `ST.Ref.get/set` on other cells. The base has `envFrame_set` (needs `SetFrame r cref`, `r.ref ≠ cref.ref`, premises) for the `set` steps; no base lemma was found for the IO steps. It also needs the tie between the `readMachine` start world `w` and the synthesis start world `ws` (env tie / C0, DG-ENV). Not touched |
| `h0` | `readsAt_self cref w` for `env₀ := envAt cref w` (E1); not an `env₀` shared with the synthesis run (unchanged from U10) |
| env tie, `hall`, run existence, `ReadWorld` for DG-ENV `EnvFrameEnd`, coverage, `FReachC`, hq, FG | not READKINDS rows or owned by other Issues (DG-ENV `sparkle-gen5-dg-env`, DG-COVER `sparkle-gen5-dg-cover`, DG-DATAOF `sparkle-gen5-dg-dataof`, DG-RUNREADS `sparkle-gen5-dg-runreads`, `sparkle-gen5-dg-closingrun`); named only |

## 2. First unit to implement: **U11** (one theorem), base-only, no new premise class
Reason: it is the only open row of this Issue for which the survey found an existing, named, built supplier in the base (`getEnvFrame_of_readKeeps`); U9a/U9b are already done, and hw1 / hag / hK were searched and no route was found. U11 does not shrink what DG-ENV must deliver for C0; it only restates U10c's `hg` in terms of the same cell condition (`ReadKeeps cref`, implied by `ReadWorld cref`) that DG-ENV's `EnvFrameEnd` rows also use (`ReadWorld cref`, per U10 freeze §1), so the two premise lists are comparable. Nothing is claimed about whether `ReadKeeps cref` holds of the runtime.

`open`: `Lean Meta`, `Sparkle.Compiler.Elab`, `Tools.ShippingEntrySoundness` (`RunsTo`), `Tools.ShippingMachineCommand Tools.ShippingMachineEntry`, `Tools.ShippingGen5ReadKinds` (`Read`, `readMachine`).
Imports: `Tools.ShippingGen5ReadKindsU10`, `Tools.ShippingStRefCorrespondence`.

```lean
theorem readMachine_agrees_runReads_of_readKeeps {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
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
Route: `Tools.ShippingGen5ReadKindsU10.readMachine_agrees_runReads_framed (Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps hk) hrun R h0 hw1 hX` (the conclusion and all other binders are U10c's, verbatim; only `hg` is replaced by `hk`). `getEnvFrame_of_readKeeps` takes `mctx mref cctx cref` implicitly (its `variable` block), so they are inferred from `hrun`/`R`.
Premises that remain: `hk`, `h0`, `hw1`, the two runs (`hrun`, `R`), `hX`. Conditional = intermediate.

## 3. Rows not implemented in U11
hw1 (post-`coreHead` world; IO steps and the env tie), `hall`, run existence, `hag`, `hK`, coverage, reader trace, hq, FG: stay 未供給 / この調査で経路未発見. `envR = envR′` and `ci ∈ envR` are still not derived. No new law or TRUSTED boundary is needed, so no decision document.

## 4. Check plan (`Tests/Gen5/ReadKindsU11Check.lean`; same requirements as U10)
Written from this document, not from the Lean statement.
1. TYPE: independent `ExpU11` statement via `Tests.Gen3.ExpectedType`; positive control (separately written copy accepted). Real count reported (expected 2: theorem + control).
2. MUTANTS (well-typed single changes only; signature/defeq rejection, not semantic counterexamples): drop the `r.shape = shape` conjunct; drop `hX`; drop `h0`; replace `ReadKeeps cref` by `∀ w, readOf cref w = readOf cref w` is NOT used (trivially different premise, would be a weaker-hypothesis claim, not a single-token change); instead `hw1` conclusion `ReadsAt env₀ cref w1` → `ReadsAt env₀ cref w2` (keeps the ∀ w1 w2 w3 and three `RunsTo`), and the premise `hk : ReadKeeps cref` → `hk : ReadWorld cref` (well-typed, different statement). Target 5; actual number and the counting rule are reported.
3. COUNT: conjunct counts (auxiliary necessary condition only).
4. CLOSURE (`reach2` defined in the new Check as in U10): root itself tested against the forbid set; unknown constant = throw; negatives for an unknown root, a helper whose VALUE mentions an unknown name, an existing helper whose TYPE only mentions an unknown name; clean control; fixtures inside `withoutModifyingEnv`. Positive requirement: closure reaches `getEnvFrame_of_readKeeps` and `readMachine_agrees_runReads_framed`. `ReadKeeps` / `GetEnvFrame` recorded as FACTs (premise use), not forbidden; forbid set = `forbidConsts` minus `Expr.equal`/`eqv` as in U8–U10.
5. AXIOMS: `propext` / `Classical.choice` / `Quot.sound` only. No sorry.
Counts are reported as real numbers with partition and counting rule. The Check is built on the committed tree itself; header NOT BUILT until a pod build succeeds. After a Lean commit this agent leaves the Issue `doing` and records "clean build is the coder's".

## 5. Not claimed
`ReadKeeps cref` of the runtime, hw1, env tie / C0 / `hall`, `ReadWorld`, existence of the runs, `envR = envR′`, `ci ∈ envR`, `hag`, `hK`, `GateDefines`, `srcDom`, `ls`/`outs`/`nexts`, hq, coverage, FG, M5. The Issue stays open.

## 6. Questions for the reviewer
(a) Is U11 (a premise restatement `hg ↦ hk`, no new content beyond composing two built theorems) acceptable as the next unit, or should the effort go to a hw1 route (IO steps of `coreHead`), which this survey did not find?
(b) Is the mutant `ReadKeeps → ReadWorld` acceptable as a "single change"?
