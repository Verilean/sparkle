# DG-READKINDS U13 freeze (Issue sparkle-gen5-dg-readkinds; base 4d033bb3 = U12 approved 2591bbc0 + header sync, branch kjob/g5rk-r21) — DESIGN ONLY, no Lean yet

Extends `DG_READKINDS_FREEZE.md` and the U5–U12 freezes. Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU13.lean`, `Tests/Gen5/ReadKindsU13Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, any built file (U9–U12 files untouched except the comment-only header sync in 4d033bb3);
no new TRUSTED boundary / law / axiom; FG not reduced; `GenWF` not strengthened; no sorry / native_decide; hq not adopted.

Wording: "未供給 / この調査で辿った候補経路では未供給" describes this survey (what was read in this branch), not impossibility or non-derivability.
A "mutant" is a rejection by signature/defeq of a changed statement, not a semantic counterexample. A result resting on a named premise is
**conditional = intermediate**, never a supply. Nothing below is reader coverage, C0, or an FG supply; the Issue stays open.

Step 1 (done, comment only, 4d033bb3): U12 headers record build rk20v-2591bbc0 (exit 0, 826 jobs, TYPE 3 / MUT 6 / AX 2, approved at 2591bbc0).

## 1. Premise ledger of the composed DG-READKINDS theorem

Top theorem now: `Tools.ShippingGen5ReadKindsU12.readMachine_agrees_runReads_of_head` (U12b). It reaches U9c's body (re-proved), U10b `h1_of_h0`, U11's `getEnvFrame_of_readKeeps`, U12a. Its hypotheses, by name and type (read from `Tools/ShippingGen5ReadKindsU12.lean`):

| premise | type (abbreviated namespaces) | who pays it | status |
|---|---|---|---|
| `hk` | `ReadKeeps cref` (`∀ w, readOf cref (getW cref w) = readOf cref w`) | 未割当 | premise on the opaque `ST.Ref.get`. `ReadWorld.readKeeps` gives it from `ReadWorld cref`; no route to either from the runtime was found in this survey |
| `hHead` | `EnvFrame (coreHead X) mctx mref cctx cref` | 未割当 (the IO steps share the name `ioEnv` with `sparkle-gen5-dg-env`; that assignment is not confirmed) | not supplied. `coreHead` runs `IO.getEnv`, `IO.eprintln`, `IO.FS.Handle.mk/putStrLn`, then `ST.Ref.get/set` on the `sparkle*` cells. Base pieces: `EnvFrame.pure/bind`, `envFrame_set` (needs `SetFrame r cref`, `r.ref ≠ cref.ref`). Not found in the candidate routes followed: an `EnvFrame` for the IO steps, a premise form for `ST.Ref.get` of a cell other than `cref` |
| `h0` | `ReadsAt env₀ cref w` | closed in the tree by `readsAt_self` (E1) for `env₀ := envAt cref w`; U12b still takes it as a hypothesis | **payable now** (U13 below) |
| `h0s` | `ReadsAt env₀ cref ws` | `sparkle-gen5-dg-env` (env tie / C0) | not supplied; `w` (readMachine start) and `ws` (core-run start) belong to two different runs and no link between them was found |
| `hrun` | `RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'` | `sparkle-gen5-dg-runreads` / `-closingrun` (run existence) | not supplied |
| `R` | `RunReadsAt … X ws ws' raw D b ci envR envR' shape w5 w6` | `sparkle-gen5-dg-runreads` (`runReads_of_run` RR3 builds it from `O`, `hA`, `JQ`/cache, `MachineDefines`, `MachineClosesAtA`) | not supplied here |
| `hX` | `declName = X` | trivial binding equation (no content beyond naming the same constant) | kept; not counted as a gap |

Also unsupplied, outside the theorem's hypotheses but needed by the larger goal: `hall` / C0 (`sparkle-gen5-dg-env`), coverage (`sparkle-gen5-dg-cover`), `hag`, `hK`, `ReadWorld`, `envR = envR'`, `ci ∈ envR`, hq, FG.

### Premises resolved / introduced by U9c–U12
| unit | introduced | resolved (as a premise of the top theorem) |
|---|---|---|
| U9c | `h0`, `h1`, `hR` (∀ triples), `hX` | — (conditional start) |
| U10 | `hg : GetEnvFrame`, `hw1` (∀ triples) | `h1` (derived from `h0` + `hg`, `h1_of_h0`), `hR` (derived from `hw1` + `hg`, `hR_of_w1`) |
| U11 | `hk : ReadKeeps cref` | `hg` (replaced via `getEnvFrame_of_readKeeps`; `ReadKeeps` is sufficient only, no converse) |
| U12 | `hHead`, `h0s` | `hw1` (replaced; ∀-form not derived from linked form, so a premise replacement, not a supply) |

Net: four of the original premises (`h1`, `hR`, `hg`, `hw1`) are gone from the top theorem; none was supplied from the runtime. All replacements are premises.

## 2. Survey: which rows can be paid from the actual run (readMachine run + `RunReadsAt` chain)

Read in this branch: `Tools/ShippingGen5RunReads.lean` (`RunReadsAt`: `run`, `chain` = head, getConstInfo, getEnv, getEnv, machine, log, cache, finally; `gates`; `shapeEq`), `Tools/ShippingEntryReadsLinked.lean` (`coreHead`, `core_chain`), `Tools/ShippingGen5Env.lean`, `Tools/ShippingEnvSnapshot.lean`, `Tools/ShippingStRefCorrespondence.lean`.

| row | from the real run? | finding |
|---|---|---|
| `hk` (ReadKeeps) | no | a statement about the opaque `ST.Ref.get`; nothing in `RunReadsAt` or the machine run speaks of the cell. Candidate route followed: `runsTo_det` (law-free) — gives determinism only, not `readOf cref (getW cref w) = readOf cref w`. 未供給 |
| `hHead` (EnvFrame coreHead) | not from `R.chain`: `hh` is a run, `EnvFrame` quantifies over all runs from all worlds | A per-run weakening (`envAt cref w1 = envAt cref ws` for the actual `hh`) would be what `of_frame` needs, but it is still not obtainable from the run's existence: the run only says the head returned. Decomposing by `EnvFrame.bind` leaves IO-step and `get`-of-other-cell premises with no named payer. 未供給 |
| `h0` (ReadsAt at the readMachine start `w`) | **yes, law-free** | `readsAt_self cref w : ReadsAt (envAt cref w) cref w`. Choose `env₀ := envAt cref w`. `env₀` is an implicit parameter of U12b that does not occur in its conclusion, so the choice is free. |
| `h0s` (ReadsAt at `ws`) | no | with `env₀ := envAt cref w` it becomes `ReadsAt (envAt cref w) cref ws`: a tie between two runs' start worlds (DG-ENV C0). The route `ReadsAt.of_envEq` needs `envAt cref ws = envAt cref w`, which is the tie itself. 未供給 |
| `hrun`, `R` | run existence | owned by other Issues; hypotheses stay |
| `hX` | binding only | not a gap |

Conclusion: **`h0` is the only row of the ledger that the actual run (its start world `w`) pays directly**, by an already-built law-free lemma. `hk`, `hHead`, `h0s` are not closed by the routes followed in this survey.

## 3. Next unit: **U13** (one theorem, base-only, REDUCES a premise)

Reason: it is the only candidate that removes a premise (`h0` and the free variable `env₀` of the top theorem's premise list) without introducing any new one. The remaining `h0s` becomes the concrete tie `ReadsAt (envAt cref w) cref ws`, which states DG-ENV's C0 in the form it would actually be supplied (start world of the readMachine run vs. start world of the core run). Alternatives considered and not chosen: (a) a partial `hHead` for the `set`-only suffix of `coreHead` — needs a `SetFrame` premise per cell with no named payer and does not close `EnvFrame (coreHead X)` since the IO steps stay; (b) weakening `h0s` to `envAt cref ws = envAt cref w` — a stronger premise (equation implies `ReadsAt` via E1/E2, not conversely), so not a reduction. No new premise is introduced by U13; no new law / TRUSTED; no decision document is needed.

`open`: `Lean Meta`, `Sparkle.Compiler.Elab`, `Tools.ShippingEntrySoundness` (`RunsTo`), `Tools.ShippingMachineCommand Tools.ShippingMachineEntry`, `Tools.ShippingGen5ReadKinds` (`Read`, `readMachine`).
Imports: `Tools.ShippingGen5ReadKindsU12`.

### U13
```lean
theorem readMachine_agrees_runReads_of_head_self {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X) :
    r.entry = Sparkle.Compiler.Elab.entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
      (Sparkle.Compiler.Elab.userInliner envR) (Sparkle.Compiler.Elab.structEnv envR) ∧
      r.shape = shape
```
(In the file the names are written as in U12b, with `open` as listed above; the statement is U12b with `h0` removed and `env₀ := envAt cref w`.)
Proof: `exact Tools.ShippingGen5ReadKindsU12.readMachine_agrees_runReads_of_head hk hHead hrun R (Tools.ShippingGen5Env.readsAt_self cref w) h0s hX`.
Premises that remain: `hk`, `hHead`, `h0s` (concrete tie), the two runs (`hrun`, `R`), `hX`. Conditional = intermediate. Not claimed: `hk`/`hHead` of the runtime, `h0s`, env tie / C0, `hall`, `ReadWorld`, run existence, `envR = envR'`, `ci ∈ envR`, hag, hK, hq, coverage, FG.

## 4. Check plan (`Tests/Gen5/ReadKindsU13Check.lean`; same requirements as U12)
Written from this document, not from the Lean statement.
1. TYPE: independent `ExpU13` via `Tests.Gen3.ExpectedType`; one positive control (separately written copy accepted); a negative control that U12b's own type is NOT accepted as `ExpU13` (premise `h0` / `env₀` present). Real count reported (expected 3: 1 theorem + 2 controls).
2. MUTANTS (well-typed single changes only; signature/defeq rejection, not semantic counterexamples): drop `r.shape = shape`; drop `hX`; drop `h0s`; `h0s` at `w` instead of `ws`; `h0s` with `envAt cref ws` as the environment instead of `envAt cref w`; drop `hHead`. Each is checked to elaborate; an ill-typed one is reported and not counted. Measured number reported, no number fixed in advance beyond "well-typed only".
3. COUNT: conjunct counts (auxiliary necessary condition only).
4. CLOSURE (`reach2` as in U12): root itself tested against the forbid set; unknown constant = throw; negatives for an unknown root, a helper whose VALUE mentions an unknown name, an existing helper whose TYPE only mentions an unknown name; clean control; fixtures inside `withoutModifyingEnv`. Required suppliers reached (assert): `readMachine_agrees_runReads_of_head` (U12b) and `readsAt_self`. `ReadKeeps` / `EnvFrame` recorded as FACTs (premise use), not forbidden; forbid set as in U12.
5. AXIOMS: `#print axioms`-equivalent via the same collector as U12, standard three only; sorry absent.
6. Build: `kjob lake build Tools.ShippingGen5ReadKindsU13` then `Tests.Gen5.ReadKindsU13Check`, one at a time. After the Lean commit the Issue stays `doing`; the clean issue-linked build is the coder's.
