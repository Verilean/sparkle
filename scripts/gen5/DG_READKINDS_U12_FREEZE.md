# DG-READKINDS U12 freeze (Issue sparkle-gen5-dg-readkinds; base 23a7b6ce = U11 approved be8ff28d + header sync, branch kjob/g5rk-r19) — DESIGN ONLY, no Lean yet

Extends `DG_READKINDS_FREEZE.md` and the U5–U11 freezes. Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU12.lean`, `Tests/Gen5/ReadKindsU12Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, any built file (U9/U10/U11 files untouched); no new TRUSTED boundary / law / axiom;
FG not reduced; `GenWF` not strengthened; no sorry / native_decide; hq not adopted.

Wording: "未供給 / この調査で辿った候補経路では未供給" describes this survey (what was read in this branch), not impossibility or non-derivability.
A "mutant" is a rejection by signature/defeq of a changed statement, not a semantic counterexample. A result resting on a named premise is
**conditional = intermediate**, never a supply. Nothing below is reader coverage, C0, or an FG supply; the Issue stays open.
Synced first (comment/docs only, 23a7b6ce): U11 headers now record build rk18v-be8ff28d (TYPE 1 theorem + positive 1, MUTANT 5).

## 1. Survey of the remaining rows (this branch only; every name below was read in the tree)

Kept as stated (nothing changes): `ReadKeeps` is a sufficient condition only; `hk`, `hw1`, C0 / runtime / FG are not supplied. U9c proof-accept is the manager's run (`kjob/g5rk-u9c-*` untouched). Rows owned by other Issues are only named: env tie / C0 / `hall` / `ioEnv` (`sparkle-gen5-dg-env`), coverage (`sparkle-gen5-dg-cover`), run existence (`sparkle-gen5-dg-runreads`, `sparkle-gen5-dg-closingrun`).

| row | status after this survey |
|---|---|
| `hk : ReadKeeps cref` | premise about the opaque `ST.Ref.get`; `ReadWorld.readKeeps` (`Tools/ShippingStRefCorrespondence.lean:50`) gives it from `ReadWorld cref`. No route to either from the runtime was found in this survey. 未供給 |
| `h0 : ReadsAt env₀ cref w` | `readsAt_self cref w : ReadsAt (envAt cref w) cref w` (E1) closes it for `env₀ := envAt cref w`; unchanged |
| **`hw1` (U10/U11 premise)** | It is `∀ w1 w2 w3, RunsTo (getConstInfo X) … w1 ci w2 → RunsTo getEnv … w2 envR w3 → RunsTo getEnv … w3 envR' w5 → ReadsAt env₀ cref w1`: the world `w1` is **not** tied to the synthesis run's own `coreHead` run. U9's body (`readMachine_agrees_runReads_at`, lines 49–51) only uses it at the run's own `(w1, w2, w3)` from `R.chain`. A `w1` that is linked to `ws` through `RunsTo (coreHead X) … ws s w1` is obtainable from `R.chain`, and then `ReadsAt env₀ cref w1` follows from **`ReadsAt env₀ cref ws`** and an **`EnvFrame` of `coreHead X`** by existing `Tools.ShippingGen5Env.ReadsAt.of_frame` (E3). The ∀-form `hw1` does not follow from the linked form (no uniqueness of `w1` was found), so U9's theorem cannot be reused; its short body is re-proved in the new file |
| `EnvFrame (coreHead X)` (new premise `hHead`) | **not supplied by this survey**. `coreHead` (`Tools/ShippingEntryReadsLinked.lean:62`) runs `IO.getEnv`, `IO.eprintln`, `IO.FS.Handle.mk/putStrLn` (class D, DG-ENV `ioEnv`), then `ST.Ref.get/set` on the other cells `sparkle*`. Existing base pieces: `EnvFrame.pure/bind` (`Tools/ShippingEnvSnapshot.lean:48,53`), `envFrame_getConstInfo`, `envFrame_set` (needs `SetFrame r cref` and `r.ref ≠ cref.ref` per cell). Not found in the candidate routes followed: an `EnvFrame` for the IO steps and `SetFrame` facts for the cells. Candidate for a later unit (partial: the `set`-only suffix of `coreHead`, premises `SetFrame` per cell) — not part of U12 |
| `ReadsAt env₀ cref ws` (new premise `h0s`) and its tie to `h0` | the env tie between the `readMachine` start world `w` and the synthesis start world `ws`: DG-ENV C0 territory, premise only. Not touched |

## 2. First unit to implement: **U12** (two theorems), base-only
Reason: of the open rows, `hw1` is the only one whose premise can be **replaced by two cell/head-level premises using only existing built lemmas** (E3 `ReadsAt.of_frame`, `getEnvFrame_of_readKeeps`, U9/U10 structure). It makes the `hw1` premise's content explicit (what must hold of `coreHead`, and which start world), and removes the over-strong `∀ w1` quantifier, which was not a statement about the actual run. It is a **change of premise, not a supply**: `hHead`, `h0s` and `hk` are premises. U9a/U9b are already implemented (U9); `hag`/`hK` and the IO steps of `coreHead` were searched and no route was found in the candidate routes followed.

`open`: `Lean Meta`, `Sparkle.Compiler.Elab`, `Tools.ShippingEntrySoundness` (`RunsTo`), `Tools.ShippingMachineCommand Tools.ShippingMachineEntry`, `Tools.ShippingGen5ReadKinds` (`Read`, `readMachine`), `Tools.Prototype.DGenProv`.
Imports: `Tools.ShippingGen5ReadKindsU11`, `Tools.ShippingEntryReadsLinked`, `Tools.ShippingEnvSnapshot`.

### U12a
```lean
theorem readsAt_chain_of_head {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name}
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {env₀ : Lean.Environment} {ws w1 w2 w3 w5 : Void IO.RealWorld}
    {s : Tools.ShippingEntryReadsLinked.CoreSaved} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref ws s w1)
    (hget : RunsTo (Lean.getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5) :
    Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
      Tools.ShippingGen5Env.ReadsAt env₀ cref w3
```
Proof sketch: `h1 := ReadsAt.of_frame hHead hh h0s`; `h2 := ReadsAt.of_frame (envFrame_getConstInfo X hg) hget h1`; `h3 := ReadsAt.of_frame hg henv h2`. (`henv'` and `w5` are unused in the proof; they are kept so the premise list matches `R.chain`; if the build warns of unused variables they stay.)

### U12b
```lean
theorem readMachine_agrees_runReads_of_head {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape
```
Proof sketch: `subst hX`; `hg := getEnvFrame_of_readKeeps hk`; `obtain ⟨_, w1, w2, w3, _, _, _, _, hget, henv, henv', _⟩ := R.chain` with the head run `hh` also taken from `R.chain` (its second component after `s`); `readsAt_chain_of_head hg hHead h0s hh hget henv henv'` gives `hA1 hA2 hA3`; then U9's remaining steps (`readMachine_run hrun`, `ci_of_readsAt`, `envR_of_readsAt`, `h1_of_h0 hg h0` for the first `getEnv`) verbatim, as in `readMachine_agrees_runReads_at` lines 52–69. The only change from U11 is: `hw1` (∀-triples) and `hg`/`hk` → `hk`, `hHead`, `h0s`.
Premises that remain: `hk`, `hHead`, `h0`, `h0s`, the two runs, `hX`. Conditional = intermediate.

## 3. Rows not implemented in U12
`hHead` supply (IO steps of `coreHead`, `SetFrame` of the `set` cells), env tie `h0` ↔ `h0s`, `hall`, run existence, `hag`, `hK`, coverage, reader trace, hq, FG: 未供給 / この調査で辿った候補経路では未供給. `envR = envR′` and `ci ∈ envR` are still not derived. No new law or TRUSTED boundary is needed, so no decision document.

## 4. Check plan (`Tests/Gen5/ReadKindsU12Check.lean`; same requirements as U11)
Written from this document, not from the Lean statement.
1. TYPE: independent `ExpU12a`, `ExpU12b` via `Tests.Gen3.ExpectedType`; one positive control (separately written copy accepted). Real count reported (expected 3: 2 theorems + 1 control).
2. MUTANTS (well-typed single changes only; signature/defeq rejection, not semantic counterexamples), U12b: drop `r.shape = shape`; drop `hX`; drop `h0`; drop `h0s`; `h0s` at `w` instead of `ws`.  U12a mutant: drop `h0s`. Target 6 in total, reported split as single-theorem/composite with the counting rule; if a mutant fails to elaborate it is reported as ill-typed and not counted.
3. COUNT: conjunct counts (auxiliary necessary condition only).
4. CLOSURE (`reach2` as in U11): root itself tested against the forbid set; unknown constant = throw; negatives for an unknown root, a helper whose VALUE mentions an unknown name, an existing helper whose TYPE only mentions an unknown name; clean control; fixtures inside `withoutModifyingEnv`. Positive requirements: U12b reaches `readsAt_chain_of_head` and `getEnvFrame_of_readKeeps`; U12a reaches `ReadsAt.of_frame` and `envFrame_getConstInfo`. `ReadKeeps` / `GetEnvFrame` / `EnvFrame` recorded as FACTs (premise use), not forbidden; forbid set = `forbidConsts` minus `Expr.equal`/`eqv` as in U8–U11.
5. AXIOMS: `propext` / `Classical.choice` / `Quot.sound` only (U12a probably none beyond these). No sorry.
The Check is built on the committed tree itself; header NOT BUILT until a pod build succeeds. After a Lean commit this agent leaves the Issue `doing` and records "clean build is the coder's".

## 5. Not claimed
`ReadKeeps cref` or `EnvFrame (coreHead X)` of the runtime, `ReadsAt env₀ cref ws`, hw1 supply, env tie / C0 / `hall`, `ReadWorld`, existence of the runs, `envR = envR′`, `ci ∈ envR`, `hag`, `hK`, `GateDefines`, `srcDom`, `ls`/`outs`/`nexts`, hq, coverage, FG, M5. The Issue stays open.

## 6. Questions for the reviewer
(a) Is replacing the ∀-triple `hw1` by `hHead` + `h0s` (premises, not supplies) acceptable as the next unit, given that `hHead` includes class-D IO steps owned by DG-ENV?
(b) Is the re-proof of U9's short body in the new file acceptable (U9 is built and cannot be changed here)?
