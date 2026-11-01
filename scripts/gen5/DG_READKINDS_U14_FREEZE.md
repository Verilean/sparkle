# DG-READKINDS U14 freeze (Issue sparkle-gen5-dg-readkinds; base 5cbcdc6a = U13 approved 25540b18 + header sync, branch kjob/g5rk-r23) — DESIGN ONLY, no Lean yet

Extends `DG_READKINDS_U13_FREEZE.md` (ledger §1, survey §2). Sections not named here are unchanged.
New Lean only in NEW files `Tools/ShippingGen5ReadKindsU14.lean`, `Tests/Gen5/ReadKindsU14Check.lean` (lakefile `lean_lib` additions only).
No edit of the compiler, `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, any built file (U9–U13 untouched except comment-only header syncs);
no new TRUSTED boundary / law / axiom; FG not reduced; `GenWF` not strengthened; no sorry / native_decide; hq not adopted. No decision document is needed.

Wording: "未供給 / この調査で辿った候補経路では未供給" describes what was read in this branch, not impossibility or non-derivability.
A "mutant" is a rejection by signature/defeq of a changed statement, not a semantic counterexample. A result resting on a named premise is
**conditional = intermediate**, never a supply. Nothing below is reader coverage, C0, or an FG supply; the Issue stays open.

Step 1 (done, comment only, 5cbcdc6a): U13 headers record build rk22v-25540b18 (exit 0, 827 jobs, dirty=false, approved at 25540b18);
counts as in the approved log: TYPE 3 comparisons (theorem + positive control + U12b-type negative control), propositional mutants 6.

## 1. Survey: which remaining rows the actual run pays (what was read: `Tools/ShippingGen5ReadKindsU12.lean` proof, `U10 h1_of_h0`, `Tools/ShippingGen5Env.lean`, `Tools/ShippingEnvSnapshot.lean`, `Tools/ShippingStRefCorrespondence.lean`, `RunReadsAt`)

Where the premises are consumed in the U12b/U13 proof (this is the finding that drives the unit):
| premise | quantifier shape in U13 | where the proof uses it |
|---|---|---|
| `hk : ReadKeeps cref` | every world `∀ w` | only through `getEnvFrame_of_readKeeps` → `GetEnvFrame` (every `getEnv` run), applied to exactly three actual runs: the machine's `getEnv` run `w → v1` (inside `h1_of_h0`), the core chain's `getConstInfo X` run `w1 → w2` (via `envFrame_getConstInfo`) and the core chain's `getEnv` run `w2 → w3` |
| `hHead : EnvFrame (coreHead X)` | every world, every run of `coreHead X` | applied to exactly one actual run: `coreHead X` `ws → w1` |
| `h0s : ReadsAt (envAt cref w) cref ws` | one world | kept |

| row | paid by the actual run? | finding |
|---|---|---|
| `h0` | yes (U13, `readsAt_self`) | done |
| `hk`, `hHead` | not as stated | They are statements over all worlds / all runs; the actual runs only say the steps returned. Candidate routes followed: `runsTo_det` (determinism only), `R.chain` (lists the runs, says nothing about `envAt` across them), `readMachine_run` (gives the machine's `getEnv`/`getConstInfo` results, `getEnv_value` gives `env = envAt cref w` for the first read; nothing relates `envAt cref v1` to `envAt cref w`). 未供給 |
| `h0s` | no | tie between the two runs' start worlds (DG-ENV C0). 未供給 |
| `hrun`, `R` | run existence (other Issues) | unchanged |

Conclusion of this survey: **no further row is paid directly by the actual run** (`h0` was the only one). What the survey did find is that `hk` and `hHead` are
stronger than the proof needs: it needs only four environment equalities along the actual runs. U14 states the premises in that exact (weaker) form.
Alternatives considered and not chosen: (a) a per-step premise list (`envAt w2 = envAt w1` etc. as separate hypotheses) — needs the existential worlds of `R.chain`, so it must be a ∀ over the chain anyway, hence the bundled `hC` below; (b) merging `h0s` and `hC` into one premise `ReadsAt (envAt cref w) cref w3`-style — stronger than the parts, not a reduction; (c) a partial `EnvFrame` for the `set`-only suffix of `coreHead` — needs `SetFrame` premises with no named payer and does not close `EnvFrame (coreHead X)`.

## 2. Next unit: **U14** (premise weakening; first to implement)

Reason: it is the only candidate found that strictly weakens premises without adding any unpaid kind of premise: `hk` and `hHead` (all worlds) are replaced by `hM` and `hC` (only the machine's `getEnv` run from `w`, and the head/`getConstInfo`/`getEnv` runs from `ws`). By U14a/U14b below, `hk` and `hHead` imply `hM` and `hC` (law-free), so U13 is a corollary of U14 (U14d) — the converse is not claimed. **This is a weakening of the premise statements, not a supply**: who pays `hM`/`hC` is the same unassigned row as `hk`/`hHead` (the `ioEnv`/`ST.Ref.get` environment-frame facts; assignment to `sparkle-gen5-dg-env` not confirmed). No unit-count of premises is claimed to drop (2 stay 2); what drops is their scope.

`open`: `Lean Meta`, `Sparkle.Compiler.Elab`, `Tools.ShippingEntrySoundness` (`RunsTo`), `Tools.ShippingMachineCommand Tools.ShippingMachineEntry`, `Tools.ShippingGen5ReadKinds` (`Read`, `readMachine`), `Tools.ShippingEntryReadsLinked (envAt coreHead CoreSaved)`.
Imports: `Tools.ShippingGen5ReadKindsU13`.
Common binders for all: `{mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}`.

### U14a (machine getEnv tie from `hk`)
```lean
theorem tieM_of_readKeeps {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref) (w : Void IO.RealWorld) :
    ∀ (e : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref w e v1 →
        Tools.ShippingEntryReadsLinked.envAt cref v1 = Tools.ShippingEntryReadsLinked.envAt cref w
```
Proof: `fun e v1 h => Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps hk w e v1 h`.

### U14b (chain tie from `hk` and `hHead`)
```lean
theorem tieC_of_head {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {X : Lean.Name}
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    (ws : Void IO.RealWorld) :
    ∀ (s : Tools.ShippingEntryReadsLinked.CoreSaved) (w1 w2 w3 : Void IO.RealWorld)
      (ci : Lean.ConstantInfo) (e : Lean.Environment),
      RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref ws s w1 →
      RunsTo (Lean.getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref w2 e w3 →
        Tools.ShippingEntryReadsLinked.envAt cref w1 = Tools.ShippingEntryReadsLinked.envAt cref ws ∧
        Tools.ShippingEntryReadsLinked.envAt cref w2 = Tools.ShippingEntryReadsLinked.envAt cref w1 ∧
        Tools.ShippingEntryReadsLinked.envAt cref w3 = Tools.ShippingEntryReadsLinked.envAt cref w2
```
Proof: `fun s w1 w2 w3 ci e hh hget henv => ⟨hHead ws s w1 hh, Tools.ShippingEnvSnapshot.envFrame_getConstInfo X (getEnvFrame_of_readKeeps hk) w1 ci w2 hget, getEnvFrame_of_readKeeps hk w2 e w3 henv⟩`.

### U14c (the weakened top theorem)
```lean
theorem readMachine_agrees_runReads_of_ties {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (hM : ∀ (e : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref w e v1 →
        Tools.ShippingEntryReadsLinked.envAt cref v1 = Tools.ShippingEntryReadsLinked.envAt cref w)
    (hC : ∀ (s : Tools.ShippingEntryReadsLinked.CoreSaved) (w1 w2 w3 : Void IO.RealWorld)
      (ci : Lean.ConstantInfo) (e : Lean.Environment),
      RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref ws s w1 →
      RunsTo (Lean.getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref w2 e w3 →
        Tools.ShippingEntryReadsLinked.envAt cref w1 = Tools.ShippingEntryReadsLinked.envAt cref ws ∧
        Tools.ShippingEntryReadsLinked.envAt cref w2 = Tools.ShippingEntryReadsLinked.envAt cref w1 ∧
        Tools.ShippingEntryReadsLinked.envAt cref w3 = Tools.ShippingEntryReadsLinked.envAt cref w2)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X) :
    r.entry = Sparkle.Compiler.Elab.entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
      (Sparkle.Compiler.Elab.userInliner envR) (Sparkle.Compiler.Elab.structEnv envR) ∧
      r.shape = shape
```
Proof: as U12b with `env₀ := envAt cref w`; `h0 := readsAt_self cref w`; `h1 := ReadsAt.of_envEq (hM env v1 he) h0`; destruct `R.chain` and use `hC s w1 w2 w3 ci envR hh hget henv` with `ReadsAt.of_envEq` three times from `h0s`; rest identical to U12b (the `rw [p1..s3]` tail).
Rationale for the shape of `hC`: the worlds `w1..w3` are existentials inside `R.chain`, so the premise cannot name them; it is a ∀ over the three chain runs *starting at the single world `ws`* (`runsTo_det` makes those runs unique, so it speaks of the one actual chain).

### U14d (U13 as a corollary — shows the weakening is strict in direction)
```lean
theorem readMachine_agrees_runReads_of_head_self_of_ties {declName X : Lean.Name} {allowGate : Bool}
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
(the U13 statement). Proof: `readMachine_agrees_runReads_of_ties hrun R (tieM_of_readKeeps hk w) (tieC_of_head hk hHead ws) h0s hX`. Its being accepted shows `hk`,`hHead` ⇒ `hM`,`hC`; the converse is not claimed.

## 3. Ledger after U14 (top theorem U14c)
| premise | status |
|---|---|
| `hk`, `hHead` | **removed from the top theorem U14c** (replaced, not supplied); remain only in the corollary U14d |
| `hM` (machine `getEnv` run from `w` keeps `envAt`) | **introduced** as a premise; payer: same unassigned row as `hk` (`ST.Ref.get` environment-frame); implied by `hk` (U14a). 未供給 |
| `hC` (head, `getConstInfo X`, `getEnv` chain runs from `ws` keep `envAt`) | **introduced** as a premise; payer: same unassigned rows as `hk`+`hHead`; implied by them (U14b). 未供給 |
| `h0s : ReadsAt (envAt cref w) cref ws` | remains (run-start-world tie, DG-ENV C0). 未供給 |
| `hrun`, `R` | run existence (other Issues), unchanged |
| `hX` | binding only |
| `h0`, free `env₀` | stay resolved (U13) |
Also unsupplied: hall / C0, coverage, hag, hK, ReadWorld, `envR = envR'`, `ci ∈ envR`, hq, FG. U9c untouched.
The ledger's earlier "not supplied" rows (hk, hHead, h0s) are unchanged in status: this survey's candidate routes did not supply them.

## 4. Check plan (`Tests/Gen5/ReadKindsU14Check.lean`; same requirements as U13)
Written from this document, not from the Lean statements.
1. TYPE: independent `ExpU14a/b/c/d` via `Tests.Gen3.ExpectedType`; positive control per theorem family (separately written copy accepted); negative controls: U13's own type is NOT accepted as `ExpU14c` (premises `hk`/`hHead` present, `hM`/`hC` absent). Real count reported by the Check itself in one line (theorems + positive + negative).
2. MUTANTS (well-typed single changes only; signature/defeq rejection, not semantic counterexamples), on U14c: drop `r.shape = shape`; drop `hX`; drop `h0s`; `h0s` at `w` instead of `ws`; `hM` world `v1` ↔ `w` swapped (`envAt w = envAt v1`); `hC` first conjunct drops `ws` (`envAt w1 = envAt w`); `hC` missing the `getEnv` run premise; `hM` quantified at `ws` instead of `w`. Each checked to elaborate; ill-typed ones reported and not counted.
3. COUNT: conjunct counts (auxiliary necessary condition only).
4. CLOSURE (`reach2` as in U13): root tested against the forbid set; unknown constant = throw; negatives for an unknown root, a helper whose VALUE mentions an unknown name, a helper whose TYPE only mentions an unknown name; clean control; fixtures inside `withoutModifyingEnv`. Required suppliers reached (assert): `readsAt_self`, `ReadsAt.of_envEq`, `getEnvFrame_of_readKeeps` (U14a/b/d), `envFrame_getConstInfo` (U14b). `ReadKeeps`/`EnvFrame` recorded as FACTs for U14c (expected: not reached) and for U14d (reached as premises).
5. AXIOMS: standard three only; sorry absent.
6. Build: `kjob lake build Tools.ShippingGen5ReadKindsU14` then `Tests.Gen5.ReadKindsU14Check`, one at a time. After the Lean commit the Issue stays `doing`; the clean issue-linked build is the coder's.
