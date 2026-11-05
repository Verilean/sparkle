# D.D-7 freeze: remove `hno : NoRawBelow D raw.name (n+1) raw` from the top transport theorems (issue sparkle-ledger-dd7, base 74343ad8)
**Design only in this commit; no Lean.** No new law/TRUSTED, no compiler/shared-definition edit, no sorry/axiom/native_decide.

## Subtraction table
| field | content |
|---|---|
| 消える台帳 ID | FG premise-ledger row D.D-7 (`hno : NoRawBelow D raw.name (n+1) raw`; def `Tools/ShippingGen5DCEntryR.lean`) |
| 消える条件 | the binder `hno` of the topmost theorems `resetNk_transport` (DCEntryR:50) and `runModuleTG_transport` (DCEntryT:156), for the core module `raw` |
| 入る束縛変数 | none new. `Start` (A.P-02) = `hS`; the real core run `RunsTo (synthesizeCombinationalCore declName [] false) … (raw, D)` = `hr`; `PostEntry b raw D D'` = `hpost`; `MachineDefines` (A.P-06 / `T1Hyp.defines`) = `hdef`; `MachineClosesAtA` (`T1Hyp.closes`) = `hcl`; package data `d : MachineData` (`T1Hyp.pkg` / DataOk). Case split on `MachineRanA` inside the proof (no binder). |
| 残る条件 | the data rows needed by the leaf case (`d.ok`, `hbody`, `callsOk`, `hslots`, `hdomB`) are taken only if they are fields of an existing counted row (DataOk / LeafDataOk ok, callsOk, ss.length); see §Leaf. `hins`/`hf` (U-CORENR) are removed: replaced by the `MachineRanA` split. (a3) see §(a3). |
| root theorem | `Tools.ShippingGen5DCEntryV.coreRun_transportAll` (and `resetNk_transportR`), new file `Tools/ShippingGen5DCEntryV.lean` |
| 台帳への効果 | FG -1 (D.D-7) only if the topmost binder list lacks `hno` and every part (one-output, group, leaf) is supplied; otherwise 0 |
| 新しい TRUSTED | なし |

## Plan
1. `noRawBelow_of_coreRunAll`: from `hS hr hdef hcl` (+ data), `∀ k, NoRawBelow D raw.name k raw`, by `MachineRanA` split (Tools/ShippingParentRanA.lean:47):
   one-output = `noRawBelow_of_coreRun` proof; group = `closeInstsG_acyclic` pattern (Gen2GroupServed:318-326) + `noRawBelow_of_closeInstsG`; leaf = raw.body has no `inst` (closedBody_kinds_of_run + noInstOfB_of_seqOk) so `NoRawBelow` is vacuous.
2. `resetNk_transportR`, `coreRun_transportAll` = the old conclusions with `hno` discharged by 1.
3. §(a3): `checkedOptimize b` instance statements are a subset of `raw`'s (module names only).

## Binders (as written in `Tools/ShippingGen5DCEntryV.lean`)
Common: `{ι dom mref cref} {L : Laws mref cref} {mctx cctx} {w w1} {declName} {b raw D D'} (p : Pkg ι dom)`,
`hS : Start L mctx cctx w` (A.P-02), `hr : RunsTo (synthesizeCombinationalCore declName [] false) … (raw, D) w1` (real core run),
`hpost : PostEntry b raw D D'`, `hdef : MachineDefines mctx mref cctx cref declName p.d.shape` (A.P-06 / `T1Hyp.defines`),
`hcl : MachineClosesAtA L.O mctx cctx declName p.d.shape` (`T1Hyp.closes`), `hdata : LeafDataOk p ∨ MemParentDataOk p` (the package `p` is
`T1Hyp.pkg`'s `q`, `hdata` its `DataOk`). Removed from U `coreRun_transport`: `d : MachineData` (now `p.d`), `hins`, `hf`.
- `noRawBelow_of_coreRunAll … : ∀ k, NoRawBelow D raw.name k raw`
- `resetNk_transportR … (n) (kids) : ResetNk n raw D kids ↔ ResetNk n raw D' kids`
- `coreRun_transportAll … (n we seed T s) : runModuleTG … D' … raw.body … = runModuleTG … D … raw.body …`
- (a3) `coreRun_transportOpt` (with `hdata : MemParentDataOk p`): the same at `(checkedOptimize b).body`.

## §Leaf
`MachineRanA` leaf branch: raw = `closeMachine layout t'`, D = `d₀`. `closedBody_kinds_of_run` (needs `Pkg.ok p`, `Pkg.body_eq p`, `callsOk p.kD`,
`ss.length`, and `hdomB`) gives the body is `seqStmtOk` and `d₀.modules = []`; `noInstOfB_of_seqOk` + `noInstOf_of_B` +
`noRawBelow_of_noInstOf`. The data used: `Pkg.ok`/`Pkg.body_eq` (properties of every package, no binder), `callsOk`, `ss.length` (fields of
`LeafDataOk` and of `MemParentDataOk`, both listed in the ledger as DataOk), and `hdomB`, DERIVED for a leaf (`hdomB_of_leaf`: `callsOk` gives
`kD = nIn` when `insts = []`, then `ok` gives slot/let binders non-domain). Nothing is assumed beyond those rows.

## §(a3)
Closed (conditional on the same rows, but `hdata : MemParentDataOk p`, because for a parent `hdomB` (`binders.drop kD` has no domain binder) is
the `domB` field of `MemParentDataOk`; it is not derivable from `ok`/`callsOk`).
`checkedOptimize_inst_subset_of_coreRun`: every `inst` in `(checkedOptimize b).body` is in `raw.body`.
leaf: `raw.body` is `seqOk`, hence `b` (`dropZeroWidth_seqOk`, `mergeChecked_seqOk`), hence `checkedOptimize b` (`checkedOptimize_seqOk_all`),
which has no `inst`. Parent: `hierGate b` (`core_hierGate_anyO`) and `b.body = raw.body` (`core_bodyEq_ranO`), then
`checkedOptimize_inst_iff_gate`. The side conditions (hierGate/hierBinds) are derived from the run, not binders.
`noRawBelow_mono` transfers `NoRawBelow` along an instance-subset. The unchecked last branch of `checkedOptimize` (`else o`) is excluded by the gate.
