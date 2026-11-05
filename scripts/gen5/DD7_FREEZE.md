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

## §Leaf / §(a3)
(to be filled in by the following commits with the exact obstacle or the closing lemma)
