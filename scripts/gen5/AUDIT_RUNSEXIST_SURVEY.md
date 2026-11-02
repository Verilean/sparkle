# AUDIT RUNSEXIST 調査（B-AUD: 非 top の RunsExistAt を既存定理から導く経路）

状態: 下書き（調査中）。Lean は scratch のみ。mutant はなし。

## 経路（この調査で辿ったもの）
1. `RealChildA O c y`（`Tools/ShippingChildCacheA.lean:105`）の `run` コンストラクタは、admissible context（`AdmCtx`）と `RunsTo (synthesizeCombinational c) …` を持つ。ここから `synthesizeCombinational_parts`（`ShippingGateChildComb.lean:139`）と `core_chain`（`ShippingEntryReadsLinked`）で `getConstInfo c` と `getEnv` の run が出る（top の `runsExist_top` と同じ手順）。
2. 子の `RealChildA`: `machineRanA_main`（`ShippingParentRanA.lean:64`）が `MachineRanA`（`ChildrenRealA O shape children` を含む、`ShippingChildRunAKids.lean:51`）を与える。`ChildrenRealA` の k 番目は `instOrigins.child? = some y ∨ RealChildA O (insts[k]).1 y`。`TgtRun.call` の `ord`（`child? = none`）で左を除くと `RealChildA`。
3. top の `RealChildA`: `Start`（`AdmCtx ∧ JQC O 0 w`）と `RealChildA.of_jqc`（`ShippingChildCacheA.lean:160`）。
(続きは scratch の elaborate 後に記入)
