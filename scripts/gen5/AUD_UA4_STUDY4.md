# U-A4 / U-A5 調査 4: DataRes2 の 5 field の供給（具体 DataOk、noMemName）— skeleton（下書き）

- Issue: sparkle-aud-ua4。base: f0f6a8d8（STUDY3 承認済み）。文書のみ。Lean のソースは編集しない（scratch は `kjob lake env lean`、ソースツリーに入れない）。
- 台帳: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。受入の数は動かさない。
- 「見つからなかった」は、この調査では供給元・経路が見つからなかったという意味で、不可能・導出不能の証明ではない。

## 0. 途中の読み（確認中、結論ではない）
1. `noMemName`（one-output 親の `memChild? x.1 = none`）は、台帳 A.P-26 と Tests/Compiler/MemNameCollisionPlainCertTest.lean:178 `collPlainCD_nomem_false` により、正当な one-output 親（memory placeholder 名の ordinary callee）で **FALSE** と記録されている。従って「新前提 +1」ではなく、DataOk に足すと有効な設計を除く（FG の縮小）ことになる。`core_kids_facts_ranA` が `hnomem` を使うのは `nomem_tag`（起源半分 `.1`）だけに見えるので、起源半分だけの O-copy で名前半分は不要になる見込み（scratch で確認中）。
2. 具体 DataOk（T1L-11/12 の行 `hMemRow : DataOk q → MemParentDataOk q ∧ ExtInS q`）は `MemParentDataOkB` = `ok ∧ callsOk kD ∧ ss.length ∧ outTy ∧ (binders.drop kD に domain なし)`。したがって `callsRows`（callsOk, ss.length, hdomB）と `outTy` は T1L-12 から出る（確認中）。
3. `leafAlias`（`letsAliasOk`）は `LeafDataOkB` / `MemParentDataOkB` に無く、`DataOkB`（SrcPkg 上、T1L-32）にある（確認中）。
