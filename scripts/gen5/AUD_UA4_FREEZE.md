# U-A4 / U-A5 freeze: 葉の `letsAliasOk` row（`leafAlias`）— 前提の追加 1 件（reviewer 承認待ち）

- Issue: sparkle-aud-ua4。base: f0f6a8d8。根拠: scripts/gen5/AUD_UA4_STUDY4.md（scratch は elaborate 済み、sorry なし、標準 axiom のみ）。文書のみ。
- 「見つからなかった」は、この調査では `Pkg` 上の既存行が見つからなかったという意味で、導出不能の証明ではない。

## 1. 追加する前提（完全な型）
`T1Hyp` の `DataOk : Pkg ι dom → Prop` に対する行（T1 台帳に追加、`hLeafAlias`）:

```lean
hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true
```

`letsAliasOk` は `Tools/ShippingMachineClosesData.lean:157`（`aliasOk d.bpos d.vpos (d.nIn + d.ss.length) d.letFields`）。`DataOkB`（SrcPkg 上、T1L-32）の 2 つ目の conjunct と同じ Bool。`insts = []` に限るのは葉だけが `closes_of_data` を使うため（calls 親は `T1Hyp.closes` から `MachineClosesAtA` を得る）。

## 2. 用途
葉の `MachineCloses mctx' mref cctx' cref c d.shape`（全 ctx、`seqChild_of_realA` が要る）を `closes_of_data`（`d.letsOk` = `insts = []` ∧ `letsAliasOk`）から出す。`MachineClosesAtA` から `MachineCloses` は出ない（STUDY3 §2）。

## 3. 台帳の数の変化
- 追加: T1 +1（`hLeafAlias`）。FG の変更なし。
- 消える見込み（条件付き、E-3/B3 の実装・受理後）: E-3 −1、B3 −1。
- 台帳（受入済み）: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。条件付き台帳: FG −2 +0 相当（E-3, B3）/ T1 +1。
- 他の field（`callsOk`・`ss.length`・`hdomB`・`outTy`・`noMemRow`）は既存行 T1L-12 / T1L-04 から出るので追加なし。`noMemName` は足さない（偽になりうる、STUDY4 §0）。

## 4. 選択肢（reviewer）
1. 承認: `hLeafAlias` を T1 に +1 として追加。
2. 既存行への読み替え: T1L-32（`DataOkB` の `letsAliasOk`）と同一視して数を増やさない（`Pkg` 上の DataOk と `SrcPkg` 上の DataOkB は別物なので、同一視の可否は reviewer の判断。この調査は同一視していない）。
3. 別経路（Tools/Prototype/DGenConnect の `dgen_connect_gen` 系）で `letsAliasOk` を出す: その open 前提（`ShippedToProto` など）が新たに要る。この調査では台帳の既存行との対応を確認できなかった。
推奨: 1（数が正直）。可逆性: 追加した行は、後で 2 や 3 で払えたら消せる。
