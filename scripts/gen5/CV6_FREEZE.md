# CV6: `rowB1_of_inv` から `hcb` を取らない（FG 台帳 C.CV-6）

Issue: `sparkle-ledger-cv6`（親 `sparkle-ledger-shorten`）。base: aab355f2。実装: `Tools/ShippingGen5Cover3R.lean`、検査: `Tests/Gen5/Cover3RCheck.lean`。
台帳（受入済み）: FG 87 / T1 57。この文書は台帳を変えない。コーダー指示により freeze と実装を続けて出す（review にしない）。

## 0. 減算表

| 項目 | 内容 |
|---|---|
| 消える ID | C.CV-6（`hcb`、リーフ） |
| 消える条件 | §2 の文の受理（reviewer: 前提の除去）と exact-head の clean build。`rowB1_of_data` に `hcb` の束縛変数が残らないこと（BINDERS） |
| 残る条件 | `ShapeAgree`、`FullInv`（C.SM-6 の他の行）、R-in / R-dom（readerTrace_final 側、§12.8） |
| root theorem | `rowB1_of_data`（部品 `hcb_of_data`） |
| 台帳への効果 | FG −1（87 → 86、リーフ −1）の見込み。受理前なので「台帳:」行は動かさない（条件付き台帳: FG 86 / T1 57） |
| 新しい TRUSTED / law / コンパイラ変更 | なし。既存ファイル・共有定義は変えない |
| 新しい前提の行 | なし（下の `hms` `hd` は `machineShape?` / `dataOfAt` の結果という入力の事実で、台帳の行ではない。数え方に異論があれば reviewer が判断） |

## 1. 何をするか

`hcb`（entry `k` の binder が `kDOf d + k` にあり、その kind が entry の kind）を、`d` を作った 2 つの関数の結果から証明の中で出す。

* `machineShape?_callBinder`: `machineShape? … (.defnInfo dd) … = some sp` から `mixedGatePeel (packTupleInputs dd.value) = some (bs, e)` と `(sp.binders.map (·.2))[bs.length + k]? = (sp.insts.map (·.2.2))[k]?`。
* `dataOfFrom_nIn` / `dataOfFrom_dims`: `dataOfAt lvl (.defnInfo dd) senv' sp = some d` は `dataOfFrom … (packTupleInputs dd.value) …` に展開され、`mixedGatePeel (packTupleInputs dd.value) = some p ∧ d.nIn = p.1.length + sp.insts.length ∧ d.shape = sp`。
* 同じ `dd` から同じ `mixedGatePeel` の結果なので `bs.length = p.1.length`、よって `kDOf d = d.nIn − insts.length = bs.length`。

一致の調査: 必要な一致は **`machineShape?` と `dataOfAt` が同じ定数 `dd`（と同じ `sp`）に対して走っていること**だけで、`senv`・`allow`・`sym`・`params`・`lvl` は一致不要（証明に使わない）。この一致を readerTrace_final や DataOf 系の既存定理が run から供給しているかは、この調査では確認していない（`dataOfAt` の `E` と run の `sp` の接続は DataOfDims.lean 冒頭に「Not supplied」とある）。この一致は新定理の仮説（`hms` `hd` が同じ `dd` `sp` を共有する形）として現れる。

## 2. 凍結する文（Lean の字面。`Cover3RCheck` の Expected と同じ）

```lean
theorem hcb_of_data {sym : Bool} {params : List (String × Nat)} {dd : DefinitionVal} {senv senv' : StructEnv}
    {allow : Bool} {sp : MachineShape} {lvl : Lean.Expr → Nat} {d : MachineData}
    (hms : machineShape? sym params (.defnInfo dd) senv allow = some sp)
    (hd : dataOfAt lvl (.defnInfo dd) senv' sp = some d) :
    ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2

theorem rowB1_of_data {d : MachineData} {nDecl : Nat} {st : MachRead} (hag : ShapeAgree d st) (hi : FullInv nDecl st)
    {sym : Bool} {params : List (String × Nat)} {dd : DefinitionVal} {senv senv' : StructEnv}
    {allow : Bool} {sp : MachineShape} {lvl : Lean.Expr → Nat}
    (hms : machineShape? sym params (.defnInfo dd) senv allow = some sp)
    (hd : dataOfAt lvl (.defnInfo dd) senv' sp = some d) :
    ∀ k, k < d.shape.insts.length → callKind d k ≠ .domain
```

結論は `rowB1_of_inv` と同じ。`rowB1_of_data := rowB1_of_inv hag hi (hcb_of_data hms hd)`。

## 3. 行との対応（Prop 束縛変数）

`rowB1_of_inv`: `[hag, hi, hcb, k<…]` → `rowB1_of_data`: `[hag, hi, hms, hd, k<…]`。`hcb` が消え、入力の事実 `hms` `hd` が入る。

## 4. 検査（`Tests/Gen5/Cover3RCheck.lean`）

TYPE（Expected は §2 の字面、`Tests.Gen3.ExpectedType.checkExpected`）、MUTANT（`hms` なし／旧の文（`hcb` あり）／結論 `= .domain`。いずれも signature / defeq での棄却であって意味的反例ではない）、BINDERS（`rowB1_of_inv` の Prop 束縛変数列 − `hcb` + `[hms, hd]` を機械比較）、AXIOMS（標準 3 つ）。

## 5. 主張しないこと

* `machineShape?` / `dataOfAt` が実際の run で `some` であること、両者が同じ `dd` `sp` に対して走ること（readerTrace_final 側で供給する必要があるかを含め、この調査では供給元・経路を確認していない）。
* `ShapeAgree`・`FullInv` の供給、R-in / R-dom、FG 台帳の数の変更。
* 非空虚性（`hms` `hd` を満たす具体例の構成）。

## 6. 追加（coder、2026-11-05）: 任意の定数 `E` の版

run の `RunReadsAt.shapeEq` は `machineShape? false [] (entryConst …) (structEnv envR') = some p.d.shape` で、定数は `entryConst …`（`.defnInfo` とは限らない形）。
`machineShape?` は `.defnInfo` 以外で `none` なので、`some sp` なら定義の場合だけが残る（`machineShape?_noMemRow` と同じ場合分け）。
そこで `hcb_of_dataE` / `rowB1_of_dataE` は `hms : machineShape? sym params E senv allow = some sp`、`hd : dataOfAt lvl E senv' sp = some d` を任意の `E` で取る（他は §2 と同じ）。
これで `hms` は run の `shapeEq` をそのまま当てられる形になる。`hd`（同じ `E`・`sp` の `dataOfAt`）は C.SM-1 の被覆半分（既存の行）。
