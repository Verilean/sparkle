# DG-READERTRACE freeze rev20 補遺（`readF_domKeep` は型どおりに閉じない: `Expr.eqv` が opaque）

対象 Issue: `sparkle-rt-rev20`。base: `par/rt-rev20` cf7eaa4a。文書のみ。Lean は編集していない。
**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。** 型は変えていない。この補遺は rev20 の実装を始めて、`readF_domKeep` の 4 腕で止まった報告で、解決策の提案は選択肢の列挙まで。

## 1. 何が足りないか

rev20 §1 の表は、`dom` を書く 5 箇所について「検査を通れば `dom' = d`（検査で `d` に等しい）」としている。検査は次の形:

| 箇所（Elab / Defs） | 検査 |
|---|---|
| conv bare register: Elab 3928 / Defs `domGuard st.dom dom'` | `d0 != dom'` なら失敗 |
| `machReserve`（nested から）: Elab 3709 | `d != dom'` なら失敗 |
| inst `domain` 引数: Elab 4067 / `instArg` | `d != v'` なら失敗 |
| instS `domain` 引数: Elab 4106 / `instSArg` | `d != v'` なら失敗 |
| loopRoot: Elab 4216 / Defs `domGuard` | `d0 != dom'` なら失敗 |

`!=` は `BEq Lean.Expr` で、これは `Lean.Expr.eqv`（`@[extern "lean_expr_eqv"] opaque eqv (a b : @& Expr) : Bool`、toolchain v4.32.1 の `Lean/Expr.lean:809-813`）。`LawfulBEq Expr` のインスタンスはこの調査で辿った範囲に見つからず、`eqv` は opaque なので `(d != dom') = false` から `dom' = d` を取り出す補題は Lean 側にない。`eqv` はコンパイラ側の実装では binder 名などを無視する比較なので、`==` で等しい別の項に `dom` が置き換わる経路が、型の上でも実装の上でも残る。同じ指摘は `Tools/ShippingGen3ArgSupply2.lean` のヘッダ（`dom` may be replaced by an `==`-equal … but different term）にすでにある。

したがって `DomKeep`（結論が `(callOut c v).dom = some d` の項の等式）は、conv（bare register）/ nested（`machReserve`）/ loopRoot の 3 箇所の書き込みで、`some dom' = some d` を導く段が **新しい前提なしには閉じない**（この調査では、前提なしで閉じる経路は見つからなかった。不可能の主張ではなく、`eqv` を opaque のまま扱う限り、その段に使える事実が手元にないという意味）。

腕ごとの状況（実装は始めていない。R5 `readF_good`（`ShippingReaderFuelR5.lean`、`LenOk` の保存）と同じ骨格 `Sat` / `sat_bindO` / `step_good` で証明する計画を立て、その上で書き込み箇所を数えた）:

| 腕 | 結果 |
|---|---|
| conv | bare register の書き込み（Elab 3933）で上記の段が要る。他の分岐は record 更新と再帰のみで骨格どおり |
| nested | `machReserve` の `dom := some dom'`（上記）で同じ段が要る |
| inst / instS | `domain` 引数の `d != v'` を通った枝は状態を変えない（`some (js, st)`）ので、この 2 腕は **等式が要らずに閉じる**。ただし `none` 枝の書き込み `dom := some v'` は入力 `dom = some d` では到達しない。したがって inst / instS は前提不要（rev20 の表の「通れば状態は変わらない」どおり） |
| chain / loopBody | `dom` を直接書かない。conv / loopRoot の帰納仮定に従う |
| loopRoot | 書き込み `dom := some dom'`（Elab 4235）で上記の段が要る |

つまり前提が要るのは、`dom` を **別の項で上書きする** 3 つの箇所（conv bare register、`machReserve`、loopRoot）。inst / instS は閉じる。chain / loopBody は conv / loopRoot の保存に依存するので、その 3 箇所が閉じなければ 7 腕は全体として閉じない。

## 2. 選択肢（決めない。reviewer / coder / ユーザーの判断事項）

いずれも型を変えるか前提を足すので、rev20 の承認範囲を超える。

* **(A) 前提を足す。** `ExprEqvLawful : ∀ a b : Lean.Expr, (a == b) = true → a = b`（または `dom` に現れる項だけに限定した形）を `readF_domKeep` の hypothesis にする。台帳の FG/T1 に 1 行増える見込み（未計数）。実装の `eqv` は binder 名を無視するので、この前提は **一般には偽**で、`dom` が `_machIn i` fvar / 定数のとき（binder を含まない）に限って成り立つ。限定形（`DomForm d → DomForm d' → d == d' → d = d'` 相当）なら成り立つ見込みだが、それも `eqv` の意味についての事実で、opaque のままでは証明できない。
* **(B) `DomKeep` の結論を弱める。** `(callOut c v).dom = some d` を `∃ d', (callOut c v).dom = some d' ∧ (d' == d) = true` にする。`DomForm` の側は項の形を使うので、`eqv` 同値な項への移行が `machDom?` の成功を保つことが別に要る（これも `eqv` の事実）。`machineShapeF_reach'` の `hform` の用意が変わる。
* **(C) D-a（`DomAtomicRun`、FG +1 見込み）に戻す。** rev20 §4 の「D-b を実装して閉じなかったときだけ」の枝。`RT_DOM_SURVEY` §1.3。
* **(D) 現状維持（判断しない場合）。** `DomAtomic dom` を持つ既存の `MidInputs` / `ShapeInputs` / `shapeInputs_of_direct`（rev19）が残る。primed 版は作らない。

## 3. 実施したことと、していないこと

* 実施: freeze 全文、`ShippingReaderFuelDefs.lean` の 7 本の step、`ShippingReaderFuelR5.lean`（`LenOk` 保存の `Sat` 骨格）、`Elab.lean` の書き込み箇所、`Expr.eqv` の宣言の読取り。
* していない: Lean の編集、build、`DomKeep` 以外の primed 定義の実装（`DomKeep` の結果に `machineShapeF_reach'` が依存するため、止めた。`nDeclOfCi` / `bs_len_eq` / `hbs_of_nDeclOfCi` / `shapeInputs_of_direct'` は `DomKeep` に依存しないが、`shapeInputs_of'` が `ShapeInputs'` 経由で primed の定義を共有するので、方針が決まってから一括で実装する）。
* 主張しない: `readF_domKeep` が証明できないこと（`eqv` の事実が前提に加われば閉じる見込みで、閉じることも確認していない）、(A)〜(C) のどれかが正しいこと。
