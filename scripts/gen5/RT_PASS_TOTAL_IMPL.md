# RT S2: MachRecUnfold の全域化（ユーザー判断 A）— 実装と検証の記録

Issue: `sparkle-rt-pass-total`。判断資料: `scripts/gen5/RT_PASS_DECISION.md`（ab7cfbe0、ユーザーは案 A を採用）。調査: `scripts/gen5/RT_PASS_TOTAL_SURVEY.md`（7f6b7880）。
台帳: FG 94 / T1 56（この単位は台帳を動かさない。保存の定理 pass_ph は別の単位）。

## 1. 変更点（compiler）

| commit | 内容 |
|---|---|
| de368dad（rt40） | `Sparkle/Compiler/MachRecUnfold.lean`: `partial` を外して全域化。`iota` / `reduceHead` / `relevantClosure` は構造再帰（挙動不変）。`headBetaM` / `betaAll` / `listLit?` / `passM` は燃料つき。燃料は構造的でない再入だけで減らし、部分項への再帰では減らさない。燃料切れは `Except String` で返し、メモ表には入れない。`Sparkle/Compiler/Elab.lean`: `userInlinerE`（燃料切れを返す版）、`userInliner`、`userInlinerError?`（コマンドでコンパイルエラーにする）。呼び出し側だけの最小の変更。`Tests/Compiler/MachRecUnfoldFuelTest.lean`（AllTests から import）、`Tools/ShippingInlCand.lean` の追従 |
| f017f97e（rt62） | 4 つの上限（`headBetaLimit` / `betaAllLimit` / `listLitLimit` / `passLimit`）を 1 つの定数 `fuelLimit` にまとめた（挙動不変） |
| 8a616cbc（coder） | `fuelLimit := 10000`（下の実測から決めた） |

燃料切れのメッセージ: `MachRecUnfold.<定義名>: fuel exhausted (limit <上限> <単位>)` と、宣言名・位置。

## 2. 上限の決め方（ユーザー: 「回路だから IP で実際に適用可能かを見て決める」）

| 上限 | 対象 | 結果 | job |
|---|---|---|---|
| 100 | IP | `IP/YOLOv8/Blocks/ConvBnSiLU.lean:68` の `convBnSiLU` が `passM` で燃料切れ（re-entries 100） | rt52 の build |
| 1000 | IP の corpus 43 本（モジュールとして build） | 43 本すべて build、燃料切れ 0 | fuel1000-ipf（exit 0、369 jobs） |
| 1000 | Tests / Examples の全モジュール（1 回の build） | 燃料切れ 0。失敗 25 件 | fuelte-l1000 |
| base（全域化前、ab7cfbe0） | 同上 | 失敗 25 件。失敗した target の集合と各 target の最初の error 行は上限 1000 と完全に一致（燃料・全域化とは無関係の既存の失敗） | fuelte-base |

→ 100 では足りず、1000 で全 corpus が足りる。10 倍のゆとりを見て **10000**。上限の値は証明に入らない（保存の定理は任意の燃料で成り立つ形にする）。

## 3. 生成物の比較（base ab7cfbe0 と 8a616cbc）

方法: 両方の計測用コピーに一時的な `lean_lib CorpusCmp`（corpus 462 本のうち両方で build できた 456 本）を足し、1 回の `kjob lake env` の中で build と `scripts/shipping-coverage/run.sh` の pass 1（生成物だけ）を続けて行った。比較は `scripts/shipping-coverage/compare_outputs.py`。jobs: ptcmp-base-ab7cfbe0、ptcmp-new-8a616cbc（どちらも exit 0、44 分）。

| 項目 | 結果 |
|---|---|
| ファイル数 | 478（両側とも） |
| 各ファイルの終了状態 | 両側で完全に一致（exit 0: 461、exit 1: 16、abort: 1） |
| compare_outputs.py | identical 437、renumbered 0、different 41、missing 0 |
| different 41 本の中身 | **どれも Verilog（`module … endmodule`）を含まない**。差は監査の出力（PROJECT OPAQUE の数 42 → 40、`passM` と `relevantClosure.go` が partial の一覧から消えた、閉包の定数の数）、`[profile]` の時間、heartbeats の数だけ |
| Verilog を含むファイル | 437 本すべて identical |

→ 生成される Verilog は全件で変わらない（測定であって証明ではない）。

## 4. 燃料切れになる条件（挙動が変わりうる入力）

展開の段数が 10000 を超える入力だけ。今の corpus では 1000 を超えるものは無い。そのような入力は、全域化前の compiler では極端に遅いか止まらない（RT_PASS_TOTAL_SURVEY §2）。全域化後は、理由つきのコンパイルエラーで止まる。

## 5. 残り

- exact-head build と AllTests（ptv2-8a616cbc）。
- 保存の定理 `pass_ph`（NoPh ∧ BvarLt の保存）と `RecRulePhU` の登録は別の単位（sparkle-rt-inline-compose の PassPh を外す）。
