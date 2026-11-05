# B4（hdisjD）の範囲: ユーザー判断 (3) の明記と corpus の測定

Issue: `sparkle-aud-ua4`（B-AUD U-A4/U-A5）。
判断: ユーザー 2026-11-03「3で」（`scripts/gen5/AUD_B4_DECISION.md` §3 の案 (3)）。文は変えず、範囲を明記して、子孫を共有する設計の本数を測る。

台帳: FG 94 / T1 54（今回 0 / 0）。前提は足さず、減らさず、文も変えていない。

## 1. 明記する内容

* FG の前提 D.E-4 の B4（`hdisjD`）は、次のどれかが成り立つ 2 つの呼び出しで偽になる:
  * 異なる callee（または同じ callee で異なる memKey）を呼ぶ 2 つの呼び出しで、
  * 一方の子の design が他方の子の module 名を含むか、
  * 2 つの子の design が同じ名前の module（共有する子孫）を含む。
* B4 が偽になる宣言を含む設計については、FG は**空虚にしか成り立たない**（何も保証しない）。
* FG の文はそのまま。この限定は、台帳（`scripts/gen2/PREMISE_LEDGER.md` §12.5）と FG の説明（`scripts/gen2/GENERAL_SPEC.md` §1.1）に書く。
* 保証を広げる道は案 (2)（B4 を「同じ名前の module は等しい」`CacheAgrees` 型に置き換える）。供給の当てがまだ無いので、今は進めない。下の測定の結果がその判断の材料になる。

## 2. 測定

### 2.1 方法

* 入力: corpus の pass 1 の出力。`scripts/shipping-coverage/run.sh` の `PASSES=1` で、`11ba0bd8`（par/rt-fuel-perf-impl）の 479 ファイル。測定の出力はソースツリーの外にある。
* 道具: `scripts/gen5/b4_shared_desc.py OUT_DIR`。
  * 出力された Verilog から、module ごとに instantiate する module 名を読む。
  * 親 module P の 2 つの instance が異なる module A ≠ B を指し、`desc*(A) ∩ desc*(B) ≠ ∅` のとき違反と数える。`desc*(X)` は X 自身と、X から到達できる全ての module。
  * 同じ module を 2 回呼ぶのは違反にしない。B4 の前提が「異なる callee か memKey」だからである。
  * memory module（`SparkleMem_*`）を含めた場合と除いた場合の両方を出す。
* 確認:
  * 出力に入っている Verilog の instance 行は 106 本で、全て読めた。
  * `inst…` / `_tmp_inst_…` を含む残り 29 行は、テストの log 文で、Verilog ではない。
  * 同じ親と子の組は 1 本にまとめたので、(親, 子) の組は 90。

### 2.2 結果

| 区分 | ファイル数 |
|---|---|
| corpus の出力 | 479 |
| Verilog を出力する | 123 |
| その中で instance を 1 つ以上持つ（階層がある） | 29 |
| **B4 が偽（共有する子孫あり）** | **1**（memory module を含めても除いても同じ） |

* 違反の 1 本は `Tests/Compiler/SubInstanceKeyTest.lean`（3 組）。
  * 例: `gTopWR` の子 `gR` と `gW` が、どちらも `kSD` を使う。
  * この test は、instance の port map の衝突を調べるための probe で、わざと子孫を共有させている。
* 残りの 28 本は 0 本だった。
  * うち 22 本は `IP/` の設計か、それを合成する test。対象は AESHW、RV32 Pipeline、YOLOv8 ActivationBuffer、PCIe、Ecdsa / P256 / Policy sign demo、Keccak、SHA、Net の各 test、Fido2 など。
  * 残る 6 本は `Tests/Compiler` と `Tests/Synthesis` の小さな階層の test。

### 2.3 この測定が言わないこと

* **Verilog を出さないファイルは数えていない**（479 − 123 = 356）。そこには、証明用の fixture で `#synthesizeVerilog` の文字列を出さないものが入る。既知の例 `mixDeep`（`Tests/Compiler/NoPortsMixDeepTest.lean`）もその 1 つで、子孫を共有する。
* **出力された module の階層だけを見ている。**
  * 呼び出し先が親に inline された場合や、展開された場合は、Verilog に別の module として現れない。
  * B4 が見る design の module 名の集合（`desNames`）と、出力の module 一覧が一致することは、この測定では確かめていない。
* **memKey は見えない。** 同じ callee を異なる memKey で 2 回呼び、それぞれが同名の module を持つ場合は、数え漏れる。
* corpus は全ての設計ではない。0 本は「corpus の IP 設計では当たらなかった」という意味で、他の設計で当たらないことの証明ではない。

## 3. 結論と次

* 範囲の限定（§1）は台帳と FG の説明に書いた。
* corpus の階層がある設計 29 本のうち、子孫を共有するのは probe の 1 本だけだった。今の corpus では、案 (2) に進む根拠は弱い。
* 子孫を共有する設計が増えたら案 (2) を再検討する。例えば、共通の部品 module を複数の子から使う IP を足したときで、そのときはこの道具で測り直す。
* 台帳: FG 94 / T1 54（今回 0 / 0）。
