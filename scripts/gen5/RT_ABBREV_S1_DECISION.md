# 判断資料: inline 枝の `inlAbbrevs` のために TRUSTED 前提（T1）を純 +1 してよいか

Issue: `sparkle-rt-abbrev-s1`（親 `sparkle-gen5-dg-readertrace`）。技術的な詳細は `scripts/gen5/RT_ABBREV_S1_FREEZE.md`（rev2）。
**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0、未登録）。採用して登録した場合は FG ±0、T1 54 → 55（純 +1）。**
この資料はユーザーの判断用。reviewer が freeze を見た後に coder がユーザーへ出す。判断が出るまで Lean の実装・登録には進まない。

## 1. 前提知識なしで分かる説明

Sparkle のコンパイラの「front-end のインライナ」には、型エイリアス（`abbrev`）を値で置き換える `inlAbbrevs` という関数がある（`Sparkle/Compiler/Elab.lean` 3376）。内部で Lean 本体（core）の 2 つの関数を呼ぶ。

* `Expr.replace`: 式の中の部分式を置き換える。実体は C++（`lean_replace_expr`）で、Lean の論理の中には本体が無い（`opaque`）。
* `Expr.headBeta`: `(fun x => b) a` を `b[x := a]` に直す。内部で `betaRev`（Lean の `partial def`、論理の中では本体が見えない）と、C++ の `instantiate` / `instantiateRange` を使う。

証明したいこと: 「`inlAbbrevs` は、プレースホルダを含まず、束縛変数が閉じている式を、その性質のまま返す」（`NoPh ∧ BvarLt 0` の保存）。これは inline 枝（`hdecl`）を閉じるのに要る。しかし上の 2 つは論理の中で中身が見えないので、そのままでは証明できない。

方針（ユーザー既定）: 「C++ / opaque の振る舞いは小さな明示的仮定にして、合成法則はそこから証明する」。

## 2. 何を信頼に足すか（2 文）

1. **`Expr.replace f e` は、同じ `f` と `e` に対する構造再帰の版 `Expr.replaceNoCache f e` と同じ式を返す**（`ReplaceAgrees`）。C++ の `replace` は共有部分式の結果を覚えておく（キャッシュする）だけで、`f` が純関数なので結果は変わらない、というソースの読みに基づく。
2. **`NoPh e` かつ `BvarLt 0 e` を満たす式 `e` について、core の `e.headBeta` は、Lean で書いた全域なモデル `headBetaSpec e` と同じ式を返す**（`HeadBetaAgrees0`）。`headBetaSpec` は core の `headBeta` / `betaRev` / `instantiate` / `instantiateRange` と同じ計算を、構造再帰の def で書き写したもの。

保存（`NoPh ∧ BvarLt 0`）そのものは仮定ではなく、文 2 から**定理として証明する**（`headBeta_good`）。`inlAbbrevs` についての保存も、文 1・文 2 と既存の候補 `DeclValuePh`（N1-a）から証明する（`inlAbbrevs_ph`）。どれも scratch（コミットしない作業ファイル）で `sorry` なしに通した。

## 3. 台帳への影響

| 単位 | FG | T1 | 内訳 |
|---|---|---|---|
| 文 1（U-1） | ±0 | **±0** | 一般形 `ReplaceAgrees` を登録し、既存の `ZeroLitAgrees0`（T1L-54）は、これから導出できる（scratch で確認）ので定理に降格。付け替えで純差分 0 |
| 文 2（U-2） | ±0 | **+1** | `HeadBetaAgrees0` を新規登録 |
| 合計 | ±0 | **+1（54 → 55）** | FG（保証）の変更・縮小は無い。新しい law・TRUSTED 境界の変更も無い。T1 の新規 1 件だけ |

## 4. 選択肢

### 選択肢 A: 採る（推奨）

文 1・文 2 を登録（T1 純 +1）。`ZeroLitAgrees0` は降格。
* 影響（利用者に見える影響）: なし。コンパイラの出力・振る舞いは変わらない。証明側の前提の台帳だけが 1 増える。データ損失の有無: なし。
* 得られるもの: `inlAbbrevs` の `NoPh ∧ BvarLt 0` 保存が仮定付きで証明に入り、inline 枝の `hdecl` の道が開く（他に `DeclValuePh` の扱いと、`rounds` / `MachRecUnfold.pass`（S2）が別に要る。それらはこの判断の範囲外）。
* コスト: 登録と証明の実装（新規ファイル、scratch 相当 ~370 行）、`ZeroLitAgrees0` の使用側の付け替え（編集範囲は未計測）、レビューと clean build。
* リスク: 仮定が偽だと、その上の定理は空になる。根拠は C++ / Lean ソースの読みと、rev1 での 8 式の実行時照合だけで、形式証明ではない。`betaRev` が `partial def` であることの読みは Lean ソースの読みで、C++ の読みではない。toolchain 更新時は再確認が要る。

### 選択肢 B: 採らない（inline 枝の `inlAbbrevs` が未解消のまま）

何も登録しない（台帳 0/0）。
* 影響: 利用者に見える影響なし。inline 枝の `hdecl`（`inlAbbrevs` の保存）は閉じない。当面は `shapeInputs_of_direct` で進める rev18/19 の選択を続け、他の枝は止まらない。
* コスト: 今は 0。ただし inline 枝を完全に閉じる目標が残る間は、いつか同じ判断が要る。
* リスク: なし（現状維持）。

## 5. 推奨と理由

**A を推奨。** 理由: (1) 純 +1 で、保存則そのものを信頼するのではなく、振る舞いの一致だけを信頼し、保存は証明した（ユーザー方針に沿う）。(2) 仮定の範囲を `NoPh ∧ BvarLt 0` の入力に限った。(3) U-1 は既存の T1 と置き換えなので増えない。
ただし根拠は読みと有限の照合であり、「成り立つと証明した」わけではない。この調査では成り立たない例は見つからなかったが、それは成り立つことの証明ではない。

## 6. 後から変えられるか（可逆性）

* 登録は新規ファイル `Tools/Assume/AbbrevExtern.lean`（予定）に閉じ、既存の共有定義・コンパイラ・FG は変えない。後で取り下げるには、この仮定に依存する定理（`inlAbbrevs_ph` 等、新規ファイル内）を外す。**取り下げ可能。**
* `ZeroLitAgrees0` の降格は、その使用側の付け替えを伴う。戻すことはできるが、編集が要る。
* 将来、C++ の `replace` や `instantiate` の形式的な仕様が core に入れば、仮定を定理に置き換えて台帳を減らせる。

## 7. 判断しない場合

選択肢 B と同じ状態が続く（inline 枝の `inlAbbrevs` は未解消、台帳は 0/0）。Issue は `decision` のまま。他の枝は止まらない。

## 8. 根拠

* `scripts/gen5/RT_ABBREV_S1_FREEZE.md`（rev2）: 完全型（§1.1, §2.2, §2.3）、C++ / core の引用（§1.3, §2.4）、scratch の `#check` 出力と axiom 一覧（§4）、台帳（§5）、未確認事項（§7）。
* reviewer の変更依頼（Issue `sparkle-rt-abbrev-s1` の履歴、796b3ff4 に対するもの）に対応した改訂。
* toolchain: `leanprover/lean4:v4.32.1`（commit f054605a）。`kernel/instantiate.cpp`（sha256 先頭 42527c96）、`kernel/replace_fn.cpp`（2edfa172）を読んだ。
* 注意: 検査（signature / defeq での mutant の棄却）は行っていない。意味的反例の探索もしていない。
