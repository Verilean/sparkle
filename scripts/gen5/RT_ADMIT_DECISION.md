# 判断資料: reader の結果（readerTrace_final）が使う仮定を、受入済みの台帳に計上するか

Issue: `sparkle-gen5-dg-readertrace`。
根拠:
- reviewer 承認の `readerTrace_final`（378f8e31、par/rt-final）
- `scripts/gen2/LEDGER_SHORTEN_PLAN2.md` rev3.1 §2.1.1–§2.1.3（3e90ef74、承認済み）

台帳（受入済み）: FG 92 / T1 55。この資料では何も変えない。

## 1. 何の話か（前提知識なしで）

* コンパイラは、Lean の定義を回路の形に読み取る「reader」を持つ。一般定理（FG）は、その読み取りが正しいことを前提の行として持っている。今は C.RT-2、C.CV-2、C.CV-3 の 3 行。
* その読み取りが正しいことを、証明でかなり置き換えた。最終定理 `readerTrace_final` は、reviewer が承認し、build と監査も通っている。
* ただし、この証明はいくつかの**小さな明示の仮定**を使う。多くは、Lean の C++ 実装（`@[extern]`）や環境の中身についての事実で、Lean の中では証明できない。あなたの方針（2026-11-01）「外部の振る舞いは `Tools/Assume/` の小さな明示的な仮定にし、合成の法則はそこから証明する」に沿った形である。
* 決めること: **これらの仮定を台帳の正式な前提として計上し、その代わりに古い 3 行を消すか。**
  * 計上すると、reader の結果が受入済みの成果になる。
  * 計上しないと、reader の結果は「条件付き」のまま残り、古い 3 行も残る。

## 2. 仮定の一覧（すべて reviewer が個別に文を承認済み。証明はしていない）

| 仮定 | 台帳 | 一言で | 種類 |
|---|---|---|---|
| `DeclValuePh`（N1-a） | FG | 環境に入っている定義の本体には、占位子（placeholder）と範囲外の束縛変数が無い | 環境の中身についての事実 |
| `PackTupleInputsBridge`（N2-b） | FG | 入力の組をまとめるコンパイラの関数が、その Lean のモデルと同じ結果を返す（条件付きの入力で） | コンパイラ内部の `partial` / 外部関数の振る舞い |
| `RawNodePh`、`NormNodePh`（N3-b × 2） | FG | 節点を読み取る 2 つの関数が、占位子と範囲外の束縛変数を持ち込まない | 同上 |
| `RecRulePhU` | FG | 環境の再帰子（recursor）の規則の右辺に、占位子と範囲外の束縛変数が無い | 環境の中身についての事実 |
| `BetaNonTargetAgrees` | T1 | `Expr.beta` が、β 簡約の対象でない頭では単なる適用 `mkAppN` と同じ | C++ 実装の振る舞い |
| `ExprEqvLaws` | T1 | `Expr` の等価判定（C++ の `Expr.eqv`）が同値関係で、hash と整合し、不変条件を保つ | C++ 実装の振る舞い |
| `HeadBetaAgreesL` | T1 | C++ の `Expr.headBeta` が、Lean で書いた全域のモデルと同じ結果を返す | C++ 実装の振る舞い。既存の行 T1L-74 の置き換えで、行数は ±0 |

既存の行（変化なし）: `FuelBridge`（C.CV-4）、T1L-72 / 73 / 50 / 51 / 53、`SigTyClosed`、`InstSFieldsDet`。

## 3. 選択肢

| 案 | 内容 | 受入済みの台帳 | 保証の見え方 | コスト |
|---|---|---|---|---|
| **(A) 計上する** | 上の仮定を台帳の行として足す。読み取りの古い 3 行（C.RT-2、C.CV-2、C.CV-3）を消す | FG 92 → **94**（+5 −3）、T1 55 → **57**（+2） | 前提の数は 4 増える。ただし「reader が正しい」という大きな前提 3 行が、小さく読める事実 7 つに分かれる。そのうち 3 つは C++ の 1 関数の振る舞いで、ソースを読んで確かめられる | 小（台帳の文書と、Issue の完了） |
| (B) 計上しない（条件付きのまま） | 何も足さず、何も消さない | 92 / 55 のまま | reader の証明は存在するが、台帳の上では使っていない。FG の前提は「reader が正しい」の 3 行のまま | 0 |
| (C) 仮定を証明で置き換える | 仮定ごとに証明を探す | 見込み不明 | (A) より強い | 大。C++ の振る舞いは Lean の中では証明できない（方針のとおり仮定にした）。環境の中身の仮定は、環境を作る側（elaborator）の性質で、範囲が大きい |

数え方の細部（reviewer がすでに判断したもの。変えるならそのときに知らせる）:
* `ExprEqvLaws` は 3 つの条項を 1 行にまとめる（rev3 承認）。
* `HeadBetaAgreesL` は T1L-74 の置き換え（別の行にしない）。
* `RecRulePhU` は N1-a とは別の行。
* C.RT-2 を消してよいかは、reviewer の判断で「成立する範囲」として承認済み。

## 4. 推奨

**(A) 計上する。**

理由:
1. あなたの 2026-11-01 の方針（外部の振る舞いは小さな明示の仮定にし、そこから証明する）を、そのまま台帳に反映する形になる。
2. 前提の数は増える（FG +2、T1 +2）。しかし中身は、大きな 1 文「reader が正しい」から、1 つずつ読んで確かめられる小さな事実に替わる。数より読みやすさが良くなる。
3. (B) のままだと、承認済みの証明が台帳の上で何の役にも立たない。後続（被覆の行など）も reader の結果を使えない。

## 5. 後から変えられるか

変えられる。
* (A) の後で、ある仮定を証明できれば、その行を消せる（−1）。
* (A) を取り消すときも、台帳の記録を戻すだけで、コードの変更は要らない。
* (B) から (A) へは、いつでも移れる。

## 6. 判断しないとどうなるか

(B) と同じになる。reader の結果は条件付きのまま、台帳は FG 92 / T1 55 のまま。`sparkle-gen5-dg-readertrace` は完了できない（完了条件は受入）。

## 7. 根拠

* `readerTrace_final`（`Tools/ShippingGen5ReaderTraceFinal.lean`、378f8e31）:
  * exact-head build `rtfv-378f8e31` exit 0（838 jobs）
  * Check: TYPE 1 / MUTANT 3 / BINDERS 21（16 hypotheses）/ CLOSURE / AXIOMS 標準 3 つ
  * reviewer 承認 2026-11-03
* 仮定の文:
  * `Tools/Assume/EnvDeclValue.lean`、`PackTupleBridge.lean`、`NormNodePh.lean`、`ExprEqvGL.lean`、`AbbrevExtern.lean:90`
  * `Tools/PassPh/Defs.lean:17,23`
  * 各 freeze（RT_U2_FREEZE §1、RT_RECRULE_FREEZE §1.2、RT_PASS_PH_FREEZE rev3）
* 行ごとの増減: `LEDGER_SHORTEN_PLAN2.md` §2.1.1。
  * 計画は FG 93 を基準に FG 95 と書いている。A.P-22 の表示変更（−1）の後なので、今の見込みは FG 94。
