# 判断資料: (1c) 再入検出の「並行する合成」への対処（invocation-local か、逐次 command に限定か）

- Issue: `sparkle-gen4-fallback-supply`（rt162）。関連: scripts/gen4/FB_CYCLE_FREEZE.md rev3 §2.6、scripts/gen4/M4_DECISION.md §7。
- 種別: 判断資料（文書のみ）。Lean・コンパイラ・Tools/ は編集していない。数は `grep` の件数で、base = 598f195e。
- 台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。どちらの選択肢も新しい FG / T1 を足さない（(ii) は保証の範囲を狭める点が問題）。

## 1. 前提知識なしの説明

(1c) は、ある宣言のコンパイル中に、同じ宣言がもう一度コンパイルされそうになったら（呼び出しの循環）、必ず失敗させるコンパイラ変更である。検出のために「いまコンパイル中の宣言名の一覧（stack）」と「再入を見た印（旗）」を持つ。

この 2 つの置き場所が問題になる。現在のコンパイラは、深さ・子 module の cache・wire cache など多数の状態を、プロセス全体で共有する 1 個の `IO.Ref`（global cell）に置いている。新しい stack / 旗も同じ形（global）にするのが最小の変更で、これを「A-global」と呼ぶ。もし同じプロセスの中で 2 つの合成が同時に進むと、stack と旗が混ざり、**循環していないのに「再入」と誤判定する**可能性がある（その合成は失敗する。出力が静かに間違うのではなく、誤ったエラーになる方向）。

同時に進みうるか、の調査結果（FB_CYCLE_FREEZE §2.6）:
- 通常の `lake build` / `lean FILE`: command は 1 つずつ実行され、`lake` の並行は module ごとに別プロセスなので、重ならない（読んだ範囲）。
- 重なりを**除外できなかった**経路は 2 つ: (1) language server で編集された時に、古い command がキャンセルされるまでの窓、(2) 非同期に走る theorem の本体から合成を呼ぶユーザーの tactic。(2) は repo 内には見つからなかった。

reviewer の指摘: 既存の cell が global だからといって、新しい検出器が正しいことの根拠にはならない。

## 2. invocation-local（合成 1 回ごとの状態）の見積もり

目標: stack と旗を、合成 1 回ごとに別の値にする。

**なぜ小さく収まらないか（この調査で見つかった範囲）**: 入れ子の子の合成は、必ず `sparkleChildSynth : IO.Ref (Option (Name → MetaM (Module × Design)))` を通って呼ばれる（`childSynthEntry` Elab.lean:5620、`closeInstsM` 5206、`closeInstsGM` 5228、`synthesizeChild` 8929）。この関数の型には「どの合成の子か」を渡す欄が無い。local 化には、次のいずれかが要る。

| 方法 | 変更 | 見積もり |
|---|---|---|
| L1: 引数で持ち回す（`Name → SynthRun → MetaM …`） | `sparkleChildSynth` の型、`childSynthEntry`、`Rec.synthesizeCombinational`（6332）、`synthesizeChild`、`closeInstsM` / `closeInstsGM`、`synthesizeCombinationalCoreWith`（5423）と、それを呼ぶ 2 つの入口（5592、8940）。translator の `partial` ブロックが `childSynthEntry` を受け取る箇所（`translateInstanceOrFallback` 8712/8730 など）にも引数が伸びる | Elab.lean で約 8 関数、各 数行（合計 約 40〜80 行の想定。実測ではなく読んだ範囲の見積もり）。**ただしこれは `sparkleChildSynth` の型を変えるので共有定義の変更** |
| L2: 呼び出しごとの token を既存の cell に入れる（global の map: token → stack） | 型は変えないが、token を子の呼び出しへ渡す経路が結局要る（MetaM の文脈に token を載せる場所が、この調査では見つからなかった） | 実質 L1 と同じか、global map に戻る（A-global と同じ露出） |
| L3: `StateRefT` / `ReaderT` で MetaM を包む | MetaM を使う全関数の型が変わる | 大きすぎる（Elab.lean 9513 行の大半） |

**証明側への波及（共有定義の変更）**: `sparkleChildSynth` の型は `JQC`（Tools/ShippingChildCacheA.lean:120。`sv w = some synthesizeChild`）、`Start`（Tools/ShippingGen2Defs.lean:52）の定義に入っている。base で `sparkleChildSynth` / `synthesizeChild` / `childSynthEntry` / `JQC` を含む `Tools/` のファイルは **153**、`Tests/` は **29**。`synthesizeCombinationalCore` を含む `Tools/` のファイルは **267**（出現 773）。型変更はこれらの statement に及ぶ。`Tools/ShippingGen2Defs.lean` と `Elab*.lean` は、この Issue の禁止対象（共有定義・コンパイラ）。

**既存の cell を変えずに済むか**: **済まない（局所化しても、他の global cell は残る）**。depth（963）、`sparkleChildCache`（1032）、`sparkleSubModuleCache`（1024）、wire cache 類（986〜1016）は depth 0 で `set {}` する global のままで、2 つの合成が重なればこれらがまず混ざる。stack / 旗だけを local にしても、重なった合成の**出力が安全になるわけではない**。重なりに対する保証を本当に得るには、これらの cell も合成ごとに分ける必要がある（さらに大きな変更）。この点は、(i) のコストを下回らない。

**出力が変わらないこと**: L1 は値の持ち回しだけなので、設計上は出力を変えない。ただしこれは見積もりで、corpus 測定（FB_CYCLE_FREEZE §4 と同じ手順）で確かめる単位が増える。

結論: invocation-local は「コンパイラの変更が新規ファイル中心で Elab.lean の変更が小さい」条件を満たさない（共有型 `sparkleChildSynth` / `JQC` を変え、Tools の 153 ファイルの statement に及ぶ）。そのため freeze rev3 の設計には採用せず、判断資料にした。

## 3. 選択肢

### (i) invocation-local（L1）にする
- 内容: `sparkleChildSynth` の型を変え、stack / 旗を合成ごとに持つ。
- 利点: 新しい検出器は他の合成から影響を受けない。ただし**既存の global cell は残る**ので、重なった合成の全体が安全になるわけではない（§2）。
- コスト: 共有定義（`sparkleChildSynth`、`JQC`、`Start`）の変更と、それに依存する `Tools/` の 153 ファイル・`Tests/` の 29 ファイルの見直し。ユーザー承認が要る変更（共有定義）。新しい freeze と clean build（共有定義の変更なので）。規模は見積もり不能（実測していない）で、数 Issue 分を想定する。
- 利用者に見える影響: なし（出力は同じ見込み）。
- 後から変えられるか: 実装前は文書の変更だけ。実装後に A-global へ戻すのは再び共有定義の変更。

### (ii) 保証の範囲を「逐次の command」に限り、並行経路は保証外と明記する（A-global 固定）
- 内容: 新 cell は global。保証（`hno_of_noReentry`）は「単一の合成が逐次に走る」モデル（`RunsTo` が 1 つの world を逐次に走らせるのと同じ）に対して。language server の cancel の窓と非同期 theorem body からの合成呼び出しは、保証外の既知の制限として FB_CYCLE_FREEZE §7 と台帳資料に明記する。
- 利点: 変更は新規ファイル + Elab.lean 約 10 行。共有定義は変えない。既存の cell と同じ前提で、証明のモデルとも一致する。
- コスト（範囲の縮小）: **保証の範囲を狭める**ので、ユーザー判断が要る。重なった場合は、循環していない設計が誤った再入エラーで落ちるか、既存の cell の混入が起きうる。
- 利用者に見える影響: 通常の `lake build` では出ない（読んだ範囲）。エディタで編集中の古い合成が残る窓で、まれに誤エラーが出る可能性を除外できていない。
- データ損失: なし（出力ファイルは書かれる前に失敗する方向）。
- 後から変えられるか: 変えられる。(i) へは後で移行でき、その時点でコストを払う。

## 4. 推奨

**(ii)**。理由: (i) は共有定義と 150 超のファイルに及び、しかも既存 global cell を残す限り「並行に対して安全」にならない。(i) の効果を得るには cell 全体の局所化が要り、(1c) の目的（循環を必ず失敗させて `hno` を供給する）に対して不釣り合いに大きい。(1c) の目的は、通常の逐次実行で達成できる。並行経路は既存 cell も保証していない範囲で、そこを (1c) だけが先に保証する意味は小さい。(ii) を採るなら、限界を明記し、将来の並行対応（cell 全体の局所化）は別 Issue として扱う。

## 5. 判断しない場合

(ii) の内容のまま文書だけが残り、実装には進まない（保証の範囲を狭める判断を勝手にしない）。(1c) の freeze は reviewer の承認も止まったまま。D.E-12 の `hno` 側（および M4 の残り）の供給が進まない。

## 6. 状態

freeze rev3 は指摘 1（Start からの reset の処理）を修正済みで、設計は A-global のまま、並行の扱いだけがこの判断待ち。判断後、(ii) なら rev3 の §2.6 / §7 を判断の記録に置き換えて reviewer へ。(i) なら、新しい freeze（共有定義変更）を一から書く。
