# 判断資料: M4 の残り 3 件 — 呼び出しの非循環・legacy の cache shim・memo の法則家族

Issue: `sparkle-gen4-fallback-supply`（項目 1・2・3）、`sparkle-gen4-parametric-supply`（項目 3）。
台帳（受入済み）: FG 91 / T1 57。この資料では何も変えない。

根拠（いずれも文書のみ）:

| 資料 | SHA | branch | 状態 |
|---|---|---|---|
| `scripts/gen4/FB_RESUME_STUDY.md` | d2ac5d60 | kjob/rt150 | reviewer 承認済み |
| `scripts/gen4/FB_HNO_STUDY.md` | 8714354b | kjob/rt156 | reviewer 承認済み |
| `scripts/gen4/PARAM_INV_ESTIMATE.md` | 014e4dc9 | — | reviewer 承認済み |
| `scripts/gen4/PARAM_MEMO_STUDY.md` | 4a54e1f0 | — | reviewer 承認済み |
| `scripts/gen4/MEMO_FAMILY_PROPOSAL.md` | 13562271 | par/memo-family | reviewer が設計資料として承認。TRUSTED 追加は未承認 |
| `docs/parallel/G2-legacy.md` §5 | — | — | — |

## 1. 何の話か（前提知識なしで）

* 一般定理（FG）は「コンパイルが成功した設計の出力は正しい」と言う。
* そのためには、コンパイラの経路（route）ごとに「この経路の出力は正しい」という部品が要る。
* M4 は、machine 以外の経路の部品を作るマイルストーン。対象は fallback / legacy / memo / parametric（幅を記号で持つ entry）。
* 今日、M4 を再開して 1 行を証明で消した（B.F-4、FG 92 → 91）。
* 残りの部品は、どれも次の 3 つのどれかに行き当たる。証明の工夫だけでは越えられない。
  * 前提を新しく足す
  * コンパイラを変える
  * 信頼する法則を足す

  そのどれを選ぶかを決めてほしい。
* 3 件は独立に決められる。
* 判断しない場合は、それぞれ「何もしない」と同じになる（§5）。

## 2. 項目 1: 呼び出しの非循環（D.E-12 の `hno`）

* **中身**: 出力の design の中に、いまコンパイルしている宣言と同じ名前の module が入っていないこと。
  * 一般定理の最後の段（Verilog を書く段）の前提。
  * machine 経路では証明済み。
* **なぜ証明できないか**: これは「成功した run の中で、同じ宣言を入れ子でもう一度コンパイルしていない」（呼び出しが循環しない）と同じである（FB_HNO_STUDY §2.2 で同値を証明）。
  * 循環すると depth 上限（1024）で失敗する、と言いたい。
  * しかし inline 展開（`tryInlineUnfold`、Elab.lean 6358-6376）が入れ子の失敗を catch して、別の道で retry する。そのため上限だけでは閉じない。
  * 反例は見つかっていない。直接の自己再帰 1 例は、実際に失敗した（観測）。
  * module 名の単射性（`ofDecl_injective`）は既に定理なので、新しい前提は要らない。
* **選択肢**:

| 案 | 内容 | 台帳 | 利用者に見える影響 | コスト |
|---|---|---|---|---|
| (1a) 前提にする | 「呼び出しグラフは循環しない」を FG の新しい前提にする（完全な型は freeze で固定） | FG +1 | なし | 小（freeze と台帳） |
| **(1c) コンパイラで必ず失敗させる** | 同じ宣言へ再入したら、catch に飲まれない形で失敗させる | 0。証明できれば D.E-12 の非 machine 分の義務が 1 つ減る | 循環する設計はエラーになる。今成功している設計で循環しているものは無いと読める（未測定。corpus で出力不変を測る） | 中（コンパイラの小変更、corpus 測定、証明） |
| (1b) 何もしない | 未解決の義務として残す | 0 | なし | 0 |

* **推奨: (1c)**。
  * 前提を増やさない。
  * 方針「出力は既定で固定。意図した変更は機能確認と測定と記録つき」の範囲で扱える。
  * 測定で出力が変わったら、そこで止めて報告する。

## 3. 項目 2: legacy 経路の cache shim（B.F-8 の legacy 腕）

* **中身**: 古い翻訳器（legacy）は、式の翻訳結果を `IO.Ref` の表に覚えて再利用する（shim）。
  * 表の中身を検証せずに返す。
  * そのため「返った wire がこの式の翻訳である」を Lean の中で示せない（`Tools/ShippingLegacySemContract.lean`）。
* **選択肢**:

| 案 | 内容 | 台帳 | 影響 | コスト |
|---|---|---|---|---|
| (2a) shim を直す | 純粋な状態に記録された wire だけを使う（`cacheLookupValidated` + `recordTranslation`、G2-legacy §5） | 0 | 受け付けるソースは同じ。古い entry が当たっていた場合だけ出力文字列が変わりうる（機能・面積・速度の測定が要る） | 大。shim の変更自体は中。その後の legacy の意味の証明が大きい（handler の数だけ constructor が要る。未計数） |
| (2b) shim を信頼する | shim の振る舞いを TRUSTED の仮定にする | FG +1 以上 | なし | 小〜中 |
| **(2c) 今は何もしない** | legacy 経路の意味保証（B.F-8）は未供給のまま | 0 | なし | 0 |

* **推奨: (2c)、今は保留**。
  * (2a) の後の証明の規模が見積もれていない。
  * 先に項目 1 と項目 3 の結果を見てから決め直すのがよい。
  * 後から (2a) に移れる。

## 4. 項目 3: memo の法則家族（parametric の F-kids と fallback の memo hit）

* **memo とは**: コンパイラが持つ「宣言名 → もう作った module」の表（`sparkleSubModuleCache`）。同じ宣言を legacy で 2 回翻訳しないために使う。
  * 各 top のコンパイルの最初に空にされ、4 つの経路の終わりに書かれる。
  * 子 module 用には別の表（child cache）があり、こちらは既存の証明が追っている。
* **なぜ Lean の中で証明できないか**: どちらの表も `initialize … ← IO.mkRef` で作られた大域の可変 cell である。
  * Lean の論理では、これは中身の分からない定数になる。
  * 2 つの cell が別物であることも、set / get が run の状態に何をするかも、論理は言わない。
  * 既存の証明は、こうした事実を「実行環境についての信頼する法則」（TRUSTED の `Laws`）として仮定している。
* **なぜ要るか**: parametric 経路の証明は翻訳器全体を辿る。その途中で legacy が memo から結果を返しうる。
  * 「子については memo が必ず外れる」（不変量 K: memo の名前は全て child cache にもあり、child cache が先に見られる）を示せば、memo の中身の話は避けられる。
  * ただし K を翻訳器の各段で保つには「その段は memo を触らない」が要る。それがこの法則家族の中身である。
  * fallback の memo hit（F-9）も、同じ家族の一部を使う。
* **法則（7 つの欄、10 の文。一文ずつ）**:
  1. `frame`: 翻訳器が memo 以外の cell に対して行う普通の段は、memo の表を変えない（memo 以外の cell が memo と別物であることの仮定も含む）。
  2. `frameCacheSet` / `frameDepthSet`: child cache や再帰の深さを書いても、memo の表は変わらない。
  3. `memoGet`: memo を読んでも変わらない。
  4. `memoSet` / `memoModify`: memo を `v` にしたら表は `v`。`f` で変えたら表は `f`（元の表）。
     * `memoModify` を `memoGet` + `memoSet` から導く `RunsTo` の補題を freeze の前に示せれば、`memoModify` を落とせる（9 文）。
     * 示せなければ 10 文のまま（reviewer）。
  5. `tele`（4 文）: 束縛を開いて続きを走らせて閉じる 4 つの helper（`forallTelescope` など）は、続きが保つ不変量を、memo に依存する分も含めて保つ。

  完全な Lean の型は MEMO_FAMILY_PROPOSAL §2。scratch で elaborate 済み（標準 axioms のみ）。仮定としてはまだ使っていない。
* **台帳への効果（数え方で変わる）**:
  * 消えうる行は B.P-8 と B.P-1 の 2 行（−1 ずつ）。ただし F-θ / F-top / F-post / shape / assembly / F-kids の全部が証明できた場合だけ。
  * F-kids の不変量の証明は 3500〜5000 行の見積り（PARAM_INV_ESTIMATE。測った値ではない）。

| 数え方 | 足す行 | 条件が全部揃ったときの FG の純差分 |
|---|---|---|
| R-1: 家族を 1 つの TRUSTED 行 | +1 | −1 |
| R-3: 法則のまとまりごと（frame / get・set / tele） | +3 | +1 |
| R-10: 文ごと | +10 | +8 |
| R-0: `Laws` の 3 つ目の欄にする（既存の TRUSTED 行 A.P-01 = T1L-01 と共有定義を変える） | 0 | −2 |

* T1: 今は 0。M3 の G-MEMO（T1L-25）は、memo の法則を使わない方針（dispatch の除外）で、今は家族を要らない。
* **選択肢**:

| 案 | 内容 | 影響・コスト |
|---|---|---|
| A. 法則を足さない | F-kids は文のまま | 0。parametric の保証は信頼集合だけには届かない。台帳は動かない |
| B. 別の TRUSTED 構造として足す（parametric のみ） | freeze（reviewer とあなた）、家族のファイル（小）、その後 F-kids の walk（3500〜5000 行の見積り） | 信頼集合が 7 欄増える。データ損失の危険はない |
| **C. B に加え、fallback の memo hit と共有する（M3 とは任意）** | B ＋ `outer_miss` を家族の下で述べ直す | 家族は 1 つで済む |
| D. `Laws` の 3 つ目の欄にする | 既存の TRUSTED の文と共有定義を変え、M3/M4/M5 の全消費者の型に効く | 調整のコストが最大 |
| E. コンパイラで memo hit を拒む | production の変更。K が要らなくなる | この調査の範囲外。評価していない |

* **推奨: C を R-1 の数え方で**（reviewer も、独立した 1 家族として R-1 を推奨）。
  * 文の数は 10。上の補題を示せたら 9。
  * memo の中身は信頼集合に入れず、cell の書き方だけを法則にする。
  * 2 つの経路で 1 つの家族を共有する。
  * 数え方 R-1 は `Laws`（2 構造で 1 行）と同じ粒度である。
  * ただし台帳が実際に減るのは、F-kids 等の大きな証明の後になる。それまでは FG +1 のまま。
* 未証明のもの:
  * `FramedA` を `FramedNM` / memo の操作に分ける補題
  * K の walk
  * F-kids の不変量

  家族を承認しても、それだけで台帳は減らない。

## 5. 後から変えられるか・判断しないとどうなるか

* **後から変えられるか**:
  * 項目 1: (1a) / (1c) とも、証明が依存するまでは取り消せる。(1c) のコンパイラ変更は元に戻せる（corpus で出力不変を確かめるので、戻しても出力は同じ）。
  * 項目 2: (2c) は、いつでも (2a) / (2b) に移れる。
  * 項目 3: freeze の承認までは、この資料以外に何も存在しない。法則を使う証明ができた後に外すと、その証明はやり直しになる。
* **判断しないとどうなるか**:
  * FG 91 / T1 57 のまま。
  * M4 の fallback と parametric はここで止まり、machine 以外の経路の保証は今の条件付きの範囲（first-gate fragment など）にとどまる。
  * M3 と M5 は止まらない。

## 6. まとめ（決めてほしいこと）

| 項目 | 推奨 | 台帳 |
|---|---|---|
| 1 非循環 | (1c) コンパイラで循環を必ず失敗させる（出力不変を corpus で確認） | 0 |
| 2 legacy shim | (2c) 今は保留 | 0 |
| 3 memo 法則 | C・R-1（parametric と fallback で 1 家族を共有、別構造。10 文、補題を示せば 9 文） | 今は FG +1。F-kids 等が全部揃えば純差分 −1 |

## 7. ユーザーの判断（2026-11-03）

ユーザー: 「1c、2c、3Cで」。

| 項目 | 決まった案 | 次 |
|---|---|---|
| 1 非循環 | (1c) 同じ宣言への再入を、catch に飲まれない形で必ず失敗させるコンパイラ変更 | 変更の設計と `hno` の供給定理の文を freeze → reviewer。実装後、corpus で出力不変を測る。変わったら止めて報告 |
| 2 legacy shim | (2c) 保留 | B.F-8 の legacy 腕は未供給のまま。項目 1・3 の結果を見て決め直す |
| 3 memo 法則 | C（parametric と fallback の memo hit で 1 家族を共有、`Laws` とは別構造）、数え方 R-1 | `memoModify` の導出補題を先に試し、家族の文（9 または 10）を freeze → reviewer。家族を使う証明が受入されたとき FG +1。純差分 −1 は F-kids 等が全部揃った後だけ |

この判断で台帳は変わらない（FG 91 / T1 57）。

## 8. ユーザーの判断（2026-11-04）: 項目 1 の (1c) を保留に上書き、memo 家族に 2 文

経緯:
* 2026-11-03 の 1c（再入したら失敗させるコンパイラ変更）を設計した（FB_CYCLE_FREEZE rev4）。
* reviewer は、新しい cell の quiet 保存が要ると指摘した。
* 判断資料: `FB_CYCLE_QUIET_DECISION.md`（a71a7340）、`KWALK_DIAG_DECISION.md`、`KWALK_LEGACY_WINDOW_DECISION.md`。
* 相談: `M4_CONSULT_2026-11-04.md`（6cd45bc2、par/memo-kwalk9）。

ユーザー: 「Diag は A、窓は A、quiet は C」。reviewer と相談したうえで「確定」。

| 項目 | 決まった案 | 次 |
|---|---|---|
| 1 非循環 | **§7 の (1c) を上書きする。1c は保留。`hno` は未供給の義務のまま** | `htop` を供給する経路が見つかったときに再検討する。§7 の (ii)（保証は逐次の command に限る）は、1c を実装するときの条件として残す。`sparkle-gen4-fallback-supply` は todo にする（解除の条件: `htop` の供給経路の特定） |
| Diag | `MemoFamily` に Diag の文を足す。reviewer の条件で狭める（下） | MEMO_FAMILY_FREEZE rev3 |
| legacy 腕の窓 | `MemoTele` の `lamTelescope` を Triple 形にする。失敗側に `OkExc` を含める | 同上 |

reviewer の条件（Diag）:
* 今の Diag 全体を 1 文で包まない。
* `ppExpr`: 任意の printer は memo の ref を書きうる。だから safe printer / `OkEnv` などの条件を完全型に含めるか、対象の経路から除く。
* `IO.FS.Handle.mk` / `putStrLn` / `flush`: `profLogIO` が実際に使う、固定の path・mode・操作列に限る。任意の path・mode・Handle 一般については主張しない。
* stderr 系（`IO.eprintln` / `flushStderr`）と、`OkMsg` の制約つきの `msgToString` は、別の文に分けてよい。

reviewer の条件（窓）:
* Triple 形が旧 `Keeps` 版を導ける完全型なら、旧版を置き換える。この場合、文の数は増えない。
* 導出と、既存の全ての利用側が通ることを Check で確かめる。
* できなければ追加する（暫定 14 文）と明記する。

台帳: R-1（`MemoFamily` の 1 行）に束ねるかぎり、rev3 の承認だけでは FG は変わらない。

| 時点 | FG |
|---|---|
| K walk 全体の受入 | 92（+1） |
| parametric の残り（F-kids の残り、F-θ、F-top、F-post、shape、assembly）が全て閉じた後 | 90（B.P-8 −1、B.P-1 −1） |

途中で仮説を独立の行として足すなら、数え直す。この判断で台帳は変わらない（FG 91 / T1 57）。
