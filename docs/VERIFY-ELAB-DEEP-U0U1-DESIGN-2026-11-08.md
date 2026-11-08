# verify_elab_deep 拡張: U0 測定の設計、厳密な axiom 監査、U1 契約の下書き（2026-11-08）

土台: par/ved-plan 8f2bcada（調査書 `docs/VERIFY-ELAB-DEEP-SURVEY-2026-11-08.md`）。この文書は**設計**で、測定はまだ一度も実行していない。cluster の Job は使っていない。`Tools/DeepElab.lean` と `Sparkle/` は変えていない。

**改訂 2（2026-11-08、reviewer の変更依頼 P1-1〜P1-4・追加への対応）**: U0 の harness を発見・観測のモードに作り直し（§3）、U1 の契約を build できる下書きにした（§4）。各項の対応と残りは **§8**。手元で実行したのは、harness の単体テスト（偽の runner、Lean なし、30 件 OK）と小さな Lean の build（`Tools.VedStrictAudit`、`Tests.Ved.StrictAuditCheck` は `MEM=8G memlimit lake build`、`Tools.VedU1Contract`、`Tests.Ved.U1ContractCheck` は `MEM=8G memlimit lake env lean`。§4.2）だけである。

**改訂 3（2026-11-08、bb58e0c6 に対する reviewer の変更依頼 P1-A・P1-B への対応）**: U1 の契約に、元の宣言の型から読む入出力の対応表を入れ、clock の値を自由にし、玩具 `toyDelay` について契約と `OutputsStmt` を kernel で証明した。**§4.2 の契約の文と clock の項は改訂 2 のもので、改訂 3 で置き換えた（§9）。**

**改訂 4（2026-11-08、83fe82b2 に対する reviewer の裁定 4 への対応）**: U1 入口の最小縦断を 1 つの小さい実宣言でつないだ（`Tools/VedU1Entry.lean`、`Tests/Ved/U1EntryCheck.lean`）。§10。

**Issue 未登録（manager 停止中）**（`managerctl` は completed Failed の Pod への exec でエラーになる）。復旧後に、U0/U1 の完了条件とこの裁定を Issue に登録する。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）

---

## 1. reviewer の裁定（原文のまま）

> 8f2bcada の調査書と DeepElab の該当コードを確認。U0→U1を採用します。実装・測定結果の受理ではなく設計裁定です。以下の条件を反映してください。
>
> 【U0】
> 1. 元の必要IP327コマンドの分母は保持。inventoryのSHAを固定し、command/file/宣言/引数/パラメータ/設定の対応を保存。SVからの179/82/階層件数は近似の分類で、raw IRの実測と分ける。「既存のdeepの実行記録なし」は未確認であって検証失敗ではない。
> 2. 最初は既存deepの代表例＋各群の代表でsmoke。その後327を行単位で分類。179以外を除外して対応率100%としない。各ケースの時間・メモリ上限、timeout/終了コード、default/shared設定、profile/trace-only設定、同期kernel登録と到達axiomsを記録。巨大な一括ファイルで前の失敗が後を隠す方式は避ける。U0全件の長時間終了待ちをU1の小さい試作の着手条件にはしない。
> 3. PROVEN文字列を成功基準にしない。SOURCE/deep定理だけ、実bodyのreplay、並べ替えbodyだけ、最適化、SV、skipped、非標準axiom依存、timeoutを別列にする。旧entryの診断用trace-onlyも完全成功に数えない。strictに必要な定理が同期登録されて存在し、型/前提/閉包を確認したものだけを対応済みに数える。
>
> 【U1の保証境界】
> 4. synthesizeEntryを1回だけ呼んだ同じModuleを検証して返すIR-only入口は可。declName/パラメータ/元Signalへの橋、module名・inputs/outputs・width表・全出力・初期値・reset/seed条件を含む契約を先に固定。bodyが同じだけでは別Moduleへの証明流用を防げない。Moduleの意味に使う全fieldと結論が結び付くことを確認。
> 5. m.bodyそのものをreplayする。順序を変えるなら、この具体的bodyの前提下の意味保存を証明し、最終結論は元bodyへ戻す。任意のstmt並べ替えが意味を保つとは仮定しない。
> 6. 最適化/SV未接続の記録は可。ただし「出荷SVを保証」「327の印字artifact検証済み」とは表示しない。IR契約成立後はcheckedOptimizeへの接続を優先度高く置く。通常entry/他の327コマンド経路は新入口で覆っていない間、別扱い。
> 7. replay省略、trace-only、証明失敗/監査失敗では新入口は返さない。生成器のコンパイル済みBoolや文字列比較はkernel証明の代用にしない。無関係な宣言やartifactの既存証明を取り違えた対照を入れる。
>
> 【native_decideと許可axiom】
> 8. 調査で判明した既存native_decide依存はU0でそのまま測定・列挙してよい。しかしU1の受理経路へ新たな信頼境界として自動採用はしない。strict経路は標準3公理（propext/Classical.choice/Quot.sound）の閉包までとし、Lean.ofReduceBoolや追加auxiliary axiomは拒否。native_decide/bv_decideというtactic名だけで決めず、到達依存で判定する。標準公理だけに帰着する証明生成は可。
> 9. sharedの現在の名前パターン許可を既定へコピーする案は不可。任意axiomをそれらしい名前にして通せるため。旧互換・測定モードは分離しNATIVE/追加信頼と明示、strict証明済み件数に含めない。G1の有限計算をkernel decideや分割補題に置き換える小例と時間を先に出す。性能が障害ならG1の該当命題/閉じた入力/依存axiom/測定を提示して再相談。新TRUSTEDは採用しない。
>
> 【検証基準の補正】
> 10. U0の旧PROVEN例すべてがU1を通ることを先に約束しない。旧replay省略/並べ替え/追加axiomで通った例は、新しい厳密な契約で拒否してよいし、未解決の対応不足として残す。
> 11. 変異は、意味の変わる入力・定数・reg初期値・出力等と、証明artifactの取り違えを拒否する。無害な並べ替えや未使用stmt変更まで必ず拒否する必要はない（新しく正しい証明を作れれば受理可）。「旧証明の使い回しは拒否」と「意味の同じ新artifactは証明可能」を区別。
> 12. printModule等の文字列一致は観測の回帰検査。内部Module/Design全構造の比較と同一artifact接続を別途確認。327 baselineは必要IPコマンド成功・stdout/stderr/rc・生成ファイルを対応づける。既存deep testの期待PROVEN数は9月の履歴のまま要求せず、U0の同じSHAでの実測を基準に差分を分類。
> 13. 全baselineの再実行は共通compiler/生成処理が変わる統合時に。Toolsの小さい単位では対象Checkを優先し、同じSparkle SHAで既受入baselineを流用する場合は差分根拠を記録する。
>
> managerctlは今もcompleted Failed podへのexecエラー。復旧前のkjobを待つ扱いは了承。待機中はU0 harness/結果schema/strict監査の型と小例の設計など、Jobを要しない準備を進めてよい。Issue登録は未実施と明記し、復旧後にU0/U1の完了条件と本裁定を登録。FG75/T157は不変。

---

## 1b. reviewer の変更依頼（2026-11-08、1cd11d0f に対して。原文のまま）

> 1cd11d0f の Tools/VedStrictAudit.lean、StrictAuditCheck、U0 scripts、設計書を読みました。監査本体の方針は適合しています（標準3公理の閉包、存在/theorem/mvar、名前偽装対照）。手元buildは報告として受領、こちらで再実行はしていません。native_decideの現toolchainの閉包観測と模型の時間を実G1へ外挿しない記録も適切です。ただし測定harnessとU1契約は以下の変更を要します。全327測定へ進む前に直してください。新規実装成果の一括受理ではありません。
>
> P1-1 U0のstrict_countedは現在の判定では過大評価できます。
> case_textのVED BODYはdeep実行後にsynthesizeHierarchicalを再実行した別runのmとの比較です。v==toExpr m.bodyを同じrunの実bodyの証拠に使えません。非一致を全てreorderedとするのも誤りです（mismatch/unknownが要る）。
> またclassifierは名前suffixの存在を見ており、定理の完全型/前提/出力全部を検査していません。複数出力で1個のtrace/replayだけでもsrc/replay=trueになります。VED REQの実装もありません。
> 対処: U0の現harnessは発見/観測モードとして strict_counted=no/unknown を維持するか、生成時に同じartifactの識別と各出力の期待型を検査するprobeを追加。body比較はobserved_against_second_runと明記し、厳密な結合と分ける。source/IR/opt/SVの段ごとに必要な定理集合とそのclosureを確認してください。text_parsesの存在だけではSV意味の橋をyesにしないこと（parse/roundtrip/SV意味を分ける）。任意の観測用extra theoremの非標準axiomを理由にIR段まで失敗とせず、その段に必要なclosureを集計する。
>
> P1-2 inventoryケースを忠実に再現していません。
> params/argsはコメントとmeta.tsvにあるだけで #verify_elab_deep decl へ渡していません。symbolicModeは捨てています。元ファイルのimportでprivate宣言は通常の名前で参照できない場合もあり、namespace/openやlocal optionはimportでは持ち越せません。『そのコマンドでの検証結果』と数えないこと。正確なwrapper/特殊化を構成するか、unsupported-invocation/unresolved-private/harness-errorとして明示して327の分母に残してください。decl_ofのqualifiedが推定である場合も検証が必要。
> smoke-splitは残した#check/証明/guard等が、削除したdeep宣言を参照する可能性があり、別namespaceに移した生成名も既存参照を壊します。as-isの結果と切出しharnessの失敗を分け、少数例で生成fileを検証してから展開。
>
> P1-3 設定・再開・プロセス隔離。
> (a) limited_runはos.environを継承して追加するだけなのでdefaultにも親のSPARKLE_DEEP_SHARE/TRACE_ONLY/NOTHM/PROFILE等が漏れます。関連overrideを一度消してから明示設定し、実効設定を記録。
> (b) genがCase.lean/meta.tsvを上書きした後run.txtがあればskipするため、別SHA/設定の古い結果と新fileが混在します。srcSHA/toolchain/inventory/casehash/実効設定でrun identityを固定。生成前に再利用可否確認し、不一致なら別attemptディレクトリ。REDOでresults.tsvへ旧新混在・二重集計しない。
> (c) p.killはkjob/lakeの親だけをkillし、Lean等の子孫が生存し得ます。新session/process groupまたはcase単位cgroupで全体を終了し、回収を確認。RLIMIT_ASだけをhostのmemlimit代用にしない（Pod -mの外側制限は保持）。SIGKILLだけでOOMと断定せずsignal_unknownを分ける。ru_maxrssがwrapperだけを測っていないか小さい負荷で確認。
> (d) run.txt欠落・classifier失敗・gen失敗はharness-errorとして残し、後続測定継続とJob全体の未完報告を両立。set -uだけではこの失敗が最後のechoで成功扱いになり得る。
>
> P1-4 U1Stmtのsrc/declNameの結合がスケッチでは不足。
> 現ShapeStmt/OutputsStmtはc.declName/paramsを意味的に使用せず、srcは自由引数。『宣言から生成する予定』だけでは別ソースやIR由来srcへの取り違えを防げません。独立の期待型に元宣言を適用したSignal式を直接固定するか、SrcBindingを実際に証明し最終文へ合成。c.clk/rstと実module入力/register reset式の結合、inputsの幅/順序/初期状態、seedInの時刻方向も明示してください。WidthStmtのdeclWidthはwire宣言のみから読む実装なので、clk/rstにwire宣言のない実artifactで契約が成立するか確認。必要以上に拒否する契約にも注意。期待型と全Moduleをbindして元宣言から返却IRを示すという目標は維持。
>
> 追加: #ved_audit_generatedは現在のnamespace配下の定理を列挙するだけで、期待する全定理が生成されたことや契約の正しさを監査しません。この限界をCLI/docに明記（strictAudit単体がその役割を持たないのは正しい）。U0側の同期設定と、汎用commandとして使用する際の同期前提も区別。
> 修正の検証は軽いharness unit/controlを先に（別SHA再開、環境変数汚染、子process timeout、複数出力欠落、params無視、body mismatch）。DeepElabを使うsmokeはmanager復旧後でよいです。U0全件を待たずU1の型と最小接続準備は継続可。FG75/T157不変。manager復旧時にIssueへこの変更依頼を記録してください。

対応は §8。

---

## 2. 厳密な axiom 監査（裁定 8・9）

### 2.1 置いたもの
- `Tools/VedStrictAudit.lean`（`import Lean` だけ。lakefile に `lean_lib «Tools.VedStrictAudit»`）。
  - 許可する集合は `strictAllowed = [propext, Classical.choice, Quot.sound]` だけ。
  - `strictAudit decl : CoreM StrictReport` は次を順に確かめ、1 つでも外れたら `throwError` する。(a) 宣言がある、(b) `theorem` である（def・axiom・opaque などは拒否）、(c) 型にも証明項にも metavariable がない、(d) `Lean.collectAxioms decl`（**到達する閉包**）が `strictAllowed` に含まれる。外れた axiom はすべてエラー文に名前で出す。`sorryAx` は axiom なので (d) で落ち、文に「depends on sorry」と付く。
  - 判定は閉包の集合の包含**だけ**で行う。tactic の名前も、axiom の名前の形も見ない。shared 経路の `isAux`（DeepElab.lean:3600–3604、`.str (.str (.str _ "_native") "native_decide") ax => ax.startsWith "ax_"`）は写していない。
  - `#ved_strict_audit decl`: 通れば `VED STRICT OK decl: [閉包]`、落ちればエラー。
  - 測定用（受理はしない）: `#ved_axioms_raw decl`（閉包をそのまま出す）、`#ved_audit_generated Ns`（このファイルで `Ns` の下に宣言された theorem ごとに `VED AUDIT <名前> strict=OK|REJECTED axioms=[閉包]` を 1 行。エラーで止まらないので、1 ケースの全定理を記録できる）。
  - `#ved_audit_current_namespace`（730341a1）: 同じことを今の名前空間について行う（U0 の写しのケースは、ファイルの名前空間の中に入れ子にした新しい名前空間で走るので、その完全な名前をケースファイルに書かない）。
  - **限界（変更依頼の追加）**: `#ved_audit_generated` と `#ved_audit_current_namespace` は、名前空間の下に宣言された theorem を**列挙するだけ**である。期待するすべての定理が生成されたこと、定理の文（契約）が正しいこと、定理がどの artifact についてのものかは監査しない（期待した定理が無ければ、一覧に出ないだけ）。`strictAudit` 単体も 1 つの宣言の閉包だけを判定する。期待する定理の集合との比較は U0 の classifier（§3.4、観測）と U1 の入口（§4.1）の仕事である。docstring に明記した。
- `Tests/Ved/StrictAuditCheck.lean`（lakefile に `lean_lib «Tests.Ved.StrictAuditCheck»`）。`#guard_msgs` で期待する出力を固定した。負の例（NEGATIVE）の axiom はこのファイルの中だけにあり、ほかから import されない。

### 2.2 各例の結果（`lake build Tests.Ved.StrictAuditCheck` exit 0 = すべての `#guard_msgs` が一致）

| 例 | 結果 | 閉包 |
|---|---|---|
| `by decide` | OK | `[]` |
| `Classical.em`（標準 3 公理だけ） | OK | `[Classical.choice, Quot.sound, propext]` |
| `by native_decide` | 拒否 | `[<decl>._native.native_decide.ax_1_1]` |
| `Lean.ofReduceBool` を直接使う | 拒否 | `[Lean.ofReduceBool, Lean.trustCompiler]` |
| 利用者の `axiom ax_fake : False` | 拒否 | `[…ax_fake]` |
| 利用者の axiom を `negSpoof._native.native_decide.ax_1_1` と名付けたもの（shared 経路の名前パターンに合う形） | 拒否 | `[…negSpoof._native.native_decide.ax_1_1]` |
| `sorry` | 拒否（depends on sorry） | `[sorryAx]` |
| 無い名前 / def / axiom | エラー（unknown declaration / is a def / is an axiom, not a theorem） | — |
| G1 風の有限計算（下）を `native_decide` | 拒否 | `[…g1Native._native.native_decide.ax_1_1, propext]` |
| 同じ命題を `decide +kernel` | OK | `[propext]` |

注意（Lean v4.32.1 での事実）: `native_decide` の閉包は補助 axiom `…._native.native_decide.ax_1_1` だけで、**`Lean.ofReduceBool` は閉包に現れない**。依頼文の「補助 axiom と Lean.ofReduceBool の名前が出る」は今の toolchain では 1 つの例では満たせないので、`Lean.ofReduceBool` は別の例で直接使って拒否を示した。docs/RefusalLedger.md:107 の「replay は `Lean.ofReduceBool` に依存」は古い toolchain の記録で、今は補助 axiom の形になっているはず（U0 で実測して確かめる）。

metavariable の検査 (c) は、宣言済みの定数に metavariable を残す例を作れなかったので、テストには入れていない（kernel が先に拒否する）。

### 2.3 裁定 9 の小例と時間
`Tests/Ved/StrictAuditCheck.lean` の末尾。DeepElab の G1 補題（`mkG1`）の義務のうち 2 つ、「cone が参照する名前はすべて停止集合にある」と「幅の表と if の連鎖で書いた `weM` が一致する」を、64 葉の cone の小さな模型で書いた（`G1Obl`）。同じ命題を `native_decide`（拒否）と `decide +kernel`（標準 axiom だけ、受理）で閉じた。手元で 1 回測った時間はコミット 8b3c39a7 のメッセージに書いた（ソースツリーには置かない）。どちらも 1 秒より十分小さい。ただしこれは模型で、実際の G1 の大きさ（cone が数 MB になるもの）での時間ではない。実物での比較は §5.3 のとおり cluster で測る。

---

## 3. U0 測定 harness の設計

### 3.1 分母と固定
- 一覧: `scripts/gen5/fgc_baseline/inventory.tsv` を **commit `f694355fcabee7c9915c9c83991e4a0b032fedf8`**（par/fgc-s0 の先端、2026-11-08 に読んだ値）から `git show` で読む。**blob `4a5b801f3a665ed95262b803109aa3f76005065d`**。この blob を最初に入れた commit は `9f0acf17`（2026-11-05「S0: FG baseline tooling … and static inventory」）。定義は同じ commit の `docs/FG-CIRCUIT-BASELINE.md`（blob 743372b5）の「必要IPの定義」（除外 0）。
- `u0_gen.py` は `git rev-parse <commit>:<path>` が上の blob と一致すること、行数が 327 であることを確かめ、違えば止まる。branch が動いても分母は変わらない。
- 行番号 `row` = ヘッダを除いた 1 から始まる行番号。結果の各行は `inv_commit`、`inv_blob`、`row`、`file`、`line`、`command`、`ns`、`top`、`decl`（`qualified` 列。無ければ `top`）、`params`、`options`、`args`、`setting` を持つ。
- 327 行すべてを測る。S 群 179 件以外を「対象外」として除き、対応率を 179 で割ることはしない。`#synthesizeParameterizedVerilog` の 4 件（`params` あり）も `#writeDesign` の 18 件も、同じ形で 1 行ずつ走らせ、拒否されればその理由を記録する。
- 179/82/40/4/18/4 の群は、調査書 C 節の**最適化後の SV**から取った近似。結果表では `sv_group_approx` という別の列に入れ、raw IR から取った値（`#verify_elab_deep` の拒否理由、レジスタ数など）と混ぜない。群の表は coder の作業領域にあり、ソースツリーには入れない。
- 「deep の実行記録が無い」は**未確認**で、失敗ではない。列 `deep_run_record` は、測った行が `measured`、まだ走っていない行が `none`。

### 3.2 1 ケース = 1 行 × 1 設定 = 元のファイルの写し 1 つ（変更依頼 P1-2 で作り直した）
`u0_gen.py gen --row N --setting S --dir DIR` が DIR に次を書く。
- `Case.lean`: **その行のソースファイルの写し**。import の並びの後に `import Tools.DeepElab` と `import Tools.VedStrictAudit` を足し、**元のコマンドの直後**に次の塊を差し込む（元のコマンドもそのまま走る）。
  ```lean
  namespace VedU0Case_R<N>
  run_cmd …   -- VED NS（いまの名前空間）、VED DECL（コマンドの識別子をこの場所で解決し、inventory の qualified と比べる）
  set_option Elab.async false in
  set_option <inventory の options> in      -- 例 maxHeartbeats 4000000
  set_option sparkle.deepShare true in       -- shared の設定のときだけ
  #verify_elab_deep <top>                    -- 元のコマンドが書いた識別子そのまま
  #ved_audit_current_namespace
  run_cmd …   -- VED RET / VED SECONDRUN / VED OUTPUT / VED BODY（観測。下の 3.4）
  end VedU0Case_R<N>
  ```
  写しなので、private の宣言（327 行のうち 153 行）、ファイルの namespace / open、scoped な `set_option`（136 ファイルのうち 54）、local な属性は、元のコマンドのものと同じになる。前の版（宣言を import して別ファイルで `open ns` するもの）は、これらを持ち越せず、private の 153 行は名前を解決できなかった。
- `case.env`: 設定の環境変数。`meta.json`: キー列、`invocation`、差し込んだ塊の行範囲（`block_begin`/`block_end`。エラーを塊の中と外に分けるため）。
- **走らせない行**（327 の分母には残す）: `#verify_elab_deep` は識別子 1 つしか取らないので、引数を持つ行は元のコマンドどおりに再現できない。`params`（`W := 8` など）と `symbolicMode` を持つ `#synthesizeParameterizedVerilog` 4 行、ファイル名などの引数を持つ `#writeDesign` 13 行と `#writeVerilogDesign` 2 行、計 19 行を `invocation=unsupported-invocation` とし、理由を `invocation_detail` に書く。手元で 327 行すべてを生成した結果: `deep-in-file` 308、`unsupported-invocation` 19、生成の失敗 0。
- ほかの `invocation`: `unresolved-name` / `unresolved-private`（VED DECL が解決できなかった）、`harness-error`（下の 3.2b）。ソースの走査で確かでないもの（コマンドが見つからない・2 つある、`end` の対応が合わない、`mutual` の中、`module` ヘッダ）は `unsupported-invocation: source scan …`。元のファイルが `Tools.DeepElab` の import の閉包に入っている場合（写しが同じ宣言を再定義する）は `harness-error`（今の 327 行では 0）。
- `decl_check`: VED DECL が解決した名前（private なら利用者名に直す）と inventory の `qualified` の比較（`match`/`mismatch`/`absent`）。`qualified` は抽出時の推定なので、`mismatch` は inventory 側の誤りとして記録し、測る宣言は元のコマンドと同じ場所での解決結果を使う。

### 3.2b 実行（`u0_run.py`。`u0_case.sh` は薄い wrapper）
- **環境（P1-3 a）**: 親の環境から `SPARKLE_` で始まる変数を**すべて消してから**、`case.env` と `SPARKLE_DEEP_TRACE=<ケース>/stages.log` を置く。DeepElab が読むのは `SPARKLE_DEEP_{DEBUG,GOALS,NOFIRST,NOTHM,SHARE,SKIP,TRACE,TRACE_ONLY}` と `SPARKLE_SL_CHECK`、compiler と Tools はほかに `SPARKLE_PROFILE`、`SPARKLE_NO_REGDEDUP`、`SPARKLE_NO_LOOPCACHE` などを読む（grep `IO.getEnv`）。接頭辞ごと消すので後から増えた変数も残らない。実効の `SPARKLE_*` を `effective_env`、消した名前を `cleared_env` に記録する。Lean の option は塊の `set_option … in` として `lean_options` に記録する。`SPARKLE_DEEP_TRACE` は STAGE の印と宣言ごとの RSS を書くだけで、証明は変えない（DeepElab.lean 2430–2442）。
- **実行の同一性（P1-3 b）**: `run_id` = src SHA + 未コミット変更の hash（`git status --porcelain` と `git diff HEAD`）+ toolchain + inventory の固定値 + harness（2 つの script）の hash + 実行設定（コマンド、timeout、grace、RLIMIT_AS）。ケースごとに `case_hash`（Case.lean・case.env・meta.json）と実効の設定。**再利用の判断は書き込む前**に行う。同じ同一性で終わった attempt があれば再利用し、無ければ新しい `cases/<key>/attempt-NNN/` を作る（古い attempt は消さず、混ぜない）。表は `results/<run_id>/` に、その `run_id` の各ケースの**最新の終わった attempt 1 つ**から毎回作り直す。別の SHA・設定の行は別の表に入り、`REDO=1` で何度やり直しても 1 ケース 1 行。
- **process（P1-3 c）**: ケースごとに補助 process（child subreaper）を起こし、その子としてコマンドを**新しい session（process group）**で始める。timeout なら group に SIGTERM、`U0_GRACE` 秒後に SIGKILL。終わった後（正常終了でも）、group に残ったものと subreaper に付け替えられた子孫を kill し、回収を確かめる（`reaped=yes|no:<pid>`）。終了は `exit_<n>`、`signal_<n>`、wrapper が 128 以上で終わった `exit_<n>(signal_unknown)`、`timeout(TERM|KILL)`。**SIGKILL だけで OOM とは書かない**。メモリの証拠は `mem_evidence` に、cgroup の `oom_kill` の増分か allocator の文（`out of memory` / `std::bad_alloc`）があるときだけ書く。
  - メモリ: `peak_rss_kb` は補助 process の `RUSAGE_CHILDREN` の `ru_maxrss` = **回収した子孫のうち最大の 1 process** の RSS（wrapper の RSS でも合計でもない）。ケースごとに新しい補助 process なので前のケースの値は混ざらない。手元で確かめた: 200 MB を確保する孫を持つ偽のケースで 216356 kB、持たないケースで 14052 kB。cgroup v2 の `memory.peak` が fd ごとに reset できる kernel（6.12 以上。手元は 6.18）では `cgroup_peak_kb` も記録する（cgroup 全体なので runner 自身の分を含む: 同じ 2 ケースで 244416 / 35072 kB）。
  - `RLIMIT_AS` は既定で使わない（`U0_RLIMIT_AS_KB` で付けられるが、Lean の仮想メモリの予約と合わない恐れがあり、メモリ上限の代わりにはしない）。上限は **kjob の Pod の `-m`**（外側）で掛ける。
- **harness の失敗（P1-3 d）**: 生成の失敗、`run.txt` が無い、分類の失敗、コマンドを起動できない、壊れた list の行は、`invocation=harness-error` の行（`harness_error` に理由）として残し、次のケースへ進む。最後の行は `U0 SUMMARY run_id=… requested=… ran=… reused=… not_run_unsupported=… harness_error=… missing=… COMPLETE|INCOMPLETE`。harness-error か欠けた行があれば `INCOMPLETE` で、終了コードは 3（`u0_case.sh` もそのまま返す）。

### 3.3 設定
| 設定 | 中身 | 数え方 |
|---|---|---|
| `default` | 既定経路（`Cdo`/`CdoM`） | 観測 |
| `shared` | 塊に `set_option sparkle.deepShare true in`（`CdoW`） | 観測 |
| `profile` | 既定 + `SPARKLE_PROFILE=1` + `SPARKLE_DEEP_DEBUG=1` | 観測（profile は観測を足すだけ） |
| `traceonly-shared` | shared + `SPARKLE_DEEP_TRACE_ONLY=1` | **trace-only。完全な成功に数えない** |
| `defsonly-default` | 既定 + `SPARKLE_DEEP_NOTHM=1` | **trace-only。完全な成功に数えない** |

- **同期の設定（U0 のケースのもの）**: 塊の `#verify_elab_deep` に `set_option Elab.async false in` を付ける。`#verify_elab_deep` も中で各定理を同期で elaborate する（DeepElab.lean 1742、1773–1776）。こうすると kernel が拒否した定理は環境に**無い**ので、`#ved_audit_current_namespace` の一覧に出ない。これは U0 のケースファイルの性質である。**`#ved_audit_generated` などを一般に使うときは**、監査する宣言が同期で登録済みであることを呼ぶ側が保証しなければならない（既定の非同期 elaboration では、検査中・後で拒否される定理が一覧に出たり出なかったりする）。コマンドはそれを強制しない（Tools/VedStrictAudit.lean の docstring）。U1 の入口は生成した宣言を `addDecl`（同期）で登録し、直後に `getConstInfo` で存在を確かめる。
- 327 行には `default` と `shared`。`profile` と trace-only は smoke の代表だけ。

### 3.4 分類（変更依頼 P1-1: 発見・観測のモード）
- **`strict_counted` は `no` か `unknown` だけで、`yes` にはならない。** DeepElab を変えずに書ける probe では、(i) deep のコマンドが検証した module と、元のコマンドが返した module が**同じ run の同じもの**であること（deep のコマンドは `synthesizeHierarchical` を自分で呼び直し、何も返さない）、(ii) 各出力の定理の**完全な型**が期待どおりであること、のどちらも確かめられないからである。`strict_blockers` には常に `artifact-identity-not-probed;theorem-types-not-checked` が入る。はっきりした失敗（rc≠0、timeout、trace-only、塊の中のエラー、`deep-in-file` 以外、harness-error、src か ir の段が `ok` でない、SKIPPED）が 1 つでもあれば `no`、無ければ `unknown`。
- **段ごとの必要な定理**（出力ごと）。`{b}` = 解決した宣言の最後の成分、`{s}` = 構造体を返す宣言では `_<port>`、Signal を返す宣言では空（DeepElab.lean 3639）。

  | 段 | default 経路 | shared 経路（1 出力だけ） |
  |---|---|---|
  | `src` | 各出力の `{b}{s}_deep_trace` | `{b}_sdeep_trace` |
  | `ir` | 各出力の `{b}{s}_deep_signal_run` | `{b}_sdeep_signal_run` |
  | `opt` | 無し（`not-in-route`） | `{b}_sdeep_signal_runOpt`（`optimizeModule`。`checkedOptimize` ではない） |
  | `sv_parse` | 無し | `{b}_sdeep_text_parses`（印字した文字列を shipping の parser で読むと RT の body になる、を native_decide で） |
  | `sv_roundtrip` | 無し | `{b}_sdeep_signal_runRT`（読み戻した body の runModule = Signal） |
  | `sv_meaning` | 無し | `{b}_sdeep_signal_svOpt`（最適化後の body の emission の M4 意味 = Signal。印字した文字列についての文ではない） |

  段ごとに `*_expected`（必要な定理の数。出力が分からないときは `?`）、`*_found`、`*_closure`（`ok` = 全部あって全部 strict 監査を通る / `rejected` / `missing` / `not-in-route` / `unknown`）、`*_axioms`（**その段に必要な定理だけ**の閉包の和）。`text_parses` があっても `sv_meaning` は `yes` にならない。必要な集合に入らない定理（`_coneEval_*` などの補助）は `n_extra` / `extra_rejected` に別に数え、段の判定に入れない（観測用の定理の非標準 axiom で ir 段を落とさない）。必要な定理の閉包は `collectAxioms` の到達閉包なので、その定理が使う補題の axiom は入る。欠けた定理の名前は `missing_theorems`。
- 期待する出力の一覧（`VED OUTPUT`）と戻り値の形（`VED RET signal|struct`）は、塊の後の **2 回目の合成**から取る観測である。2 回目の合成が deep のコマンドの中のものと同じ module だという保証は無い（上の (i)）。
- **body の比較は `observed_against_second_run`**（`match` / `mismatch` / `unknown`）。生成された `{b}_deep_body`（shared は `_sdeep_body`）の値と、2 回目の合成の `toExpr m.body` を Expr として比べた**観測**で、同じ run の body の証拠ではない。`mismatch` から「並べ替え」とは推定しない（理由は分からない）。定数が無い・probe が失敗したときは `unknown`。
- VED REQ の行は使わない（前の版の docstring にあったが実装が無かった）。必要な集合は VED RET / VED OUTPUT から classifier が作る。
- 型・前提: U0 は「名前の決まった定理が同期登録されて存在し、theorem で、閉包が何か」までで、文の中身は見ない。`#ved_audit_generated` / `#ved_audit_current_namespace` は名前空間の下の定理を**列挙するだけ**で、期待するすべての定理が作られたことも、契約が正しいことも監査しない（Tools/VedStrictAudit.lean の docstring に明記した）。

### 3.5 順序: smoke → 327 行
1. **smoke（既存の deep のテスト）**: 次の 5 ファイルを、(a) そのまま 1 回（`--smoke-file`。表 `results_smoke_asis.tsv`。PROVEN の文の数は 9 月との比較のための観測で、成功の基準ではない）と、(b) `#verify_elab_deep` 1 つごとに分けた版（`--smoke-split`。表 `results_smoke_split.tsv`）で走らせる。2 つの表は分けて、混ぜない。
   - `Tests/Verification/DeepElabReifyDemo.lean`（20 コマンド）、`DeepElabRealIP.lean`（6）、`ValueParamInitRepro.lean`（5）、`ConeSharingGen.lean`（2、shared）、`ConeSharingCrc16.lean`（1、shared）。
   - **分けた版の危険**: ほかの `#verify_elab_deep` を comment にすると、その後の `#check`・証明・guard がそれらの生成した名前を参照していれば壊れる。残した 1 つも新しい名前空間 `VedU0Smoke<k>` の中に移すので、その生成名を名前空間の外から参照している行も壊れる。手元で 5 ファイルの分けた版を生成して見た: 変種は 20/6/5/2/1、後ろの行にある生成名への参照は 900/126/10/2/1 か所（各変種の `split_report.txt` に行番号つきで出る）。したがって ReifyDemo と RealIP の変種のほとんどで、塊の外のエラー（`split-harness`）が出る見込みである。塊の外のエラーは `harness_error=split-harness: …` として deep のコマンドの結果（塊の中）と分けて記録し、run は `INCOMPLETE` になる。分けた版の結果を広げる前に、最初の smoke で数個の変種の Case.lean とエラーを見て確かめる。分けた版の変種の経路は、残したコマンドの前の `set_option sparkle.deepShare true in` から決める。
2. **smoke（群の代表）**: 前の版の表のとおり（row 6, 212, 244, 63, 3, 9, 71, 1, 260 を 5 つの設定で）。row 9（`synth_aesSbox`）と 244（`synth_uartTx`）は private で、前の版では名前を解決できなかったが、写しの方式では解決できる。row 260（`symbolicXor`）は `unsupported-invocation` で走らない（表には残る）。
3. **327 行すべて**を `default` と `shared` で（654 ケース、直列、再開可能）。
4. U0 全件の終了を待つことは、U1 の小さな試作の着手条件にしない（裁定 2）。

### 3.6 結果の表
`u0_gen.py header` が列を出す（行の表）。キー（`inv_commit` … `setting`）、`invocation` `invocation_detail` `decl_resolved` `decl_check`、同一性（`run_id` `attempt` `src_sha` `src_dirty_hash` `toolchain` `case_hash` `harness_hash` `effective_env` `lean_options` `cleared_env`）、`sv_group_approx`（SV からの近似の群。raw IR の値と混ぜない）、実行（`ran` `rc` `term` `timeout` `wall_s` `peak_rss_kb` `peak_rss_source` `cgroup_peak_kb` `mem_evidence` `reaped` `time_limit_s` `rlimit_as_kb`）、観測（`ret_kind` `second_run_modules` `outputs`）、段ごとの 4 列（3.4）、`missing_theorems`、`observed_against_second_run`、`skipped`、`trace_only`、`refusal`（塊の中の最初のエラー）、`errors_outside_block`、`n_theorems` `n_extra` `extra_rejected` `raw_axioms`、`strict_counted`、`strict_blockers`、`harness_error`、`deep_run_record`（`measured` / `not-run` / `none`。none は未確認で失敗ではない）、`stdout_ref` `stderr_ref`。as-is の smoke は別の列（`u0_run.py` の `ASIS_COLUMNS`）。

### 3.7 script と harness の単体テスト
- `scripts/ved/u0_gen.py`（生成・分類）、`scripts/ved/u0_run.py`（実行・同一性・表）、`scripts/ved/u0_case.sh`（前と同じ呼び方の wrapper）。
- `scripts/ved/tests/test_u0.py` と偽の runner `scripts/ved/tests/fake_lean.py`（Lean を動かさない。決めた VED の行を出す、環境の SPARKLE_* を出す、sleep、子・setsid した子・親が先に終わる孫を作る、子で 200 MB 確保、決めた終了コード・自分への signal）。inventory とソースは使い捨ての git repo をテストの中で作る。`TMPDIR=<scratchpad> MEM=4G memlimit python3 -I -W ignore scripts/ved/tests/test_u0.py -v` で **30 件すべて OK**（内訳はコミット 53127556 のメッセージ）。依頼の 7 つの対照: 別 SHA での再開、環境の汚染、子 process の timeout kill と回収、複数出力で 1 つ欠ける、params の無視（走らせず unsupported として残す）、body mismatch、harness-error の後の継続。
- 後で走らせるときの呼び方（今は走らせない。`<ISSUE>` は復旧後に登録する U0 の Issue）。Case.lean は元のファイルの写しなので、**元の module の import** が build 済みであればよい（module 自身を build すると import も build される）。

```sh
cd /home/junji-hashimoto/git/.kjob/src-ved-plan      # 測る SHA の worktree（Job はこの時点の copy を使う）

# smoke: 既存 deep テスト 5 本と群の代表
kjob -N sparkle-dev run --issue <ISSUE> -n mkvs-dell -c 8 -m 24Gi --name ved-u0-smoke -d -- bash -c '
  set -u
  OUT=$(dirname "$KJOB_REPORT_PATH")/ved_u0
  kjob lake build Tools.DeepElab Tools.VedStrictAudit Tests.Verification.DeepElabReifyDemo Tests.Verification.DeepElabRealIP \
    Tests.Verification.ValueParamInitRepro Tests.Verification.ConeSharingGen Tests.Verification.ConeSharingCrc16 \
    IP.Arbiter.RoundRobin Tests.IP.Net.CRC32Test Tests.IP.Net.UARTTest Tests.CircuitDoTest Examples.HierarchicalCPU IP.Crypto.AESHW \
    Tests.Compiler.ShippingMachineFuseTest Examples.CDC.MultiClockSim || exit 2
  rc=0
  for f in DeepElabReifyDemo DeepElabRealIP ValueParamInitRepro ConeSharingGen ConeSharingCrc16; do
    scripts/ved/u0_case.sh "$OUT" --smoke-file  Tests/Verification/$f.lean || rc=$?
    scripts/ved/u0_case.sh "$OUT" --smoke-split Tests/Verification/$f.lean || rc=$?
  done
  mkdir -p "$OUT"
  for r in 6 212 244 63 3 9 71 1 260; do
    for s in default shared profile traceonly-shared defsonly-default; do echo "$r $s"; done
  done > "$OUT/rows_smoke.txt"
  scripts/ved/u0_case.sh "$OUT" --list "$OUT/rows_smoke.txt" || rc=$?
  exit $rc'

# 327 行（smoke の後）
kjob -N sparkle-dev run --issue <ISSUE> -n mkvs-dell -c 8 -m 24Gi --name ved-u0-all -d -- bash -c '
  set -u
  OUT=$(dirname "$KJOB_REPORT_PATH")/ved_u0
  mkdir -p "$OUT"
  python3 -I scripts/ved/u0_gen.py rows > "$OUT/rows_all.raw" || exit 2
  kjob lake build Tools.DeepElab Tools.VedStrictAudit $(cut -f2 "$OUT/rows_all.raw" | sort -u | sed "s/\.lean$//; s#/#.#g") || exit 2
  awk -F"\t" "{print \$1\" default\"; print \$1\" shared\"}" "$OUT/rows_all.raw" > "$OUT/rows_all.txt"
  scripts/ved/u0_case.sh "$OUT" --list "$OUT/rows_all.txt"'
```
- Job の終了コードは `u0_case.sh` のもの（3 = INCOMPLETE）。`rows_all.txt` を分けて複数の Job にしてもよい。同じ `run_id`（同じ SHA・設定・harness）の Job の結果だけが同じ表に入る。
- `IP/Crypto/*` の file は、`IP.Crypto` の lean_lib に root file が無い（BASELINE.md の手順 2 の注意）。その module の build が通らなければ、その行のケースは `harness-error`（Lean が import を見つけられない）になり、表に残る。

### 3.8 U0 で言えないこと
- U0 は「今の `#verify_elab_deep` が、必要IPの宣言それぞれに何をするか」の観測で、保証ではない。`#verify_elab_deep` は `synthesizeHierarchical`（診断の入口）を自分で呼び直すので、`#synthesizeVerilog` が印字した成果物そのものを検査したことにはならない（調査書 B7）。写しの方式でも、元のコマンドと deep のコマンドはそれぞれ合成し直す。
- `printModule` などの文字列一致は観測の回帰検査で、内部の Module/Design の構造比較や同じ artifact への接続の代わりにならない（裁定 12）。

---

## 4. U1 の契約（下書き。定義は `Tools/VedU1Contract.lean` で build する。入口と証明はまだ）

### 4.1 入口の形
新しいファイル（compiler のファイルは小さく保つ）に、次の入口を置く。
1. `synthesizeEntry declName` を **1 回だけ**呼び、返った `(m, D)` を持つ。`synthesizeHierarchical` は呼ばない。
2. `m` を `toExpr` で定数 `{f}_u1_mod : Module` として `addDecl`（同期）する。以後の定理はすべてこの定数について述べる。
3. 契約（下の `U1Stmt`）の文を生成し、証明を作って同期登録する。
4. 登録した定理の型が、期待する文と（定数 `{f}_u1_mod` を含めて）Expr として一致すること、`#ved_strict_audit` と同じ `strictAudit` を通ること、`{f}_u1_mod` の値が手元の `m` の `toExpr` と一致することを確かめる。
5. どれか 1 つでも外れたら（replay を省いた、trace-only、証明の失敗、監査の失敗）`throwError` し、`m` を返さない。代わりの経路に落とさない。

返すのは IR の `m` まで。最適化（`checkedOptimize`）と SV は未接続と記録する。「出荷 SV を保証」「327 の印字 artifact を検証済み」とは書かない。IR の契約が通った後の次の接続先は `checkedOptimize`（`refineCheck_transfer` / `optCheck_sound` との合成）。`#synthesizeVerilog` などの通常の入口と、ほかの 327 コマンドの経路は、新しい入口が覆うまで別扱いにする。

### 4.2 契約の文（変更依頼 P1-4 で作り直した改訂 2 の記録。現行は §9）
DeepElab を import しない（`Sparkle.IR.Semantics`、`Sparkle.IR.RegDedup`、`Sparkle.Core.Signal` だけ）ので、下書きをそのまま Lean のファイルにしてコンパイルした。lakefile に `lean_lib «Tools.VedU1Contract»` と `«Tests.Ved.U1ContractCheck»` を足したが、**手元の確認は `lake build` ではなく `MEM=8G memlimit lake env lean <file>`**（既にある olean に対して 1 ファイルずつ。Check が import する `Tools.ShippingFGCircuitS3rArtifact` と `Tools.VedU1Contract` の olean は scratchpad に出した。どちらも rc=0）。`lake build` で Sparkle を import する target を作ると、`Sparkle` lib の `precompileModules := true` のために Sparkle 全体の共有ライブラリ（`Sparkle/Compiler/Elab.c` の gcc を含む）を作り始め、小さな build ではなくなったので途中で止めた（必要な olean はその前にできていた）。cluster では通常の `kjob lake build Tools.VedU1Contract Tests.Ved.U1ContractCheck` で確かめる。定義と小さな補題だけで、入口・生成器・`OutputsStmt` の証明はまだ無い。要点（全文はファイル）:

```lean
structure Contract where
  modName : String
  clkRst : Option (String × String)   -- (clock 入力, reset 入力)。register の無い module は none
  dataInputs : List Port              -- port の順。i 番目が宣言の i 番目の Signal 引数に入る
  outputs : List Port
  wires : List Port
  inits : List (String × Int)         -- register の出力 ↦ 初期値（body の順）

def ShapeCore (c : Contract) (m : Module) : Prop :=
  m.name = c.modName ∧ m.parameters = [] ∧ m.assertions = [] ∧ m.isPrimitive = false ∧
  m.inputs = c.dataInputs ++ clkRstPorts c ∧          -- 入力の順と幅。clk・rst は実際の入力
  m.outputs = c.outputs ∧ m.wires = c.wires ∧
  (regsOf m.body).map (fun r => (r.1, r.2.2.2)) = c.inits ∧
  (∀ r ∈ regsOf m.body, c.clkRst = some (r.2.1, r.2.2.1))   -- 各 register の clock・reset の名前 = その入力

def ShapeStmt (c : Contract) (m : Module) : Prop :=
  ShapeCore c m ∧ memInstFree m.body = true           -- v1 の範囲: memory と子 instance は無し

def WidthStmt (c : Contract) (m : Module) : Prop :=
  (m.wires.map (·.name)).Nodup ∧
  (∀ p ∈ c.dataInputs, scalar p.ty = true ∧ declWidth m p.name = p.ty.bitWidth) ∧
  (∀ p ∈ c.outputs, scalar p.ty = true) ∧
  (∀ r ∈ regsOf m.body, ∃ p ∈ m.wires, p.name = r.1 ∧ scalar p.ty = true)

def InputsOk (c : Contract) (m : Module) (ins : Nat → String → Nat) : Prop :=
  (∀ t, ∀ p ∈ c.dataInputs, ins t p.name < 2 ^ declWidth m p.name) ∧
  (∀ t kr, c.clkRst = some kr → ins t kr.1 = 0 ∧ ins t kr.2 = 0)

def st0 (c : Contract) (m : Module) : String → Nat := fun n =>
  match c.inits.lookup n with | some i => encodeInit i (declWidth m n) | none => 0

def seedFwd (m : Module) (K : Nat) (ins : Nat → String → Nat) : Nat → (String → Nat) → Env :=
  fun j st n => if (m.inputs.map (·.name)).contains n then ins (K - 1 - j) n else st n

theorem seedFwd_time (m K ins) {t} (ht : t < K) (st) :
    seedFwd m K ins (K - 1 - t) st = seedIn m ins t st        -- 証明済み

def OutputsStmt (c : Contract) (m : Module) (src : (Nat → String → Nat) → String → Nat → Nat) : Prop :=
  ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
    runModule (declWidth m) m.body (seedFwd m K ins) K (st0 c m) (fun _ _ => 0) = some envs ∧
    ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧ env o.name = src ins o.name t

def U1Stmt c m src := ShapeStmt c m ∧ WidthStmt c m ∧ OutputsStmt c m src
```

- **元の宣言への結合（src は自由な引数ではない）**: 入口が登録する定理は `U1Stmt f_u1_contract f_u1_mod (fun ins o t => SRC)` で、`SRC` は入口が**元の宣言の定数** `declName` から構文的に作る項である: `declName` を params の値と、データ入力ごとの入力 Signal（`sigBV ins "<port>" w` / `sigB ins "<port>"`）に適用し、`obsBV` / `obsB` で観測し、出力 port `o` へ射影する（構造体なら field、Signal なら 1 つ）。`Tests/Ved/U1ContractCheck.lean` の `toySrc` がこの形。入口は (1) 登録した定理の型が、`declName`・params・2 つの定数から自分で作った文と Expr として等しいこと、(2) `f_u1_mod` の値が同じ 1 回の `synthesizeEntry` の `toExpr m` であること、(3) `f_u1_contract` の値が `contractOf m` の `toExpr` であることを確かめる。(1) により、別のソース（ほかの宣言、IR 由来の Signal）を src に使った証明は型が合わない。(2) により、検証した module と返す module は同じ値になる（これが U0 では確かめられなかった同一性）。
  - 宣言の引数とデータ入力の対応は**順番**で、入口はさらに宣言の i 番目の Signal 引数の名前 `x` と i 番目のデータ入力の名前（`pilotB0` では `_gen_<引数名>`）が合うことを確かめ、合わなければ throw する（名前の付け方が一般にこうであることは U1 の最初の試作で確かめる）。DomainConfig の引数は `defaultDomain` にする（DeepElab と同じ）。値の引数（params）は具体的な値を代入した後の宣言を使う。
- **clk・rst**: `m.inputs = dataInputs ++ [clk, rst]`（`pilotB0` の形: データ入力の後に `clk`、`rst`）で、clk・rst が module の実際の入力であることと、その順を固定する。各 register 文の clock と reset の名前がその 2 つであることも `ShapeStmt` に入れた。reset の種類（sync/async）は意味に効かない（`regNexts` はどちらも `env rst ≠ 0` で初期値にする。`InputsOk` で rst は常に 0）。register の無い組合せ回路は `clkRst = none`（register があれば `ShapeStmt` が偽）。データ入力の後に clk・rst が来ない module が実際にあれば、この節は合わないので、並べ替えを許す形に直す（黙って並べ替えない）。
- **幅（WidthStmt）**: `declWidth` は `m.wires` だけを読む（Sparkle/IR/RegDedup.lean 172）。実物の `pilotB0`（Tools/ShippingFGCircuitS3rArtifact.lean、`pilotEntry3` の 1 回の結果）を確かめた: データ入力 5 つと register の出力 17 個は wire 宣言があり幅が合う。**`clk`、`rst`、出力 `out` には wire 宣言が無い**。前の下書きの「inputs ++ outputs ++ wires の全部で `declWidth m p.name = p.ty.width`」は `pilotB0` を拒否する（Check で `#guard !decide (WidthStmtDraft1 pilotB0)`）。新しい `WidthStmt` は、意味が `declWidth` を読む所（データ入力の幅の前提、register の更新の mask）だけに wire 宣言を求め、clk・rst・出力 port には求めない（`#guard decide (WidthStmt (contractOf pilotB0 …) pilotB0)`。`ShapeCore` も成り立つ）。ただし **`pilotB0` には子の instance 文が 2 つあり、v1 の範囲（memory・instance 無し）の外**なので `ShapeStmt` は成り立たない。これは幅や名前による拒否ではなく範囲の制限で、子を持つ module は後の単位（子の意味との合成）で扱う。出力の値の幅は、期待する文の側（`obsBV` の `BitVec w`、`w` = 出力 port の型の幅）で決まる。
- **入力の幅・順・初期状態・時刻の向き**: 幅はデータ入力ごとに `declWidth` = port の型の幅（`WidthStmt`）、その中に収まる入力（`InputsOk`）。順は `m.inputs` の等式と宣言の引数の順。初期状態は `st0`（各 register の初期値を宣言幅で `encodeInit`。Signal 側の `Signal.register init` の時刻 0 の値に当たる）と、memory は 0（v1 は memory 無し）。**時刻の向き**: `runModule` は周期の番号を**数え下ろして** seed に渡す（最初の周期が `k-1`）。前の下書きは `seedIn m ins` をそのまま渡して `envs[t]` を時刻 `t` と比べていたので、入力列を逆向きに読んでいた。`seedFwd m K ins` は番号を `K-1-j` に戻し、trace の `t` 番目（古い順）が `ins t` を読む（`seedFwd_time`、`runModule_first` は rfl で確かめた）。
- **clock の値（改訂 2 の誤り。改訂 3 で撤回、§9.2）**: 改訂 2 は「IR の意味は clock の値を読まないので 0 に固定しても振る舞いを失わない」と書き、`InputsOk` で clock を 0 に固定していた。これは `ShapeStmt` からは言えない: register 文の clock 欄は読まれないが、`evalExpr (.ref clk)` は env の clock の値を読み、assign や register の入力式から参照できる。改訂 3 では clock の値を自由（全称）にした。
- 目標は変えない: 期待する文と Module 全体を bind し、返す IR が元の宣言から来たことを示す。`OutputsStmt` は `m.body` そのものの `runModule` について述べる（`deepOrderBody` ではない）。

### 4.2b Check（改訂 2 の記録。現行は §9.1・§9.3・§9.4）
- 玩具の宣言 `toyDelay`（1 周期遅延）と、`synthesizeEntry` の形の module `toyMod`（データ入力、clk、rst。clk・rst・out に wire 無し）、`toyC = contractOf toyMod …`、`toySrc`（宣言から作った src）。`U1Stmt toyC toyMod toySrc` が elaborate する。`ShapeStmt`・`WidthStmt` は `decide` で成り立ち、`WidthStmtDraft1` は成り立たない。
- 負の例（同じ契約に変えた module を当てる）: 初期値、入力の幅、出力を 1 つ足す、register の reset を別の wire にする、入力の順を変える → `¬ ShapeStmt`。register の出力の wire 宣言を消す → `¬ WidthStmt`。
- `pilotB0` の形: clk・rst・out に wire 宣言が無いこと、`ShapeCore`・`WidthStmt` が成り立ち、`WidthStmtDraft1` が成り立たないこと、instance 文が 2 つあって v1 の範囲外（`memInstFree` が false）であることを `#guard`。
- `OutputsStmt` の証明は無い（U1 の本体の仕事）。

### 4.3 対照（U1 の Check に入れるもの）
**拒否すべきもの**（意味が変わる変異と、証明の取り違え）:
1. 入力: 入力 port の幅を変える / 1 つ消す。
2. 定数: body の中の定数を 1 つ変える。
3. register の初期値を変える。
4. 出力: 出力 port を 1 つ足す・消す・別の wire に付け替える。
5. 証明の取り違え: 宣言 B の `U1Stmt` の証明を宣言 A の定数に当てる。同じ宣言の別の artifact（例えば `deepOrderBody` の body の定数）の証明を当てる。どちらも型が合わず、入口は throw する。
6. 監査: 証明の中に `native_decide`、`sorry`、利用者の axiom が入る。

**拒否しなくてよいもの**: 意味の変わらない文の並べ替え、使われない文の変更。新しい正しい証明が作れれば受理してよい（裁定 11）。「古い証明の使い回しは拒否」と「意味の同じ新しい artifact は証明できる」を分けて書く。

U0 で PROVEN だった例が U1 をすべて通るとは約束しない。replay を省いた、並べ替え、追加の axiom で通っていた例は、U1 で拒否されてよく、未解決の不足として残す（裁定 10）。生成器の中でコンパイルした Bool や文字列比較は、kernel の証明の代わりにしない（裁定 7）。

---

## 5. G1 と native_decide

### 5.1 G1 とは
DeepElab の「deep 側のつなぎ（G1）」は、宣言ごとに生成する補題 `{base}_deep_coneEval_*`（生成器 `mkG1`、Tools/DeepElab.lean:3846–3888）。deep 値の結論 `evalExpr (weOfC …) env (CExpr.compile nm …)` を、解決済みの cone 定数と幅の表 `weM` の上の `evalExpr weM env cone` に書き換える。中身は「fidelity（構文の等式）∘ `concatNorm_eval` ∘ `evalExpr_we_congr`」で、閉じた入力（その宣言の cone、停止集合、幅の表）についての有限の計算を `native_decide` で示している。
**一般の定理（ファイルの前半の theorem）は native_decide を使わない**（1302 行は comment）。native_decide はすべて、生成器が宣言ごとに作る証明の中にある。同じ形の閉じた計算は G1 の外（replay の前提）にもあるので、下の表に一緒に載せる。

### 5.2 native_decide の場所（Tools/DeepElab.lean、HEAD 8f2bcada。comment の行は除く）

| 行 | 生成する補題・場所 | 示している閉じた命題 |
|---|---|---|
| 3863 | `mkG1` の `hinl` | `inlineConeT (buildDefMap bodyC) stopAtM 10000 eIn = .ok coneRaw` |
| 3866 | `mkG1` の `hres` | `cone = resolveSlicesT wtM 10000 coneRaw` |
| 3869 | `mkG1` の `hag` | `∀ n ∈ stopL, weOfC nm Γ n = weM n` |
| 3872 | `mkG1`、`concatNorm_eval` の前提 | cone に単一要素の concat が無い（singleton-freedom） |
| 3945, 3958 | register / latch の G1（`hnormTac` = `rw [fid]; native_decide`） | `compile (reify) = concatNorm 10000 cone` |
| 3950 | メモリありの register の G1（`hnormTac` = `native_decide`） | 同上（literal に対して） |
| 3978 | メモリの書き込み port（wa/wd/we）の G1 | 同上 |
| 3999 | 組合せ読み出しのアドレスの G1 | 同上 |
| 4012 | 出力 cone の G1 | 同上 |
| 4776 | 組合せ読み出しの継ぎ目 | `curT = bodyP ++ memStmt :: bodyQ` |
| 4778 | 同 | `evalAssigns_isSome` の前提（`bodyEvalOk bodyP = true`） |
| 4784, 4793, 4794, 4797, 4799 | 同（`cone_resolved_agrees_at_seed` の前提） | `hres`、`hwfCheck … = true`、`hwt_of_assoc` の表の一致、`stopAtFrozenCheck … = true`、`hinl` |
| 4813 | 同 | `evalAssigns_frame` の前提（読み出し wire が bodyP で書かれない） |
| 4825 | 同 | `curT = bodyC` |
| 4847, 4863 | `seed_bounded`（メモリあり / なし） | `∀ i : Fin Γ.length, weM (nm i) = Γ.get i` |
| 4929, 4941, 4942, 4945, 4947 | slot ごとの step 補題 | `hres`、`hwfCheck`、`hwt_of_assoc`、`stopAtFrozenCheck`、`hinl` |
| 5007 | register の段の reset | `evalAssigns_frame` の前提（reset 名が bodyC で書かれない） |
| 5129 | メモリの payload | `evalPayload_evalOk` の前提（`evalOk e = true`） |
| 5385, 5397, 5398, 5401, 5403 | 出力の step 補題 | `hres`、`hwfCheck`、`hwt_of_assoc`、`stopAtFrozenCheck`、`hinl` |
| 5506 | `{f}_deep_signal_run` | `runModule_isSome` の前提（`bodyEvalOk body = true`） |
| 3538 | shared 経路の `_sdeep_signal_sv{tag}` | `seqCheck wofM (weOf wofM) body = true` |
| 3589 | shared 経路の `_sdeep_text_parses` | 印字した文字列を shipping の parser で読むと RT の body になる |

既定経路の生成コードに 34 か所、shared 経路に 2 か所。どれも宣言・slot・port ごとに繰り返されるので、1 つの宣言での補助 axiom の数はもっと多い（RefusalLedger.md:107 の initCirc7 で 23 個）。`bv_decide` も補助 axiom を作る（既定経路 4262、shared 経路 2601–2602、2662、2671、2702）。これも strict 監査では拒否される（§2）。

### 5.3 置き換えの計画
shared 経路は 2026-09-19/20 に、同じ種類の義務の多くを kernel の `decide` と構造的な補題に置き換え済み（DeepElab.lean 2771–2818、3032–3046、3150–3194 の F2 の comment と測定）。既定経路の各場所を、それと同じ補題で置き換える。

| 義務 | 置き換え（既にある補題） |
|---|---|
| `hinl` | 停止集合を `stopOfL stopL` の定数にし、`Tools.ConeFold.inlineConeT_of_listS body stopL 10000 root cone (by decide)`（ConeFoldRT.lean:819） |
| `hres` | `resolveSlicesT_list`（ConeFoldRT.lean:1028）で構造的な `resolveSlicesS (assocGetR wtL)` に直して `rfl`/`decide`（shared の `hresL`、2816 行） |
| `hag`、`seed_bounded` の表 | `by decide`（shared の `hag`・`hagK`、2778・2790 行） |
| `hnorm`、singleton-freedom | cone を `resolveSlicesT_list` で書き直してから `decide`（2805–2815 行の測定: slot ごと 21/2/1/0 ms、native_decide は 4–6/1 ms） |
| `hwfCheck` | `hwfCheckL_to_hwfCheck` + `stopOfL_contains_elem` + `hwfCheckL_of_bodyWidthOk`、`bodyWidthOk … = true` は `decide`（3150–3175 行） |
| `hwt_of_assoc` の表 | 1 回だけ `theorem hwt : ∀ p ∈ wtL, weM p.1 = p.2 := by decide`（2775 行） |
| `stopAtFrozenCheck` | `stopAtFrozenCheckL_to_check`（ConeFoldRT.lean:335）+ `decide` |
| `evalAssigns_frame` の前提 | `by decide`（shared の `frameOf`、3207 行） |
| body の分割の等式（4776、4825） | body の定数を `bodyP ++ memStmt :: bodyQ` の形で**定義**し、等式を `rfl` にする（分割補題） |
| `bodyEvalOk`、`evalOk` の前提 | `decide`。kernel で重ければ、文ごとに分けた補題（`bodyEvalOk_cons`）にする |
| `seqCheck`、parser（shared） | U1 の範囲外（SV は未接続）。strict の数には入れない |

- 置き換えた後の閉包は標準 3 公理だけになるはず。これを `#ved_strict_audit` で確かめる。
- 時間: 小さな模型では kernel の `decide` は `native_decide` より遅いが 1 秒より十分小さい（§2.3）。実物の cone（crc16 のように数 MB のもの）での時間は、置き換えた版を cluster で測るまで分からない。性能が障害になれば、その G1 の命題・閉じた入力・依存する axiom・測定値を出して再相談する（裁定 9）。新しい TRUSTED は置かない。
- 置き換えは `Tools/DeepElab.lean` の変更で、その build と測定は重いので cluster で行う（この作業では DeepElab を変えていない）。

---

## 6. cluster が無いとできなかったこと（2026-11-08 変更依頼の後も残るもの）
- U0 の測定そのもの（smoke も 327 行も）。`Tools.DeepElab` を import するものの build と実行は、この作業では一度も行っていない（指示どおり）。**DeepElab を使う smoke は manager の復旧後**に行う。
- 生成する Case.lean の Lean の部分（塊の 2 つの `run_cmd`: VED NS / VED DECL と VED RET / VED SECONDRUN / VED OUTPUT / VED BODY）は、DeepElab を import するので**一度もコンパイルしていない**。最初の smoke で通ることと、出す行の形が classifier の正規表現と合うことを確かめる。合わなければ classifier は `?`/`unknown` を出し（`yes` にはならない）、そのケースは `strict_counted=no` になる。
- 写しの方式で、元のファイルの import（`Tools.DeepElab` を足した後）と後ろのコマンドが実際にどう振る舞うか（後ろのコマンドのエラーは `errors_outside_block` に数える）。
- 分けた版（smoke-split）の変種のエラーが、`split_report.txt` の予想どおり塊の外に出るか。
- G1 の実物の置き換えと時間（§5.3）。今あるのは模型の時間だけ。
- `memory.peak` の per-fd reset が kjob の Pod の kernel で使えるか（使えなければ `cgroup_peak_kb=unavailable` と記録される）。
- Issue の登録（manager の停止中）。

## 7. このコミットまでの成果物
- `Tools/VedStrictAudit.lean`、`Tests/Ved/StrictAuditCheck.lean`、lakefile の 2 つの `lean_lib`（8b3c39a7）。`#ved_audit_current_namespace` と限界の docstring（730341a1）。
- `scripts/ved/u0_gen.py`、`scripts/ved/u0_run.py`、`scripts/ved/u0_case.sh`、`scripts/ved/tests/{test_u0.py,fake_lean.py}`（53127556）。
- `Tools/VedU1Contract.lean`、`Tests/Ved/U1ContractCheck.lean`、lakefile の 2 つの `lean_lib`、この文書の改訂 2（bb58e0c6）。
- 改訂 3（P1-A・P1-B、`toyDelay` の証明）: 同じ 2 ファイルとこの文書（§9）。

## 8. 2026-11-08 の変更依頼（P1-1〜P1-4、追加）への対応

**Issue 未登録（manager 停止中）**。復旧後に、この変更依頼（原文は reviewer の依頼文。要旨は下の各項）と U0/U1 の完了条件を Issue に記録する。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）

新しい実装成果の受理を求めるものではない。下の「済み」は harness の単体テストと小さな Lean の build で確かめた範囲で、DeepElab を使う実測は含まない。

| 項 | 依頼 | 変えたこと | 確かめたこと | まだ満たしていない・cluster が要るもの |
|---|---|---|---|---|
| P1-1 | strict_counted の過大評価、body 比較、名前の suffix だけの判定、段の分離、段ごとの閉包、VED REQ | 発見・観測のモード（§3.4）。`strict_counted` は `no`/`unknown` だけ。body の比較は `observed_against_second_run`（match/mismatch/unknown、並べ替えと推定しない）。出力ごとの必要な定理を段（src/ir/opt/sv_parse/sv_roundtrip/sv_meaning）ごとに数え（expected/found）、閉包はその段に必要な定理だけで集計。補助の定理は `n_extra`/`extra_rejected` に別に。VED REQ は削除 | 単体テスト: 1 出力で `unknown`（yes にならない）、2 出力で 1 つ欠けると ir 2/1 `missing`、body mismatch で `mismatch`（"reorder" の文字列は出ない）、補助の定理の native axiom で ir は `ok`、必要な定理が拒否されると `rejected`、text_parses だけなら sv_parse `ok`・sv_meaning `missing`、probe が無ければ `unknown` | **同じ run の artifact の同一性 (i) と、各出力の完全な型 (ii) を確かめる probe は、DeepElab を変えずには作れない**（deep のコマンドは合成をやり直し、何も返さない）。そのため strict に数える経路は U0 には無く、U1 の入口（§4.1、§4.2 の (1)(2)）で作る。probe の Lean 部分は未コンパイル |
| P1-2 | params/args/symbolicMode を渡していない、private・namespace/open・local option、qualified の推定、smoke-split の危険 | ケースを元のファイルの写しにし、元のコマンドの直後に deep の塊を差し込む（§3.2）。private 153 行、scoped option のあるファイル 54 を元の文脈で扱う。引数を持つ 19 行は走らせず `unsupported-invocation`（分母に残す）。VED DECL で解決した名前と `qualified` を比べる（`decl_check`）。smoke-split は表を分け、塊の外のエラーを split-harness として記録し、生成名の参照を `split_report.txt` に出す | 327 行を手元で生成: deep-in-file 308 / unsupported-invocation 19 / 失敗 0。単体テスト: params・symbolicMode・`#writeDesign` の引数の行は偽の runner が呼ばれず表に残る、写しに private 宣言・scoped option・元のコマンドの識別子が入る、解決できない名前は unresolved-name / unresolved-private、smoke の 2 つの表は別、塊の外のエラーで split-harness。実ファイル 5 本の分けた版を生成して見た（§3.5: 後ろの参照 900/126/10/2/1） | `#verify_elab_deep` は識別子しか取らないので、**params / symbolicMode / ファイル引数の 19 行を「そのコマンドの検証」として再現する方法は無い**（DeepElab の変更か、特殊化した wrapper を別の宣言として作る必要があり、後者は元のコマンドと同じではない）。写しの方式が実際に Lean で通るか（import の追加、後ろのコマンド）は最初の smoke で確かめる |
| P1-3 (a) | 環境変数の漏れ | `SPARKLE_*` をすべて消してから明示の設定を置き、実効の設定と消した名前を記録 | 単体テスト: 親に 5 つの `SPARKLE_*` を置いても子には `SPARKLE_DEEP_TRACE` だけ、`profile` は明示の 2 つ + TRACE | — |
| P1-3 (b) | 再開で古い結果と新しい file が混ざる | run_id（SHA・dirty・toolchain・inventory・harness・設定）と case_hash で同一性を固定、書き込む前に再利用を判断、不一致は新しい attempt、表は run_id ごとに最新の終わった attempt から作り直す | 単体テスト: 同じ SHA は再利用、別 SHA は attempt-002 と別の表（古い表はそのまま）、REDO でも 1 行、終わっていない attempt は再利用しない、ソースの変更で case_hash が変わる | — |
| P1-3 (c) | 子孫の生存、OOM の断定、RLIMIT_AS、ru_maxrss | 新しい session で始め、group ごと TERM→KILL、残りと付け替えられた子孫も kill、回収を確認。signal は `signal_<n>` / `exit_<n>(signal_unknown)`、OOM は cgroup か allocator の文があるときだけ。`ru_maxrss` は補助 process の RUSAGE_CHILDREN（最大の 1 子孫）、`memory.peak` は per-fd reset。RLIMIT_AS は既定で使わず、Pod の `-m` を保つ | 単体テスト: timeout で子 2・setsid の子・孤児の孫がすべて死に `reaped=yes`、正常終了後の残りも kill、SIGKILL は `signal_9`・137 は `exit_137(signal_unknown)` でどちらも oom ではない、200 MB の孫を `peak_rss_kb` 216356 で捉え、無いケースは 14052（ケースごと） | Pod の中の kernel で `memory.peak` の reset が使えるかは未確認（使えなければ unavailable と記録） |
| P1-3 (d) | 失敗が最後の echo で成功扱いになる | 生成・run.txt・分類・起動の失敗と壊れた行を harness-error の行にし、続け、`U0 SUMMARY … INCOMPLETE` と終了コード 3 | 単体テスト: 範囲外の行・壊れた行・分類の失敗の注入・起動できないコマンド・run.txt 無しで、ほかの行は正しく分類され、終了コード 3 / INCOMPLETE（`u0_case.sh` 経由でも 3） | — |
| P1-4 | src が自由な引数、clk/rst の結合、入力の幅・順・初期状態、seedIn の向き、WidthStmt の過剰な拒否 | `Tools/VedU1Contract.lean`（§4.2）。src は入口が元の宣言から作る項で、型の Expr の一致を入口が確かめる。clk/rst は実際の入力で、全 register の clock/reset の名前。`seedFwd` で時刻の向きを直した（前の下書きは逆向き）。`WidthStmt` は wire 宣言を、意味が読む所（データ入力、register の出力）だけに求める | `MEM=8G memlimit lake env lean` で 2 ファイルとも rc=0（§4.2。`lake build` は Sparkle 全体の precompile になるので手元では止めた）。`seedFwd_time` 証明済み。`pilotB0` に clk・rst・out の wire 宣言が無いこと、`ShapeCore`/`WidthStmt` が成り立ち前の下書きの幅の節が成り立たないこと、instance 文 2 つで v1 の範囲外であること、玩具の module の 6 つの変異が拒否されること | `OutputsStmt` の証明、入口（`synthesizeEntry` を 1 回、定数の登録、型の Expr 比較、strict 監査）、宣言の引数名とデータ入力名の対応規則の実物での確認、memory・instance のある module（v1 の範囲外。実物の `pilotB0` も子 instance を持つので範囲外）、`lake build` での 2 target の確認（cluster）。データ入力の後に clk・rst が来ない module があれば `ShapeStmt` の入力の節を直す |
| 追加 | `#ved_audit_generated` の限界、U0 の同期設定と一般の使用の同期前提 | Tools/VedStrictAudit.lean の docstring と §3.3・§3.4 に明記。`#ved_audit_current_namespace` を追加（同じ限界） | `lake build Tools.VedStrictAudit Tests.Ved.StrictAuditCheck` rc=0（730341a1）。期待した定理が無くても一覧に出ないだけであることを Check に書いた | — |

DeepElab を使う smoke（§3.5 の 1・2）は manager の復旧後に行い、その結果で、塊の Lean の部分がコンパイルできるか、VED の行の形、写しの方式と分けた版の振る舞いを確かめる。U0 全件を待たずに、U1 の型と最小の接続（§4.2 の入口の試作）は進めてよい（reviewer の依頼文）。

## 9. bb58e0c6 に対する変更依頼（P1-A・P1-B）への対応（改訂 3）

**Issue 未登録（manager 停止中）**。復旧後に、この変更依頼と U1 の完了条件を Issue に記録する。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）

新しい実装成果の一括受理を求めるものではない。下の「証明した」は `MEM=8G memlimit lake env lean <file>`（既にある olean に対して 1 ファイルずつ）で確かめた範囲である。`lake build` は Sparkle を import する target で Sparkle 全体の共有ライブラリの precompile を始めるので手元では実行しておらず、**2 target の `lake build`（`kjob lake build Tools.VedU1Contract Tests.Ved.U1ContractCheck`）は cluster が要る**。

### 9.1 P1-A: 元の宣言の入出力の対応表（`Tools/VedU1Contract.lean`）
- **対応表 `DeclTable`** は元の宣言の**型**から作る。`binders`（明示の引数の名前、順）、`ins`（引数ごとの port の型: `Signal defaultDomain Bool` → `.bit`、`Signal defaultDomain (BitVec w)` → `.bv w`）、`out`（結果 `Signal defaultDomain T` の `T` を `Bool`・`BitVec w`・`×` の木として。`OTy.flat` が左から平らにした出力の射影の固定の順）。
- **読み取り**: 項の elaborator `ved_table% decl` が、宣言の型だけ（`forallTelescopeReducing`）から表の literal を作る。v1 の範囲外（Signal でない引数 = params、暗黙の引数、`defaultDomain` 以外の domain、literal でない幅、`Bool`/`BitVec`/`×` 以外の型、universe 多相）は throw する。
- **宣言への結合（kernel）**: `DeclTable.Ty tbl` は表が表す Lean の型。最終の文 `U1Stmt c m f` は宣言そのものを `f : c.table.Ty` として取るので、宣言の型が表の型と（定義的に）一致しないと文が型検査を通らない。`src` は `srcOf c f`（`f` を表の port ごとの入力 Signal に適用し、全射影を観測して名前で引く）で、呼び出し側が与える自由な引数ではない。Check の `toyBound : toyTable.Ty := toyDelay` がこの結合の確認。
- **照合**（`CorrStmt`・`ShapeCore`・`WidthStmt`、すべて decidable）:
  - arity: `binders`・`inNames` の長さ = `ins` の長さ（`zip` が黙って切り詰めないように）;
  - 順と port ごとの幅: `m.inputs = c.dataInputs ++ [clk, rst]`、`c.dataInputs` は**表から**作る（名前 i 番目と `ins` i 番目の `hw` 型）。データ入力の `declWidth` = 表の幅;
  - 全出力の射影: `outNames` の長さ = `out.flat` の長さ、`m.outputs = c.outputs`（表の全射影を順に、幅つき）;
  - 名前の単射性: `inNames ++ outNames ++ [clk, rst]` が `Nodup`（独立な 2 入力が 1 つの stream に縮まない、入力と出力が同じ名前にならない）;
  - clk/rst との分離: 同じ `Nodup` に clk・rst を含める;
  - 幅は正（`BitVec 0` の port は拒否。v1 の範囲）。
- **`contractOf tbl outNames clkRst m`**: 表（arity・順・幅・出力の射影）は宣言から。入力 port の名前は合成器の名前の規則 `_gen_<引数名>`（玩具と `pilotB0` で観測。規則が違えば `ShapeCore` が拒否するだけで、受理はしない）。`outNames` は出力の射影ごとに与える（1 出力は `"out"`。複数出力の名前の規則は実物で未確認）。module 名・wires・register の初期値は `m` から読む: 宣言の型には現れず、初期値や wire の幅が違えば `OutputsStmt` が証明できなくなる（真にはならない）。
- **対照（kernel の拒否、`example … := by decide`）**:
  - 別の宣言の表: `toyAdd`（2 入力）と `toyDelay8`（8 bit）の表で `toyMod` に対して `¬ ShapeCore`。3 つの別の宣言の表は `toyDelay` の表と異なる（よって `U1Stmt toyC _ f` はそれらの `f` で型検査を通らない）;
  - 2 入力の併合: `toyAdd` の `a`・`b` を 1 つの stream `_gen_a` から取る `mergedMod`。2 つの引数を `_gen_a` に名付けた契約は `¬ CorrStmt`（単射性）、名前の規則どおりなら `_gen_b` が無く `¬ ShapeCore`、入力 port を 2 重に並べても `¬ CorrStmt`;
  - 出力の欠落: 2 射影の `toyPair` に対して出力 port 1 つの module。名前 1 つでは `¬ CorrStmt`（網羅）、名前 2 つでは `¬ ShapeCore`（名前 2 つの契約自体は `CorrStmt` を満たす）;
  - 幅違い: 正しい表で、入力 5 bit・出力 8 bit の module は `¬ ShapeCore`、入力の wire 宣言 5 bit は `¬ WidthStmt`;
  - clk との分離: 出力を `"clk"` と名付けると `¬ CorrStmt`;
  - 改訂 2 の module の変異（初期値、出力の追加、reset を別の wire、入力の順）は引き続き `¬ ShapeStmt`。
- **正直な状態**: 改訂 2 の `toyExpected` は `Prop` の**定義**で、証明ではなかった（elaborate することを見ただけ）。改訂 3 で玩具については証明した（§9.3）。実際の `declName` の表を読み、`synthesizeEntry` を 1 回呼び、`m` と `c` を定数として登録して `U1Stmt` を証明する**入口（元の宣言への自動の結合と、その意味の証明）はまだ予定**である。

### 9.2 P1-B: clock
- `InputsOk` は、データ入力が `declWidth` に収まることと **reset を 0 に保つこと**だけを要求し、**clock の値は自由**（各周期で全称）。「IR の意味は clock を読まない」の主張は撤回した（§4.2 の項を訂正）。`evalExpr (.ref clk)` は env の clock を読み、データの式から参照できるので、0 に固定すると保証が狭くなる。clock を自由にしたので、「データの式が clock を読まない」条件も非干渉の補題も要らない。0 に固定する部分は残っていない。
- 確認: `toy_inputsOk_toggling_clock`（clock が周期ごとに 0/1 に変わる入力が `InputsOk` を満たす）。`toyDelay_outputs` はこの入力にも適用される。
- reset = 0 の範囲は引き続き明示（reset の掛かる run は保証の外）。
- 最適化との接続（`seqOptCheck_run_sound` の `hinsFit` は clk を `2^declWidth clk = 1` で抑える）は、その単位で橋を作る。今の IR の保証を将来の前提に合わせて狭めない。

### 9.3 `toyDelay` の証明（`Tests/Ved/U1ContractCheck.lean`）
- `theorem toyDelay_u1 : U1Stmt toyC toyMod toyDelay`。`CorrStmt`・`ShapeStmt`・`WidthStmt` は kernel の `decide`、`OutputsStmt`（`toyDelay_outputs`）は構造的な証明: 範囲内のすべての入力 stream、すべての clock の stream、reset 0、すべての run の長さ `K`、すべての周期 `t < K`、すべての出力 port について、`m.body` そのものの `runModule` が `some envs` を返し、`envs[t]` の出力が宣言 `toyDelay` の値に等しい。run の前提は無い。
  - 補題: `toy_step`（1 周期の `stepModule`）、`toy_run`（`K` 周期の run の時刻 `s` から始まる `k` 周期の末尾を `k` の帰納法で）、`toy_src`（`srcOf toyC toyDelay ins "out" t` = `toyR ins t`: 時刻 0 は 0、`t+1` は `ins t x % 16`）。
  - `native_decide`・`sorry`・新しい axiom は使っていない。
- 監査（Check の中で `#guard_msgs` に固定）:
  `VED STRICT OK Tests.Ved.U1ContractCheck.toyDelay_u1: [Classical.choice, Quot.sound, propext]`

### 9.4 記録の区別（評価の観測と kernel の事実）
- **kernel の事実**: Check の `example … := by decide` と `theorem`（玩具の表・契約・対照・`toyDelay_u1`）。
- **評価の観測**: `pilotB0` の `#guard` の行（コンパイルされた評価器が `Decidable` の instance を実行する。kernel は検査しない）。`pilotB0` について言えるのは観測で、clk・rst・out に wire 宣言が無い、`CorrStmt`・`ShapeCore`・`WidthStmt` が成り立つ、`WidthStmtDraft1` が成り立たない、instance 文が 2 つで v1 の範囲外。`pilotB0` の表は宣言 `synth_hftPcieOutByte` と同じ型の写し `pilotSig` から `ved_table%` で読んだ（元の宣言の olean は手元に無い。読むのは型だけ）。

### 9.5 確かめたこと
- `MEM=8G memlimit lake env lean Tools/VedU1Contract.lean`: rc=0（olean は scratchpad に出力）。
- `MEM=8G memlimit lake env lean Tests/Ved/U1ContractCheck.lean`: rc=0、約 6 秒（`Tools.VedStrictAudit`・`Tools.ShippingFGCircuitS3rArtifact` の olean も scratchpad から）。

### 9.6 まだ開いているもの
- **U1 の入口**: `synthesizeEntry` を 1 回呼んだ同じ artifact の同一性（`f_u1_mod` の値 = その run の `toExpr m`）、登録した定理の完全な型と期待する文の Expr の一致、strict 監査、失敗したら `m` を返さない（§4.1）。これは U1 入口の束で確かめ、U0 準備の完成とは数えない。
- **実際の宣言**: 実物の `declName` での表の読み取りと名前の規則（`_gen_<引数名>`、複数出力の名前）の確認、params を持つ宣言、構造体を返す宣言（今の読み取りは `×` の木だけ）。
- **`OutputsStmt` の一般の生成**: 玩具は手で証明した。実物の body ごとの証明の生成（replay）は U1 の本体の仕事。
- **memory と instance**: v1 の範囲外（`pilotB0` も子 instance を持つので範囲外）。
- reset の掛かる run、最適化（`checkedOptimize`）と SV への接続。
- 2 target の `lake build`（cluster）。

## 10. U1 入口の最小縦断（改訂 4、83fe82b2 に対する裁定 4 への対応）

**Issue 未登録（manager 停止中）**。復旧後に、この裁定と U1 入口の完了条件を Issue に記録する。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）

**受理済みのコンパイル済み IP には数えない**。小さい試験用の宣言 1 つ（と同じ型の対照用の宣言）で入口をつないだもので、必要 IP 327 のどれでもない。下の「証明した」は `MEM=16G memlimit lake env lean <file>`（既にある olean に対して 1 ファイルずつ、scratchpad の wrapper `u1lean.sh` で LEAN_PATH に新しい olean を足す）で確かめた範囲で、`lake build` は実行していない（§9 と同じ理由。cluster が要る）。`Sparkle/` と `Tools/DeepElab.lean` は変えていない。DeepElab は import していない。

### 10.1 つないだもの（`Tools/VedU1Entry.lean`、`vedU1Entry` / `#ved_u1 decl`）
1. 元の宣言の**型**から対応表を読む（`readTable`、`ved_table%` の中身と同じ関数）。出力の射影が 1 つでなければ、**合成の前に**拒否する（段 `multi-output`。複数出力の port 名の規則は実物で未確認なので、推測で受理しない）。
2. コマンドと同じ `inlinerFuelGuard` の後、`synthesizeEntry declName` を**ちょうど 1 回**呼び、返った `(m, design)` を保持する。再合成はしない。
3. `declName.ved_mod : Module := toExpr m` を登録する。その閉じた項を評価し直した値が `m` と `DecidableEq` で等しいこと、登録した定数の値がその項と `Expr` として等しいことを確かめる（段 `artifact`）。契約 `declName.ved_contract := contractOf (表) ["out"] clkRst declName.ved_mod`（clk/rst の名前は `m` の register から選ぶだけで、`ShapeCore` が全 register と入力の末尾で照合する）、出力の一覧 `declName.ved_outs` も登録する。
4. 期待する文 `U1Stmt declName.ved_contract declName.ved_mod declName`（**元の定数そのもの**）を `Expr` として作り、型検査する（段 `type`）。生成した証明 script をその型で elaborate する（`sorry` への置き換えをしない。elaborate 中に error が出たら拒否。段 `proof`）。`Elab.async false` で kernel に `declName.ved_u1` を**ちょうどその型で**同期登録し（段 `kernel`）、登録された型を読み直して期待の `Expr` と比べる（段 `type`）。
5. `Tools.VedStrictAudit.strictAudit`（存在、theorem、mvar なし、到達閉包 ⊆ 標準 3 公理）を通す（段 `audit`）。
6. 3〜5 が通ったときだけ `m` を返す／表示する。fallback、trace だけの経路、replay の省略は無い。
- **失敗したときに戻すもの（記録修正 1、裁定 5）**: `checkU1` は**自分の開始時**（つまり `synthesizeEntry` の後）に `saveState` を取り、`checkU1` の中の失敗（heartbeat／max recursion の runtime 例外も `tryCatchRuntimeEx` で捕まえる）ではその TermElabM の状態に戻す。戻るのは checker が足した定数（`ved_mod`・`ved_contract`・`ved_outs`・`ved_u1`、kernel の段で残ったもの）と message を checker 開始時へ、まで。**合成の副作用の復元は主張しない**: `synthesizeEntry` の前の環境、`IO.Ref`／cache、ファイルは戻さない。以前の「どの失敗でも環境全体を戻す／何も残らない」はこの範囲に限定した。
- **`VED U1 REFUSED <decl> [<段>]` の形で出るもの（実装を変えて合わせた）**: `vedU1Entry` が捕まえる例外はすべてこの形。段は、合成の前の `table`・`multi-output`、`inliner`（`inlinerFuelGuard`、今回包んだ）、`synthesis`（`synthesizeEntry`、今回包んだ）、`checkU1` の中の `table`・`multi-output`・`artifact`・`type`・`proof`・`kernel`・`audit`、それ以外の `checkU1` 内の例外（登録名の `addDecl` の失敗、runtime 制限など）は `checker`（今回追加）。**この形で出ないもの**: interrupt 例外（elaborator は捕まえない）と、`checkU1` より前（`readTable`・`inlinerFuelGuard`・`synthesizeEntry`）で起きた heartbeat／max recursion の例外（そこは通常の `try … catch` なので runtime 例外は捕まえず、そのままの error で出る。戻しもしない）。
- 証明 script は**信頼しない**（kernel が検査する）。この縦断の script が扱うのは、register の無い module と、register が 1 つでその現在値が出力になる module（delay）だけ。それ以外の body では script が失敗して入口は拒否する（受理はしない）。
- 一般の補題 `outputs_of_step`（1 周期の不変条件 `R` から `OutputsStmt` を、`seedFwd_time` で時刻の向きを合わせて run の長さの帰納法で導く）は 1 回だけ証明した。生成した script はこの補題に、各 instance の `R`（delay なら「register の値 = 宣言の時刻 `s` の出力」）と 1 周期の計算（`simp` で `m.body` そのものの `stepModule` を評価、連結の算術は `or_mod`）を渡す。
- `SPARKLE_PROFILE` は `synthesizeEntry` が読む（設定されていれば診断用の entry が走る）。どちらの枝でも、証明するのは返った `m` そのもの。
- `checkU1` は入口の下の検査器で、module・文に入れる定数・証明を別々に受け取る。これは**対照のためだけ**（差し替えを 1 つずつ注入する）。入口自身は常に、合成した `m`、宣言そのもの、生成した script を渡す。

### 10.2 証明したもの（`Tests/Ved/U1EntryCheck.lean`、`#guard_msgs` で固定）
- `delay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := Signal.register 0#8 x`（corpus の書き方、cf. `Tests/TestCircuits.lean`）。`synthesizeEntry` が返す module は loop の機械の形（`_gen_out := {_gen_reg0, _gen_x}`、`next_gen_reg0 := _gen_out[7:0]`、register `_gen_reg0` init 0、`out := _gen_out[15:8]`、clk/rst、module 名 `Tests_Ved_U1EntryCheck_delay8`）。
- `#ved_u1 delay8` → `theorem Tests.Ved.U1EntryCheck.delay8.ved_u1 : U1Stmt delay8.ved_contract delay8.ved_mod delay8`。監査の行（固定）:
  `VED U1 OK Tests.Ved.U1EntryCheck.delay8.ved_u1: [Classical.choice, Quot.sound, propext]`
  続けて返った `m` の全体を表示（`#guard_msgs` に固定）。文の第 3 引数が定数 `Tests.Ved.U1EntryCheck.delay8` そのものであることも `run_meta` で確認した。
- 同じ入口で、それぞれ**自分の** module について受理: `ident8`（恒等。合成された module は `out := _gen_x` で clk/rst なし、文は真）、`delay8k`（init 5）、`delay8b`（`delay8` と同じ中身で別名）。
- `native_decide`・`sorry`・新しい axiom は、受理した証明に使っていない。

### 10.3 対照（すべて `#guard_msgs` で固定。拒否の対照はすべて共通 helper `expectRefused stage absent act` を通し、拒否のたびに `absent`〔その base の checker の定数 4 つ、`checkerNames base`〕が環境に無いことも確認する。記録修正 2）
- **同じ型で意味が違う宣言**:
  - 入口: delay の module に恒等 `ident8` を差し替えた完全な期待型 → 拒否 `[proof]`。逆（恒等の module に `delay8`）→ 拒否 `[proof]`。
  - kernel: `theorem ident_not_delay : ¬ U1Stmt delay8.ved_contract delay8.ved_mod ident8`（閉じた入力 `x = 1` の 1 周期の run: register は 0、恒等は 1。`not_outputs_of_witness`、`decide`/`rfl`）。script の失敗だけでなく、文が偽であることを kernel で示した。
- **変異した module と元の宣言**（`delay8` に対して、`m` を 1 箇所だけ変える）: register の init 0→5、出力が連結の入力側を読む、出力 port の幅 8→9、register の入力を定数 3 に → すべて拒否 `[proof]`。init の変異は kernel でも `theorem init5_not_delay : ¬ U1Stmt cInit5 mInit5 delay8`（全 0 の入力の時刻 0 で 5 ≠ 0。`mInit5` は `mutInit` の値と `DecidableEq` で一致することを確認）。
- **別の宣言の証明・artifact の流用**: `delay8` の文の証明に `delay8k.ved_u1`・`delay8b.ved_u1`（同じ意味でも module 名が違うので型が合わない）・`ident8.ved_u1` → 拒否 `[proof]`。`delay8k` の module（init 5）・`ident8` の module を `delay8` に → 拒否 `[proof]`。
  - **拒否ではない記録（欠陥でもない。裁定 5 の名前の裁定）**: `delay8b` の module（同じ意味、別の module 名）に**新しく生成した証明**を付けると `delay8` について受理される（`ctlArtB`）。下位の `checkU1` が検証するのは「この `m` がこの宣言の意味を持つ」なので、同じ意味で別名の `m` が証明できてよい。本番の `vedU1Entry` が受け取った `m` を差し替えずに検査・返却することは、これとは別の問題。
  - 3 つを分けて記録する: (a) 別の宣言の**旧い証明**の流用は拒否（`ctlProofB`・`ctlProofK`・`ctlProofI`）。(b) 同じ意味の artifact に対する**新しい正しい証明**は受理（`ctlArtB`）。(c) 入口は**同じ実行の artifact** を保持する（`synthesizeEntry` 1 回の `m` をそのまま `checkU1` に渡して返す。構成による性質で、`checkU1` の段 `artifact` が登録した `ved_mod` がその `m` を表すことを確かめる）。
- **複数出力**: `pair8 : … → Signal defaultDomain (BitVec 8 × BitVec 8)` → `VED U1 REFUSED … [multi-output]: 2 output projections; …`（合成の前に拒否。コマンドの error を固定し、同じ拒否を helper でも通して名前が無いことを確認）。
- **範囲外の body**: `inc8 := (· + 1#8) <$> Signal.register 0#8 x`（register はあるが出力ではない）→ 入口が拒否 `[proof]`、checker の定数は残らない（`synthesizeEntry` 自体の副作用は戻さず、確認もしていない）。これは script の**網羅の限界**であって反例ではない（文は真かもしれない）。
- **strict 監査**: 完全な文の正しい証明に `native_decide` の事実を混ぜた項（`(fun (_ : 2 + 2 = 4) => delay8.ved_u1) (by native_decide)`）は kernel が受理するが、到達閉包に `Lean.ofReduceBool` があるので拒否 `[audit]`、定理は残らない。（契約の節そのものに `native_decide` を使う形は、`ved_mod`/`ved_contract` が kernel 用の未コンパイルの定義なので compile できない。）

### 10.4 記録の区別
- **kernel の事実**: `delay8.ved_u1` ほか受理した 4 つの定理、`ident_not_delay`、`init5_not_delay`、`ones_ok`/`zeros_ok`。
- **入口の拒否**: `checkU1`/`vedU1Entry` が throw したこと（段の名前つき）。拒否は「この script では証明できなかった」までで、文が偽であることの証明ではない（偽であることは上の kernel の定理で別に示した 2 例だけ）。
- `pilotSig`（`Tests/Ved/U1ContractCheck.lean`）は引き続き、`synth_hftPcieOutByte` の**型を写した観測用の宣言**で、元の宣言についての証明ではない。今回の入口は `pilotB0` も `synth_hftPcieOutByte` も扱っていない（子 instance を持つので v1 の範囲外）。

### 10.5 確かめたこと（rc と時間、このマシンで 1 ファイルずつ、`MEM=16G memlimit`）
- `Tools/VedU1Contract.lean`（`contractOf` の docstring の修正のみ）: rc=0。
- `Tools/VedU1Entry.lean`: rc=0、約 8 秒。
- `Tests/Ved/U1ContractCheck.lean`: rc=0、約 6 秒（変更なし、再確認）。
- `Tests/Ved/U1EntryCheck.lean`: rc=0、約 29 秒（`synthesizeEntry` は計 5 回: 入口の実行 5 回〔delay8・ident8・delay8k・delay8b・inc8〕で各 1 回。pair8 は合成の前に拒否。対照は登録済みの module を評価し直して使い、合成し直さない）。
- `synthesizeEntry` は import した olean の IR を interpreter で実行した。共有ライブラリの precompile・gcc の build は要らなかった。
- 文言の修正（裁定 4 の軽微な点）: `contractOf` の docstring を「不一致が出力意味に影響する場合は `OutputsStmt` を証明できず拒否。未使用 register など観測出力に影響しないものは拒否しなくてよい」に直した。module 名も `m` から読み宣言名に結び付けていないことを書き足した。
- lakefile に `Tools.VedU1Entry`・`Tests.Ved.U1EntryCheck` の `lean_lib` を足した。

### 10.6 まだ満たしていないもの
- **一般の証明生成**: script は register なし／register 1 つで出力 = register の形だけ。それ以外（`inc8` のような一般の 1 register の機械、複数 register、比較・mux 等の演算を含む body、Bool の出力）は拒否する。必要 IP の body ごとの replay の生成が U1 の本体の仕事として残る。
- **複数出力**: 拒否のまま。synthesizer の複数出力の port 名の規則の確認が要る。
- **module 名と宣言名の結合**: 今の IR の意味の契約には**加えない**（裁定 5）。名前の規則が要るのはファイル出力／階層の consumer へ進むときで、そのときに別の仕様として扱う。
- params を持つ宣言、構造体の出力、memory、instance（`pilotB0` を含む）、reset の掛かる run、最適化（`checkedOptimize`）と SV への接続。
- `#verify_elab_deep` のコマンド自体（DeepElab）と 327 の経路への接続はしていない。通常の entry・他のコマンドの経路は別扱い。
- `lake build`（`kjob lake build Tools.VedU1Entry Tests.Ved.U1EntryCheck`）は cluster が要る。未実行。
- reviewer の確認は未（このコミットは受理を求める成果の一括ではない）。

### 10.7 裁定 5（762b3466 に対する静的レビュー）への対応と次の優先
- 記録修正 1（戻す範囲と段の形）: 文言を実装どおりに限定し、加えて実装を変えた（`inliner`・`synthesis`・`checker` の段で包む、`checkU1` の戻しを runtime 例外にも広げる）。§10.1 の 6 の下の 2 項目。
- 記録修正 2（拒否のたびの確認）: 実装を変えた。`expectRefused` と `assertClean` を 1 つの helper（`absent` の名前の一覧を引数に取る）にまとめ、Check の拒否の対照すべてで使う（`pair8` はコマンドの error の固定に加えて helper でも通す）。
- 名前の裁定: §10.3 と Check のコメントに (a)(b)(c) を分けて記録した。
- 再確認（このマシン、1 ファイルずつ、`MEM=16G memlimit`、scratchpad の `u1lean.sh`）: `Tools/VedU1Entry.lean`（olean を出力）rc=0 約 8 秒、続けて `Tests/Ved/U1EntryCheck.lean` rc=0 約 31 秒。`lake build` は未実行。
- **次の優先（reviewer）**:
  1. Issue 登録の後、exact-head で必要な target の build と U0 smoke。
  2. その結果を見て、既存の DeepElab の proof generator をこの入口の契約へ接続する最小 1 例。
  3. `scriptFor` の手書きの専用対応を際限なく広げる方向は避ける。
  4. 多出力／階層／opt／SV は、明示的な範囲外のまま。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）

必要 IP 327 の受理数には加えない。

## 11. DeepElab の生成器を U1 入口へ（最小 1 例、Issue sparkle-ved-gen1、裁定 6 への対応）

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。必要 IP 327 の受理数には加えない（下の 2 例はどちらも試験用の宣言で、必要 IP ではない）。

### 11.1 裁定 6（経路 1–4 と accK9 を設計として許可）
- 第一例 `accK9`、第二例 `natInit5`（`Tests/Verification/ValueParamInitRepro.lean` の形）。native の G1（`mkG1` の HashMap/String 計算）の全面改修は先行条件にしない。
- 返却 `m.body` そのものの step を証明する。cone の `Expr` 一致だけでなく、`declWidth` と `weOfC`/`weM` の一致（必要な参照の上）、register/input の slot 対応、mask と範囲、init、時刻の向きを kernel で閉じる。二度の合成の一致を観測で使わない。失敗したら拒否する。
- 最終の U1 定理の型と証明の axiom 閉包は標準 3 公理だけ。名前付きの native 定理に依存しないと言うなら、`collectAxioms` とは別に定数依存閉包を確かめる。DeepElab の native 依存の生成物が環境に在ること自体は拒否の理由にしない。native 証明の流用の対照を残す。
- 元の宣言が違うだけで常に拒否とはしない。意味が違う証拠の流用は拒否し、意味が同じ新しい正しい証明は許す。
- 不要な HashMap/String 抽出の正しさを、checker の証明対象に戻さない。ただし残る幅表や concatNorm の前提を、観測や新しい仮説に移さない。

### 11.2 つないだもの（`Tools/VedU1Deep.lean`、`vedU1DeepEntry` / `#ved_u1_deep decl`）
- 入口は `vedU1Entry` と同じ形: 型から表を読む（複数出力は合成の前に拒否）、`inlinerFuelGuard`、`synthesizeEntry` を**ちょうど 1 回**、返った `m` を `checkU1` に渡して、成功したときだけ `m` を返す。違いは証明源だけ。
- `checkU1` に証明源 `.built mk` を足した（`Tools/VedU1Entry.lean`、8 行）。`mk` は checker が `ved_mod`・`ved_contract`・`ved_outs` を登録した**後**に、名前と返却 `m` から script を作る。`mk` が環境に足すもの（補助の定義）は checker の save/restore の中にあり、拒否したら戻る。`mk` の失敗は段 `proof` の拒否。
- builder（`buildDeepWith stmtDecl decl`）が script に書く DeepElab の定数は、`#verify_elab_deep decl` が作ったもののうち次だけ: `{f}_deep : Cdo Γr Γi w`、`{f}_nm`、`{f}_inp`、`{f}_deep_trace`、`{f}_deep_next`、`{f}_deep_inits`、`{f}_deep_out`（smoke2 の row 212 の監査ではどれも strict OK の系統）。このうち `_deep_next`/`_deep_inits`/`_deep_out` は `rfl` の定理で、最終の証明項には残らない（`simp` の定義的な書き換え）。無ければ拒否（`#verify_elab_deep` を先に）。`Cdo` でなければ（memory を持つ `CdoM` 等）範囲外として拒否。
- **使わないもの**: cone の定数、`_deep_fidelity_*`、DeepElab の再合成 IR、native 依存の定理（`_deep_coneEval_*`、`_deep_regstep`、`_deep_step_*`、`_deep_seed_bounded`、`_deep_signalM*`、`_deep_signal_fold`、`_deep_state_trace`、`_deep_signal_run`）。提案の段階で予定した「cone の `Expr` 一致を閉じた `decide` で」も、不要だったので使っていない。返却 `m.body` と DeepElab の `Cdo` の compile をそれぞれ kernel で算術まで評価して比べるので、2 つの合成が同じ module を返すこと（probe1 で観測、BEq で一致）を前提にも観測の根拠にもしていない。
- 補助の定義 2 つ（checker の base の下、通常の reducibility）: `ved_inpU ins t j`（U1 の入力の流れ `ins` を DeepElab の入力の値へ: `({f}_inp (PTy.sig (.bv w) ins "_gen_<binder>") …) j).val t`）と `ved_irS ins t := Cdo.irState {f}_deep {f}_nm (ved_inpU ins) t ⟨0, _⟩`。`abbrev` にすると `simp`/`omega` が別の形に開いて atom が揃わなかった（probe4）ので通常の定義にした。
- 生成した script（信頼しない、kernel が検査）:
  1. `hinj`（`{f}_nm` の単射、`decide`）、`hlt : ved_irS ins t < 2^w`（`Cdo.irState_eq` から、値は `BitVec w` の `toNat`）。
  2. `hSI : srcOf C f ins "out" t = ved_irS ins t`: `srcOf` を宣言の Signal の値へ開き、`{f}_deep_trace` で書き換え、`{f}_deep_out` の compile を `evalExpr` で評価する。`envOfC`/`weOfC`/`chainMap` を `List.finRange` の上で計算して名前を照合する（`envOfC_names` は `simp` が暗黙の長さを正規化して当たらなかった、probe3）。
  3. `outputs_of_step` に不変条件 `R ins s st := st r = ved_irS ins s` を渡す。初期: `st0`（`encodeInit` と `declWidth`）と `Cdo.irState` の 0 と `{f}_deep_inits`。1 周期: `stepModule (declWidth m) m.body (seedIn m ins s st)` を `simp` で計算し（`hrst` で reset 0、`hin` で入力の範囲）、出力は `hSI` と `R` で、次の register の値は `Cdo.irState` を 1 段開いて `{f}_deep_next` の compile を同じ評価で計算し、`omega` で比べる。時刻の向きは `outputs_of_step`（`seedFwd_time`）が持つ。
- 範囲（この外では script が失敗し、入口は拒否する。受理はしない）: register 1 つで、その値が出力、データ入力は bit-vector、出力 1 つ、memory なし。

### 11.3 経緯（probe、ソースツリー外 `~/git/workspaces/ved-inputs`、Issue 付き Job）
- probe1（`ved-probe1-b316` exit 0）: `accK9`・`natInit5` で `synthesizeEntry` の `m` と `synthesizeHierarchical` の単一 module が BEq で一致（観測。証明には使わない）。
- probe2（exit 0）: DeepElab の生成文の形（`accK9_nm` は 0 ↦ `_gen_acc`、1 ↦ `_gen_d`。next/out は concat の slice）。
- probe3〜7（exit 1）: 依存型の注釈、`envOfC_names` が当たらない、`evalOp` の展開、`abbrev` の atom、`srcOf C f` の rewrite で motive が型不正、`← hR` が構文一致しない。各回の原因と対処は Issue の note。
- 生成器の build: `ved-deep-5fc2`（`evalExpr` が `Meta.evalExpr` と曖昧、2 例とも `[proof]` で拒否）、`ved-deep-2260`（`simp` が先に goal を閉じ `No goals`、同じく拒否）、`ved-deep-f66f`（入口の受理と対照は通過、閉包の検査が空虚で停止）、`ved-deep-332e`（閉包の要件を `_deep_next` に置いた誤り）。各回とも入口は fallback なしで拒否し、誤りは script か検査の側だった。
- probe8（`ved-probe8-b316` exit 0）: 手書きの定理 `accK9_u1 : U1Stmt accK9.ved_contract accK9.ved_mod accK9`、`sorry` なし、strict 監査 `[Classical.choice, Quot.sound, propext]`。この証明の形を 11.2 の生成器にした。

### 11.4 Check（`Tests/Ved/U1DeepCheck.lean`）
- `#verify_elab_deep` の後、入口が `accK9`・`natInit5` を受理: `VED U1 OK …ved_u1: [Classical.choice, Quot.sound, propext]`（`#guard_msgs` で固定）。
- 完全型: 登録された定理の型が `U1Stmt f.ved_contract f.ved_mod f`（宣言の定数そのもの）と `Expr` として等しい。
- 定数依存閉包（`collectAxioms` とは別）: `accK9.ved_u1` から型と値をたどった閉包が `accK9_deep_trace`・`accK9_deep`（reify した回路）・`Cdo.irState` を含み（空でない）、`_native` の補助と native 系の DeepElab 定理を含まない。環境には `accK9_deep_signal_run` が在ることも確かめる。
  - 定理の値は `thmInfo`/`defnInfo`/`opaqueInfo` を明示的に読む。最初の版は `ConstantInfo.value?` を使い、これが定理に `none` を返したので型だけをたどっていた（空虚な検査。probe9 で発見）。strict 監査は `collectAxioms`（定理の値をたどる）なので、この誤りの影響を受けていない。
  - `{f}_deep_next`・`{f}_deep_inits`・`{f}_deep_out` は `rfl` の定理で、`simp` は定義的な書き換えとして使うので項に定数が残らない。したがって閉包の要件はこの 3 つではなく、回路 `{f}_deep` とその漸化式 `Cdo.irState` に置く。
- 拒否（共通 helper `expectRefused`。拒否のたびに checker の定数と補助の定義が残っていないことも確かめる）:
  - 変異した module（init 0→5、定数 9→10）と、元の宣言と自分の DeepElab の事実 → `[proof]`。変異が元と異なることも確かめる。
  - 別の宣言の DeepElab の事実（意味が違う `accK10`、`natInit5`）→ `[proof]`。
  - 別の宣言の受理済みの証明（`natInit5.ved_u1`）→ `[proof]`。
  - `native_decide` の事実を混ぜた正しい証明、DeepElab の native の replay 定理（`accK9_deep_signal_run`）を引き込む正しい証明 → `[audit]`。
  - `#verify_elab_deep` を走らせていない宣言（`accK11`）→ `[proof]`。
- kernel: `acc5_not_accK9 : ¬ U1Stmt cAcc5 mAcc5 accK9`（init 5 の module、全 0 の入力の時刻 0 で 5 ≠ 0。宣言側の 0 は `{f}_deep_trace` と `{f}_deep_inits` から）。
- 意味が同じ別の宣言の DeepElab の事実で受理する対照は置いていない。この script は `{f}_deep_trace` で宣言そのものを書き換えるので、別名の宣言の trace は当たらず拒否になる（裁定の「常に拒否とはしない」に反する設計の規則ではなく、script の網羅の限界）。

### 11.5 まだ満たしていないもの
- 一般の生成: register 複数、register が出力でない形、Bool の入出力、memory、struct 出力、instance、reset の掛かる run、最適化と SV。
- `#verify_elab_deep` の全実行を使っているので、補助的な再合成（DeepElab 側の `synthesizeHierarchical`）とその native 依存の生成物の費用が掛かる。U1 の対象の `synthesizeEntry` は 1 回のまま。費用と失敗は build の記録に残す。emit だけの flag が要るなら独立の小さな差分にする。
- 327 行への接続。
