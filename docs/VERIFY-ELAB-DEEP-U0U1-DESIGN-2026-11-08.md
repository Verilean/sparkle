# verify_elab_deep 拡張: U0 測定の設計、厳密な axiom 監査、U1 契約の下書き（2026-11-08）

土台: par/ved-plan 8f2bcada（調査書 `docs/VERIFY-ELAB-DEEP-SURVEY-2026-11-08.md`）。この文書は**設計**で、測定はまだ一度も実行していない。cluster の Job は使っていない。実行したのは、手元での小さな build 2 件（`Tools.VedStrictAudit`、`Tests.Ved.StrictAuditCheck`、どちらも `MEM=8G memlimit lake build`、exit 0）だけである。`Tools/DeepElab.lean` と `Sparkle/` は変えていない。

**Issue 登録は未実施**（manager が停止中。`managerctl` は completed Failed の Pod への exec でエラーになる）。復旧後に、U0/U1 の完了条件とこの裁定を Issue に登録する。

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

## 2. 厳密な axiom 監査（裁定 8・9）

### 2.1 置いたもの
- `Tools/VedStrictAudit.lean`（`import Lean` だけ。lakefile に `lean_lib «Tools.VedStrictAudit»`）。
  - 許可する集合は `strictAllowed = [propext, Classical.choice, Quot.sound]` だけ。
  - `strictAudit decl : CoreM StrictReport` は次を順に確かめ、1 つでも外れたら `throwError` する。(a) 宣言がある、(b) `theorem` である（def・axiom・opaque などは拒否）、(c) 型にも証明項にも metavariable がない、(d) `Lean.collectAxioms decl`（**到達する閉包**）が `strictAllowed` に含まれる。外れた axiom はすべてエラー文に名前で出す。`sorryAx` は axiom なので (d) で落ち、文に「depends on sorry」と付く。
  - 判定は閉包の集合の包含**だけ**で行う。tactic の名前も、axiom の名前の形も見ない。shared 経路の `isAux`（DeepElab.lean:3600–3604、`.str (.str (.str _ "_native") "native_decide") ax => ax.startsWith "ax_"`）は写していない。
  - `#ved_strict_audit decl`: 通れば `VED STRICT OK decl: [閉包]`、落ちればエラー。
  - 測定用（受理はしない）: `#ved_axioms_raw decl`（閉包をそのまま出す）、`#ved_audit_generated Ns`（このファイルで `Ns` の下に宣言された theorem ごとに `VED AUDIT <名前> strict=OK|REJECTED axioms=[閉包]` を 1 行。エラーで止まらないので、1 ケースの全定理を記録できる）。
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

### 3.2 1 ケース = 1 行 × 1 設定 = 1 つの小さな Lean ファイル
`u0_gen.py gen --row N --setting S --out DIR` が `DIR/R<NNN>_<S>/` に次を書く。
- `Case.lean`: `import Tools.DeepElab`、`import Tools.VedStrictAudit`、`import <その行のファイルの module>`。`set_option Elab.async false`。inventory の `options` 列（例 `maxHeartbeats=4000000`）。設定の option。新しい名前空間 `VedU0.R<N>` の中で `open <ns>` と `#verify_elab_deep <decl>`、続けて `#ved_audit_generated VedU0.R<N>` と、replay の本体が `m.body` そのものか並べ替えかを調べる `run_cmd`（`VED BODY …`、§3.4）。
- `case.env`: 設定の環境変数。`meta.tsv`: 上のキー列。

`u0_case.sh` がケースを**それぞれ別の `lean` process** で走らせる。前のケースが timeout・OOM・エラーになっても、後のケースはその影響を受けない（巨大な一括ファイルにしない）。ケースごとに次を `run.txt` に書く。
- `rc`（終了コード）、`timeout`（yes/no）、`limit`（メモリ上限に当たったと見られる場合 `mem`）、`wall_s`、`peak_rss_kb`（子 process の `ru_maxrss`）、`time_limit_s`（`U0_TMO`、既定 1800）、`mem_limit_kb`（`U0_MEM_KB`、既定 12 GiB。`RLIMIT_AS` で掛ける）、`sparkle_sha`（`HEAD` と、追跡ファイルの未コミット変更数）。
- `SPARKLE_DEEP_TRACE=<ケース>/stages.log` を常に設定する。DeepElab の STAGE の印は kill されても残るので、timeout がどの段で起きたかが分かる。
- stdout と stderr は `stdout.txt` / `stderr.txt`。すべて `OUT`（Job の `KJOB_REPORT_PATH` の置き場）の下で、ソースツリーには何も書かない（両 script とも、OUT がツリーの中なら止まる）。
- `RLIMIT_AS` が Lean の仮想メモリの予約と合わず、正常なケースまで落とすようなら、Pod の `-m` を上限にして 1 ケース 1 Job にする（その場合も記録する列は同じ）。

### 3.3 設定
| 設定 | 中身 | 数え方 |
|---|---|---|
| `default` | 既定経路（`Cdo`/`CdoM`） | 通常 |
| `shared` | `set_option sparkle.deepShare true`（`CdoW`） | 通常 |
| `profile` | 既定 + `SPARKLE_PROFILE=1` + `SPARKLE_DEEP_DEBUG=1`（合成側の profile と STAGE 情報） | 通常（profile は観測を足すだけ） |
| `traceonly-shared` | shared + `SPARKLE_DEEP_TRACE_ONLY=1`（trace 定理だけで止まる） | **trace-only。完全な成功に数えない** |
| `defsonly-default` | 既定 + `SPARKLE_DEEP_NOTHM=1`（定義だけ作って定理を作らない） | **trace-only。完全な成功に数えない** |

- 同期 kernel 登録: ケースのファイル全体に `set_option Elab.async false` を付ける。`#verify_elab_deep` 自身も中で `Elab.async false` にして各定理を elabCommand している（DeepElab.lean:1742、1773–1776）。こうすると、kernel が拒否した定理は環境に**無い**ので、`#ved_audit_generated` の一覧に出ない。U1 の入口では、生成した宣言を `addDecl`（同期）で登録し、その直後に `getConstInfo` で存在を確かめる。
- 327 行には `default` と `shared` の 2 つを走らせる。`profile` と trace-only の 2 つは smoke の代表だけ（trace-only はどの段で止まるかの診断用）。

### 3.4 axiom と「strict に数える」の規則
- 各ケースが出した theorem すべてについて、`#ved_audit_generated` が strict の判定と raw の閉包を 1 行ずつ出す（`VED AUDIT …`）。`#verify_elab_deep` 自身の PROVEN 文（"axioms clean" など）は判定に使わない。
- `VED BODY _deep_body|_sdeep_body real|reordered|absent`: 生成された本体の定数の値（`toExpr (deepOrderBody m.body)`）が、同じ `synthesizeHierarchical` の `toExpr m.body` と Expr として等しいかどうか。等しくなければ「並べ替えた本体だけ」。この比較は列の分類に使うだけで、kernel の証明の代わりではない（裁定 7）。
- 列 `strict_counted = yes` になるのは、次の全部を満たすときだけ。
  1. `rc = 0`、timeout でない、trace-only の設定・文がない、`#verify_elab_deep` のエラーがない。
  2. source の deep 定理（`{base}…_deep_trace` か `{base}_sdeep_trace`）と、**`m.body` そのもの**についての replay 定理（`…_signal_run`、`VED BODY … real`）が、同期登録されて環境にあり theorem である。
  3. そのケースで出た theorem すべてが strict 監査を通る（閉包 ⊆ 標準 3 公理）。
  4. replay や橋の SKIPPED が無い。
- 今の DeepElab では、replay は `deepOrderBody m.body` について（調査書 B5）で、G1 などに `native_decide` がある（§5）ので、**`strict_counted` はほぼすべて no になる見込み**。それが U0 で測る事実で、U1 で直す対象である。U0 の数を良く見せるために規則を緩めない。
- 型・前提の確認: U0 では「定理が存在し、その名前の役割（trace / signal_run / Opt / SV）が分かる」ところまでしか見ない。定理の文が契約どおりか（どの Module のどの field に結び付くか）は U1 の Check で確かめる（§4）。

### 3.5 順序: smoke → 327 行
1. **smoke（既存の deep のテスト）**: 次の 5 ファイルを、(a) そのまま 1 回（9 月の数との比較用。`--smoke-file`）と、(b) `#verify_elab_deep` 1 つごとに分けた版（`--smoke-split`。ほかのコマンドは comment にし、残した 1 つを名前空間 `VedU0Smoke` の中で走らせ `#ved_audit_generated` を付ける）で走らせる。
   - `Tests/Verification/DeepElabReifyDemo.lean`（行頭の `#verify_elab_deep` 20 コマンド）
   - `Tests/Verification/DeepElabRealIP.lean`（6 コマンド）
   - `Tests/Verification/ValueParamInitRepro.lean`（5 コマンド）
   - `Tests/Verification/ConeSharingGen.lean`（2 コマンド、shared）
   - `Tests/Verification/ConeSharingCrc16.lean`（1 コマンド、shared。9 月は 93 秒 / 1.98 GB）
   - （行頭の `#verify_elab_deep` だけを分割の対象にする。comment の中の行は数えない。`DeepElabDemo.lean` と `ConeSharingProto/Replay/Premises`、`ConeKernelSlot*` は手書きの試作で `#verify_elab_deep` を呼ばない。build が通るかだけを記録する。）
   9 月の期待数（Demo 21 以上、RealIP 17 以上、VPI 5、ConeSharing 3）は要求しない（裁定 12）。同じ SHA での今回の実測を基準にし、9 月との差を分類する。
2. **smoke（必要IPの群ごとの代表）**: 次の行を 5 つの設定すべてで走らせる。
   | 群（近似） | row | 宣言 |
   |---|---|---|
   | S | 6 | `Sparkle.IP.Arbiter.RoundRobin.arbiterSignal` |
   | S（RealIP と重なる wrapper） | 212 / 244 | `SynthesisChecks.crc32EngineTop` / `synth_uartTx` |
   | S（複数出力） | 63 | `pairCounterCdo` |
   | C | 3 | `adder16` |
   | H | 9 | `Sparkle.IP.Crypto.AESHW.synth_aesSbox` |
   | M | 71 | `Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory` |
   | D | 1 | `Examples.CDC.MultiClockSim.domainACounter` |
   | P | 260 | `symbolicXor` |
3. **327 行すべて**を `default` と `shared` で（654 ケース、直列、再開可能）。
4. U0 全件の終了を待つことは、U1 の小さな試作の着手条件にしない（裁定 2）。smoke の結果が出た時点で U1 の試作を始めてよい。

### 3.6 結果の表（1 inventory 行 × 1 設定 = 1 TSV 行）
`u0_gen.py header` が出す列（順に）:

| 列 | 意味 |
|---|---|
| `inv_commit` `inv_blob` `row` `file` `line` `command` `ns` `top` `decl` `params` `options` `args` `setting` | キー（§3.1） |
| `sparkle_sha` | 測った worktree の HEAD（+ 未コミット変更数） |
| `sv_group_approx` | SV からの近似の群（S/C/H/M/D/P）。raw IR の値と混ぜない |
| `rc` `timeout` `oom_or_limit` `wall_s` `peak_rss_kb` `time_limit_s` `mem_limit_kb` | 実行 |
| `source_deep_theorem` | SOURCE/deep の定理（trace）だけでもあるか |
| `real_body_replay` | `m.body` そのものの replay があるか |
| `reordered_body_replay` | 並べ替えた本体の replay だけか |
| `opt_bridged` | `_sdeep_signal_runOpt`（`optimizeModule` についてで、`checkedOptimize` ではない）があるか |
| `sv_bridged` | `_sdeep_signal_svOpt` / `_sdeep_text_parses` があるか |
| `skipped` | replay や橋の SKIPPED の文（複数は `;`） |
| `nonstd_axioms` | strict 監査で落ちた theorem があるか |
| `trace_only` | 診断の設定・文か |
| `refusal` | 最初のエラー文（拒否理由）。名前が解決できないものは `unresolved-name:` を前に付ける（harness 側の問題で、deep の拒否と区別する） |
| `strict_counted` | §3.4 の規則 |
| `n_theorems` `n_strict_ok` `n_rejected` `raw_axioms` | 監査の数と、閉包の和集合 |
| `deep_run_record` | `measured` / `none`（none は未確認で、失敗ではない） |
| `stdout_ref` `stderr_ref` `audit_ref` | 出力ファイルの場所 |

分類の列は 1 つにまとめない（「PROVEN」1 列にしない）。`n_theorems` には生成器が作る補助の theorem（`_proof_1_1` など）も入る。

### 3.7 script（書いたが、まだ走らせていない）
- `scripts/ved/u0_gen.py`: `rows` / `gen` / `smoke-split` / `classify` / `header`。inventory は §3.1 の固定値で `git show` から読む。手元で確かめたのは文法の検査と、`rows`（327 行）、`gen` と `smoke-split` が scratch に書いたファイルの見た目だけ（Lean は動かしていない）。
- `scripts/ved/u0_case.sh`: `OUT ROW SETTING` / `OUT --list ROWS.txt` / `OUT --smoke-file FILE` / `OUT --smoke-split FILE`。既に `run.txt` のあるケースは飛ばす（`REDO=1` でやり直す）。各ケースは `kjob lake env lean <Case.lean>`（`U0_LEAN` で変えられる）。
- 後で走らせるときの呼び方（今は走らせない。`<ISSUE>` は復旧後に登録する U0 の Issue）:

```sh
cd /home/junji-hashimoto/git/.kjob/src-ved-plan      # 測る SHA の worktree（Job はこの時点の copy を使う）

# smoke: 既存 deep テスト 5 本と群の代表 10 行
kjob -N sparkle-dev run --issue <ISSUE> -n mkvs-dell -c 8 -m 24Gi --name ved-u0-smoke -d -- bash -c '
  set -u
  OUT=$(dirname "$KJOB_REPORT_PATH")/ved_u0
  kjob lake build Tools.DeepElab Tools.VedStrictAudit IP.Net.CRC32 IP.Net.UART IP.Crypto.EcdsaSignSmall IP.Bus.DroneCANHW IP.Bus.SBUSHW IP.Bus.SPIHW \
    IP.Arbiter.RoundRobin Tests.IP.Net.CRC32Test Tests.IP.Net.UARTTest Tests.CircuitDoTest Examples.HierarchicalCPU IP.Crypto.AESHW \
    Tests.Compiler.ShippingMachineFuseTest Examples.CDC.MultiClockSim Tests.SymbolicParameterEmit
  for f in DeepElabReifyDemo DeepElabRealIP ValueParamInitRepro ConeSharingGen ConeSharingCrc16; do
    scripts/ved/u0_case.sh "$OUT" --smoke-file  Tests/Verification/$f.lean
    scripts/ved/u0_case.sh "$OUT" --smoke-split Tests/Verification/$f.lean
  done
  mkdir -p "$OUT"
  for r in 6 212 244 63 3 9 71 1 260; do
    for s in default shared profile traceonly-shared defsonly-default; do echo "$r $s"; done
  done > "$OUT/rows_smoke.txt"
  scripts/ved/u0_case.sh "$OUT" --list "$OUT/rows_smoke.txt"'

# 327 行（smoke の後）。import する module は inventory の file 列から作る
kjob -N sparkle-dev run --issue <ISSUE> -n mkvs-dell -c 8 -m 24Gi --name ved-u0-all -d -- bash -c '
  set -u
  OUT=$(dirname "$KJOB_REPORT_PATH")/ved_u0
  mkdir -p "$OUT"
  python3 -I scripts/ved/u0_gen.py rows > "$OUT/rows_all.raw"
  kjob lake build Tools.DeepElab Tools.VedStrictAudit $(cut -f2 "$OUT/rows_all.raw" | sort -u | sed "s/\.lean$//; s#/#.#g")
  awk -F"\t" "{print \$1\" default\"; print \$1\" shared\"}" "$OUT/rows_all.raw" > "$OUT/rows_all.txt"
  scripts/ved/u0_case.sh "$OUT" --list "$OUT/rows_all.txt"'
```
- 327 行の Job は長くなる（1 ケースの上限 1800 秒）。`--list` は再開できるので、`rows_all.txt` を分けて複数の Job にしてもよい。その場合も各 Job が同じ SHA の worktree から出ていることを `env.txt` で確かめる。
- `IP/Crypto/*` の file は、`IP.Crypto` の lean_lib に root file が無い（BASELINE.md の手順 2 の注意）。module 単位の `kjob lake build IP.Crypto.AESHW` が通らなければ、その行は harness の問題として `refusal` に記録し、BASELINE.md の手順（file ごとに elaborate）に合わせて直す。

### 3.8 U0 で言えないこと
- U0 は「今の `#verify_elab_deep` が、必要IPの宣言それぞれに何をするか」の測定で、保証ではない。`#verify_elab_deep` は `synthesizeHierarchical`（診断の入口）を自分で呼び直すので、`#synthesizeVerilog` が印字した成果物そのものを検査したことにはならない（調査書 B7）。
- `printModule` などの文字列一致は観測の回帰検査で、内部の Module/Design の構造比較や同じ artifact への接続の代わりにならない（裁定 12）。

---

## 4. U1 の契約（下書き。コンパイルしていない）

### 4.1 入口の形
新しいファイル（compiler のファイルは小さく保つ）に、次の入口を置く。
1. `synthesizeEntry declName` を **1 回だけ**呼び、返った `(m, D)` を持つ。`synthesizeHierarchical` は呼ばない。
2. `m` を `toExpr` で定数 `{f}_u1_mod : Module` として `addDecl`（同期）する。以後の定理はすべてこの定数について述べる。
3. 契約（下の `U1Stmt`）の文を生成し、証明を作って同期登録する。
4. 登録した定理の型が、期待する文と（定数 `{f}_u1_mod` を含めて）Expr として一致すること、`#ved_strict_audit` と同じ `strictAudit` を通ること、`{f}_u1_mod` の値が手元の `m` の `toExpr` と一致することを確かめる。
5. どれか 1 つでも外れたら（replay を省いた、trace-only、証明の失敗、監査の失敗）`throwError` し、`m` を返さない。代わりの経路に落とさない。

返すのは IR の `m` まで。最適化（`checkedOptimize`）と SV は未接続と記録する。「出荷 SV を保証」「327 の印字 artifact を検証済み」とは書かない。IR の契約が通った後の次の接続先は `checkedOptimize`（`refineCheck_transfer` / `optCheck_sound` との合成）。`#synthesizeVerilog` などの通常の入口と、ほかの 327 コマンドの経路は、新しい入口が覆うまで別扱いにする。

### 4.2 契約の文（Lean の下書き）

```lean
namespace Tools.VedU1
open Sparkle.IR.AST Sparkle.IR.Semantics

/-- 入口が固定する値。どれも `synthesizeEntry` の同じ 1 回の結果 `m` と
    宣言 `declName` から取る。 -/
structure Contract where
  declName : Lean.Name
  params   : List (String × Nat)      -- 具体化した値引数（無ければ []）
  modName  : String
  inputs   : List Port
  outputs  : List Port                -- 全出力
  wires    : List Port                -- width 表の元（declWidth m）
  inits    : List (String × Nat)      -- register ごとの初期値（m の register 文から）
  rst      : Option String            -- reset の入力名
  clk      : String

/-- Module の意味に使う全 field が契約と一致する。body は別に「そのもの」を使う。 -/
def ShapeStmt (c : Contract) (m : Module) : Prop :=
  m.name = c.modName ∧ m.inputs = c.inputs ∧ m.outputs = c.outputs ∧
  m.wires = c.wires ∧ m.parameters = [] ∧ m.assertions = [] ∧
  m.isPrimitive = false ∧ regInits m.body = c.inits

/-- width 表: 各 port の宣言幅（`declWidth m`）が型の幅と一致。 -/
def WidthStmt (m : Module) : Prop :=
  ∀ p ∈ m.inputs ++ m.outputs ++ m.wires, Sparkle.IR.RegDedup.declWidth m p.name = p.ty.width

/-- 入力の前提: 幅に収まる、reset は low（契約で固定した条件。ほかの条件は足さない）。 -/
def InputsOk (c : Contract) (m : Module) (ins : Nat → String → Nat) : Prop :=
  (∀ t p, p ∈ m.inputs → ins t p.name < 2 ^ Sparkle.IR.RegDedup.declWidth m p.name) ∧
  (∀ t r, c.rst = some r → ins t r = 0)

/-- 元の Signal への橋: `src` は宣言ごとに生成する、宣言 `declName` を
    `params` と入力列に適用した Signal の出力 `o` の時刻 `t` の値。 -/
def OutputsStmt (c : Contract) (m : Module)
    (src : (Nat → String → Nat) → String → Nat → Nat) : Prop :=
  ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
    runModule (Sparkle.IR.RegDedup.declWidth m) m.body   -- m.body そのもの
      (seedIn m ins) K (initState c.inits) (fun _ _ => 0) = some envs ∧
    ∀ t < K, ∀ o ∈ m.outputs, ∃ env, envs[t]? = some env ∧ env o.name = src ins o.name t

/-- U1 の入口が返す前に、定数 `{f}_u1_mod` について登録しておく定理の文。 -/
def U1Stmt (c : Contract) (m : Module) (src : _) : Prop :=
  ShapeStmt c m ∧ WidthStmt m ∧ OutputsStmt c m src

end Tools.VedU1
```

- `regInits`、`initState`、`HWType.width` は下書きの名前で、実装時に既存の定義（`theRegisters`、`seedIn`（Tools/ShippingSeqOptSoundness.lean:892）、`declWidth`（Sparkle/IR/RegDedup.lean:172））に合わせる。
- `m.body` そのものを replay する。順序を変えて証明するなら、この具体的な body について「並べ替えた body の run = 元の body の run」を前提つきで証明し、結論は元の `m.body` に戻す。任意の文の並べ替えが意味を保つとは仮定しない（裁定 5）。今の `{f}_deep_signal_run` は `deepOrderBody m.body` についてなので、そのままでは `OutputsStmt` にならない。
- 結論は `m` の全 field（名前、inputs/outputs、wires による幅、初期値、reset、body）に結び付く。body が同じでも別の Module（初期値や幅の違うもの）の証明は流用できない（裁定 4）。
- 証明の閉包は標準 3 公理まで（`strictAudit`）。G1 などの `native_decide` は §5 の置き換えが済むまで U1 の入口を通らない。

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

## 6. cluster が無いとできなかったこと
- U0 の測定そのもの（smoke も 327 行も）。`Tools.DeepElab` とそれを import するものの build も、この作業では行っていない。§3.4 の `VED BODY` の `run_cmd` と `Case.lean` の生成文は、Lean で一度もコンパイルしていない（DeepElab を import するため）。最初の smoke で通ることを確かめる。
- G1 の実物の置き換えと時間（§5.3）。今あるのは模型の時間だけ。
- `RLIMIT_AS` によるケースごとのメモリ上限が Lean と合うかの確認（§3.2）。
- Issue の登録（manager の停止中）。復旧後に、U0 と U1 の完了条件とこの裁定を登録する。

## 7. このコミットまでの成果物
- `Tools/VedStrictAudit.lean`、`Tests/Ved/StrictAuditCheck.lean`、lakefile の 2 つの `lean_lib`（8b3c39a7）。
- `scripts/ved/u0_gen.py`、`scripts/ved/u0_case.sh`、この文書（次のコミット）。
