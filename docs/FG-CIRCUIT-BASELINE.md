# FG S0: 既存IPの一覧と baseline

Issue `sparkle-fg-circuit-baseline`（S0、親 `sparkle-fg-circuit-strategy`）。土台 SHA: `ff3d31c6`（par/fgc）。toolchain `leanprover/lean4:v4.32.1`（`lean-toolchain`）。
戦略: `docs/FG-CIRCUIT-STRATEGY-2026-11-06.md` §3（利用者の契約）、§7 S0。

## 状態（正直に）

| 項目 | 状態 |
|---|---|
| 静的な一覧（top・パラメータ・オプション・ファイル・SHA） | **完了**: `scripts/gen5/fgc_baseline/inventory.tsv`, `files.tsv`（`extract_inventory.py` が生成、下の再実行手順） |
| 動的な baseline（成功／失敗、IR→SV hash、ポート／clock／reset／memory、route） | **未取得**: この worktree は未 build（`.lake` なし）。取得スクリプトは用意済み。重い実行は `kjob run` で投げる（下「実行手順」） |
| 既存 simulation／vector 検査の結果 | **未取得**: `sim_checks.sh` を用意。同上 |
| 除外 | 事前に説明できるもの 1 件のみ（`exclusions.tsv`）。他は動的取得後、FAIL 行ごとに原因と修正先を付ける。付かないものがある間は baseline を固定しない（`summary.txt` の `unexplained failures` が 0 になること） |

動的な値は、取得前に推測で書かない。このファイルの数は静的に数えたものだけである。

## 母集団の区別（同一視しない）

| 母集団 | 件数 | 出所 | このリストとの関係 |
|---|---|---|---|
| (P1) **IP一覧（本書）**: `Tests` `IP` `Examples` の `*.lean` にある `#synthesizeVerilog` `#synthesizeParameterizedVerilog` `#synthesizeVerilogDesign` `#writeDesign` `#writeVerilogDesign` の行頭コマンド | **327 コマンド**／136 ファイル／異なる (file, top) 327、名前空間修飾後の top 322 | `extract_inventory.py`（`scripts/shipping-coverage/run.sh` の grep 対象 + `#synthesizeParameterizedVerilog`・`#synthesizeDesign` のみのファイル） | これが「必要IP」の候補。下の層に分ける |
| (P1a) 層 A: 出荷 IP（`IP/**` `Examples/**` `Tests/IP/**`） | 225 コマンド／117 ファイル | 同上 | 必要IPの中心 |
| (P1b) 層 B: コンパイラ機能・回帰テスト（その他の `Tests/**`） | 102 コマンド／19 ファイル | 同上 | 既存挙動の回帰として必要IPに含める |
| (P1c) うち `lake build Tests.AllTests` の import 閉包内 | 218 コマンド（A 193 / B 25） | `Tests/AllTests.lean` の import 推移閉包（1542 module） | 閉包外は `lake build IP.*` 等の別ライブラリ／exe で build する |
| (P2) API 呼び出しのみのファイル（`synthesizeCombinational` / `synthesizeHierarchical` を Lean から直接呼ぶ） | 372 ファイル／呼び出し 1875 | `files.tsv` の `api_calls`。大半が `Tests/Compiler/Shipping*`（309 ファイル）の認証テスト | **IP一覧に入れない**。top を持たない。戦略の「235 root」はこの周辺の測定で、リポジトリにその一覧は無い |
| (P3) 「235 root」 | 235 | D.D-4 `e37da005` の測定（戦略 §2）。リポジトリ内に root 一覧なし | 測定の対象は Signal+BitVec の root。P1 の部分集合と仮定しない。S1 で 3 root を選ぶ際に P1 との対応を取る |
| (P4) 「以前の1369成功コンパイル」 | 1369 | 以前の測定（コマンド回数。同じ宣言が複数ファイルで数えられる）。一覧はリポジトリ内に無い | P1（327）と数が違う。同一視しない |

注意:
- P1 は静的な数。`#synthesizeVerilog` は同じ top が複数ファイルにあれば別行で数える。ネストした `namespace` から修飾名を推定したが、`open` による解決は見ていない（`qualified` は参考値）。
- コメント内（`/- -/`）のコマンドは数えない。`--` で始まる行も数えない。
- オプション欄: `set_option … in` が直前にあれば記録（現状 `maxHeartbeats=4000000` が 1 件）。`#synthesizeParameterizedVerilog` は `symbolicMode=true` と書き、パラメータ（`W := 8` など）が 4 件。`route` は選択ではなく実行時にコンパイラが決める値なので、動的取得で記録する（`certified` / `mixed` / `machine` / `legacy` / `memo`、`/tmp/sparkle-profile.log` の `[profile] synthesizeCombinational` 行）。

## 必要IPの定義

必要IP = P1 の全コマンドから、`exclusions.tsv` の行を引いたもの。除外は「原因」と「修正先」が付いたものだけ。未説明の除外はしない。

事前に説明できる除外（1 件）:

| 対象 | 原因 | 修正先 |
|---|---|---|
| `Tests/Compiler/MultiOutputSubModuleHangRepro.lean` の `reproKvHw2Reg` | ファイル冒頭に記載された elaborator の hang（`circuit do` が 2 個以上の register を持ち、大きい `@[hardware_module]` を呼ぶ）。バグ再現で、出荷 IP ではない。同ファイルの `baselineNoSubmodule` `baselineKvHw1Reg` は除外しない | `Sparkle/Compiler/Elab.lean` のサブモジュール走査（別 Issue）。timeout は KNOWN-HANG と記録し、成功として数えない |

動的取得の後、FAIL になった行は次のどれかに分類する: (a) 環境（未 build の lib、メモリ不足の timeout → 再実行）、(b) 既知の既存不具合（原因と Issue を `exclusions.tsv` に追記）、(c) 新経路の問題（baseline に成功として固定すべきもの。除外しない）。

## 実行手順（再実行可能）

すべて repo ルートで実行する。生の出力は `$OUT`（= `KJOB_REPORT_PATH` の置き場）に出す。ソースツリーには置かない。

```sh
OUT=$(dirname "$KJOB_REPORT_PATH")/fgc_baseline_raw     # 例
S=scripts/gen5/fgc_baseline

# 1. 静的な一覧（軽い。結果は commit 済み）
python3 $S/extract_inventory.py . $S            # inventory.tsv / files.tsv を再生成
mkdir -p $OUT && cp $S/inventory.tsv $OUT/

# 2. build（重い。kjob run に投げる）
kjob lake build Tests.AllTests
kjob lake build IP.RV32 IP.YOLOv8 IP.Video IP.Bus IP.Arbiter IP.Crypto Examples.CDC   # 閉包外の IP/Examples

# 3. 生成物の取得（重い。kjob run。ファイル毎 timeout 900、直列、再開可能）
timeout 900 $S/capture.sh $OUT                  # CAP_TMO=秒, REDO=1 で再実行
# 4. 表にまとめる（軽い）
python3 $S/summarize.py $OUT                    # baseline_{files,modules,commands}.tsv, summary.txt

# 5. 既存の simulation / vector 検査（重い。EXES.txt を分割して複数 job に）
SKIP_BUILD=1 $S/sim_checks.sh $OUT [EXES.txt]
```

`capture.sh` 全体は長いので 1 job にしない。`$OUT/files_run.txt` を分割して `capture.sh $OUT part.txt` を複数の `kjob run` に投げる（`$OUT` は共有の置き場、各ファイルの状態は `status/` に別ファイルで残る）。`lake env lean` は必ず `timeout 900` で包む（スクリプト内で実施）。

### summarize が出す列

- `baseline_commands.tsv`: file, line, command, top, params, options, **result**（OK / OK-nostdout / FAIL / KNOWN-FAIL / UNATTRIBUTED / NOT-RUN）, **route**, module, **sha256**（生成 SV の module 文字列。IR→SV の現行 printer の出力）, method（name / order：コマンドとモジュールの対応づけ方）, file_exit, area, in_alltests, tier, excluded, fix_target
- `baseline_modules.tsv`: module 毎に **外部ポート**（`方向:名前:幅[:s]`）、**パラメータ**、**clock**、**reset**（名前、sync/async、極性。printer は `if (rst)` のみで active-high 固定）、**register の初期値**（reset アームの値）、`$signed` の数、**memory**（`名前:w幅xd深さ:comb-read|sync-read:wports数`）、インスタンス数。
- `UNATTRIBUTED`: exit 0 だがモジュールが対応づかないコマンド（`#writeDesign` は stdout に SV を出さないので `OK-nostdout`、出力ファイルの hash は別途 `$OUT` で取る）。0 になるまで直す。

### 取得できる範囲と、取得できないもの

- ポート・幅・clock・reset 極性と初期値・memory の read 種別と write ポート数は、生成 SV から静的に取る。
- **符号**: 現行 printer は port を符号なしの `logic [..]` で出す。符号は `$signed` の使用数でしか見えない。符号の意味は simulation/vector 検査（5）に頼る。
- **レイテンシ**: SV からは register 数しか取れない。レイテンシの baseline は既存の vector／sim 検査（`sim_checks.sh`）の通過で固定し、IP 毎の値は新経路との比較時に同じ検査を流して取る。
- 有限テストは全入力証明の代替にならない（戦略 §3-3）。baseline は「新経路と比べる基準」で、保証ではない。
- 保証の出力境界は現行 `runModuleTG` / IR から。SV printer 以降は含まない（戦略 §3-5）。IP の SV 生成と実行回帰は別の受入条件として、この表の hash と sim 結果で維持する。

## 再現に必要な固定値

`env.txt`（`capture.sh` が書く）に SHA・toolchain・日付を残す。比較は同じ SHA で取り直した 2 つの `baseline_commands.tsv` を `file,line,top` で結合して `result` `route` `sha256` の差を見る。hash が変わる場合は、戦略 §3-3 のとおり差分理由と意味の同値、既存の sim/vector 検査の通過を示す。

## 動的な baseline の結果（2026-11-06、coder）

取得: kjob-run-src-fgc-s0run-0474（土台 46874da9 = a618db86 の上の capture.sh の修正 3 件）。生の出力は `/home/junji-hashimoto/git/.kjob-state/namespaces/sparkle-dev/kjob-run-src-fgc-s0run-0474/fgc_baseline_raw`（ソースツリーの外）。ここには集計の数だけを書く。

| 項目 | 結果 |
|---|---|
| 取得したファイル | 136 / 136（exit 0 は 135） |
| コマンド（必要 IP の候補、P1） | **327 / 327 が成功**（OK 309、OK-nostdout 18。後者は stdout に出さず、ファイルに書く命令） |
| AllTests の閉包の中 | 218（OK 210、OK-nostdout 8） |
| 層 A 出荷 IP | 225 / 225 成功（OK 210、OK-nostdout 15） |
| 層 B 機能・回帰 | 102 / 102 成功（OK 99、OK-nostdout 3） |
| route（OK のコマンド） | machine 252、mixed 32、certified 18、legacy 7 |
| 生成 module | 309 |
| unexplained failures | **0** |

見つかったこと:
- `Tests/VerifyVerilog.lean` は exit 1。原因は 44 行目の `Unknown identifier 'current'` で、合成コマンドではない部分のエラー。この file の合成コマンド 5 件はすべて成功している。必要 IP の失敗ではなく、file そのものの既存の不具合（修正先: Tests/VerifyVerilog.lean の 44 行目）。
- 事前に除外した `Tests/Compiler/MultiOutputSubModuleHangRepro.lean` の `reproKvHw2Reg`（記録された elaborator の hang）は、この土台では **OK（machine route）** だった。exclusions.tsv の除外は古いので、「この土台では hang しない」と注記し、必要 IP の対象に戻す。
- 1 回目の取得の失敗（lakefile の `lean_lib «IP.Crypto»` の root `IP/Crypto.lean` がどの commit にも存在しない）は既存の lakefile の欠陥。IP/Crypto/* の合成コマンドは file ごとの実行ですべて成功した。修正先: lakefile の `IP.Crypto` の root。

したがって必要 IP = P1 の 327 コマンドで、除外は 0。成功 327 / 327。シミュレーションと vector の検査（手順 5）はまだで、別の job で取得する。

## シミュレーションの検査

取得: kjob-run-src-fgc-s0run-babb（147 件: AllTests の build 1、exe 144、`lake exe test`、verify_parameterized_csim）。**136 件が exit 0、11 件が exit 0 ではない**。生の log は `.kjob-state` の下（ソースツリーの外）。再実行は `scripts/gen5/fgc_baseline/sim_rerun.sh GROUP OUT`（GROUP = env / h264 / test / toplevel）。

| # | 検査 | 分類 | 根拠（log の行） | 状態 |
|---|---|---|---|---|
| 1 | rv32-flow-test | (a) 環境 | `[skip] Verilator not found`、`rv32-lean-sim-runner not built`。失敗した `generated_soc.sv exists` 等は `verilator/generated_soc.sv`（`IP.RV32.SoCVerilog` の `#writeDesign` の出力）が未生成のため | `lake build IP.RV32.SoCVerilog` で再実行（env）。Verilator の軸は、Verilator のあるノードがあればそこで再実行 |
| 2 | cdc-multi-clock-test | (a) 環境 | `failed to load cdc_runner shared library. Build it with: make -C c_src/cdc cdc_runner.so` | `make -C c_src/cdc cdc_runner.so` の後に再実行（env） |
| 3 | sim-runner-test | (a) 環境 | 同上（A1 A2 は PASS、cdc の段で停止） | 同上 |
| 4 | bitnet-soc-test | (a) 環境（前提 build の順序） | 失敗した軸は Axis 2 のみ: `verilator/generated_soc.sv missing — run lake build IP.RV32.SoCVerilog first`。Axis 1 functional と Axis 3 firmware は ✅ | `lake build IP.RV32.SoCVerilog` の後に再実行（env） |
| 5 | verify-parameterized-csim | (a) 環境 | `could not execute external process 'lean'`（入れ子の `lake env lean`） | `scripts/verify_parameterized_csim.sh` を修正: `LEAN` と `LEAN_PATH` があれば直接使う（env） |
| 6 | toplevel-sim-test | (b) 既存の不具合（性能） | exe の build 後、900 秒出力なし（timeout 124）。lakefile.lean の `toplevel-sim-jit-test` の注: pure-Lean の Signal 評価は O(t²) で CI でも timeout する | 長い timeout では直らない。同じ刺激を JIT で流す `toplevel-sim-jit-test` を baseline の行にする。exclusions.tsv に記録。`sim_rerun.sh toplevel` で JIT 版の通過を確認 |
| 7 | exe-test（2 回目、exit 124） | (a) 環境（timeout） | 900 秒で停止（log は 29 万行、AllTests の build と実行の途中） | 1 回目と同じ名前の log を上書きしていた。`sim_rerun.sh test` で別名の log に取り直し、timeout が足りるか判断 |
| 8 | exe-test（1 回目、exit 1、65 秒） | 未確定 | 同名の log を 2 回目が上書きし、原因の行が残っていない | `sim_rerun.sh test` で再取得して分類する |
| 9-11 | h264-bitstream-test / h264-playable-test / h264-frame-encoder-test | (b) 候補（再実行で確認） | `uncaught exception: JIT: wire '_gen_done' not found`（frame-encoder は `_gen_cavlcBitBuffer`）。ただし log では `Written JIT wrapper to .lake/build/gen/h264/*_jit.c` が同じ run の中で出ており、古い gen ではない。`EncoderSynth` `CAVLCSynth` `FrameEncoderSynth` は `#writeDesign … observableWires` で当該 wire を宣言している | `sim_rerun.sh h264`（gen を消して再生成、生成した `_jit.c` の wire 名を記録、3 本を再実行）。それでも失敗なら (b): 修正先は `Sparkle/Backend/CSim.lean` の `toCJITUnchecked`（`_gen_*` の member 化）と `Sparkle/IR/Optimize.lean` の observable の扱い |

件数: (a) 環境 6（1-5 と 7）、(b) 既存の不具合 1 確定（6）+ 3 候補（9-11）、未確定 1（8）。合計 11。**未説明のものは 8 と 9-11 の再実行結果待ち**で、それまで baseline の sim 側は固定しない。(c)（新経路の問題）は 0。

## シミュレーションの検査の確定（2026-11-06、coder）

最初の実行（kjob-run-src-fgc-s0run-babb、147 件）では 136 件が exit 0、11 件がそうでなかった。分類（fbaf7427）のあと、取得の手順を直して再実行した（sim_rerun.sh、生の log はソースツリーの外）。

| 件 | 確定した結果 | 根拠の Job |
|---|---|---|
| cdc-multi-clock-test、sim-runner-test | 成功 | kjob-run-src-fgc-s0r-5120 / 0a87 |
| bitnet-soc-test、rv32-flow-test | 成功（原因は verilator/generated_soc.sv がないことだけで、Verilator がないことではなかった） | kjob-run-src-fgc-s0r-0a87 |
| verify-parameterized-csim | 成功 | kjob-run-src-fgc-s0r-5120 / 0a87 |
| toplevel-sim-test | 置き換え: 純粋な Lean の評価が O(t²) で 900 秒で timeout。同じ 50 cycle の刺激の toplevel-sim-jit-test が ALL PASS（exclusions.tsv） | kjob-run-src-fgc-s0r-38fb |
| test（1 回目の exit 1 と、2 回目の timeout） | 成功（失敗した 15 個の assertion は、すべて RV32 SoC Flow の generated_soc.sv / _cppsim.h がないことだった） | kjob-run-src-fgc-s0r-249c |
| h264-bitstream-test、h264-playable-test | **既存の不具合**: JIT: wire `_gen_done` not found | kjob-run-src-fgc-s0r-bd46 |
| h264-frame-encoder-test | **既存の不具合**: JIT: wire `_gen_cavlcBitBuffer` not found | kjob-run-src-fgc-s0r-bd46 |

h264 の 3 件について:
- 生成した CAVLC の module（`cavlc_synth_jit.c`、wire 100 本）に、`IP/Video/H264/CAVLCSynth.lean:794` が残す指定をした wire がない。
- poc fea429da でも同じく `_gen_done` がない（kjob-run-src-cavlc-poc-bc79）ので、この土台の新しい経路の問題ではない。
- 修正先は、名前を指定した wire を残すコンパイラの処理（keep-wire の一覧と、JIT の wire の出力）。

取得の手順で直したこと（すべて par/fgc-s0）:
- 46874da9: capture.sh は kjob lake env が設定した LEAN / LEAN_PATH を使う（入れ子の lake env は失敗する）。
- 8d15caa9: exe は lake build で作り、binary を直接実行する（入れ子の lake exe は binary を起動できない）。
- d24963dd / 9b58713d / 86e3a86b: verilator/generated_soc.sv は #writeDesign が elaborate 中に書くので、SoC の import を build してから lean で直接 elaborate する（キャッシュからの lake build は olean を再生するだけで書かない）。

まとめ:
- 合成の必要 IP: 327 / 327 が成功、除外 0、未説明 0。
- シミュレーション: 147 件のうち、既存の不具合が 3 件（h264）、JIT 版への置き換えが 1 件（toplevel）、それ以外はすべて成功。
- 未説明: 0。
