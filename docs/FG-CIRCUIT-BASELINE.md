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
