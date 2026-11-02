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

## 6. 燃料切れの経路（変更依頼 rt81）

### 6.1 userInliner / entryConst の呼び出し箇所（grep、Sparkle/ と Tools/ の本体。Tests の呼び出しは下に別記）

| file:line | 呼ぶもの | トップ / 子 | 燃料切れ（rt81 後） |
|---|---|---|---|
| Sparkle/Compiler/Elab.lean:5639（`synthesizeCombinationalCoreWith` の `doSynth`） | `entryConst … (userInliner env)` | **両方**: トップも、`synthesizeChild`（8981 付近）→ `synthesizeCombinational` → この関数の経由で子も | ここでは fallback のまま（`userInliner` は純関数で、`doSynth` と `synthesizeChild` は Tools の多数の定理が `unfold` する定義なので編集しない）。エラーは下のコマンド入口の guard が、ここへ来る前に出す |
| Sparkle/Compiler/Elab.lean:5340 付近 `entryInlinerErrorWith?` / `userInlinerErrorWith?` | `userInlinerEWith` の `.error` を `Option String` で返す | guard から、宣言ごとに | エラー（理由つき） |
| Tools/Prototype/DGenProv.lean, DGenConnect.lean | `entryConst … (userInliner env)`（証明の中の記述） | 証明用。実行経路ではない | 変更なし |
| Tests/**（`entryConst … (userInliner env)`）約 60 ファイル | 純関数として直接呼ぶテスト | 実行経路ではない | 変更なし（fallback のまま。入力は燃料切れしない） |

`userInlinerE` を呼ぶのは `userInliner` と `userInlinerErrorWith?` だけ（Sparkle/Compiler/Elab.lean）。

### 6.2 コマンド入口（`synthesizeCombinational` / `synthesizeHierarchical` / `…WithParameters` を呼ぶ箇所）

| file:line | 入口 | guard（rt81 後） |
|---|---|---|
| Elab.lean `#synthesize` / `#synthesizeVerilog` / `#showVerilog` / `#synthesizeDesign` / `#synthesizeVerilogDesign` / `#writeVerilogDesign` / `#writeCppSimDesign` / `#writeCudaDesign` / `#writeCudaIntraDesign` / `writeDesignCore`（`#writeDesign`）/ `#sim` | `inlinerFuelGuard`（トップと子） | あり（もとからあった呼び出しが、子も見るようになった） |
| Elab.lean `#synthesizeParameterizedVerilog`、`#writeParameterizedCppSimDesign`、`#writeParameterizedCudaDesign` | `synthesizeCombinationalWithParameters` / `synthesizeHierarchicalWithParameters` | **新規**: `inlinerFuelGuardParams`（トップは symbolic で展開しないので見ない。子は symbolic でなく合成されるので見る） |
| Sparkle/Verification/CostCmd.lean:59,88、Sparkle/Verification/CoSim.lean:90、Sparkle/Compiler/SimChecked.lean:77、Sparkle/Display/Synthesise.lean:68,83 | `synthesizeCombinational` / `synthesizeHierarchical` を直接呼ぶ | **なし**。この Issue の編集許可（Elab.lean の呼び出し側と MachRecUnfold.lean）の外なので触っていない。ここでは燃料切れは黙って fallback する。→ coder へ: 許可を広げて `inlinerFuelGuard` を足すか、判断の差としてユーザーに戻すか |

### 6.3 実装と根拠

- 実装: `inlinerFuelGuardWith fuel symbolicMode declName`。宣言自身（symbolic でないとき）と、`hardwareChildren`（宣言の値と型から、user モジュールまたは hardware_module の定義を辿って届く `@[hardware_module]` の定数。最大 100000 定数を訪問）の各々に `entryInlinerErrorWith?` を当てる。子は `synthesizeChild` が `synthesizeCombinationalCoreWith … [] false` で合成するので、見ている条件（`certifiedFrontEnd true`、`symbolicMode false`、パラメータ無し）は子の `entryConst` の条件と同じ。
- `userInliner`（純関数）の fallback は残す。役割: Tools と Tests の純関数の呼び出し、および 6.2 の最後の行の入口。`inlinerFuelGuard` は要らなくならないので整理せず、役割をコメントに書いた。
- 燃料を渡せる版: `MachRecUnfold.passWith`、`userInlinerEWith`、`userInlinerErrorWith?`、`entryInlinerErrorWith?`、`inlinerFuelGuardWith`。本番はそれぞれ `passLimit` を渡す（`pass` / `userInlinerE` / `userInlinerError?` / `entryInlinerError?` / `inlinerFuelGuard`）。`userInliner` の本体は変えていない。燃料切れしない入力の挙動は同じ。
- 子の探索は値と型の定数の走査であって、展開後の値ではない。展開の途中で初めて現れる子（展開で出る hardware_module の呼び出し）は、展開前の定義に定数として現れる前提。この調査では、展開で初めて出る子の経路は見つからなかったが、網羅の証明ではない。
- 負例テスト: `Tests/Compiler/MachRecUnfoldFuelTest.lean`（`MachRecUnfoldFuelTest` 名前空間）。`chainN 4 a` を値に持つ `@[hardware_module] kid` を `parent` が呼ぶ。燃料 1 で、`parent` のコマンド guard が子 `kid` の名前と `fuel exhausted` を含むエラーになること、パラメータ版も同じこと、トップ `topChain` も同じこと、燃料 100 と本番の上限では通ること、`synthesizeHierarchical parent` の design に `kid` のモジュールがあること（子が実際に合成される経路であること）を確かめる。本番と同じ関数 `inlinerFuelGuardWith` を燃料だけ小さくして通す。エラー文の上限の数は本番の定数（10000）のまま出る。
- ビルド: `kjob lake build Tests.Compiler.MachRecUnfoldFuelTest` ok、`Tools.ShippingInlineSoundness` / `Tools.ShippingInlCand` / `Tools.ShippingEntrySoundness`（とその依存）ok。clean build、AllTests、corpus の再確認は coder。
