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

### 3.1 rt81 の変更と入口 guard の後（27c6d1ea）の再比較

同じ方法で 8a616cbc と 27c6d1ea を比べた（job ptcmp-27c6d1ea、exit 0、build 1954 jobs、39 分。比較の相手は ptcmp-new-8a616cbc の出力）。

| 項目 | 結果 |
|---|---|
| ファイル | 8a616cbc の 478 本はすべてある。新しい 1 本は `Tests/Compiler/MachRecUnfoldFuelTest.lean`（rt81 の負例テスト、exit 0） |
| 各ファイルの終了状態 | 478 本で完全に一致（並べ替えたうえで比較） |
| compare_outputs.py | identical 437、renumbered 0、different 41、missing 0（different の 41 本は 8a616cbc と base の比較のときと同じ集合） |
| different 41 本の中身 | Verilog（`endmodule`）を含むものは 0 本。数字を伏せると 31 本は同じ文で、差は `[profile]` の時間、heartbeats、閉包の定数の数だけ。残る 10 本は、もとから exit 1 のファイル（CorpusCmp の外の olean が無い）。そのエラー文の build ディレクトリの名前だけが違う |
| 燃料切れ | 0 |

→ 入口の guard を足しても、生成物と終了状態は変わらない（燃料切れが起きない corpus では guard は何もしない。測定であって証明ではない）。
exact-head build（ptv4-27c6d1ea）: `kjob lake build Sparkle.Compiler.MachRecUnfold test` exit 0、3150 jobs（AllTests を含む）。

## 4. 燃料切れになる条件（挙動が変わりうる入力）

展開の段数が 10000 を超える入力だけ。今の corpus では 1000 を超えるものは無い。そのような入力は、全域化前の compiler では極端に遅いか止まらない（RT_PASS_TOTAL_SURVEY §2）。全域化後は、理由つきのコンパイルエラーで止まる。

## 5. 残り

- exact-head build と AllTests: ptv2-8a616cbc（8a616cbc）と ptv4-27c6d1ea（27c6d1ea）、どちらも exit 0。
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
| Sparkle/Verification/CostCmd.lean（`#verify_cost` / `#verify_fpga`）、Sparkle/Verification/CoSim.lean（`generateVerilogFile`）、Sparkle/Compiler/SimChecked.lean（`#simChecked`）、Sparkle/Display/Synthesise.lean（`#showDiagram` / `#showDesign`） | `synthesizeCombinational` / `synthesizeHierarchical` を直接呼ぶ | **あり（coder、par/rt-pass-total-entry）**: 合成の直前に `inlinerFuelGuard declName`（トップと子）。ユーザー判断 A（燃料切れはコンパイルエラー）の実装の続きで、新しい判断ではない |
| Examples/MemorySynthesis.lean、Examples/VectorTest.lean | ライブラリ関数 `synthesizeCombinational` を直接呼ぶ例 | なし（コマンドでなく API を直接使う例。Tests の純関数の呼び出しと同じ扱い。入力は燃料切れしない） |

### 6.3 実装と根拠

- 実装: `inlinerFuelGuardWith fuel symbolicMode declName`。宣言自身（symbolic でないとき）と、`hardwareChildren`（宣言の値と型から、user モジュールまたは hardware_module の定義を辿って届く `@[hardware_module]` の定数。最大 100000 定数を訪問）の各々に `entryInlinerErrorWith?` を当てる。子は `synthesizeChild` が `synthesizeCombinationalCoreWith … [] false` で合成するので、見ている条件（`certifiedFrontEnd true`、`symbolicMode false`、パラメータ無し）は子の `entryConst` の条件と同じ。
- `userInliner`（純関数）の fallback は残す。役割: Tools と Tests の純関数の呼び出し、および 6.2 の最後の行の入口。`inlinerFuelGuard` は要らなくならないので整理せず、役割をコメントに書いた。
- 燃料を渡せる版: `MachRecUnfold.passWith`、`userInlinerEWith`、`userInlinerErrorWith?`、`entryInlinerErrorWith?`、`inlinerFuelGuardWith`。本番はそれぞれ `passLimit` を渡す（`pass` / `userInlinerE` / `userInlinerError?` / `entryInlinerError?` / `inlinerFuelGuard`）。`userInliner` の本体は変えていない。燃料切れしない入力の挙動は同じ。
- 子の探索は値と型の定数の走査であって、展開後の値ではない。展開の途中で初めて現れる子（展開で出る hardware_module の呼び出し）は、展開前の定義に定数として現れる前提。この調査では、展開で初めて出る子の経路は見つからなかったが、網羅の証明ではない。
- 負例テスト: `Tests/Compiler/MachRecUnfoldFuelTest.lean`（`MachRecUnfoldFuelTest` 名前空間）。`chainN 4 a` を値に持つ `@[hardware_module] kid` を `parent` が呼ぶ。燃料 1 で、`parent` のコマンド guard が子 `kid` の名前と `fuel exhausted` を含むエラーになること、パラメータ版も同じこと、トップ `topChain` も同じこと、燃料 100 と本番の上限では通ること、`synthesizeHierarchical parent` の design に `kid` のモジュールがあること（子が実際に合成される経路であること）を確かめる。本番と同じ関数 `inlinerFuelGuardWith` を燃料だけ小さくして通す。エラー文の上限の数は本番の定数（10000）のまま出る。
- ビルド: `kjob lake build Tests.Compiler.MachRecUnfoldFuelTest` ok、`Tools.ShippingInlineSoundness` / `Tools.ShippingInlCand` / `Tools.ShippingEntrySoundness`（とその依存）ok。clean build、AllTests、corpus の再確認は coder。

## 7. 全経路の燃料切れ（変更依頼 2 回目、rt83）— 設計調査（下書き）

状態: 調査の途中。実装は未着手。この節は grep と定義の読みによる件数で、ビルドで確かめた結果ではない。

### 7.1 案 A（番兵: `userInliner` の `.error` 枝が合成できない式を返す）

- 調べたこと: `entryConst`（Sparkle/Compiler/Elab.lean:5320）は、`inlinedConst inl ci` が `certifiedShape?` / `mixedCertifiedShape?` / `machineShape?` のどれかを通るときだけ展開後の値を返し、通らなければ **元の `ci` を返す**（`else ci`）。
- したがって、番兵（本体の無い opaque 定数の適用）を `userInliner` が返しても、どのゲートも通らないので `entryConst` が捨てて元の `ci` を返し、合成は燃料切れを黙って無視して続く。この調査の読みでは、案 A は `entryConst` の本体を変えない限り、エラーにならない。`entryConst` の本体の編集は今回の許可範囲（呼び出し側のみ）の外で、また `entryConst` は Tools の多数の定理の文に現れる。
- 定理への影響（grep）: `userInliner` を unfold/simp する定理は 0 件（`Tools/ShippingInlTypeReads.lean:150` は `userInlinerC`）。`userInliner env ty = userInlinerC env ty` の形は仮説（`Tools/ShippingP5Forall.lean:78`、証明されていない）。多くの定理は `userInliner envR` を不透明な引数として持つだけ。つまり影響は小さいが、**効かない**。
- 番兵がゲートを通る形にする案は、この調査では安全な形を見つけていない（opaque 定数の適用は翻訳できない）。

### 7.2 案 B（`doSynth` / `synthesizeChild` の入口で `.error` を throw）

- `doSynth` は `synthesizeCombinationalCoreWith`（Elab.lean:5633）の中。トップも、`synthesizeChild`（8996）→ `synthesizeCombinational` → この関数の経由で子も通る。API 直接呼び出しも通る。展開で初めて現れる子も、確定して合成される時点で必ずここを通る（静的走査に依存しない）。
- 定理への影響（grep、unfold/simp している箇所）:
  - `synthesizeCombinationalCoreWith`: 27 箇所 / 25 ファイル（Tools/ShippingCacheCoherentVia.lean:181、ShippingEntrySoundness.lean:1105、ShippingChildPinC.lean:141、ShippingLeafKeepCache.lean:150,245 ほか）。
  - `synthesizeChild`: 約 25 箇所 / 17 ファイル（ShippingChildCacheA.lean:306,358、ShippingCacheCoherent.lean:250、ShippingLeafKeepCache.lean:402,442 ほか）。
  - `synthesizeCombinationalWith` を unfold: 17 ファイル。
- 新しい throw 枝は、各定理の run の場合分けに「失敗の枝」を 1 つ増やす。多くは「run が ok のとき…」の形なので、文を変えずに枝を閉じられる見込みだが、Triple / Keeps 型の文（`Keeps … (synthesizeChild c)` など）では例外の扱いが文に出るかどうかは、この調査では未確認。

### 7.3 結論（暫定）

- 案 A は効かない（7.1）。案 B は 25 ファイル規模の証明の追従が要り、定理の文を変えずに済むかは未確認。
- 次: 案 B を 1 つの代表ファイルで試して、文を変えずに済むかを確かめる（結果をこの節に追記）。済まなければ実装を止め、`scripts/gen5/RT_PASS_ALLROUTE_DECISION.md` を書いて `decision`。
