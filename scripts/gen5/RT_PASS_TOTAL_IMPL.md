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

### 7.3 結論と実装（案 B を採用）

- 案 A は効かない（7.1）。案 B を実装した。`doSynth`（`synthesizeCombinationalCoreWith`）が `getConstInfo` と `getEnv` の直後に `entryInlinerError?`（本番の上限）を当て、燃料切れなら `throwError "<宣言名>: <理由>"` する。トップ、子（`synthesizeChild` がこの入口を呼ぶ）、`synthesizeCombinational` / `synthesizeHierarchical` の直接呼び出し、展開の後で初めて確定する子のどれも、合成される時点でこの入口を通る。静的走査（`hardwareChildren`）には依存しない。`inlinerFuelGuard` は残す（コマンドでの早い、分かりやすいエラー。役割はコメントに書いた）。燃料切れのない入力では `entryInlinerError?` が `none` で、挙動は変わらない（`userInliner` / `entryConst` は変更なし）。
- 定理への影響（途中の記録。ビルドは未完）: これまでに追従した証明は 10 ファイル（EntrySoundness / ChildKeeps / ChildRun / ChildVertA / ChildBalance / ChildCoreC / MemoLaws / ChildRunA / MemoLawsWith と、下の書き方）、定理の文は変えていない。**追従の残りは rt86 で完了（定理の文は変えていない）**: 直したファイル（rt86）: Tools/ShippingChildDepthA, ShippingChildDepthC（`body` に `if` を足し `Triple.ite`）、ShippingCacheCoherentVia、ShippingMachineOutcomeA, ShippingMachineOutcomeA3, ShippingMachineOutcomeA4, ShippingSharedLeafNL, ShippingTopShareRun（`RunsTo.ite` で throw 枝を閉じる）、ShippingEntryReadsLinked（`coreRest` の `doSynth` 定義に `if` を足し、`core_chain` で `RunsTo.throwError_false`）、ShippingChildPinC, ShippingLeafKeepCache（`body` に `if` を足し `Triple.ite` + `tripleA_throwErr`）、ShippingLeafBodyCi（新しい補助定理 `leaf_body_triple_fuel` を追加。`leaf_body_triple` の文は不変）。AllTests（`kjob lake build test`）の結果: Build completed successfully (3150 jobs)、エラー 0（TestTemporal の既存 sorry 警告のみ、今回の変更と無関係）。clean build と corpus の再確認は coder。 最初に追従した 5 ファイルの内訳: `Tools/ShippingEntrySoundness.lean`（`RunsTo.throwError_false` を追加し、`synthesizeCombinationalCore_reads` に throw 枝を閉じる場合分けを足した）、`ShippingChildKeeps.lean`（`core_keeps` の `body` に新しい `if` を足し、`Triple.ite` で throw 枝を `Triple.throwErr` で閉じる）、`ShippingChildRun.lean`（2 箇所、`RunsTo.ite` で throw 枝を閉じる）、`ShippingChildVertA.lean`、`ShippingChildBalance.lean`（`body` に `if` を足し、throw 枝を閉じる）。ほかの `synthesizeCombinationalCoreWith` / `synthesizeChild` / `synthesizeCombinationalWith` を unfold する 35 ファイルは、変更なしでビルドが通った（`kjob lake build` で確認）。
- テスト（`Tests/Compiler/MachRecUnfoldFuelTest.lean`、`MACHRECUNFOLD-FUEL-API`）: `loopN 20000 a`（値が増えず 1 ステップ 1 re-entry の構造再帰）は本番の上限 10000 を超える。コマンドの guard を通さず `synthesizeCombinational` / `synthesizeHierarchical` を直接呼び、(a) トップ `topBig` のエラー（両方）、(b) 親 `parentBig` が呼ぶ子 `kidBig` のエラー（両方、メッセージに子の名前と `fuel exhausted`）、(c) 燃料切れしない `parent` は通ること、を本番の関数・本番の上限のまま確かめる。既存の子・トップ・パラメータ版（燃料 1、`inlinerFuelGuardWith`）のテストは残す。
- **残る範囲**: 依頼の「展開で初めて現れる子」の `#guard`（`hardwareChildren` に載らないことの確認）は書けなかった。この調査では、`hardwareChildren` に載らない形の hardware module の使い方（定義の値または型の定数でない呼び出し）が見つからなかった（ユーザー定義・hardware_module の定義の定数は辿るため、再帰 helper・高階引数・instance 経由でも載る）。見つからなかったのであって、存在しないことの証明ではない。そのため、この場合の担保は例ではなく構成による（すべての子は `doSynth` を通る）。
- ビルド: `Tests.Compiler.MachRecUnfoldFuelTest` ok、上の 5 ファイルと 40 ファイルの対象は下の記録。clean build / AllTests / corpus の再確認は coder。
