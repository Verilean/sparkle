# Claude Code 引き継ぎ — Signal DSL → RTL の証明

更新: 2026-09-28(3 回目)。対象ブランチ: `poc/roundtrip-proof`。
S3「相互再帰する mux 合成」の作業単位は完了した。統合 `Term` ドメインの実 fuel 再帰・
予約親保護・依存順序・入口・出力 RTL 実行の一般定理
`Tools/ShippingUnifiedExecutionSoundness.lean: execution_source_of_env` が接続済み。
`mixedCertifiedShape?` に純追加の `unifiedGateRoot` 判定を足し、該当ソースは certified 経路に入る。
以下の「証明済みと未完の境界」「次の作業単位」は完了分を反映して読むこと。
vector mux のキャッシュ再利用も復旧済み(検証付きラッパー経由、旧 VExpr endpoint は ofV 埋め込みで導出)。
演算ごとの異幅(per-operation mixed widths)も完了: `Term` は幅インデックス化され
(`SType.bits w`)、endpoint は入力ごとの幅割当 `vw` を取る。
幅変更演算(setWidth)も完了: 正のリテラル幅の `Signal.map (BitVec.setWidth w)`/`zeroExtend`
は `translateFallback` の total lowering(`translateSetWidthUncachedWith`、検証付きキャッシュ共有)
に入り、`Term.setw` として同じ endpoint に接続済み。拡大は `{k'd0,x}`、縮小は `w'(x)` エンコード、
同幅は alias。RTL 側連鎖(simpleRhs/TypedExpr/PrintShape/renderer/文法/束縛/zero-width/merge)も
両 IR 形状を受理し、`checkedOptimize_cast` で cast を含む本体の非変換を証明済み。
次の候補: 符号拡張(legacy の縮小挙動が未証明なので除外中)、一般の slice/concat 表面演算、
シンボリック幅、残る組合せ構文、S4–S7。

## 最初に読むこと

目標は **既存の Signal DSL コンパイラで成功する全経路について、実際の出力 RTL がソースと等価であること**。
小さい別コンパイラへの置き換え、成功領域の縮小、回路ごとの再実行証明だけでは完了にならない。

現在の最短の次工程は、統合済みの Bool／BitVec ソース意味とキャッシュ不変条件を使って、
**相互再帰する実際の翻訳を閉じ、入口・出力・RTL 実行の最終定理へつなぐこと**。
ソース言語を定義しただけ、キャッシュの補題を追加しただけで領域拡大を完了扱いにしない。

ユーザーは細かいコミットや短い作業セッションより、仕事が早くまとまって終わることを重視している。
コミットは許可済み。中間コミットごとに「続けますか」と止まらず、まとまった完了条件まで進める。
ただし未証明の範囲や前提を隠さない。TODO とマイルストーンも実装に合わせて更新する。

現行計画の正本:

- [TODO](CertifiedRoundtrip-TODO.md#current-shipping-compiler-todo)
- [マイルストーンと完了条件](ShippingCompiler-Milestones.md)
- [成功経路のカバレッジ](ShippingCompiler-Coverage.md)
- [証明記録](ShippingCompiler-Soundness.md)（長い履歴。末尾に直近の変更）

## 証明済みと未完の境界

| 範囲 | 現状 |
| --- | --- |
| 正の共通幅 BitVec の入力・定数・加減乗・and/or/xor・同幅論理シフト | 出力構文、宣言・参照、RTL の一意な有界解、有限 delta 安定まで接続済み |
| Bool 入力・定数・Bool mux・標準 Bool 論理／等値、上記 BitVec 式の ult/ule/slt/sle・標準等値 | 同じく一般的なソース → RTL 定理まで接続済み |
| BitVec 結果の mux 木 | 条件が既存 `BExpr`、葉が既存 `FExpr` の `VExpr` について接続済み |
| mux を算術・比較の子に置く相互再帰 | 完了。`ShippingUnifiedRecursion`(fuel 契約)+ `ShippingUnifiedProtection`(保護・順序)+ `ShippingUnifiedEntrySoundness` + `ShippingUnifiedExecutionSoundness.execution_source_of_env`(両ソート) |
| 演算ごとの異幅(サブツリー間で異なる正幅) | 完了。幅インデックス付き `Term` と入力別幅割当 `vw` で同じ endpoint に接続 |
| 幅変更演算(setWidth/zeroExtend の canonical map、リテラル正幅) | 完了。`canonicalSetWidth?` 認識 + total lowering + `Term.setw` で同じ endpoint に接続。拡大 8→16・縮小 65→8・同幅・算術親下の 72 SV 実行ケースで検証 |
| 符号拡張、一般 slice/concat 表面演算、シンボリック幅、残る組合せ構文・インターフェース | 未完。legacy 経路のまま(一般定理なし)。成功分岐との網羅的な突合せも必要 |
| 状態・reset、メモリ、階層、成功領域全体の最終合成 | S4–S7、未完 |

既存の主要エンドポイント:

- `Tools/ShippingExecutionSoundness.lean`: `compiledFragment_execution`
- `Tools/ShippingMixedExecutionSoundness.lean`: `execution_source_of_env`
- `Tools/ShippingVectorMuxSoundness.lean`: `execution_source_of_env`

これらは実際の合成、ゼロ幅後処理・検査付き重複統合、検査付き最適化、出力 AST と同じ文字列の構文・名前保証、
2 値・遅延なしの RTL 意味と有限並行 delta 安定を接続する。入力との一致、有界な初期環境などの前提は残る。
未駆動値は delta 実行中に固定。X/Z、実時間遅延、外部シミュレータ自体の正しさは証明範囲外。
`EnvDefines`（実行時 Lean 環境が対象宣言を保持する）は明示した信頼境界として残す。

未完とは、主に対象経路の一般定理・接続がまだ存在しないという意味。
直近の統合基盤 4 ファイルには `sorry`／新規 `axiom` はなく、テストで主要定理の依存公理を監査している。
これはリポジトリ全体の全ファイルに `sorry` がないという主張ではない。

## 直近の実装地図

### 新しい統合基盤 — `52ab4c3`

| ファイル | 役割・再利用する定義 |
| --- | --- |
| `Tools/ShippingUnifiedSource.lean` | `SType` と型付き `Term`。Bool／共通幅 BitVec が自由に相互再帰。`WF`, `eval`, `denote`, `quote`, `denote_val`。旧 `FExpr/BExpr/VExpr` の埋込みと意味・引用・WF 保存、`instFVars_quote` |
| `Tools/ShippingUnifiedMeaning.lean` | `Value`, `Kind`, 純粋な構文認識 `view`, `Meaning`。`Meaning.deterministic` は一つの Lean 式の値・型の一意性。`meaning_quote`／`meaning_quote_mixed` が引用式を意味へ接続。Bool と BitVec 1 も区別 |
| `Tools/ShippingUnifiedCache.lean` | `Records`。実際の `cacheLookupValidated` と `recordTranslation` の保存。`validated_hit`, `record_preserves`, `cached_action`。後者は uncached lowering の正しさが前提 |
| `Tools/ShippingUnifiedInvariant.lean` | `Inputs`, `Inv`, `Outcome`。実行、入力、キャッシュ記録、型付き body、既存ワイヤ値の保存。`cached_outcome`, `Inv.allocate`, `Inv.emit_reserved`, `Inputs.of_mixed` |
| `Tests/Compiler/ShippingUnifiedSourceTest.lean` | 実ソースの意味証明、コンパイル成功と source/legacy/SV/delta の 2,322 ケース、公理監査。相互再帰コンパイルの一般定理の代用ではない |

`Inv.emit_reserved` は、予約した親ワイヤへ最後に代入する際の入力非衝突・記録非衝突をまだ仮定する。
それを子の再帰翻訳から導出し、fuel 帰納を閉じるのが次の中心課題。

### 既存の局所翻訳・再帰・入口

- `Tools/ShippingMixedBinarySoundness.lean`
  - `Frame` は構造的な宣言増加、使用名、bindings、記録、単純文などの保存。新しい意味でも再利用できる。
  - `Frame.record_reserved`: 開始時に使用済みだったワイヤの記録を、翻訳後から開始時へ戻す。
  - `binary_returns`: 実際の算術 lowering を「親名確保 → 子 a → 子 b → 親代入」へ分解。
  - `translateCanonicalSignalBinary_mixed`, `binary_frame`, `core_binary_recorded` が旧不変条件による証明の手本。
  - 旧 `Child`／`Lookup` は旧 Bool／BitVec valuation に依存する。新 `Inv` 用の契約か一般化が必要。
- `Tools/ShippingMixedRecursion.lean`
  - `Contract`, `ActionSpec`, `FreshAction`, 入力・定数・比較・Bool 演算・Bool mux の契約。
  - `bool_fuel_contract` が旧閉じた再帰証明。統合版の構成の手本。
  - `emit_bool_frame`, `translateBoolBinary_returns`, `typed_bool_bin`, `bool_bin_rhs`、各 `*_step` は再利用候補。
- `Tools/ShippingVectorMuxRecursion.lean`
  - `vector_step`, `emit_vector_frame`, `vector_fuel_contract`, `vector_fuel_orders`。
  - 構造補題は再利用し、旧意味を前提とする部分は新契約へ接続する。
- `Tools/ShippingPendingSoundness.lean` と `Tools/ShippingTranslationOrder.lean`
  - `Protected`, `Protects`, `Orders`。予約親を子が読まない／駆動しないこと、単一代入・依存順序の既存証明。
  - 値の保存だけで RTL 安定性の条件が全て導けるとは仮定しない。統合版でも順序の接続が必要。
- `Tools/ShippingContractEntrySoundness.lean`
  - `emitLeaves_correct`, `emitLeaves_from_ports`, `emitLeaves_postReady_at`。
  - 出力幅は一般化済みだが、翻訳契約は旧 mixed 不変条件に依存している。
- `Tools/ShippingVectorMuxSoundness.lean`
  - 実宣言、入力準備、引用・置換、出力、後処理、RTL までの接続の手本。
- `Tools/ShippingMixedEntrySoundness.lean`: `PrintBaseAt`, `RawValueAt`。
  `Tools/ShippingTypedPostSoundness.lean`: `OutputTypedAt`。
  `Tools/ShippingMixedExecutionSoundness.lean`: `execution_of_entry`。
  これらの backend は既に任意の出力幅を扱う。まず再利用を検討する。

### 実コンパイラの注意点

`Sparkle/Compiler/Elab.lean` が対象。
`mixedGateVectorBody`／`mixedGateVectorRoot` と `mixedCertifiedShape?` の保証対象はまだ旧 `VExpr`。
統合 `Term` のゲートは未接続で、統合テストは該当ソースが現在のゲートでは `none` になることも検査する。
**ゲートに入らないことと、コンパイラ全体で失敗することは別**。該当ソースは fallback で成功する。

リテラル幅 BitVec mux の fallback は `translateControlCachedWith (translateVectorMuxUncachedWith rec n)` を
経由するようになった(hit は記録式との構造一致を検証、miss は lowering 後に記録)。
hit の正当化は統合 `Meaning`/`Records` 不変条件による。旧 `VExpr` endpoint は文を維持したまま
`ofV` 埋め込みで統合 endpoint から導出される。

## 次の作業単位と完了条件

1. **統合された実再帰翻訳を閉じる。** 新 `Inputs` から環境に依存しない lookup 条件を取り出し、
   `Frame` と新 `Outcome` を備えた契約を用意する。算術・比較・Bool 演算・両型 mux・葉を接続し、
   実際の fuel 再帰の帰納で子の正しさの仮定を消す。キャッシュ hit/miss と記録保存も含む。
2. **予約親と順序を導出する。** 算術は親名を子より先に確保する。
   `Frame.record_reserved` を子 b、子 a の順に適用すれば、親ワイヤの記録を確保前の状態へ戻せる。
   元の `Records` と fresh 性から `recordSafe` を、bindings 保存と元の `Inputs` から `inputSafe` を導く。
   これは値の保存への方針。依存順序には別途 pending 保護の証明も接続する。
3. **実入口・同じ出力 RTL へ接続する。** 統合構文の認識、入力準備、実宣言からのソース意味、
   `emitLeaves`、`RawValueAt` をつなぎ、既存 backend を使って構文・binding・RTL 安定まで閉じる。
   定理の呼び出し側に子の正しさやコンパイルの再実行証明を渡させない。
4. **回帰・公理監査と報告。** mux が算術の子、比較の子、さらに mux 条件へ戻る実宣言を使い、
   新しい一般定理をインスタンス化する。1/8/65 幅、キャッシュ共有、後処理選択を確認。
   既存 endpoint の後退がないことを検証し、TODO・カバレッジを更新する。

上記で完了するのは S3 の「相互再帰する mux 合成」の単位であり、S3 全体でも最終目標でもない。
続いて未網羅の組合せ成功経路を調査・接続し、S4–S7 を進める。
残りセッション数や「壁はない」は未確認なので断言しない。

## 検証と環境

- `lean-toolchain`: `leanprover/lean4:v4.32.1`。既存のプロジェクト環境を使う。
- 直近の全体検証: `lake build Tests.AllTests`、**635 jobs 成功**。
  前回ログは `/tmp/unified-all-tests.log` にあるが、一時ファイルなので引き継ぎ先では存在を仮定しない。
  この資料作成時は同ログの成功を確認した。ドキュメント変更のみなのでビルドは再実行していない。
- 対象の反復検証例:

  ```sh
  lake build Tools.ShippingUnifiedInvariant
  lake build Tests.Compiler.ShippingUnifiedSourceTest
  lake build Tests.AllTests
  ```

- `lake build` は同時に複数走らせない。全体ビルドは変更のまとまりで実施する。
  `lake test` には以前 macOS の別の linker 問題があったため、今回の受入検証は `Tests.AllTests` のビルド。
- 公理監査は統合テスト末尾の `collectAxioms` を手本にする。
  許容する依存は `propext`, `Classical.choice`, `Quot.sound` のみ。
  新 endpoint と実宣言への適用の両方を監査し、`sorryAx` や native oracle で置き換えない。
- `Tests/AllTests.lean` は統合テストを import 済み。
  統合基盤 4 モジュールは `lakefile.lean` の `lean_lib` roots に登録済み。追加モジュールも必要な登録を行う。

Lean 実装上の既知の注意:

- `SType.Type` は `abbrev` を維持する。`def` にすると既存コードで型クラス推論が失敗した。
- 依存型 mux の帰納パターンは `| s, .mux ...` と型を明示する必要がある箇所がある。
- `bitVecEqualityWidth?` の返り値は `Option Expr`。幅の Nat には `canonicalNatLitValue?` を通す。
- `view_binary` の現在の `simp only` を単純な `cases op <;> rfl` にすると elaboration が非常に重くなった。
- HashMap の挿入時の名前同一性は `beq_iff_eq` で取り出す。`simp [eq_comm]` は再帰深度問題になった。

## 作業ツリーとコミット

引き継ぎ時には `git status --short` を確認する。この資料の変更とは別に、ユーザーの未コミット作業がある。
`shell.nix` の変更、H264 関連、資料・スライド、firmware、repl、scratchpad、verilator 生成物、モデルファイル等は今回の証明作業と無関係。
`.env`／`.mcp.json` も未追跡だが、内容を開いたりコミットしたりしない。
`git add .`、一括 clean/reset、無関係な変更の取り消しはしない。タスクのファイルだけ明示して stage する。

直近のコード履歴:

| コミット | 内容 |
| --- | --- |
| `075e9f4` | mixed RTL 実行 endpoint、S2 完了 |
| `9345209` | signed 比較を endpoint へ接続 |
| `f40317b` | 標準 BitVec 等値、custom BEq 関連の修正 |
| `da72d14` | Bool 論理・標準 Bool 等値を endpoint へ接続 |
| `dabcbcb` | BitVec mux 木を endpoint へ接続、任意出力幅の backend |
| `52ab4c3` | 統合ソース意味・キャッシュ・不変条件の基盤。相互再帰 endpoint はまだ未完 |

## Claude Code に渡す開始指示

```text
docs/ShippingCompiler-ClaudeCode-Handoff.md を読み、既存 Signal DSL コンパイラの
CompCert 化を引き継いでください。基準コードは 52ab4c3 です。
次は ShippingUnifiedInvariant を実際の Bool/BitVec 相互再帰翻訳に接続し、
予約親の保護・fuel 帰納・入口・出力 RTL の一般定理まで進めてください。
既存成功領域を狭めたり、小さい別コンパイラに置き換えたりしないでください。
ユーザーの未コミット変更を保存し、TODO とマイルストーンを実態に合わせて更新してください。
中間コミットごとに停止せず、まとまった完了条件まで作業してください。
完了と未完を区別し、Tests.AllTests と endpoint の依存公理監査で検証してください。
```
