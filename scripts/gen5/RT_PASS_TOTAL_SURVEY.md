# RT S2 調査: `MachRecUnfold` の partial 定義を挙動を変えずに全域化できるか

Issue: sparkle-rt-pass-total（親 sparkle-gen5-dg-readertrace）。base: par/rt-inline-p1 `d68b167c`。
調査だけ（compiler・Lean ライブラリは編集していない）。台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
前提知識: `scripts/gen5/RT_INLINE_SURVEY.md` §1.4（S2）、ptot-m4（`965fe51b` / `6e3739fd`）の全域化。

## 0. 結論（先に）

| 定義 (`Sparkle/Compiler/MachRecUnfold.lean`) | 現状の再帰 | 全域化の方法 | 挙動不変の根拠 | 変更規模 |
|---|---|---|---|---|
| `iota` (`:62`) | 既に `fuel` 引数があり各再帰で `fuel-1` | **WF/構造再帰（`fuel` の `match`）**。新しい fuel は不要 | 同じ fuel を同じ位置で減らすだけ。`fuel==0 → none` もそのまま | ~6 行（`if fuel == 0` → `match fuel`、`fuel - 1` → `fuel`、`partial` 除去） |
| `reduceHead` (`:127`) | 同上 | **同上** | 同上 | ~5 行 |
| `headBetaM` (`:54`) | `f.beta args` の結果に再帰 | **fuel が要る**（measure なし） | §2.1: 型なしの `Expr` で停止しない入力がある（Ω）。実行した | fuel 引数 1 つ + 呼び出し 3 か所 |
| `betaAll` (`:142`) | 子と `betaAll (headBetaM …)` | **fuel が要る** | 子の呼び出しは構造的だが、再入 `betaAll (headBetaM e')` は部分項でない | fuel 引数 1 つ、再帰 5 か所 |
| `listLit?` (`:172`) | `letE` 腕が `listLit? (b.instantiate1 v)` | **fuel が要る**（この調査では measure が見つからなかった） | §2.4: WF の目標 `sizeOf (b.instantiate1 v) < …` が立たない | fuel 引数 1 つ、呼び出し 8 か所 |
| `passM` (`:243`) | 子 + `evalNode?`/`unfoldCall?` の結果に再帰 | **fuel が要る**（env に依る） | §2.5: `env` / `isUser` が引数で、悪い env では停止しない。実行した | `passF` 型（precedent: `Tools/ShippingInlCand.lean`）。メモの扱いが論点（§3） |

* 追加の観察（調査対象の 5 定義の外）: `relevantClosure` (`:283`) は `partial` だが自身を再帰せず、`go` は `fuel` の構造再帰。`partial` を外すだけで通る（scratch で確認、§5）。
* **fuel が要る 4 定義（`headBetaM` / `betaAll` / `listLit?` / `passM`）は、fuel 切れの扱いで成功集合が変わりうる**（§4）。成功集合を狭めるのはユーザー判断なので、§4 を判断資料の材料とする。
* `iota` / `reduceHead` は WF で挙動不変。ただしこれ単独で証明の止まる箇所（S2）は解けない（`headBetaM` が呼び出し元にあるため。§2.1）。

## 1. 各定義の再帰呼び出しの引数と measure

### 1.1 `iota` / `reduceHead`（WF で足りる）
* `iota`: 再帰 3 か所（`_sparseCasesOn` の展開、`rec` の rule、`casesOn` の alt）はいずれも `iota … (fuel - 1) …`。冒頭の `if fuel == 0 then none` を `match fuel with | 0 => none | fuel + 1 =>` に書き換えれば構造再帰になる。
* `reduceHead`: `letE` 腕（`reduceHead … (fuel-1) b`）、matcher 腕（`reduceHead … (fuel-1) r`）。同じ書き換え。
* measure は `fuel` 自身。**新しい fuel も新しい仮定も要らない**。呼び出し側の初期値（`reduceMatcher?` の 256、`unfoldCall?` の 64）も変わらない。
* 中で呼ぶ `headBetaM` が partial の間は、`iota` / `reduceHead` を全域にしても `headBetaM` は不透明のまま（§2.1）。

### 1.2 `headBetaM`
* 再帰: `headBetaM (f.beta e.getAppArgs)`。`Expr.beta` は先頭の λ を引数で置換するだけで、置換後に頭が再び λ になっても `beta` 自身は簡約しない。
* measure の候補: `sizeOf e`（置換で増える）、λ の数（置換で増える）、引数の数 — **どれも減らない**。
* 停止の理由は型付けにある（強正規化）。型なしの `Expr` では停止しない: `(fun x => x x) (fun x => x x)` は `f.beta args` の結果が元の項と等しい（scratch で `true`、`headBetaM` は 20 秒でタイムアウト）。したがって `Expr` 全体を定義域とする WF は**存在しない**。
* production の入力は elaborate 済みの型付き項なので Ω は現れないが、それは `Expr` の型の上では表せない（`Sparkle` の定理として導出する経路は、この調査では見つからなかった）。

### 1.3 `betaAll`
* 再帰: ① `betaAll e.getAppFn`、`getAppArgs.map betaAll`（部分項）、② `lam` / `letE` / `mdata` の子（部分項）、③ `betaAll (headBetaM e')`（部分項でない、`headBetaM` の結果）。
* ①②は `sizeOf` が減る（ただし `getAppFn` / `getAppArgs` の要素の `sizeOf` の補題が要る。`Array.map` は `attach` が要る）。③ は `headBetaM` が増やしうるので `sizeOf` は減らない。
* fuel の形: 「③ の再入回数の上界」を fuel にして、①② は構造再帰にする（辞書式 `(fuel, sizeOf e)`）か、単に全再帰で fuel を減らす（scratch は後者。コンパイルは通る）。
* 前者のほうが fuel が小さくて済む。後者は fuel が式の深さ（実測は式の深さが 10^5 を超える前に実行時スタックが尽きる見込みだが、実測していない）を上回る必要がある。

### 1.4 `listLit?`
* 再帰: `mdata` の子（部分項）、`cons` の `rest`、`Array.toList` / `List.toArray` / `Array.mk` / `zipIdx` の引数（部分項）、**`letE` 腕の `listLit? (b.instantiate1 v)`**（`v` は閉じている）。
* 最後だけが部分項でない。scratch の WF 試作の失敗: `sizeOf (b.instantiate1 v) < 1 + sizeOf name + sizeOf type + sizeOf v + sizeOf b + 1` が目標になり、証明できない（`instantiate1` は C++ の extern で、論理では不透明。置換は `b` 中の `bvar 0` の個数だけ `v` を複製するので、`sizeOf` は実際に増えうる）。
* 停止すると思われる理由（let の zeta 展開だけの簡約は強正規化）はあるが、**この調査では、Lean の `termination_by` に載る具体的な measure は見つけていない**（導出不能の意味ではない）。仮に作るなら `Inst1Agrees`（既存、T1L-51）で `instantiate1` をモデルに置き換えた上で、let の入れ子の重みづけ（置換される `v` の重みを掛ける形）が要り、それなりに大きい（見積もり ~200 行。未確認）。
* fuel の形: `letE` 腕だけ fuel を減らせば足りる（他は構造的）。scratch は全再帰で fuel を減らす形でコンパイルが通った。

### 1.5 `passM`（再帰ヘルパの展開 `unfoldCall?` の停止）
* 再帰: ① `passM e.getAppFn`、`getAppArgs.mapM passM`、`lam`/`letE`/`mdata` の子（部分項）、② `passM r`（`r` は `evalNode?` の結果）、③ `passM r`（`r` は `unfoldCall?` の結果）、④ `letE` 腕の `passM (b.instantiate1 v')`。
* ②: `evalNode?` の結果は `ite` の腕 `a`/`b`（部分項）か、`mkListLit α xs`（`zipIdx` の場合、要素ごとに `Prod.mk` と `natLitE` が増えるので、元の項より大きいことがある。ただし再度の `passM` は `Prod.mk` / `List.cons` に `evalNode?` も `unfoldCall?` も効かないので止まる）。
* ③: `unfoldCall?` は `_sunfold` の値を `reduceHead`（matcher の判別対象が構造子のときだけ成功）で簡約する。**停止の具体的な理由**: 成功するたびに、構造再帰の引数（`List` なら先頭の `cons` を 1 個、`Nat` なら `succ n` を `n` に、`natLitE (n)` の値）が 1 つ小さくなる。「リテラルデータが残る間」とはこの意味である。measure の候補は「構造再帰の引数のデータの大きさ」（`List` は長さ、`Nat` は値）の多重集合、再帰ヘルパは相互・入れ子の場合があるので辞書式／多重集合順序が要る（未試作）。`Nat` リテラルは `Expr` として定数サイズ（`OfNat.ofNat Nat n inst`）なので、`sizeOf` ではなくリテラルの値が要る。
* ただしこの理由は「`isUser` の関数に `_sunfold` があり、それが実際に構造再帰の展開形である」ことに依る。`passM` は `env` と `isUser` を引数に取るので、**`env` に依らない WF は存在しない**。実行した反例（§2.5）: `foo._sunfold := fun n => foo n`（matcher を含まない定義）を持つ `env` と `isUser = (· == foo)` で、`pass env _ isUser (foo 3)` は停止しない。この `env` は `Environment` として正しく構成できる（axiom + 定義）が、Lean が生成する `_sunfold` ではない。
* ④: ① ③ と同じ（`instantiate1`）。

## 2. WF と fuel の別と、その根拠

### 2.1 `headBetaM` — fuel（measure なし）
* Ω の実行結果（scratch `PB.lean`）: `(omega.getAppFn.beta omega.getAppArgs) == omega` は `true`、`headBetaM omega` は 20 秒でタイムアウト（exit 124）。
* fuel の形: `headBetaM : Nat → Expr → Expr`、`0` で `e` を返す（または `Option`）。呼び出し 3 か所（`iota` / `reduceHead` / `betaAll`）に初期値を渡す。
* **fuel 切れが成功集合を変えるか**: production は Ω のような入力では停止しない（成功集合に入らない）。fuel を `N` にすると、`N` 回を超えて停止する型付き項（頭の β 簡約が `N` 回超）では結果が変わる。型付きの項で頭の β 簡約が 10^6 回を超える入力が production で現れるかは、この調査では調べていない。

### 2.2 `iota` / `reduceHead` — WF（fuel 既存）
§1.1。`lean` で `PA.lean` がエラーなしで通った（`partial` を外し、`match fuel` に変更）。

### 2.3 `betaAll` — fuel（再入）
§1.3。

### 2.4 `listLit?` — fuel（この調査では measure が見つからなかった）
§1.4。

### 2.5 `passM` — fuel（env に依る）
* `PD.lean`（`foo._sunfold := fun n => foo n`）は 20 秒でタイムアウト、`isUser` を別名にした `PD2.lean` は `foo 3` を返す。メモは `insert` が結果の計算後なので、自己呼び出しを止めない。
* fuel の形: `passF`（`Tools/ShippingInlCand.lean`、fuel 0 は元の `passM` を呼ぶ）は **実行時の互換の議論だけ**で、論理では `passM` は不透明のままなので、保存の証明には使えない（`RT_INLINE_SURVEY.md` §1.4 のとおり）。論理で全域にするには、fuel 0 の腕を `passM` ではなく結果（`e` かエラー）にする必要があり、**これは production の挙動を変える**（§4）。

## 3. メモ（`StateM (Std.HashMap Expr Expr)`）の影響

* メモは `e ↦ passM e` の表。`passM` は `env` / `isUser` / `natLit?` が固定なら `e` だけの関数なので、メモの命中は再計算と同じ値を返す（純粋関数のキャッシュ）。
* **fuel を入れるとこの性質が壊れる**: fuel 切れで打ち切った途中の結果をメモに入れると、後で別の深さ（fuel が多い位置）から同じ `e` を引いたとき、打ち切り結果が返る。メモ付きの結果が「fuel に依らない関数」でなくなる。対策は、fuel 切れを結果の型（`Option` / `ExceptT`）で伝え、打ち切りの結果はメモに入れないこと。
* 全域化版とメモ付き版の一致の形（候補、どれも未証明・未 elaborate）:
  1. **ビッグステップ関係**: `Pass env e r` を帰納述語として定義し、メモの不変量「`(k, v) ∈ s → Pass env k v`」を置く。`passF n e s = some (r, s') → Inv s → Pass env e r ∧ Inv s'`。保存の証明（`NoPh` / `BvarLt` の保存）はこの関係の上で進める。最も小さく、`partial` と無関係に述べられる。
  2. **fuel 単調性**: `passF n e s = some (r, s') → passF (n+1) e s = some (r, s')`。実行時の互換（fuel を増やしても結果が同じ）はこれで言えるが、`partial` の `passM` との一致は言えない（論理では不透明）。
  3. **メモなしの全域版との一致**: メモなしの `passNoMemo` を置き、`(passF n e s).1 = passNoMemo n e` を示す。メモなしは指数的になりうる（DAG の共有）が、証明の対象にするだけなら問題ない。
* 保存の証明に必要なメモの不変量は `RT_INLINE_SURVEY.md` §1.4 のとおり（`NoPh k → NoPh v ∧ ∀ L, BvarLt L k → BvarLt L v`）。形 1 と合わせれば足りる。

## 4. fuel 切れで結果が変わる条件（判断資料の材料）

production（`partial`）には fuel 切れがない。fuel を入れた全域版が production と**結果が異なりうる**のは次の場合に限る（いずれもこの調査では「production でそのような入力が現れる経路は見つからなかった」。現れないとは証明していない）。

| fuel | 切れる条件 | production での挙動 | 全域版 |
|---|---|---|---|
| `headBetaM` | 頭の β が `N` 回を超える | 停止すれば結果を返す／Ω は停止しない | `N` 回で打ち切り（`e` または失敗） |
| `betaAll` | 再入または深さが `N` を超える | 同上、深さはスタックが先に尽きる見込み | 打ち切り |
| `listLit?` | `letE` の連鎖が `N` を超える | `letE` が 10^6 段の閉じたデータは現れない見込み | `none`（リスト扱いにしない）→ 展開しない |
| `passM` | 展開の深さが `N` を超える | 停止（データが尽きる）か、悪い env で停止しない | 打ち切り |

* 影響する成功集合: fuel 切れが `none` / 失敗なら、その入力を production は変換するが全域版は変換しない（成功集合が狭まる、結果は「変換されない」側）。`e` を返す形でも同じ（変換が部分的になる）。
* `N` を十分大きくしても、**「どのソースでも切れない」ことは証明できない**（Ω と悪い env が `Expr` の型の上では存在する）。ソース単位の述語（例えば「`isUser` の関数は `_sunfold` が構造再帰で出る」）を仮定として置くと、新しい env 条件（台帳 FG +）になる。fuel 版は仮定を増やさず、代わりに production の挙動が「大きい入力で変わる」ことを受け入れる。
* 選択肢（判断はユーザー）:
  * (A) fuel 版に置き換える（compiler 変更、`partial` 4 定義が fuel 付き、`iota` / `reduceHead` は WF）。FG 増なし。挙動は §4 の表の範囲で変わる。可逆（コミットを戻せる）。
  * (B) production は `partial` のまま、`PassPh`（候補 U-3、`RT_INLINE_SURVEY.md` §1.4）を FG +1 で置く。挙動不変、仮定が増える。
  * (C) `iota` / `reduceHead` / `relevantClosure` だけ WF にして、残りは据え置き。挙動不変・仮定増なしだが、S2 は解けない（`headBetaM` が残る）。
* 推奨は判断資料の別の段階（ここは調査）。上の表のとおり、(A) は挙動が変わりうる条件が具体的に書けるので、ユーザー判断に出す材料にはなる。

## 5. 実行した probe（scratch、コミットしない）

すべて `Scratch/` 配下、`lean` 直接実行（Lean 4.32.1）。`MachRecUnfold.lean` は `import Lean` のみなので複製で足りた。

| ファイル | 内容 | 結果 |
|---|---|---|
| `PA.lean` | `iota` / `reduceHead` を `match fuel` の構造再帰にした | エラーなし |
| `PB.lean` | Ω と `headBetaM` | `beta` の結果 `== omega` は `true`、`headBetaM omega` は 20 秒タイムアウト |
| `PC.lean` | `listLit?` から `partial` を外した | 失敗: `sizeOf (b.instantiate1 v) < …` |
| `PD.lean` / `PD2.lean` | `foo._sunfold := fun n => foo n` の env で `pass` | `isUser = foo`: 20 秒タイムアウト／別名: `foo 3` を返す |
| `PE.lean` | `headBetaM` / `betaAll` / `listLit?` を fuel 版にし、`PA` と合わせた | エラーなし（`passM` は `partial` のまま。fuel 版の `passM` は `Tools/ShippingInlCand.lean` の `passF` が前例） |
| `PF.lean` | `relevantClosure` から `partial` を外した | エラーなし |

* fuel 版は**コンパイルが通っただけ**で、production との一致（成功集合、出力）は実行・証明していない。
* 上の「反例」（Ω、悪い env）は `Expr` / `Environment` の型の上での停止性の反例であって、production のコンパイラが生成する入力ではない。mutant の棄却（signature / defeq）の話ではなく、停止性の議論である。

## 6. 規模・止まる箇所・台帳

| 項目 | 内容 |
|---|---|
| 変更規模（compiler、案 A） | `iota` ~6 行、`reduceHead` ~5 行、`headBetaM`/`betaAll`/`listLit?` 各 fuel 引数と呼び出し（計 ~30 行）、`passM` を `passF` 型に（~25 行）。`pass` / `relevantClosure` の外向きの型は同じ（`Elab.lean:3400,3404` は変更なし） |
| 保存の証明（全域化後） | ~400〜700 行（`RT_INLINE_SURVEY.md` §1.4）。メモの不変量は §3 の形 1 |
| 止まる箇所 | (a) compiler 変更（案 A）はユーザー承認。(b) `listLit?` / `passM` の `letE` 腕の `instantiate1`（`Inst1Agrees` 既存＋`inst1Spec_noPh`/`inst1Spec_bvarLt`）。(c) `unfoldCall?` の `instantiateLevelParams` と `Expr.beta`（U-1 / U-2 の領域、S1）。(d) `iota` の `rec` 腕の `RecRulePh`（別件、`RT_INLINE_SURVEY.md` §1.4） |
| 台帳 | **この調査: FG -0 +0 / T1 -0 +0。** 案 A なら `PassPh`（FG +1 候補）は不要になるが `RecRulePh` は残る（FG 側の増減は別 Issue で計数）。案 B は FG +1。T1 側の付け替えは調べていない（未計数） |

## 7. 未確認

* fuel 版の production との一致は未検証（コンパイルのみ）。`N` の適切な値、`betaAll` の再入回数の実測は未取得。
* `listLit?` の measure、`passM` の多重集合 measure は未試作・未証明。
* `Expr.beta` / `instantiate1` / `instantiateLevelParams` の extern と measure の関係は未 elaborate。
* `passF` の fuel 0 腕が `passM` を呼ぶ形（実行時のみの議論）と、論理で全域な形の差が、`ShippingInlCand` の既存証明にどう響くかは確認していない。
