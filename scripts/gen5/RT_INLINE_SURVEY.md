# RT inline 枝の調査: `UserInlinerPh` を仮定せずに `hdecl` を出す経路（調査のみ。Lean 未実行）

対象 Issue: `sparkle-rt-inline-survey`（親 `sparkle-gen5-dg-readertrace`）。base: `par/rt-direct` 046d1d56。
台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。**Lean のソースは編集していない。scratch の Lean probe も走らせていない**（下の「未確認」）。以下の「見込み」「規模」はソースを読んだ上での見積もりで、証明の存在や成立の確認ではない。

## 0. 何を示したいか（inline 枝の入力）

* inline 枝: `ci = inlinedConst (userInliner env) ci0`（`Sparkle/Compiler/Elab.lean:5272` `entryConst`、`inlinedConst` は `:3405` 付近、`userInliner` は `:3387`）。`ci0 = .defnInfo d`、`env.find? c = some ci0`。
* `shapeInputs_of`（`Tools/ShippingGen5ReaderTraceShapeIn.lean:458`）の入力のうち、inline 枝で変わるのは `hdecl`（`ci' = .defnInfo d' → NoPh d'.value ∧ BvarLt 0 d'.value`、`d'.value = userInliner env d.value`）だけ。
  * `hpack`（`packTupleInputsF_ph`、`Direct.lean:86`）、`hnorm`（`machNormF_ph`、`Direct.lean:142`）は `L` と `e` について一般で、`ci` の形に依らない。`hdom` / `hbs` は `ci'` についての既存の形のまま（供給側は別の義務）。
  * `d'.type = userInliner env d.type` は `ShapeInputs` の `NoPh` / `BvarLt` 入力には現れない（`shapePre`、`Tools/ShippingReaderFuelShape.lean:105`、は `d.type` を `machTupleKinds?` / `machOuts?` で読むだけ）。ただし `machOuts?` が読む型が inline 後に変わる点は `hdom` / `hbs` 側の読みの問題で、この調査では確かめていない。
* したがって目標は次の 1 文（`UserInlinerPh`、rev18 §2 と同じ）:
  `DeclValuePh env → env.find? c = some (.defnInfo d) → NoPh (userInliner env d.value) = true ∧ BvarLt 0 (userInliner env d.value) = true`

## 1. 項目別の調査

### 1.1 `userInliner` の構成（`Elab.lean:3387`）

```
e1 = inl e                                -- inlineDefs（fuel inlineDepth=4096, budget 16000000）、none なら e
if relevantClosure …                      -- MachRecUnfold.relevantClosure（partial）の Bool
then inlFoldNat (inlAbbrevs env 4 (rounds 64 e1))
else inlFoldNat (inlAbbrevs env 4 e1)
rounds (k+1) e = let e' := MachRecUnfold.pass env … e; if e' == e then e else rounds k (inl e')
inlAbbrevs env (n+1) e = let e' := e.replace abbrevFn; if e' == e then e else inlAbbrevs env n e'.headBeta
```

`relevantClosure` は `partial` で値を展開できないが、`if` の条件としてしか使われない。**両腕で保存を示せば値に依らず結論が出る**（証明は Bool の場合分け）。ただし真の腕に `rounds`（= `pass`）が入るので、真の腕は §1.4 の S2 を避けられない（`relevantClosure = false` を導く経路は、`partial` のため見つからなかった）。

### 1.2 P1: `inline` 後も `NoPh ∧ BvarLt` を保つ理由（全域で、新しい前提なし、の見込み）

`inlineDefs`（`:3202`）は fuel と budget の構造再帰で、`Option` を返す全域 `def`。`none` の腕は `inl` が元の `e` を返すので保存は自明。`some` の腕の理由:

| 部品 | 場所 | 保存の理由 | 補題の形（候補） |
|---|---|---|---|
| `inlLift k c` | `Elab.lean:2988` | `bvar i` を `i<c` ならそのまま、そうでなければ `i+k` に。binder 内で `c+1` | `BvarLt L e → inlLift k c e b = some (e',_) → BvarLt (L+k) e'`、`NoPh e → NoPh e'`。既存 `liftSpec_noPh` / `liftSpec_bvarLt`（`Tools/ShippingGen5ReaderTraceLift.lean:15,39`）は `liftSpec` 用で、`inlLift` は別の関数なので流用できない（同じ形の証明を書き直す） |
| `inlSubst xs d` | `:3028` | `i<d` はそのまま、`i-d<xs.size` は `xs` の要素（`d>0` なら `inlLift d 0` で持ち上げ）、それ以外は `i - xs.size` | `∀ x ∈ xs, NoPh x ∧ BvarLt L x` かつ `BvarLt (d + xs.size) e` なら結果は `NoPh ∧ BvarLt (d + L)`。`mdata` / `proj` は `none`（拒否） |
| `inlBeta acc v args` | `:3072` | `lam` を引数の数だけ剥がして `inlSubst` | `v` が `BvarLt k`（`k = acc.size` の剥がし後）で上の補題に帰着。`defs n` の値 `v` は閉じている（下の `userDefinition?`）ので `acc = #[]` から始めれば `BvarLt 0` |
| `userDefinition? env n` | `:3330` | `env.find? n = some (.defnInfo d)` のときだけ `some d.value` | **`DeclValuePh env`（N1-a、`Direct.lean` 内の仮説）がそのまま `NoPh ∧ BvarLt 0` を与える**。新しい前提なし |
| `inlHeadCtor` | `:3170` | `letE` の腕は `inlSubst #[v] 0 body`、`const` の腕は `inlBeta #[] v args`、`lam` の腕は `inlBeta`。返すのは `ctor` の引数リスト | fuel 帰納で「返った引数は各々 `NoPh ∧ BvarLt L`」 |
| `userProjection?` | `:3349` | 名前と数だけを返す。式を作らない | 補題不要 |
| `inlSignalApplicative` / `inlSignalMapOfFunctor` / `inlCanonLam` / `inlCanonPi` / `inlDropBinder` | `:3150` / `3135` / `3122` / `3114` / `3100` | `mkApp5 (.const …) dom α β f mx'`。`inlCanonLam` / `inlCanonPi` は binder 名を変えるだけ。`inlDropBinder c` は `bvar i>c` を `i-1` に下げ、`i=c` なら `none` | `inlDropBinder`: `c ≤ M → BvarLt (M+1) e → inlDropBinder c e = some e' → BvarLt M e'`（`M` を一般化。binder で `c+1`, `M+1`）。`NoPh` は保つ。残りは構造的 |
| `inlineDefs` 本体 | `:3202` | 上の部品の合成。`lam` / `letE` は body を `L+1`、`app` の引数は `L` | fuel 帰納（`fuel` と `b` を一般化、`L` を全称） |

* **使う既存定理**: `NoPh` / `BvarLt` の定義（`Tools/ShippingGen5ReaderTrace.lean:22,33`）、`DeclValuePh`（`Direct.lean` の N1-a）。`inlFoldNat_ph`（`ShapeIn.lean:32`、構造的、前提なし）は最後の `inlFoldNat` の段でそのまま使える。`BvarLt` の単調性（`BvarLt a e → a ≤ b → BvarLt b e`）は既存の補題を grep では見つけられなかった（この調査では見つからなかった。新規に ~15 行）。
* **`Inst1Agrees` は P1 に要らない**: `inlSubst` は `Expr.instantiate` を使わず自前の置換（rev18 §3.1 の訂正と同じ）。
* **全域化が要る def: なし**（P1 の範囲はすべて通常の `def`）。
* **最小の振る舞い仮定: なし**。
* **規模の見積もり**: 新規 1 ファイル、補題 ~12 個、~450〜650 行。分類としては既存の `inlFoldNat_ph`（~50 行）と同種の構造帰納の拡張で、`inlSubst` / `inlineDefs` の入れ子 `match`（`Option (Expr × Nat)` の連鎖）を `split` で分解する手間が主。
* **止まる箇所: なし**（P1 の範囲では）。

### 1.3 S1: `inlAbbrevs` の `Expr.replace` と `Expr.headBeta`（C++ / core の opaque）

* `Expr.replace`（`Lean/Util/ReplaceExpr.lean:16-20`）は `@[extern "lean_replace_expr"] opaque replaceImpl`。論理に内容がない。構造版 `replaceNoCache`（`:23-32`）は通常の `def`。
* `Expr.headBeta`（`Lean/Expr.lean:1658`）は `betaRev`（`:1593`、**core の `partial def`**）を呼び、その中で `instantiateRange`（`:1473`、extern）と `instantiate`（`:1430`、extern）を使う。Sparkle 自身の `partial` ではないので「全域化して証明」の方針の対象外で、論理上は opaque。
* `Expr.instantiateLevelParams`（`Util/InstantiateLevelParams.lean:35`）は `e.replace replaceFn` で、同じ `replace` の extern に依存する（`passM` 側の `unfoldCall?` / `iota` / `reduceMatcher?` が使う。§1.4）。
* 既存: `ZeroLitAgrees0`（T1L-54、`Tools/Assume/N3Extern.lean`）は `zeroLit` についてだけ。`abbrevFn` の `replace` は含まない（`zeroLitF` の置換のみの文）。`Inst1Agrees`（T1L-51、`Tools/ShippingLetsExternSpec.lean:121`）は `instantiate1` だけで、`instantiate` / `instantiateRange` は含まない。`Tools/ShippingInlCand.lean` の `abbrevStep` は `replaceNoCache` との一致を OPEN と明記し、値（`ci0.value`）の `replace` は扱っていない。
* 保存の証明そのもの（仮定が入った後）は構造的: `replaceNoCache (abbrevFn env)` は `.const c []` を `userAbbrev? env c = some v` の `v`（= `env` の `defnInfo` の値）に置き換えるだけで、`DeclValuePh` から `v` は `NoPh ∧ BvarLt 0`、つまりどの `L` でも `BvarLt L`（単調性）。`userAbbrev?` の `!d.value.hasLooseBVars` の guard は使わなくてよい（`hv` が直接 `BvarLt 0` を与える。`hasLooseBVars` と `BvarLt 0` の関係は、`Expr.data` のビット詰めを経由するため、今回は経路に入れない）。
* **最小の振る舞い仮定の候補（完全型。`Tools/Assume/` の流儀。登録はしない）**:

```lean
/-- (候補 U-1。T1 +1 候補) `Expr.replace` は構造版と一致する。一般形。 -/
def ReplaceAgrees : Prop :=
  ∀ (f : Lean.Expr → Option Lean.Expr) (e : Lean.Expr), e.replace f = e.replaceNoCache f

/-- (候補 U-2。T1 +1 候補) `Expr.headBeta` が `NoPh ∧ BvarLt L` を保つ。core の `partial def betaRev` + extern `instantiate*` の挙動。 -/
def HeadBetaPh : Prop :=
  ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
    NoPh e.headBeta = true ∧ BvarLt L e.headBeta = true
```

  * U-1 を一般形にすると `zeroLit`（`Sparkle/Compiler/MachRawSurface.lean:231`、`e.replace fun x => …`）にも効き、`ZeroLitAgrees0`（T1L-54）が導出できる可能性がある。その場合 T1 の件数は ±0 になりうるが、**この調査では導出していない**。台帳の付け替えになるので、数えない・決めない。`abbrevFn` に狭めた形（`e.replace (Tools.ShippingInlCand.abbrevFn env) = e.replaceNoCache (Tools.ShippingInlCand.abbrevFn env)`）も作れる。
  * U-2 は「保存」の形で、`Inst1Agrees` / `LiftAgrees` のような「モデルとの一致」の形ではない。一致の形にするには全域モデル `betaRevF`（`go` の fuel 版）と、`instantiate` / `instantiateRange` のモデルが要る（~100 行の新規定義 + 一致の文が 2〜3 本）。保存の形は小さいが、`UserInlinerPh` 型の「性質そのものの仮定」に近い（`RawNodePh` / `NormNodePh` と同じ種類）。どちらにするかは判断事項（§3）。
* **規模の見積もり**: 仮定が入った後の `inlAbbrevs` 保存（`Nat` の構造帰納 + `replaceNoCache` の構造帰納）は ~100 行。
* **止まる箇所**: U-1 / U-2（または一致の形の補題群）は証明できない。C++ の読み（`replace_fn.cpp` 等）でしか支えられない。

### 1.4 S2: `MachRecUnfold.pass` / `passM`（Sparkle 自身の `partial`）

* `passM`（`MachRecUnfold.lean:243`）は `partial`、`StateM (Std.HashMap Expr Expr)` のメモ付き。中で `iota`（`:62`）、`reduceHead`（`:127`）、`betaAll`（`:142`）、`headBetaM`（`:54`）、`listLit?`（`:172`）も `partial`。`unfoldCall?`（`:155`）、`reduceMatcher?`、`evalNode?`、`natVal?`、`boolVal?`、`ctorApp?`、`mkListLit` は全域。
* 停止性は自明ではない（再帰ヘルパの展開は「リテラルデータが残る間」だけ続く、という設計。`passM` の docstring）。したがって「全域化して証明」の対象に入るが、**全域化の方法は fuel 版（ptot-m4 の前例、`machBoolMap` / `machLiftScalarN` / `rootFloat`）で、production の定義を変える = compiler 変更（ユーザー承認が要る範囲、この Issue では禁止）**。`Tools/ShippingInlCand.lean` の `passF` は fuel 版の候補だが、同ファイルのヘッダのとおり `passF n e s = passM e s` は実行時の互換の議論で、kernel の等式ではない（`passM` は logic で opaque）。
* 全域化したときに保存が成り立つ理由（見込み。未 elaborate・未証明）:
  * 状態不変量: メモ表の各 `(k, v)` が「`NoPh k → NoPh v` かつ `∀ L, BvarLt L k → BvarLt L v`」を満たす（`pass` は `e` だけの関数で、`L` に依らないので、キーに深さを持たなくてよい）。`Std.HashMap` の `get?` / `insert` の補題で保てる。
  * `app` の腕: `getAppFn` / `getAppArgs.mapM` / `mkAppN` は部分項の再構成。`evalNode?` はリテラル、`mkListLit`（`List.cons` / `List.nil` の const + 引数）、引数の返却のみ（`ite` の腕は `a` / `b` を返す = 部分項）。
  * `letE` の腕: `b.instantiate1 v'` は `Inst1Agrees`（既存、T1L-51）+ `inst1Spec_noPh` / `inst1Spec_bvarLt`（`Tools/ShippingGen5ReaderTraceInst1.lean:14,47`）で保存。ただし `v'` が閉じている（`!v'.hasLooseBVars`）ことを `BvarLt 0 v'` として使う箇所が要る（`hasLooseBVars` と `BvarLt` の関係は上と同じ理由で今回は未接続。guard を `BvarLt 0` に読み替える補題が別に要る）。
  * `unfoldCall?`: `d.value`（`_sunfold` の値。`env.find?` が `.defnInfo` を返すので **`DeclValuePh` がそのまま効く**）に `instantiateLevelParams`（§1.3 の extern 依存）と `Expr.beta`（`betaRev`、U-2 の領域）。`reduceHead` / `reduceMatcher?`: matcher の `d.value` も `defnInfo`（`DeclValuePh` が効く）。
  * **`iota` の `rec` の腕: `rule.rhs`（`.recInfo` の規則）は `defnInfo` ではないので `DeclValuePh` が覆わない**。ここは**新しい env 条件が要る**: `RecRulePh env`（`env.find? n = some (.recInfo rv) → ∀ r ∈ rv.rules, NoPh r.rhs ∧ BvarLt 0 r.rhs`）。この調査では「供給元・経路が見つからなかった」（`Environment` の `recInfo` の規則の閉性を kernel が検査するのは通常の理解だが、Sparkle の側の定理としては見つけていない）。台帳に +1 の候補（N1-a の拡張か別行かは未定）。
* **最小の振る舞い仮定の候補（完全型。登録しない）**。全域化が承認されない場合の代替で、方針（Sparkle の `partial` は全域化して証明。停止が示せないものだけ仮定）には**停止性を示せないと判断された後でなければ合わない**:

```lean
/-- (候補 U-3。FG +1 候補。停止が示せない場合のみ) `MachRecUnfold.pass` が `NoPh ∧ BvarLt L` を保つ。 -/
def PassPh : Prop :=
  ∀ (env : Lean.Environment) (isUser : Lean.Name → Bool) (L : Nat) (e : Lean.Expr),
    Tools.Assume.EnvDeclValue.DeclValuePh env →
    NoPh e = true → BvarLt L e = true →
    NoPh (Sparkle.Compiler.MachRecUnfold.pass env Sparkle.Compiler.Elab.canonicalNatLitValue? isUser e) = true ∧
      BvarLt L (Sparkle.Compiler.MachRecUnfold.pass env Sparkle.Compiler.Elab.canonicalNatLitValue? isUser e) = true
```

  これは rev18 の候補 U-A と同じ内容を完全型にしたもの。停止性の議論をせずに足すと `UserInlinerPh` と同種の「保存の仮定」になり、ユーザー方針（仮定より証明）に反するので、**足す前に停止性の調査（fuel 版が十分かの確認）が先**。
* **規模の見積もり**: 全域化した `passF` 相当に対する保存の証明は ~400〜700 行（メモ不変量 + 5 つの `partial` の fuel 版の保存）。全域化そのもの（5 定義 + 互換）は production 変更で、見積もりに含めない。
* **止まる箇所**: (a) production の `partial` 5 定義の全域化 = compiler 変更（承認待ち）。(b) `RecRulePh`（新しい env 条件）。(c) `instantiateLevelParams` / `Expr.beta` の extern（§1.3 の U-1 / U-2 の領域）。

### 1.5 合成（`userInliner` 全体）

* `userInliner env e` の `NoPh ∧ BvarLt 0` は P1（`inl`）→ 場合分け（`relevantClosure` の Bool）→ [真] `rounds`（`Nat` 帰納、各ステップ `pass`（§1.4）→ `inl`（P1））→ `inlAbbrevs`（§1.3）→ `inlFoldNat`（既存 `inlFoldNat_ph`）。
* `if e' == e then e else …` の `==` は `Expr.eqv`（extern）だが、両腕で保存を示せば値に依らない（`Bool` の場合分けだけ。仮定を要しない）。
* 偽の腕（`relevantClosure = false`）は P1 + §1.3（U-1, U-2）+ `inlFoldNat_ph` だけで閉じる。真の腕に §1.4 が加わる。
* 規模（合成）: ~100 行。
* **止まる箇所の総括**: P1 は無仮定で進める（見込み）。残りは (S1) U-1 / U-2、(S2) 全域化の承認または U-3、`RecRulePh`。この調査では、これらを越える経路は見つからなかった（導出不能の意味ではない）。

## 2. 台帳への影響

| 項目 | 内容 | 件数 |
|---|---|---|
| 今回 | 調査のみ | **FG ±0 / T1 ±0**（FG 103 / T1 54） |
| P1（`inlineDefs` 等の保存） | 新しい前提なし（`DeclValuePh` は N1-a で、`shapeInputs_of_direct` が既に取っている候補と同じ） | 0 |
| U-1 `ReplaceAgrees`（または `abbrevFn` 限定） | T1（C++ extern）の候補。`ZeroLitAgrees0` を導出できれば付け替えの可能性 | +1（付け替え分は未計数） |
| U-2 `HeadBetaPh`（または一致の形） | T1（core `partial` + extern）の候補 | +1（一致の形なら +2〜3 の可能性、未計数） |
| S2 全域化 | production 変更。承認が出れば FG +0（`PassPh` を足さずに済む）。出なければ U-3 | 0 または FG +1 |
| `RecRulePh` | 新しい env 条件の候補 | +1（N1-a と束ねるか未定） |
| inline 枝の `ShapeInputs` が得られた場合の減算 | `UserInlinerPh` は足さない。上の候補が登録されれば、それらが inline 枝の前提になる | 未計数 |

上の +1 はいずれも**候補で未登録・未計数**。登録・付け替え・束ね方は reviewer の承認が要る freeze の範囲。

## 3. 判断が要る点（この Issue では決めない）

1. S2: `MachRecUnfold` の `partial` 5 定義を fuel 版に全域化する（ptot-m4 と同じ。compiler 変更でユーザー承認）か、停止性を示せないと判断して U-3 を足すか。方針上は前者が先。
2. S1: `Expr.replace` / `headBeta` を「一致」の形（モデル + 一致、T1 件数が増える）で書くか、「保存」の形（U-1 / U-2、件数が少ない）で書くか。U-1 を一般形にして `ZeroLitAgrees0` を導出する付け替えを行うか。
3. `RecRulePh` を N1-a に束ねるか。
4. 当面 inline 枝を未解消のまま `shapeInputs_of_direct` で進める（rev18 / rev19 の選択）のを続けるか。

## 4. 次の単位の提案（調査の結果。着手は coder / reviewer の合意の後）

* **P1 の freeze → 実装**: 新規ファイル（例 `Tools/ShippingGen5ReaderTraceInlineP1.lean`）で `inlineDefs_ph`（と `inlLift_ph` / `inlSubst_ph` / `inlBeta_ph` / `inlHeadCtor_ph` / `inlDropBinder_ph` / `inlSignalApplicative_ph`）。**新しい前提を増やさない**（`DeclValuePh` は既存の候補の再利用）ので、台帳差分 0/0 の freeze で進められる見込み。ただし完全型は freeze 文書で固定してから（本調査はその型を固定していない）。
* 並行して S2 の全域化と S1 の形の判断（§3）を reviewer / ユーザーに出す。

## 5. 未確認・主張しないこと

* **scratch の Lean probe は走らせていない**。ソースの読みと既存の補題名・行番号の確認（grep）のみ。補題の形（§1.2〜1.4 の式）はすべて未 elaborate・未証明で、`autoImplicit false` での型確認もしていない（U-1 / U-2 / U-3 の型も同じ）。`e.replace f` の引数順、`DefinitionVal` / `RecursorVal` の欄名、`instantiateLevelParams` の extern 依存（`Util/InstantiateLevelParams.lean:18-19` の `e.replace replaceFn` までは読んだ）の細部は elaborate で確かめていない。
* `ci.type` 側の `userInliner env d.type` が `hdom` / `hbs` に影響しないことは確かめていない。
* `inlineDefs` 経路の保存、`rounds` / `pass` の保存、`inlAbbrevs` の保存が**成り立つ**ことは、読んだ範囲の見込みで、反例の探索も証明もしていない。「この調査では供給元・経路が見つからなかった」は導出不能の意味ではない。
* 実際の run が inline 枝を取る頻度、`hci` の供給、`GetEnvFrame` は範囲外。
* コンパイラ・共有定義・TRUSTED 境界・law は変えていない。`GenWF` は強化していない。mutant は使っていない（signature / defeq での棄却も行っていない）。
