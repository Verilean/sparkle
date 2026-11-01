# Freeze: N3 の 9 件を狭めた原文で条件付き TRUSTED にする(Lean / Sparkle の二種版固定)

- Issue: `sparkle-trust-expr`(N3)。親 `sparkle-gen3-src-argw`。agent `tre1`、branch `kjob/tre1`、base `a386389d`(`kjob/nopay4`)。**文書のみ。Lean は書いていない。ビルドもしていない。**
- 根拠: `scripts/gen5/PREMISE_NOPAY_DECISION.md`(a386389d)§4.3・§4.3.1・§4.4、`sparkle-premise-nopay` の裁定 seq 5995(ユーザー委任で reviewer が推奨を採用)。**この裁定だけでは TRUSTED は有効にならない。この freeze を reviewer が個別に承認して初めて、次段の Lean 単位に進む。**
- 元の命題の出所: `kjob/g3aw-a24` 8fff703c(`Tools/ShippingLetsExternSpec.lean`、`Tools/Prototype/{RawNodeRangeLetOk,PreprocLetOk,LiftScalarModelLetOk,BoolMapModelLetOk,NormNodeRangeLetOk}.lean`、`Tools/ShippingLetsReaderInvMain.lean`、`Tools/ShippingGen3ArgSupply{13,14,15}.lean`)を `git show` で読んだ。
- 書き方の規則: 「見つからなかった」は「この調査では供給元・経路が見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant(棄却)は signature / defeq での棄却で、意味的反例ではない(この文書は mutant を扱わない。次段の Lean 単位で出る)。数えていない数は書かない。
- 台帳: FG 102 / T1 57(今回 FG -0 +0 / T1 -0 +0、文書のみ。次段の Lean 単位での変化は §5 に条件つきで書く。**T1 57 に T1L-50..59 の 9 行が含まれる件数は、この文書では数えていない**)。

## 1. 9 件の原文(番号は PREMISE_NOPAY_DECISION §4.4 末尾の表と同じ)

`LetOk` は `Tools.ShippingLetsAliasInv.LetOk`。「原文案」は未 elaborate(次段の Lean 単位で型検査される。型が通らなければ、その時点で止まって報告する)。

### #1 T1L-50 — 元のまま
```
LiftAgrees : Prop :=
  ∀ e, LetOk 0 e = true → e.liftLooseBVars 0 1 = liftSpec e 0 1 ∧ e.liftLooseBVars 1 1 = liftSpec e 1 1
```
- 元の命題との関係: **同じ**(`ShippingLetsExternSpec:115`、LC6 で既に `(0,1)`/`(1,1)` に絞られた形)。
- 合わせた callsite: `machConv` Elab.lean:3993、`machChain` Elab.lean:4158、`rootFloat` MachRawSurface.lean:201・205。

### #2 T1L-51 — 狭めた(`Inst1Agrees` → `Inst1Range`)
```
Inst1Range : Prop :=
  ∀ n b a, LetOk n b = true → LetOk n a = true → LetOk n (b.instantiate1 a) = true
```
- 元(`∀ b a, b.instantiate1 a = inst1Spec b a 0`)からは `inst1Range_of_agrees`(ExternSpec:128)で導ける。**元より弱い**(逆は言えない)。
- 合わせた callsite: `machInstanceS` の `inst` Elab.lean:4095、`machNorm` Elab.lean:4989・4992、`zetaAll` MachRawSurface.lean:220。`n` は一般のまま(`n = 0` で足りるかは未確認)。

### #3 T1L-52 — 狭めた(`RootFloatAgrees` → `RootFloatRange`)
```
RootFloatRange : Prop :=
  ∀ v, LetOk 0 v = true → LetOk 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = true
```
- 元(`∀ e, LetOk 0 e = true → rootFloat e = rootFloatS e`)からは `rootFloatRange_of_agrees`(ExternSpec:239)で導ける。**元より弱い**。
- 合わせた callsite: `machConv` Elab.lean:3990、`machChain` Elab.lean:4155(`let` の値)、`machineShape?` Elab.lean:5088。

### #4 T1L-54 — 狭めた(`ZeroLitAgrees` → `ZeroLitRange`。原文案)
```
ZeroLitRange : Prop :=
  ∀ (n : Nat) (e : Lean.Expr), LetOk n e = true →
    LetOk n (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true
```
- 元(`Tools/Prototype/PreprocLetOk.lean:143`。`zeroLit … e = e.replaceNoCache (…)` の等式。本体の続き(`replaceNoCache` に渡す関数)は PreprocLetOk:143 が正本で、ここには写さない)からは `zeroLit_ok`(同:151)が示す形。**元より弱い**。
- 合わせた callsite: `machineShape?` Elab.lean:5088(`zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat (machNorm senv e))`)。`n` を 0 に絞れるかは未確認なので一般のまま。

### #5 T1L-55 — 狭めた(`LiftLooseRange` を `s = 0` に)(原文案)
```
LiftLooseRange0 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), LetOk 0 e = true → LetOk 0 (e.liftLooseBVars 0 d) = true
```
- 元 `LiftLooseRange`(`RawNodeRangeLetOk:45`)は `∀ e s d`。`LiftLooseRange0` は元から `s := 0` で導ける(**元より弱い**)。
- 合わせた callsite: `rawNode` MachRawSurface.lean:100・102・104・120・122・124・148(`(s,d) = (0, n/i/j)`)。
- **注意(次段で確認すべき点)**: 元の `rawNode_ok`(RawNodeRangeLetOk:428)と `build_ok`(:235)の証明は `hl _ _ _` と書いてあり、証明項が `s = 0` しか使わないかを、この調査では項ごとには確認していない。`build_ok` の `hl regs 0 j`・`hl y 0 j`(:251・254)は `s = 0`。他の `hl _ _ _`(:496〜539)は未確認。もし `s ≠ 0` が要る箇所が出たら、#5 の形は成立せず、次段は止まって報告する。

### #6 T1L-56 — 狭めた(`LowerLooseRange` を `s = d` に)(原文案)
```
LowerLooseRangeEq : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), LetOk 0 e = true → LetOk 0 (e.lowerLooseBVars i i) = true
```
- 元 `LowerLooseRange`(`RawNodeRangeLetOk:49`)は `∀ e s d`。**元より弱い**。
- 合わせた callsite: `rawNode` MachRawSurface.lean:142(`t.lowerLooseBVars i i`)。証明側の使用は `hlo t i i ht`(RawNodeRangeLetOk:553)で `s = d = i`。

### #7 T1L-57 — 元のまま
```
BetaRange : Prop :=
  ∀ (f a : Lean.Expr), LetOk 0 f = true → LetOk 0 a = true → LetOk 0 (f.beta #[a]) = true
```
- 元の命題との関係: **同じ**(`RawNodeRangeLetOk:53`)。
- 合わせた callsite: `rawNode` MachRawSurface.lean:100・102・120(引数 1 個)。`MachRecUnfold.lean:57・161` の `beta`(引数個数が可変)は範囲外(§6)。

### #8 T1L-58 — 狭めた(`LiftScalarCorr` → `LiftScalarRange`)
```
LiftScalarRange (senv : StructEnv) : Prop :=
  ∀ (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) (w : Nat) (r : Lean.Expr),
    LetOk 0 dom = true → (∀ p ∈ vars, LetOk 0 p.2 = true) → LetOk 0 e = true →
    machLiftScalarN senv dom vars e = some (w, r) → LetOk 0 r = true
```
- 元(`LiftScalarModelLetOk:350`。`machLiftScalarN` の成功 → 燃料つきモデル `liftN` の成功)からは `liftScalarRange_of`(同:355)で導ける。**元より弱い**。`senv := structEnv env₀`。
- 合わせた callsite: `machNormApLift` Elab.lean:4806・4815、`machLiftScalar` 4768、`machLiftScalarN` の再帰(4664 ほか)。

### #9 T1L-59 — 狭めた(`BoolMapCorr` → `BoolMapRange`)
```
BoolMapRange (senv : StructEnv) : Prop :=
  ∀ (dom a : Lean.Expr) (wa : Nat) (body r : Lean.Expr),
    LetOk 0 dom = true → LetOk 0 a = true → LetOk 0 body = true →
    machBoolMap senv dom a wa body = some r → LetOk 0 r = true
```
- 元(`BoolMapModelLetOk:100`)からは `boolMapRange_of`(同:106。**`LiftScalarRange` も使う**)で導ける。**元より弱い**(ただし導出は #8 の `LiftScalarRange` を経由する。#8 と #9 を単独で見ない)。`senv := structEnv env₀`。
- 合わせた callsite: `machNormMap` Elab.lean:4911、自身の再帰 4835。

### 集計(数えたもの)
件数 9。元のまま 2(#1, #7)、狭めた 7(#2, #3, #4, #5, #6, #8, #9)。T1L-53(`EnvTypesFVarFree env₀`)は 9 件に入らない(台帳が「不明(kernel fact)」)。**この 9 件の「元より弱い」は、既存の補題で元から導ける(#2, #3, #4, #8, #9)か、量化子の特殊化(#5, #6)かのどちらかで、いずれも読んだ上での判断であり、Lean で再確認していない。**

## 2. 版固定(2 種類)

### (A) Lean 本体: #1 #2 #5 #6 #7(#4 も `Expr.replace` を通して結び付く)
- 記録するもの: `lean-toolchain` の内容。**確認した値(a386389d の `lean-toolchain`): `leanprover/lean4:v4.32.1`**。
- 対象の実体: #1 `Expr.liftLooseBVars`(C++ extern `lean_expr_lift_loose_bvars`、Expr.lean:1362)、#2 `Expr.instantiate1`(`lean_expr_instantiate1`、:1446)、#5 同 #1、#6 `Expr.lowerLooseBVars`(`lean_expr_lower_loose_bvars`、:1357)、#7 `Expr.beta`(:1624。`partial def betaRev` :1593 に依存)、#4 は `Expr.replace`(`lean_replace_expr`、ReplaceExpr.lean:16-19)。(行は v4.32.1 のソースで PREMISE_NOPAY_DECISION §4.4 が確認した値で、この文書では読み直していない。)

### (B) Sparkle コンパイラ側: #3 #4 #8 #9
- 記録するもの: file:line、その定義を含むコミット SHA、そのファイルの blob SHA。
- **今の候補(a386389d で `git rev-parse HEAD:<path>` と `grep -n` で確認)**:

| # | 定義 | file:line | blob SHA |
|---|---|---|---|
| 3 | `partial def rootFloat` | `Sparkle/Compiler/MachRawSurface.lean:198` | `bc4a2ed36808b568ebb12b2899c7b434163c6d18` |
| 4 | `def zeroLit` | `Sparkle/Compiler/MachRawSurface.lean:211` | 同上 |
| 8 | `partial def machLiftScalarN` | `Sparkle/Compiler/Elab.lean:4652` | `f796bd4ad7b6665ddf9f3d36e9b904ee096e3c85` |
| 9 | `partial def machBoolMap` | `Sparkle/Compiler/Elab.lean:4831` | 同上 |

- 定義を含むコミット SHA の候補: `a386389d3930f7072828f0a49cef788c746b09f1`(上の blob を持つ)。両 blob は 8fff703c でも同じ(PREMISE_NOPAY_DECISION §4.3 が確認済み)。ファイルを最後に変えたコミットは `MachRawSurface.lean` が `9b86eb38`、`Elab.lean` が `71e43864`。
- **正とするコミット**: T1 を組み立てる側(`sparkle-gen3-t1-assembly`)が最終定理を build するコミット。それまでは上の値は「今の候補」であって確定値ではない。build コミットの blob が上と異なる場合は、まず差分が #3/#4/#8/#9 の定義(本体、または呼ぶ関数)に及ぶかを見る。
- **定義が変わったときの再確認規則**: (A) の `lean-toolchain` が変わる、または (B) の 4 定義のどれかが変わった(本体の変更、または本体が呼ぶ関数の変更)ら、該当項目の TRUSTED を再確認する。再確認が済むまで、変わった項目を含む保証の文面を「確認済み」と書かない。ファイルの blob が変わっても当該定義が変わらないことは、差分で確認する(確認は reviewer の作業)。再確認は、命題の原文(§1)が新しい定義で偽にならないことの読み直しであって、再証明ではない。

## 3. 差分テストの範囲(検査であって証明ではない)

- 目的: 運用上の緩和。TRUSTED の 9 件が偽であることを**見つけることはできるが、真であることを示さない**。
- 範囲(案): reader が実際に見る Expr(コーパスのうち `LetOk 0` を満たすもの)について、(A) の 5 項目は、本体の関数(`liftLooseBVars` など)の結果が `LetOk` を保つか、#1 は `liftSpec` と等しいかを比べる。(B) の 4 項目は、`rootFloat` / `zeroLit` / `machLiftScalarN` / `machBoolMap` の結果が `LetOk` を保つかを比べる。
- 範囲外: コーパスに無い入力、`LetOk` を満たさない入力、(s,d) の全組(#5 #6 は呼び出される `s=0` / `s=d` のみ)。
- この freeze の時点では**実行していない**。実行する単位は別(次段の Lean 単位とは独立)。結果は「N 件の入力で食い違いなし」の形で書き、「正しい」とは書かない。

## 4. 次段の Lean 単位(狭めた命題を前提に、元の利用箇所を通す)

新規ファイル `Tools/ShippingGen3TrustExpr.lean`(namespace `Tools.ShippingGen3TrustExpr`)。`lakefile.lean` に `lean_lib` を追加してよい。共有定義・compiler は編集しない。`sorry` / `axiom` / `native_decide` は使わない。以下は**型案**で未 elaborate。

新しい定義(§1 の原文そのもの): `LiftLooseRange0`(#5)、`LowerLooseRangeEq`(#6)、`ZeroLitRange`(#4)。既存の定義を再利用する: `LiftAgrees`(#1、ExternSpec:115)、`Inst1Range`(#2、ReaderInvMain:62)、`RootFloatRange`(#3、ReaderInvMain:53)、`BetaRange`(#7、RawNodeRangeLetOk:53)、`LiftScalarRange`(#8、NormNodeRangeLetOk:146)、`BoolMapRange`(#9、同:152)。

補題(型案。8fff703c の同名補題の仮説を置き換えるだけで、結論は同じ):

```
-- U1: rawNode_ok の仮説を (#5, #6, #7) に置き換える
theorem rawNode_ok' (hl : LiftLooseRange0) (hlo : LowerLooseRangeEq) (hb : BetaRange)
    (pm : Name → Option Nat) :
    ∀ e e', LetOk 0 e = true → Sparkle.Compiler.MachRawSurface.rawNode pm e = some e' → LetOk 0 e' = true

theorem rawNodeRange_of' {senv : StructEnv} (hl : LiftLooseRange0) (hlo : LowerLooseRangeEq)
    (hb : BetaRange) : RawNodeRange senv

-- U2: zeroLit 側
theorem readSub_letOk' (senv : StructEnv) (F : PureFacts senv) (hz : ZeroLitRange) (en : Lean.Expr)
    (hen : LetOk 0 en = true) : <readSub_letOk(ArgSupply13:36)の結論と同じ>
theorem siteLetOk_of' (senv : StructEnv) (F : PureFacts senv) (hz : ZeroLitRange) (en : Lean.Expr)
    (hen : LetOk 0 en = true) : SiteLetOk senv en

-- U3: PureFacts / LetOk 0 en(#2, #3 を Range のまま取る)
theorem pureFacts_structEnv' (env₀ : Lean.Environment) (hla : LiftAgrees) (hia : Inst1Range)
    (hrt : RootFloatRange) (hK : EnvTypesFVarFree env₀) : PureFacts (structEnv env₀)
theorem letOk_norm_structEnv' (env₀ : Lean.Environment) (hia : Inst1Range)
    (hraw : RawNodeRange (structEnv env₀)) (hnode : NormNodeRange (structEnv env₀))
    (e en : Lean.Expr) (he : LetOk 0 e = true) (hex : execNorm (structEnv env₀) e = some en) :
    LetOk 0 en = true

-- U4: NormNodeRange(#8, #9)
theorem normNodeRange_structEnv' (env₀ : Lean.Environment)
    (hls : LiftScalarRange (structEnv env₀)) (hbc : BoolMapRange (structEnv env₀)) :
    NormNodeRange (structEnv env₀)

-- U5: 最終(siteLetOk_structEnv'(ArgSupply15:30)の置き換え)
theorem siteLetOk_structEnv'' (env₀ : Lean.Environment) (hla : LiftAgrees) (hia : Inst1Range)
    (hrt : RootFloatRange) (hK : EnvTypesFVarFree env₀) (hz : ZeroLitRange)
    (hl : LiftLooseRange0) (hlo : LowerLooseRangeEq) (hb : BetaRange)
    (hls : LiftScalarRange (structEnv env₀)) (hbc : BoolMapRange (structEnv env₀))
    (e en : Lean.Expr) (he : LetOk 0 e = true) (hex : execNorm (structEnv env₀) e = some en) :
    SiteLetOk (structEnv env₀) en
```

- 証明の方針(型案の根拠。elaborate していない): U3 は `pureFacts_of` を 8fff703c と同じ形で使い、`inst1Range_of_agrees hia` を `hia` に、`rootFloatRange_of_agrees hrt` を `hrt` に置き換える。U4 は `normNodeRange_of hls hbc` を直接使う。U2 は `zeroLit_ok hz 0 _ …`(ArgSupply13:42)を `hz 0 _ …` に置き換える。**U1 は `rawNode_ok` の証明の書き直しを含む(§1 #5 の注意)。ここが唯一、元の証明がそのまま通らない可能性のある単位**。
- 追加の前提・TRUSTED・law は**増えない**(仮説は §1 の 9 件と `EnvTypesFVarFree env₀` のみ)。前提 delta が 9 件の外に出たら自動受理せず止まって coder に報告する。
- 受理: freeze 承認後、proof-accept(manifest は coder が作る)。型・意味の変更、検査の失敗は自動受理しない。

## 5. 台帳の差分

台帳の版は PREMISE_NOPAY_DECISION が読んだ T1 `51ebec20`(`scripts/gen3/PREMISE_LEDGER.md` §3 の表)、FG `b54e343d`。

| ID | 今の欄 | この freeze の判定での移動先 | 備考 |
|---|---|---|---|
| T1L-50 | payer `sparkle-gen3-src-argw`、実 run で払える `no`、class `obligation` | payer `sparkle-trust-expr`、class `trusted (N3, conditional)` | 命題は変わらない(#1) |
| T1L-51 | 同上 | 同上 | 命題を `Inst1Range` に差し替え(#2) |
| T1L-52 | 同上 | 同上 | `RootFloatRange`(#3) |
| T1L-54 | 同上 | 同上 | `ZeroLitRange`(#4) |
| T1L-55 | 同上 | 同上 | `LiftLooseRange0`(#5) |
| T1L-56 | 同上 | 同上 | `LowerLooseRangeEq`(#6) |
| T1L-57 | 同上 | 同上 | `BetaRange`(#7。命題は変わらない) |
| T1L-58 | 同上 | 同上 | `LiftScalarRange`(#8) |
| T1L-59 | 同上 | 同上 | `BoolMapRange`(#9) |
| T1L-53 | `unknown` | **変更なし** | 9 件に入らない |

- **FG 側: 変更なし**(この調査では対応する FG 行は見つからなかった)。FG 102 → 102(-0 +0)。
- **T1 57 が変わるか**: 行は 9 件とも**残る**(TRUSTED は「払われた」ではなく「条件付きで受け入れた」)。台帳の数え方が「TRUSTED の行を T1 の残りから除く」なら T1 -9 +0 になりうるが、**57 に 9 行が全て含まれるかを数えていないため、この数は「未計数」**。残す数え方なら T1 -0 +0。**どちらの数え方にするかは reviewer の判断(§7 の質問 1)。**
- ID は増減しない。行の統合・新 ID は作らない。

## 6. 範囲外(この freeze が閉じないもの)

PREMISE_NOPAY_DECISION §4.3.1 のとおり、9 件を TRUSTED にしても T1 が閉じるとは限らない。次は**今回の範囲外で、別の監査・判断資料が要る**(この調査で辿った候補経路では未確認):
1. `MachTupleIn.lean:87`(`packTupleInputs`。`liftLooseBVars` (1,1)・(0,1))の入力が `LetOk 0` か。
2. `MachRecUnfold.lean:57・161` の `beta`(引数の個数が可変。#7 は 1 引数)。
3. elaboration 側の `instantiate1`(Elab.lean:6206 ほか。`fvar` で呼ぶ)。#2 は reader 側の呼び出しだけを覆う。
4. `ReadTyped` の残り 3 要素(`ConvKind`、`LetSrcKinds`、`CallSrcKinds`)と `argWidthAt_of_closingRun` までの組み立て。
5. `Inst1Range`・`ZeroLitRange` の `n` が `n = 0` で足りるか(#2・#4 は `n` 一般のまま)。

## 7. reviewer への質問
1. 台帳の数え方: TRUSTED にした 9 行を T1 の残り件数から除くか、残すか(§5)。
2. #5 の形(`s = 0`)が U1 で成立しない場合、止まって報告する、でよいか(代替は元の `LiftLooseRange` 全体を TRUSTED に戻すことで、これは「狭める」の取り消しなので、ここで勝手に選ばない)。
3. (B) の「正とするコミット」を T1 組み立ての build コミットとする規則でよいか。

## 8. この文書が確認したこと / していないこと
- 確認した: `lean-toolchain` の値(`leanprover/lean4:v4.32.1`)、a386389d での 4 定義の file:line と 2 つの blob SHA、8fff703c の 9 命題の原文と `siteLetOk_structEnv'`・`siteLetOk_structEnv`・`siteLetOk_of`・`rawNode_ok` 等の型(`git show` で読んだ)。
- していない: Lean の elaborate / ビルド、Lean v4.32.1 のソース行の読み直し(PREMISE_NOPAY_DECISION §4.4 の記載を引用)、原文案(#4 #5 #6)の型検査、`rawNode_ok` の `hl _ _ _` の全使用箇所が `s = 0` か、差分テストの実行、T1 57 の内訳の計数。
