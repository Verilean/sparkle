# DG-READERTRACE freeze rev9 — rev8 の changes requested を反映: A4 撤回、`Inst1Ph` は補題、U-R4e を U-R4e1 / U-R4e2 に分割（reviewer 判断待ち、Lean なし）

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt12` bffc1c67（rev8）。`DG_READERTRACE_FREEZE_REV5.md` の単位表、`..._REV8.md` の続き。**文書のみ。Lean は書いていない。未 elaborate。** 以下の Lean は提案の型で、通らない箇所は addendum で直す。
用語: 「見つからなかった / 未確認」は「この調査で辿った経路では見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant は signature / defeq での棄却であって意味的反例ではない。条件付きの結果は中間結果。

**この rev9 が台帳に与える差分: なし**（現在値 FG 102 / T1 54、今回 FG -0 +0 / T1 -0 +0）。§3 の `SigTyClosed` の +1 は**承認前の候補**で、現在値には入れていない。

## 0. rev8 に対する reviewer 判定と反映

| 判定 | 反映 |
|---|---|
| T1L-51 は canonical ledger（`par/t1-ledger-sync` 5e915142 `scripts/gen3/PREMISE_LEDGER.md` row 161）で `Inst1Agrees`（制限なし）。base の `ExternSpec:121` と一致 = 場合 X。A4 は不要 | **A4（`Inst1AgreesLetOk` / `Inst1Range` の付け替え案）を撤回**する。rev8 §2.2 の場合 Y と §2.3 の A4 の型、§2.4 の場合 Y の行は取り下げ。`Inst1Ph` は既存の等式 `Inst1Agrees` からの**補題**（§1）。新しい前提なし |
| S-B（T1L-53 を `EnvTypesClosed` に強めて ±0）は不可。`EnvTypesClosed` は `EnvTypesFVarFree` より強く、行を強めることは ±0 ではない | **S-B を撤回**。U-R4e を 2 つに分ける（§2、§3） |
| U-R4e1: 前提なしの部分は進めてよい | §2。rev9 の commit 後に Lean へ |
| U-R4e2: `instS` の型閉性を S-A の「名前付き条件 +1」として条件名・完全な型・domain を明記し、DG-ENV owner と調整する案を書く。Lean に置くのは承認後 | §3。**承認前の候補**。承認まで Lean に置かない |

## 1. `Inst1Ph` は補題（新しい前提なし）

```lean
-- Ph 版（trace が使う形。定義は rev8 §2.3 と同じ）
def Inst1Ph : Prop := ∀ (b a : Lean.Expr) (m m' : Nat), NoPh b = true → NoPh a = true →
    BvarLt (m + 1) b = true → BvarLt m' a = true → m ≤ m' →
    NoPh (b.instantiate1 a) = true ∧ BvarLt m' (b.instantiate1 a) = true

-- 構造補題（inst1Spec の offset 付き帰納。前提なし）
theorem inst1Spec_noPh : ∀ (b a : Lean.Expr) (off : Nat), NoPh b = true → NoPh a = true →
    NoPh (inst1Spec b a off) = true
theorem inst1Spec_bvarLt : ∀ (b a : Lean.Expr) (off m m' : Nat), BvarLt (m + 1 + off) b = true →
    BvarLt (m' + off) (liftSpec a 0 off) = true → m ≤ m' → BvarLt (m' + off) (inst1Spec b a off) = true

-- 既存の等式から補題として
theorem inst1Ph_of_agrees (h : Inst1Agrees) : Inst1Ph
```
* 使う既存: `Inst1Agrees`（`Tools/ShippingLetsExternSpec.lean:121`、T1L-51、既存行）、`inst1Spec`、`liftSpec_noPh` / `liftSpec_bvarLt`（U-R4c で証明済み）。bvar は `i < off` / `i = off`（`liftSpec a 0 off`）/ `i > off`（`i - 1`）の 3 分岐。
* domain: `Inst1Agrees` は制限なしなので `Inst1Ph` は全 `b a` で出る。T1L-51 の行は読み替えず、新しい行も足さない。
* 新ファイル: `Tools/ShippingGen5ReaderTraceInst1.lean`（+ `Tests/Gen5/ReaderTraceInst1Check.lean`）。共有定義は編集しない。
* `instRes` の反復（`forallE` の本体を取り `BvarLt` が 1 つずつ増える）は U-R8 の補題で、ここでは作らない。

## 2. U-R4e1: 前提なしの抽出子 Ph 版

rev5 の U-R4e のうち `machInstCallS?` の `ty` 成分以外。

```lean
-- spine 補題（`inlSpine e acc` は `argsAcc` と同じ形: `.app f a ↦ inlSpine f (a :: acc)`）
theorem inlSpine_ph {L : Nat} : ∀ (e : Lean.Expr) (acc : List Lean.Expr), NoPh e = true → BvarLt L e = true →
    (∀ a ∈ acc, NoPh a = true ∧ BvarLt L a = true) →
    ∀ a ∈ (inlSpine e acc).2, NoPh a = true ∧ BvarLt L a = true

-- machInstCall?: 結果の args 全部
theorem machInstCall?_ph {L} {senv e c kinds res args} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machInstCall? senv e = some (c, kinds, res, args)) : ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true

-- machInstCallS?: args 成分のみ（`ty` 成分は U-R4e2、§3）
theorem machInstCallS?_args_ph {L} {senv e c kinds ty args} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machInstCallS? senv e = some (c, kinds, ty, args)) : ∀ a ∈ args, NoPh a = true ∧ BvarLt L a = true

-- machRunApp?: dom / αs / inits は NoPh ∧ BvarLt L、body は NoPh ∧ BvarLt (L+1)
theorem machRunApp?_ph {L} {e dom αs inits body} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : machRunApp? e = some (dom, αs, inits, body)) :
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh αs = true ∧ BvarLt L αs = true) ∧
    (NoPh inits = true ∧ BvarLt L inits = true) ∧ (NoPh body = true ∧ BvarLt (L + 1) body = true)

-- memCall?: dom と 4 つの operand
theorem memCall?_ph {L} {natOf e combo aw dw dom ops} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops)) :
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ ∀ a ∈ ops, NoPh a = true ∧ BvarLt L a = true
```
* 使う既存: `ph_argsAcc` / `phArgs_getAppArgs`（`Reg.lean`）、`machInstCall?_spec` / `machInstCallS?_spec`（Ctl）。
* 前提: なし（`senv` への条件も無し。`machInstCallS?` の `args` は `inlSpine` の結果で `senv` の表の値に依存しない）。
* 新ファイル: `Tools/ShippingGen5ReaderTraceExtract.lean`（+ Check）。共有定義は編集しない。
* 台帳: FG -0 +0 / T1 -0 +0。

## 3. U-R4e2: `machInstCallS?` の `ty` 成分（承認前の候補。Lean に置かない）

### 3.1 内容
`ty` は入力式の部分項ではなく、`senv.instS c = some (kinds, ty)` の表（`structEnv env₀` 由来、`ty = ci.type`、`instSignatureS_type`（証明済み、`ShippingLetsSigTy.lean:67`））から来る。`PhPre (.instS …)` を引き継ぐには `NoPh ty ∧ BvarLt 0 ty` が要る。

* `NoPh ty`: 既存の T1L-53 `EnvTypesFVarFree env₀` から**補題で出る**（`NoFv e = true → NoPh e = true`、構造帰納、前提なし）。
* `BvarLt 0 ty`（型が閉じている）: `EnvTypesFVarFree` からは出ない（fvar の有無と loose bvar の有無は別）。この調査では供給元・経路が見つからなかった（`Environment` はこの development でモデル化されていない）。

### 3.2 S-A の名前付き条件（候補）
```lean
-- 候補名: SigTyClosed
def SigTyClosed (senv : StructEnv) : Prop :=
  ∀ (c : Lean.Name) (kinds : List MixedGateBinder) (ty : Lean.Expr),
    senv.instS c = some (kinds, ty) → BvarLt 0 ty = true

-- `NoPh` は T1L-53 から。両者から U-R4e2 が使う形を組む（補題）
def SigTyPh (senv : StructEnv) : Prop :=
  ∀ c kinds ty, senv.instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true
theorem sigTyPh_of (env : Environment) (hK : EnvTypesFVarFree env) (hC : SigTyClosed (structEnv env)) :
    SigTyPh (structEnv env)
```
* domain: `structEnv env₀` の `instS` 表が返す `(kinds, ty)` 全て。`env₀` は DG-ENV の C0 が運ぶ単一の環境。
* `SigTyClosed` は T1L-53 と同種（Lean カーネルが `addDecl` で定数の型を検査する事実）。ただし**この development では証明していない**ので、名前付き条件（仮説）として扱う。
* S-B（T1L-53 の文を強める）は撤回済み。既存行は変えない。

### 3.3 台帳（承認前の候補）
| 項目 | 内容 |
|---|---|
| 候補 | `SigTyClosed` を新しい名前付き条件として **+1**。T1 に数えるか FG（DG-ENV の環境の事実）に数えるかは reviewer 判断 |
| 現在値への影響 | **なし**（FG 102 / T1 54 のまま。承認まで計上しない） |
| 既存行の変更 | なし（T1L-53 は読み替えない） |
| 除去 | この調査では「実際に消える行」は見つからなかったので 0 |
| 取り下げ | 可（行を足すだけ。Lean 側は別ファイルの名前付き仮説） |

### 3.4 DG-ENV owner（`sparkle-gen5-dg-env`）との調整案
* 配置案: `SigTyClosed` を DG-ENV の C0（`inst`/`instS` の SigEq を全 world で運ぶ環境条件）の隣に、`EnvTypesFVarFree` とは**別の名前付き条件**として置く。C0 に畳み込むかは DG-ENV の freeze で決める。
* 依頼内容（`herdr-request --project` で DG-ENV 側へ。reviewer 承認後）: (1) `SigTyClosed` の完全な型と domain、(2) 台帳でどちらに数えるか、(3) DG-ENV の `EnvTypesFVarFree` を運ぶ箇所に併記できるか。
* readertrace 側は、条件が承認されるまで U-R4e2 を仮説付きの形でも Lean に置かない。承認されない場合は S-C（`machInstCallS?` の `ty` 成分と U-R8 を止める。`TraceGood` 全体は条件付きのまま閉じない）。

## 4. 進め方と今回の依頼（reviewer）
1. A4 撤回、`Inst1Ph` を補題（§1）、U-R4e1（§2）で進めることの確認。これらは台帳差分 0 で、承認済みの文の中の単位なので rev9 の commit 後に Lean へ進める。
2. U-R4e2: `SigTyClosed`（§3.2）を S-A の名前付き条件 +1 として出すこと、T1 / FG どちらに数えるか、DG-ENV 側への依頼（§3.4）。承認までは Lean に置かない。
3. その後: U-R5a/b（`RootFloatAgrees` T1L-52 と `LiftAgrees` T1L-50 の名前付き仮説に条件付き）→ U-R6 / U-R7 / U-R9 / U-R10 は新しい前提なしの見込み。U-R8 は `Inst1Ph`（本書 §1）+ `SigTyPh` + `InstSFieldsDet`（この調査では未確認で、U-R8 の freeze の前に調べる）。

## 5. この rev9 が主張しないこと
`SigTyClosed` が真であること、`TraceGood senv nDecl (readF senv n)` の成立、§1〜§3 の型が elaborate すること、台帳の数の変更。新しい law / TRUSTED 境界 / コンパイラ・共有定義の変更 / FG の縮小 / `GenWF` の強化は含まない。
