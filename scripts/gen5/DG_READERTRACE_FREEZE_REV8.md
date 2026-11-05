# DG-READERTRACE freeze rev8 — rev5 の続き: A4（`Inst1Range` の付け替え案）と `SigTyPh` の提案（reviewer 判断待ち、Lean なし）

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt12` 830f0c05（U-R4b / U-R4c / U-R4d まで Pod build 済み、clean build は coder）。`DG_READERTRACE_FREEZE_REV5.md` §2 の A4 / `SigTyPh`、`..._REV7.md` の続き。**文書のみ。Lean は書いていない。未 elaborate。** 以下の Lean は提案の型で、通らない箇所は addendum で直す。
rev5 §1 の止まる条件に従い、`SigTyPh` が要る単位 **U-R4e**（rev5 の定義どおり、`machInstCallS?` の結果成分）の直前で止めた。承認されるまで U-R4e 以降には Lean を置かない。
用語: 「見つからなかった / 未確認」は「この調査で辿った経路では見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant は signature / defeq での棄却であって意味的反例ではない。条件付きの結果は中間結果。

**この rev8 が台帳に与える差分: なし**（FG 102 / T1 54、今回 FG -0 +0 / T1 -0 +0）。以下の選択肢ごとの差分は、承認された場合に初めて起きる**見込み**で、台帳の再計数ではない。

## 0. 前提知識なしの説明

`TraceGood`（reader `readF` の各呼び出しが、状態の不変条件を保ち、出力式がプレースホルダ `_machIn/_machInst/_machSlot/_machLet` の範囲に収まり、loose bvar を持たないことの帰納）は、**入力式が `NoPh`（プレースホルダ fvar を含まない）かつ `BvarLt L`（loose bvar の添字が `L` 未満）**であることを各呼び出しの前提（`PhPre`）に持つ。reader が再帰呼び出しに渡す式（`app` の `f` と `a`、`letE` の各部分）は、入力の部分項かその構造的な加工なので、この前提は引き継げる。例外が 2 つある。

1. **`machInstCallS?` の結果 `ty`**（構造体インスタンスの型。`senv.instS c = some (kinds, ty)` の `ty` で、環境 `structEnv env₀` の定数の宣言型）。これは入力の部分項ではなく環境から来る式なので、`PhPre (.instS …)` が要求する `NoPh ty ∧ BvarLt (env.length+nDecl) ty` を引き継げる元が、この調査で辿った経路にはなかった。
2. **`instRes ty args`**（`ty` の `forallE` の本体に引数を `Expr.instantiate1`（C++ extern）で代入して結果型 `resTy` を作る）。`resTy` の spine の引数は次に `cConv` の入力になるので、`NoPh ∧ BvarLt (env.length+nDecl)` が要る。`instantiate1` の中身は Lean からは見えないので、振る舞いについての仮定（等式）が必要。

## 1. `SigTyPh`（U-R4e の前に要る環境条件）

### 1.1 内容
```lean
def SigTyPh (senv : StructEnv) : Prop :=
  ∀ c kinds ty, senv.instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true
```
* `NoPh ty`: 既存の T1L-53 `EnvTypesFVarFree env₀`（`∀ n ci, env.find? n = some ci → NoFv ci.type = true`、`Tools/ShippingLetsSigTy.lean:63`、台帳が「不明（kernel fact）」とする行）から**補題で出る**（`NoFv e = true → NoPh e = true` は `NoFv` が fvar を全て拒否し `NoPh` は一部の名前の fvar だけを拒否するため。構造帰納、新規補題、前提なし）。
* `BvarLt 0 ty`（型が閉じている＝loose bvar を持たない）: `EnvTypesFVarFree` からは出ない（fvar の有無と loose bvar の有無は別）。Lean カーネルが定数の型を型検査する（loose bvar を含む式は型推論で拒否される）ことに由来する **kernel の事実**で、この development では `Environment` をモデル化していないので証明できない。T1L-53 と同じ種類・同じ根拠（`addDecl`）。
* domain: `structEnv env₀` の `instS` 表が返す `(kinds, ty)` 全て（`ty` は `instSignatureS_type`（証明済み、`ShippingLetsSigTy.lean:67`）により `env₀.find? c = some ci` の `ci.type`）。

### 1.2 選択肢
| 案 | 内容 | 台帳（見込み） | 影響・コスト | 可逆性 |
|---|---|---|---|---|
| **S-A** | 新しい名前付き条件 `SigTyClosed senv := ∀ c kinds ty, senv.instS c = some (kinds, ty) → BvarLt 0 ty = true`（`NoPh` は T1L-53 から補題）。`sigTyPh_of` で `SigTyPh` を組む | **T1 または FG（DG-ENV 側と見る案）に +1**。数える側は reviewer 判断 | 既存の行は変えない。DG-ENV Issue（`sparkle-gen5-dg-env`、環境の事実の持ち主）に新しい行が増える | 取り下げ可（行を足しただけ。Lean 側は別ファイルの名前付き仮説） |
| **S-B**（推奨） | T1L-53 の文に「閉じている」を足す: `EnvTypesClosed env := ∀ n ci, env.find? n = some ci → NoFv ci.type = true ∧ BvarLt 0 ci.type = true`。既存の使用箇所は `.1` で従来どおり。Lean の既存定義 `EnvTypesFVarFree` は**編集しない**（`EnvTypesClosed` を新ファイルに置き、`EnvTypesFVarFree` を補題で導く） | **±0（既存行 T1L-53 の文の強化）**。「同じ型・domain の行が実際に消えたときだけ計上」の規則上、増えも減りもしない | 行の文が変わる（変更行として計上）。根拠は同じ `addDecl` のカーネル検査で 2 つの性質（fvar 無し、loose bvar 無し）を並べるだけ。DG-ENV の持ち主との合意が要る | 取り下げ可（新ファイルの定義を捨てれば元の文に戻る） |
| S-C | 何もしない | 0 | U-R4e の `machInstCallS?` 部分と U-R8、したがって `TraceGood` 全体が条件付きのまま閉じない（`PhPre (.instS …)` を作れない）。`machRunApp?` / `machInstCall?` / `memCall?` の Ph 版（U-R4e の他の部分）は `SigTyPh` なしで進められる（分割案、下記） | — |

推奨は S-B（台帳が増えない、種類が同じ）。ただし既存行の文を変えるので DG-ENV の持ち主と reviewer の合意が先。合意が取れなければ S-A。

分割案: U-R4e を **U-R4e1**（`machRunApp?` / `machInstCall?` / `memCall?` の結果成分が `NoPh ∧ BvarLt (env.length+nDecl)`。新しい前提なし）と **U-R4e2**（`machInstCallS?` の `ty` 成分。`SigTyPh` が要る）に分ける。承認前でも U-R4e1 は進められるが、rev5 の単位の定義を変えるので、これも承認を求める。

## 2. A4（`Inst1Range` の付け替え案）

### 2.1 この base で読んだこと（行の現行の文は未確認）
* この base の Lean が名前付き仮説として持つのは `Inst1Agrees : Prop := ∀ b a, b.instantiate1 a = inst1Spec b a 0`（`Tools/ShippingLetsExternSpec.lean:121`、制限なしの等式。台帳の T1L-51）。そこから `inst1Range_of_agrees : Inst1Agrees → Inst1Range`（同 128 行、証明済み）で `PureFacts.inst1` が作られる。
* `par/ptot-m4` の `scripts/gen3/TRUST_EXPR_FREEZE.md`（#2）と `scripts/gen5/PREMISE_NOPAY_DECISION.md`（§4.4）は、T1L-51 を `Inst1Agrees` から**弱い `Inst1Range`（`LetOk n b → LetOk n a → LetOk n (b.instantiate1 a)`）に差し替える**案を書いている。その案がいまの台帳の行（T1 54）に入っているか、この調査では**確認できなかった**（台帳本体はこの worktree にない）。rev5 §2 は「現行は T1L-51（`Inst1Range`）」と書いたが、この base の Lean 上の根拠は `PureFacts.inst1` が `Inst1Range` を取ることだけで、行の文そのものを確かめたものではない。

### 2.2 場合分け
* **場合 X: 台帳の T1L-51 が（この base の Lean と同じ）制限なしの `Inst1Agrees` のまま**。trace が要る Ph 版は**補題で出る**。新しい前提・変更・付け替えは**ない**（A4 は不要）。
* **場合 Y: T1L-51 が `Inst1Range` に差し替え済み（または差し替える）**。`Inst1Range` は「プレースホルダを作らない（`LetOk` の保存）」だけで、trace が要る `NoPh ∧ BvarLt` の保存は出ない。ここで A4 が要る。

### 2.3 型
```lean
-- trace が使う Ph 版（どちらの場合も同じ結論。補題として証明する対象）
def Inst1Ph : Prop := ∀ (b a : Lean.Expr) (m m' : Nat), NoPh b = true → NoPh a = true →
    BvarLt (m + 1) b = true → BvarLt m' a = true → m ≤ m' →
    NoPh (b.instantiate1 a) = true ∧ BvarLt m' (b.instantiate1 a) = true

-- 場合 X（新しい前提なし）
theorem inst1Ph_of_agrees (h : Inst1Agrees) : Inst1Ph

-- 場合 Y（A4: 場合 Y の行の置換案）
def Inst1AgreesLetOk : Prop := ∀ (n : Nat) (b a : Lean.Expr), LetOk n b = true → LetOk n a = true →
    b.instantiate1 a = inst1Spec b a 0
theorem inst1Range_of_agreesLetOk (h : Inst1AgreesLetOk) : Inst1Range          -- inst1Spec_ok（証明済み）
theorem inst1Ph_of_agreesLetOk (h : Inst1AgreesLetOk) : Inst1Ph                -- NoPh ⇒ LetOk n（noPh_letOk）で domain に入る
```
証明の中身（どちらの場合も新しい前提なし）: `inst1Spec b a off` について `NoPh b ∧ NoPh a → NoPh (inst1Spec b a off)` と `BvarLt (m+1+off) b → BvarLt (m'+off) (liftSpec a 0 off) → BvarLt (m'+off) (inst1Spec b a off)`（`m ≤ m'`）を `inst1Spec` の構造帰納で示す（bvar は `i < off` / `i = off`（`liftSpec a 0 off`、既存の `liftSpec_noPh` / `liftSpec_bvarLt`）/ `i > off`（`i - 1`）の 3 分岐）。`instRes` の反復（`forallE` の本体を取り、`BvarLt L` の次の本体は `BvarLt (L+1)`）は U-R8 の補題。
* domain: A4 の等式の domain は `LetOk n b ∧ LetOk n a`（`Inst1Range` と同じ domain）。`Inst1Agrees`（場合 X）の domain はその上位集合。trace が使う入力は `NoPh`（`noPh_letOk` で `LetOk n`）なので domain に入る。
* 正しさの根拠（読み取りで、形式証明ではない）: `instantiate1` の C++ 側（`instantiate.cpp:44-53`）が `inst1Spec`（offset 付き、置換する式を offset だけ持ち上げる）と構造一致することは N3 設計 §1.2（`bb665fa2:scripts/gen3/N3_EXTERN_MIN.md`）で読み取り済み。既知の限界（`unsigned` 切り捨て、実行バイナリがその source から作られていること）は N3 と同じ。

### 2.4 crosswalk と台帳（見込み）
| 項目 | 内容 |
|---|---|
| 既存 ID | T1L-51（`Inst1Agrees` / 差し替え案 `Inst1Range`）。T1L-50 `LiftAgrees` と同種（C++ extern との一致） |
| 場合 X | 新規 0・変更 0・除去 0。**T1 ±0** |
| 場合 Y・A4 採用 | T1L-51 の文を `Inst1Range` → `Inst1AgreesLetOk` に置換（range → 等式。**N3 の T1L-54/55/56 と同じ形の置換、reviewer の結論「range→等式の置換で純 0」に倣う**）。**T1 ±0（変更行 1）**。domain は `Inst1Range` と同じ |
| 場合 Y・A4 不採用 | 名前付き条件 `Inst1Ph`（上の型）を新規に持つ。**+1**（T1 か FG かは reviewer 判断）。`Inst1Range` の行は残る |
| どの案でも | この調査では「実際に消える行」は見つからなかったので、除去の計上は 0 |

## 3. 今回の依頼（reviewer）
1. 場合 X / Y のどちらかの確認: 台帳の T1L-51 の現行の文（`Inst1Agrees` 制限なし か `Inst1Range`）。X なら A4 は撤回し、`Inst1Ph` は補題として U-R8 で作る。
2. Y の場合、A4（`Inst1AgreesLetOk`）の採否。
3. `SigTyPh`: S-A / S-B / S-C のどれにするか。S-B は DG-ENV の持ち主との合意が要る。分割案 U-R4e1 / U-R4e2 の採否。
4. 承認後の進め方: 承認された範囲で U-R4e1（承認なら）→ U-R5a/b（`RootFloatAgrees` T1L-52 と `LiftAgrees` T1L-50 の名前付き仮説に条件付き。新しい前提なし）→ U-R6 / U-R7 / U-R9 / U-R10 は新しい前提が要らない見込みで進められる。U-R8 は上記 + `InstSFieldsDet`（`GroupsPh` 用。この調査では未確認で、U-R8 の freeze の前に調べる）。

## 4. この rev8 が主張しないこと
`SigTyPh` / `Inst1Ph` / A4 が真であること（カーネルの事実と C++ extern の振る舞いについての仮定で、証明も差分テストも与えていない）、`TraceGood senv nDecl (readF senv n)` の成立、U-R4e 以降の型の elaborate、台帳の数の変更。新しい law / TRUSTED 境界 / コンパイラ・共有定義の変更 / FG の縮小 / `GenWF` の強化は含まない。
