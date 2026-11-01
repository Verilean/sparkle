# RT abbrev S1 freeze rev2: `inlAbbrevs` の `Expr.replace`（U-1）と `Expr.headBeta`（U-2、振る舞い一致形）

Issue: `sparkle-rt-abbrev-s1`（親 `sparkle-gen5-dg-readertrace`）。rev1 = 796b3ff4。調査: `scripts/gen5/RT_INLINE_SURVEY.md` §1.3（S1）。既存の書き方: `Tools/Assume/N3Extern.lean`。ユーザー向け判断資料: `scripts/gen5/RT_ABBREV_S1_DECISION.md`。
**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0。未登録。登録時の増減は §5: FG ±0、T1 純 +1）。**
この文書は、台帳前提の追加・付け替えの候補と TRUSTED 境界の文を含むので reviewer の承認が要る freeze（その後、新しい T1 のためユーザー判断）。承認が出るまで Lean 実装（`Tools/Assume/` への登録を含む）には進まない。Lean ソースは何もコミットしていない（scratch のみ）。

方針（ユーザー）: 「C++/opaque の振る舞いは小さな明示的仮定にして、合成法則はそこから証明する」。

## 改訂履歴

| rev | SHA | 内容 |
|---|---|---|
| rev1 | 796b3ff4 | 初版。U-1 一般形で `ZeroLitAgrees0` を導出、U-2 は保存形 `HeadBetaPh0` を推奨 |
| rev2 | （この文書をコミットした SHA） | reviewer 変更依頼（796b3ff4）への対応。(1) U-1 は一般形 `ReplaceAgrees` で `ZeroLitAgrees0` と置換（純差分 0）をそのまま採用。(2) U-2 の `HeadBetaPh0`（保存則を仮定）は取り下げ。`NoPh e ∧ BvarLt 0 e` の入力に限った一致形 `HeadBetaAgrees0 : e.headBeta = headBetaSpec e` を唯一の案とし、保存（`NoPh ∧ BvarLt 0`）を**定理として証明**（scratch、sorry なし）。(3) `inlAbbrevs_ph` を `ReplaceAgrees` と `HeadBetaAgrees0` から証明（scratch、sorry なし）。(4) 型を `set_option autoImplicit false` で再 elaborate し `#check` を §4 に写し直し。(5) C++ / core の根拠を §1.3 / §2.4 に再引用（v4.32.1 取得ソースを今回再読、sha256 先頭は rev1 と同じ）。(6) 限定形 `AbbrevReplaceAgrees`、`HeadBetaPh`/`HeadBetaPh0`、3 本分割 A は選択肢から外した（理由は §2.5） |

## 0. 要約

| 項目 | 内容 | 結果 |
|---|---|---|
| U-1 `ReplaceAgrees` | `Expr.replace f e = Expr.replaceNoCache f e`（全 `f`, `e`） | 既存 `ZeroLitAgrees0`（T1L-54）を scratch で sorry なしに導出 → 付け替えで **T1 ±0** |
| U-2 `HeadBetaAgrees0` | `NoPh e ∧ BvarLt 0 e` の入力で `e.headBeta = headBetaSpec e`（`headBetaSpec` は Lean の全域なモデル） | **T1 +1**。保存は定理（`headBetaSpec_good` / `headBeta_good`）、scratch で sorry なし |
| 合成 `inlAbbrevs_ph` | `DeclValuePh env`（既存の仮説候補）+ `ReplaceAgrees` + `HeadBetaAgrees0` から `inlAbbrevs` が `NoPh ∧ BvarLt 0` を保つ | scratch で sorry なしに証明済み |
| 純差分 | FG ±0、T1 54 → 55（純 +1） | 登録・付け替えは reviewer 承認、新しい T1 はユーザー判断 |

## 1. U-1: `Expr.replace` と `Expr.replaceNoCache` の一致

### 1.1 完全型（scratch で elaborate、`set_option autoImplicit false`、§4 に出力）

```lean
/-- (U-1 一般形) -/
def ReplaceAgrees : Prop :=
  ∀ (f : Lean.Expr → Option Lean.Expr) (e : Lean.Expr), e.replace f = e.replaceNoCache f

/-- (U-1 限定形。rev2 では採らない。比較のためだけに残す) `inlAbbrevs` が使う置換関数だけ。`abbrevFn` は `Tools.ShippingInlCand`（Elab.lean 3379–3381 のラムダに名前を付けたもの） -/
def AbbrevReplaceAgrees : Prop :=
  ∀ (env : Lean.Environment) (e : Lean.Expr),
    e.replace (Tools.ShippingInlCand.abbrevFn env) = e.replaceNoCache (Tools.ShippingInlCand.abbrevFn env)
```

* `abbrevFn env` と production のラムダ `fun x => match x with | .const c [] => userAbbrev? env c | _ => none` が関数として等しいことは `funext x; cases x <;> rfl` で scratch に通った（マッチャ補助定義が別なので syntactic には別物）。
* 一般形から限定形は自明（`fun env e => h _ e`）。

### 1.2 一般形から `ZeroLitAgrees0` を導けるか（scratch、sorry なし）

```lean
theorem zeroLit_of_replaceAgrees (h : ReplaceAgrees) : Tools.Assume.N3Extern.ZeroLitAgrees0 := by
  intro e _
  unfold Sparkle.Compiler.MachRawSurface.zeroLit
  exact h _ e
```

* `zeroLit` は `e.replace fun x => …` で、`ZeroLitAgrees0` の右辺 `replaceNoCache zeroLitF` の `zeroLitF` と**ラムダが定義上一致**するので `exact h _ e` で閉じた（`LetOk 0` の仮定は使わない）。axioms: `propext` のみ。
* したがって一般形を登録し、`ZeroLitAgrees0` を定理に降格（`Tools/Assume/N3Extern.lean` の A3 を定理に置き換える）なら **T1 ±0**（T1L-54 を外し、`ReplaceAgrees` を 1 件足す）。`ZeroLitAgrees0` を使う側（`Tools/ShippingN3ExternAgree.lean` 等）は、仮説の型を `ReplaceAgrees` に付け替えるか、`zeroLit_of_replaceAgrees` を挟む。付け替えの編集範囲は未計測（実装時に数える）。これは台帳の付け替えで reviewer の承認事項。

### 1.3 根拠（C++ の読み。toolchain v4.32.1 = commit f054605a、`lean --version` と一致）

`Lean/Util/ReplaceExpr.lean:16-19` で `replace f e := replaceImpl f e`、`replaceImpl` は `@[extern "lean_replace_expr"] opaque`。論理には本体がない。構造版 `replaceNoCache`（:22-35）は通常の `def`。

C++（toolchain に `src/kernel` は無いので、tag `v4.32.1` を取得して読んだ。sha256 先頭: `replace_fn.cpp` 2edfa172…。N3_EXTERN_MIN.md の記録と一致。取得ファイルはコミットしない）:

| 箇所 | 読み |
|---|---|
| `replace_fn.cpp:151-154` `lean_replace_expr` | `replace_fn(f)(e)` を呼ぶ（`f` は Lean の関数、`lean_apply_1`） |
| :97-113 `replace_fn::apply` | `e` が共有なら `m_cache`（キーは `e.raw()` ポインタ）を引く。無ければ `f e` を呼び、`some r` ならそれを返す（共有ならキャッシュに保存）。`none` なら :115-143 で子に再帰 |
| :115-143 の再帰 | `Const/Sort/BVar/Lit/MVar/FVar` はそのまま、`MData/Proj` は 1 子、`App` は関数・引数、`Pi/Lambda` は domain・body、`Let` は型・値・本体。`update_*` で再構成。**子に渡す引数は式だけ（深さのオフセットを持たない版）。`replaceNoCache` の match と 1 対 1 に対応する**（`f e` が `some` なら置換して子へは降りない、`none` なら子へ降りる、までが同じ） |
| 差分 | (a) キャッシュ: 共有ノードの結果をポインタで再利用する。`f` が純関数なら同じノードへの結果は同じなので、キャッシュは結果を変えない。(b) `update_*` は子が変わらなければ元のノードを再利用するが、構造としては同じ式 |

読みの限界（主張しないこと）:
* 形式証明ではなく、ソースを読んだ照合。
* キャッシュが結果を変えないのは `f` が純関数であることに依る。Lean の `f : Expr → Option Expr` は純関数なので成り立つはずだが、ポインタ同一性に基づくキャッシュの正しさ（`lean_object*` の再利用・アドレスの再利用が起きない前提）は C++ の実行時の性質で、この読みでは確かめていない（`m_cache` は 1 回の呼び出しの間だけ生き、キーのノードは `e` から到達可能で解放されない、という読みに留まる）。
* 実行中のバイナリがこのソースから作られたこと（commit 文字列の一致のみ）。toolchain 更新時は再確認。
* `update_*` が `mdata` / `proj` / 束縛の binder 名・binderInfo・`nondep` フラグを保つことは、`replaceNoCache` 側の `updateXxx!` との一致として読んだが、`update_let` の `nondep` の扱いは細部を再確認していない。
* scratch の実行時照合（証明ではない）: コンパイル済みの `Expr.replace` と `replaceNoCache` が 8 個の式（入れ子の束縛・`letE`・`mdata` を含む）で `Expr.equal` 一致した。例の少なさは根拠にならない。

### 1.4 範囲について（使う向き・範囲）

* 使う向き: `inlAbbrevs` の証明で `e.replace f` を `e.replaceNoCache f` に**書き換える**一方向だけ。
* 一般形は `f` と `e` を全称にする。C++ の読みは `f` の中身にも `e` の形にも依らない（純関数であること以外）ので、範囲を狭める根拠が読みからは出ない（`LetOk 0` のような `e` の制限は読みでは不要）。限定形は「使う範囲」には合うが、`ZeroLitAgrees0` を導出できず T1 が +1 余分に付くので、rev2 では一般形を採る（reviewer の変更依頼 1 に従う）。
* 領域をさらに `NoPh e ∧ BvarLt L e` に狭める形は作れる（`inlAbbrevs` が呼ぶ入力はそれ）が、C++ の読みがその領域を使わないので、狭めても支えが増えない。本文では採らない。

## 2. U-2: `Expr.headBeta` の振る舞い一致形

### 2.1 何が opaque か

`headBeta e := let f := e.getAppFn; if f.isHeadBetaTargetFn false then betaRev f e.getAppRevArgs else e`（`Lean/Expr.lean:1658-1660`）。`getAppFn` / `isHeadBetaTargetFn` / `getAppRevArgs`（private な補助 `getAppRevArgsAux`）は通常の `def`。`betaRev`（:1593-1617）は core の **`partial def`**（論理では本体が見えない）で、中で `Expr.instantiate`（extern）と `Expr.instantiateRange`（extern）と `mkAppRevRange`（通常の `def`、private 補助 `mkAppRevRangeAux`）を使う。`headBeta` では `useZeta := false`, `preserveMData := false`。

### 2.2 全域なモデル（完全型。scratch で elaborate、`set_option autoImplicit false`）

```lean
def instSpec (subst : Array Lean.Expr) (b e : Nat) : Lean.Expr → Nat → Lean.Expr  -- instantiate / instantiateRange のモデル（構造再帰、fuel 不要）
  | .bvar i, off =>
    if i < off then .bvar i
    else if i - off < e - b then liftSpec (subst[b + (i - off)]!) 0 off
    else .bvar (i - (e - b))
  | .app f x, off => .app (instSpec subst b e f off) (instSpec subst b e x off)
  | .lam n t bd bi, off => .lam n (instSpec subst b e t off) (instSpec subst b e bd (off + 1)) bi
  | .forallE n t bd bi, off => .forallE n (instSpec subst b e t off) (instSpec subst b e bd (off + 1)) bi
  | .letE n t v bd nd, off =>
    .letE n (instSpec subst b e t off) (instSpec subst b e v off) (instSpec subst b e bd (off + 1)) nd
  | .mdata m x, off => .mdata m (instSpec subst b e x off)
  | .proj n i x, off => .proj n i (instSpec subst b e x off)
  | x, _ => x

def betaGo (revArgs : Array Lean.Expr) (sz : Nat) : Lean.Expr → Nat → Lean.Expr   -- betaRev.go のモデル
  | .lam _ _ bd _, i => if i + 1 < sz then betaGo revArgs sz bd (i + 1) else instSpec revArgs 0 sz bd 0
  | .mdata _ bd, i => betaGo revArgs sz bd i
  | e, i => Lean.Expr.mkAppRevRange (instSpec revArgs (sz - i) sz e 0) 0 (sz - i) revArgs

def betaRevSpec (f : Lean.Expr) (revArgs : Array Lean.Expr) : Lean.Expr :=
  if revArgs.size == 0 then f else betaGo revArgs revArgs.size f 0

def headBetaSpec (e : Lean.Expr) : Lean.Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then betaRevSpec f e.getAppRevArgs else e
```

* **fuel の扱い**: fuel は使わない。core の `betaRev.go` は `partial def` だが、再帰の引数は `lam` / `mdata` の本体（部分式）だけなので、`betaGo` は式への構造再帰として全域。`instSpec` も式への構造再帰（`off` は増えるだけ）。`mkAppRevRange`、`getAppFn`、`getAppRevArgs`、`isHeadBetaTargetFn` は core の通常の `def` をそのまま呼ぶ（モデル側で再定義しない）。
* `betaGo` の対応: core の `go e i` は `lam` で `i+1<sz` なら `go b (i+1)`、そうでなければ `b.instantiate revArgs`（= `instSpec revArgs 0 sz b 0`）。`mdata` は `preserveMData=false` なので `go b i`。`letE` は `useZeta=false` なので `done`。それ以外も `done`＝`mkAppRevRange (e.instantiateRange (sz-i) sz revArgs) 0 (sz-i) revArgs`。`betaGo` の 3 腕目が `letE` を含む残り全部に当たる。
* `instSpec` の範囲: `b ≤ e ≤ subst.size` のとき C++ の `instantiate_core` に対応（範囲外は C++ が `lean_internal_panic`）。`betaGo` は `b = sz - i`, `e = sz = revArgs.size`（`i < sz`）または `b = 0`, `e = sz` でしか呼ばないので範囲内。
* `instSpec` が使う `liftSpec`（`Tools/ShippingLetsExternSpec.lean`）は既存。

### 2.3 仮定（完全型）と証明する定理

```lean
def HeadBetaAgrees0 : Prop :=
  ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true → e.headBeta = headBetaSpec e
```

* 件数: 仮定 1 本。範囲: `NoPh e ∧ BvarLt 0 e` の入力だけ（`inlAbbrevs` が `headBeta` を呼ぶ入力はこの範囲。§3）。全 `Expr` の等式ではない。
* **保存は仮定ではなく定理**（scratch、sorry なし）: `headBetaSpec_good`（`NoPh e ∧ BvarLt 0 e → NoPh (headBetaSpec e) ∧ BvarLt 0 (headBetaSpec e)`）と、それに `HeadBetaAgrees0` を重ねた `headBeta_good`。部品: `instSpec_noPh` / `instSpec_bvarLt`（代入配列の全要素が `NoPh ∧ BvarLt 0` のとき）、`betaGo_good`（`lam` を i 個剥いだ本体は `BvarLt i`）、`mkAppRevRange_good`、`getAppRevArgsAux_good`、`getAppFn_good`。`liftSpec_noPh` / `liftSpec_bvarLt`（`Tools/ShippingGen5ReaderTraceLift.lean`）と `bvarLt_mono` を流用。
* 証明の規模: scratch 全体（U-1 の導出と `inlAbbrevs_ph` を含む）で 368 行、定理・定義 20 個。private な補助（`mkAppRevRangeAux` / `getAppRevArgsAux`）は名前に数値成分があり書けないので、scratch 内にだけ小さな meta 補助（`unfold_priv` / `priv%`）を置いて unfold / 参照した。実装時にこの補助を新規ファイルに置くか、private 補助に触れない別の補題に替えるかは未決（実装単位で決める）。

### 2.4 C++ / core の根拠（v4.32.1、commit f054605a）

引用の目的: `headBetaSpec` が core の `headBeta` と同じ計算であることの根拠。

1. `headBeta` / `betaRev`（`Lean/Expr.lean:1593-1617, 1658-1660`）は Lean ソース。`headBetaSpec` / `betaRevSpec` / `betaGo` は同じ分岐（`revArgs.size == 0` → `f`、`lam`、`mdata`、その他）をそのまま写したもの。**この対応づけは Lean ソースの読みであって C++ の読みではない**。`partial def` の実行時の挙動が、ソースを素直に読んだ再帰と同じ（コンパイラが再帰をそのまま実行する）ことは形式的に確かめていない。
2. `instantiate` / `instantiateRange`（`kernel/instantiate.cpp`、sha256 先頭 42527c96…）:
   * `lean_expr_instantiate_core(a, n, subst)`（:55-79）は `replace(a, λ(m, offset))`。ラムダ: `offset >= get_loose_bvar_range(m)` なら `m` を変えない。`m` が `bvar vidx` で `vidx >= offset` のとき、`vidx < offset + n` なら `lift_loose_bvars(subst[vidx - offset], offset)`、そうでなければ `mk_bvar(vidx - n)`。他は `none`（子へ降りる）。`instSpec` の 3 分岐はこれに対応（`loose_bvar_range` による早期打ち切りは無変更部分木の最適化で値は同じ、と読んだ）。
   * `lean_expr_instantiate(a, subst)`（:81-83）は `n = subst.size`、`lean_expr_instantiate_range(a, begin, end, subst)`（:85-97）は `b ≤ e ≤ size` を確かめ（違えば `lean_internal_panic`）`subst + b` から `e - b` 個で `instantiate_core`。`instSpec subst b e` に対応。
3. `lift_loose_bvars`（`kernel/expr.cpp:448-475`）は、`Expr.liftLooseBVars e 0 d` の C++。`instSpec` は `liftSpec _ 0 off` を使う。これは既存仮定 `LiftAgrees0`（T1L-55）が述べる対応と同じ。ただし `HeadBetaAgrees0` 自体は `headBeta` 全体についての等式で、`LiftAgrees0` から導出される文ではない（C++ の中で lift が呼ばれる、というだけ）。
4. `lean_replace_expr` / `replace_fn`（`replace_fn.cpp:87-154`）は U-2 の等式には現れない（`instantiate*` は offset 付きの別の `replace` を使う）。

読みの限界（主張しないこと）:
* 形式証明ではなくソースの読み。有限個の実行時照合は rev1 で 8 式（部分適用・過剰適用・`mdata`・`letE`・入れ子 `lam`）について `headBeta` / `instantiate` / `instantiateRange` と `Expr.equal` 一致を確認した。**rev2 では実行時照合をやり直していない**（モデルのコードは rev1 と同じ定義で、型の elaborate と証明をやり直した）。例の少なさは根拠にならない。
* `instantiate_core` の `unsigned` へのオフセット・個数の切り詰め（`s, d ≥ 2^32`）と `vidx.is_small()` でない `bvar` は、モデルが扱わない範囲。`NoPh ∧ BvarLt 0` の入力ではインデックスは式の大きさで押さえられるが、2^32 を超える式は主張の外。
* `mk_bvar(vidx - n)` などの `nat` 演算は Lean の `Nat` の引き算と同じと読んだ。
* 実行中のバイナリがこのソースから作られたこと（commit 文字列の一致のみ）。toolchain 更新時は再確認。

### 2.5 既存の仮定との重なり、他の案を外した理由

| 既存 | 重なり |
|---|---|
| `Inst1Agrees`（T1L-51） | 仮定としての重なりはない。`instantiate1` と `instantiate` / `instantiateRange` は C++ の入口が別（`lean_expr_instantiate1` / `lean_expr_instantiate` / `lean_expr_instantiate_range`）で、論理では別の opaque 定数。`HeadBetaAgrees0` を `Inst1Agrees` から小さくする道は見つからなかった。モデル側の流用は `inst1Spec` の 1 要素の場合に限られ、今回の保存補題は `instSpec` の形で新たに証明した |
| `LiftAgrees` / `LiftAgrees0` | 仮定としては使わない（`instSpec` が呼ぶのは純粋な `liftSpec`）。保存補題 `liftSpec_noPh` / `liftSpec_bvarLt` は流用した。意味の上では §2.4-3 のとおり同じ C++ 関数を指す |
| `ZeroLitAgrees0` | U-1 一般形で導出（§1.2）。U-2 とは無関係 |

外した案: 保存形 `HeadBetaPh` / `HeadBetaPh0`（reviewer 不承認: 法則そのものを仮定する）。限定形 `AbbrevReplaceAgrees`（`ZeroLitAgrees0` を導出できず T1 +1 が余分に付く）。3 本分割（`InstantiateAgrees` / `InstantiateRangeAgrees` / `BetaRevAgrees`）: `betaRev` の右辺を `Expr.instantiate*` を呼ぶモデルに作り直す版の型を固定していない（rev1 §2.3 の注意）ので、完全型を示せない。**「小さい仮定の本数」の点では束 1 本の `HeadBetaAgrees0` より 3 本の方が各文は小さいが、型を固定できていないため、この調査では比較できなかった。**

## 3. 合成: `inlAbbrevs` の `NoPh ∧ BvarLt 0` 保存（scratch で sorry なしに証明済み）

仮説: `DeclValuePh env`（N1-a、既存の候補。登録しない）、`ReplaceAgrees`（U-1）、`HeadBetaAgrees0`（U-2）。

```lean
theorem rnc_ph (f : Lean.Expr → Option Lean.Expr)      -- 汎用: 置換結果が NoPh ∧ BvarLt 0 なら replaceNoCache は NoPh ∧ BvarLt L を保つ
    (hf : ∀ x v, f x = some v → NoPh v = true ∧ BvarLt 0 v = true) : …
theorem abbrevFn_ph … ;  theorem inlAbbrevs_ph (env) (hv : DeclValuePh env) (hr : ReplaceAgrees) (hb : HeadBetaAgrees0) : …
```

* 証明の骨子: `n` の帰納。`succ` の腕で `e.replace (production のラムダ)` を `e.replaceNoCache (abbrevFn env)` に書き換え（`hr`。ラムダと `abbrevFn env` の関数としての等式は `cases x <;> rfl`）、`rnc_ph` で `NoPh ∧ BvarLt 0`、`if e' == e` は Bool の場合分け、`headBeta_good` で `headBeta` の結果の `NoPh ∧ BvarLt 0`、`ih`。`headBeta` を呼ぶ入力は `e'`（`rnc_ph` の結果）なので、`HeadBetaAgrees0` の定義域 `NoPh ∧ BvarLt 0` が満たされる。
* `userAbbrev?` の `!d.value.hasLooseBVars` の guard は使わない（`DeclValuePh` が `BvarLt 0` を直接与える）。
* これは条件付きの中間結果: 3 つの仮説（`DeclValuePh`、U-1、U-2）がいずれも受理するソースで成り立つことは、この文書では示していない。`userInliner` 全体の合成には `rounds` / `MachRecUnfold.pass`（S2）が別に要る。

## 4. scratch の `#check` / `#print axioms` 出力（`set_option autoImplicit false`、`kjob lake lean`、error / sorry なし）

scratch: base 796b3ff4 のツリーで `Tools.ShippingGen5ReaderTraceInlineP1`、`Tools.ShippingInlCand`、`Tools.Assume.N3Extern` を import した 1 ファイル 368 行、`sorry` 0 件。ファイルはコミットしない（sha256 先頭 63cd387e）。

```
ReplaceAgrees : Prop
HeadBetaAgrees0 : Prop
instSpec : Array Expr → Nat → Nat → Expr → Nat → Expr
betaGo : Array Expr → Nat → Expr → Nat → Expr
betaRevSpec : Expr → Array Expr → Expr
headBetaSpec : Expr → Expr
zeroLit_of_replaceAgrees : ReplaceAgrees → Tools.Assume.N3Extern.ZeroLitAgrees0
instSpec_noPh : ∀ (subst : Array Expr),
  (∀ (a : Expr), a ∈ subst → Good a) →
    ∀ (b e : Nat) (x : Expr) (off : Nat), NoPh x = true → NoPh (instSpec subst b e x off) = true
instSpec_bvarLt : ∀ (subst : Array Expr),
  (∀ (a : Expr), a ∈ subst → Good a) →
    ∀ (b e : Nat) (x : Expr) (off m : Nat),
      BvarLt (m + (e - b) + off) x = true → BvarLt (m + off) (instSpec subst b e x off) = true
betaGo_good : ∀ (revArgs : Array Expr),
  (∀ (a : Expr), a ∈ revArgs → Good a) →
    ∀ (sz : Nat),
      sz = revArgs.size →
        ∀ (x : Expr) (i : Nat), i < sz → NoPh x = true → BvarLt i x = true → Good (betaGo revArgs sz x i)
headBetaSpec_good : ∀ (e : Expr),
  NoPh e = true → BvarLt 0 e = true → NoPh (headBetaSpec e) = true ∧ BvarLt 0 (headBetaSpec e) = true
headBeta_good : HeadBetaAgrees0 →
  ∀ (e : Expr), NoPh e = true → BvarLt 0 e = true → NoPh e.headBeta = true ∧ BvarLt 0 e.headBeta = true
rnc_ph : ∀ (f : Expr → Option Expr),
  (∀ (x v : Expr), f x = some v → NoPh v = true ∧ BvarLt 0 v = true) →
    ∀ (e : Expr) (L : Nat),
      NoPh e = true →
        BvarLt L e = true → NoPh (Expr.replaceNoCache f e) = true ∧ BvarLt L (Expr.replaceNoCache f e) = true
abbrevFn_ph : ∀ (env : Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env →
    ∀ (x v : Expr), Tools.ShippingInlCand.abbrevFn env x = some v → NoPh v = true ∧ BvarLt 0 v = true
inlAbbrevs_ph : ∀ (env : Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env →
    ReplaceAgrees →
      HeadBetaAgrees0 →
        ∀ (n : Nat) (e : Expr),
          NoPh e = true → BvarLt 0 e = true → NoPh (inlAbbrevs env n e) = true ∧ BvarLt 0 (inlAbbrevs env n e) = true
'S1.zeroLit_of_replaceAgrees' depends on axioms: [propext]
'S1.headBetaSpec_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'S1.headBeta_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'S1.inlAbbrevs_ph' depends on axioms: [propext, Classical.choice, Quot.sound]
```

（`Good a := NoPh a = true ∧ BvarLt 0 a = true`。`Expr` は `Lean.Expr`。`Good` は scratch の補助定義で、実装時は同じ意味の名前を新規ファイルに置く。）`ReplaceAgrees` の定義は §1.1 と同じ。

## 5. 台帳（登録時の増減。現時点は 0/0、未登録）

| 単位 | FG | T1 | 内訳 |
|---|---|---|---|
| U-1 付け替え | ±0 | ±0 | `ReplaceAgrees` +1、`ZeroLitAgrees0`（T1L-54）−1（定理に降格） |
| U-2 | ±0 | **+1** | `HeadBetaAgrees0` +1 |
| 合計 | ±0 | **+1（54 → 55）** | |

* `ZeroLitAgrees0` を使う側（`Tools/ShippingN3ExternAgree.lean` 等）の付け替えの編集範囲は未計測（実装時に数える）。登録先は新規 `Tools/Assume/AbbrevExtern.lean`（予定）。
* 「何も登録しない」場合は 0/0 で、inline 枝の `inlAbbrevs` が未解消のまま（判断資料に選択肢として書いた）。
* `DeclValuePh`（N1-a）、`RecRulePh`（S2）、U-3（`PassPh`）は本 freeze の範囲外で、台帳に載せていない。

## 6. reviewer に確認してほしい点

1. U-1: 一般形 `ReplaceAgrees` で `ZeroLitAgrees0` を降格（T1 ±0）。C++ の読み（§1.3）とその限界（キャッシュのポインタ同一性は読みの範囲外）で足りるか。
2. U-2: `HeadBetaAgrees0`（`NoPh ∧ BvarLt 0` の入力に限った一致形）の型と、モデル（`instSpec` / `betaGo` / `headBetaSpec`）と core / C++ の対応づけ（§2.4）で足りるか。保存を定理にした証明（scratch）で方針に沿うか。
3. 範囲: 定義域を `NoPh ∧ BvarLt 0` に限ったことで、仮定の文が「使う範囲」だけになっているか。さらに狭める（例: `NoPh` を外す）必要はないか。
4. 承認後の実装単位: 仮定の登録（新規 `Tools/Assume/AbbrevExtern.lean`）+ 保存の証明（新規ファイル、scratch 相当 ~370 行）。`ZeroLitAgrees0` 降格の編集は別単位。
5. ユーザー判断: 新しい T1 の純 +1 は `scripts/gen5/RT_ABBREV_S1_DECISION.md` に分けた（reviewer が freeze を見た後に coder がユーザーへ出す）。

## 7. 未確認・主張しないこと

* U-1 / U-2 の仮定が**成り立つ**ことは C++ / Lean ソースの読みと有限個の実行時照合（rev1 の 8 式）による。証明ではなく、反例の網羅探索もしていない。この調査では「仮定が成り立たない」例は見つからなかったが、それは成り立つことの証明ではない。
* `HeadBetaAgrees0` のモデルが `partial def betaRev` の実行時の挙動と同じ、という点は Lean ソースの読みで、C++ の読みでも形式証明でもない。
* `userInliner` 全体、`relevantClosure` の真の腕（S2）、`RecRulePh`、`hdom` / `hbs` への `d.type` の影響は範囲外で未確認。
* コンパイラ・共有定義（`Tools/ShippingGen2Defs.lean`、`T1Hyp`、`T1HypND`、`Elab*.lean`）・TRUSTED 境界・law・FG は変えていない。`GenWF` は強化していない。mutant は使っていない（signature / defeq での棄却も行っていない。mutant による棄却は意味的反例ではない）。
* `sorry` / `axiom` / `native_decide` は scratch にも無い。Lean はコミットしていない。
