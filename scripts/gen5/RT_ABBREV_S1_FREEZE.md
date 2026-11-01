# RT abbrev S1 freeze: `inlAbbrevs` の `Expr.replace`（U-1）と `Expr.headBeta`（U-2）の最小振る舞い仮定

Issue: `sparkle-rt-abbrev-s1`（親 `sparkle-gen5-dg-readertrace`）。base: `par/rt-inline-p1` d68b167c。調査: `scripts/gen5/RT_INLINE_SURVEY.md` §1.3（S1）。既存の書き方: `Tools/Assume/N3Extern.lean`。
**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0。未登録。案ごとの登録時の増減は §5）。**
この文書は、台帳前提の追加・付け替えの候補と TRUSTED 境界の文を含むので reviewer の承認が要る freeze。承認が出るまで Lean 実装（`Tools/Assume/` への登録を含む）には進まない。Lean ソースは何もコミットしていない。

方針（ユーザー）: 「C++/opaque の振る舞いは小さな明示的仮定にして、合成法則はそこから証明する」。仮定は使う向き・範囲だけに限定する（rev21.1 で reviewer が求めた点）。

## 0. 要約

| 項目 | 内容 | 結果 |
|---|---|---|
| U-1 一般形 `ReplaceAgrees` | `Expr.replace f e = Expr.replaceNoCache f e`（全 `f`, `e`） | **既存 `ZeroLitAgrees0`（T1L-54）を scratch で sorry なしに導出できた** → 付け替えなら T1 ±0 |
| U-1 限定形 `AbbrevReplaceAgrees` | 同じ式を `f = abbrevFn env` に限る | 導出に使えるのは `inlAbbrevs` のみ。`ZeroLitAgrees0` は残る → T1 +1 |
| U-2 保存形 `HeadBetaPh0` | `NoPh ∧ BvarLt 0` を `headBeta` が保つ | 1 本。使う向き・範囲が最小（`L = 0`、保存の一方向） |
| U-2 一致形 | `headBeta` の構造モデルとの等式。1 本の束（`HeadBetaAgrees`）か 3 本の分割（`BetaRevAgrees` + `InstantiateAgrees` + `InstantiateRangeAgrees`） | モデルは新規 ~35 行（scratch で elaborate 済み）。保存の証明は別途 ~250 行の見積もり（未証明） |
| 合成 `inlAbbrevs_ph` | U-1 限定形 + U-2 `HeadBetaPh0` + `DeclValuePh` から `NoPh ∧ BvarLt 0` の保存 | **scratch で sorry なしに証明済み**（axioms: propext, Classical.choice, Quot.sound） |

推奨（§2.5 / §5）: U-1 は一般形（`ZeroLitAgrees0` を導出して付け替え、T1 ±0）、U-2 は `HeadBetaPh0`（T1 +1）。合計 T1 +1。ただし U-2 は「性質そのものの仮定」に近いので、方針に最も忠実な一致形（束 1 本、T1 +1）との選択を §2.5 に書く。決めるのは reviewer（および新しい T1 のためユーザー）。

## 1. U-1: `Expr.replace` と `Expr.replaceNoCache` の一致

### 1.1 完全型（scratch で elaborate、`set_option autoImplicit false`、§4 に出力）

```lean
/-- (U-1 一般形) -/
def ReplaceAgrees : Prop :=
  ∀ (f : Lean.Expr → Option Lean.Expr) (e : Lean.Expr), e.replace f = e.replaceNoCache f

/-- (U-1 限定形) `inlAbbrevs` が使う置換関数だけ。`abbrevFn` は `Tools.ShippingInlCand`（Elab.lean 3379–3381 のラムダに名前を付けたもの） -/
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
* 一般形は `f` と `e` を全称にする。C++ の読みは `f` の中身にも `e` の形にも依らない（純関数であること以外）ので、範囲を狭める根拠が読みからは出ない（`LetOk 0` のような `e` の制限は読みでは不要）。限定形は「使う範囲」には合うが、`ZeroLitAgrees0` を導出できず T1 が +1 になる。この 2 つのどちらが「小さな仮定」かは reviewer の判断（§2.5 と同様）。
* 領域をさらに `NoPh e ∧ BvarLt L e` に狭める形は作れる（`inlAbbrevs` が呼ぶ入力はそれ）が、C++ の読みがその領域を使わないので、狭めても支えが増えない。本文では採らない。

## 2. U-2: `Expr.headBeta`

### 2.1 何が opaque か

`headBeta e := let f := e.getAppFn; if f.isHeadBetaTargetFn false then betaRev f e.getAppRevArgs else e`（`Lean/Expr.lean:1658-1660`）。`getAppFn` / `isHeadBetaTargetFn` / `getAppRevArgs` は通常の `def`。`betaRev`（:1593）は core の **`partial def`**（論理では本体が見えない）で、中で `Expr.instantiate`（:1430、extern）と `Expr.instantiateRange`（:1473、extern）と `mkAppRevRange`（通常の `def`）を使う。`headBeta` では `useZeta := false`, `preserveMData := false`。

### 2.2 案 P: 保存形（完全型。scratch で elaborate）

```lean
def HeadBetaPh : Prop :=            -- 一般形（L 全称）
  ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
    NoPh e.headBeta = true ∧ BvarLt L e.headBeta = true

def HeadBetaPh0 : Prop :=           -- 最小形（L = 0 のみ。inlAbbrevs の入力は BvarLt 0）
  ∀ (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
    NoPh e.headBeta = true ∧ BvarLt 0 e.headBeta = true
```

* 件数: 仮定 1 本。規模: 文 3 行。
* 性質そのものの仮定（`NoPh` / `BvarLt` という Sparkle 側の述語が入る）。`RawNodePh` / `NormNodePh` と同種で、「C++ の振る舞いを小さく仮定する」というより「合成法則の一部を仮定する」側に寄る。方針との緊張がある点を隠さない。
* 使う向き: `inlAbbrevs` の再帰（`e'.headBeta` が次の入力）で 1 回ずつ、`L = 0` で使う。

### 2.3 案 A: 一致形（完全型。scratch で elaborate。モデルは新規定義）

```lean
def instSpec (subst : Array Lean.Expr) (b e : Nat) : Lean.Expr → Nat → Lean.Expr  -- instantiate / instantiateRange のモデル
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

def betaGo (revArgs : Array Lean.Expr) (sz : Nat) : Lean.Expr → Nat → Lean.Expr   -- betaRev.go の構造モデル（fuel 不要: lam / mdata の本体への構造再帰）
  | .lam _ _ bd _, i => if i + 1 < sz then betaGo revArgs sz bd (i + 1) else instSpec revArgs 0 sz bd 0
  | .mdata _ bd, i => betaGo revArgs sz bd i
  | e, i => Lean.Expr.mkAppRevRange (instSpec revArgs (sz - i) sz e 0) 0 (sz - i) revArgs

def betaRevSpec (f : Lean.Expr) (revArgs : Array Lean.Expr) : Lean.Expr :=
  if revArgs.size == 0 then f else betaGo revArgs revArgs.size f 0

def headBetaSpec (e : Lean.Expr) : Lean.Expr :=
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then betaRevSpec f e.getAppRevArgs else e
```

仮定の切り方は 2 通り:

```lean
-- A' (束 1 本)
def HeadBetaAgrees : Prop := ∀ e : Lean.Expr, e.headBeta = headBetaSpec e

-- A (分割 3 本)
def InstantiateAgrees : Prop := ∀ (e : Lean.Expr) (subst : Array Lean.Expr),
  e.instantiate subst = instSpec subst 0 subst.size e 0
def InstantiateRangeAgrees : Prop := ∀ (e : Lean.Expr) (b e' : Nat) (subst : Array Lean.Expr),
  b ≤ e' → e' ≤ subst.size → e.instantiateRange b e' subst = instSpec subst b e' e 0
def BetaRevAgrees : Prop := ∀ (f : Lean.Expr) (revArgs : Array Lean.Expr),
  Lean.Expr.betaRev f revArgs = betaRevSpec f revArgs
```

* 注意: 上の `BetaRevAgrees` の右辺は `instSpec` を使うモデルなので、`betaRev` と、その中の `instantiate*` を**束ねた**仮定になっている。このため `InstantiateAgrees` / `InstantiateRangeAgrees` は、この形では `BetaRevAgrees` と併用しても使い道がなく（冗長）、3 本を独立にするには `BetaRevAgrees` の右辺を `Expr.instantiate` / `Expr.instantiateRange` を呼ぶモデルに作り直す必要がある（その版は未 elaborate で、型をこの文書で固定しない）。したがって、型を固定できている一致形は **A'（束 1 本）だけ**。A（3 本分割）の件数 +3 は、作り直した版の見込みであって、確認していない。
* モデルの確かめ: コンパイル済みの実物と照合（証明ではない）。`headBeta` / `instantiate` / `instantiateRange` が 8 個の式（部分適用・過剰適用・`mdata`・`letE`・入れ子 `lam` を含む）で `Expr.equal` 一致した。
* C++（`instantiate.cpp:15-37, 55-79, 85-96`、sha256 先頭 42527c96…）の読み: `instantiate_core` は `replace` のラムダで、オフセット `offset` の位置の `bvar vidx`（`vidx ≥ offset`）を、`vidx < offset + n` なら `lift_loose_bvars(subst[vidx - offset], offset)`、そうでなければ `bvar (vidx - n)` に置換。`offset >= loose_bvar_range(m)` の部分木は無変更。`instSpec` はこれに対応する（`loose_bvar_range` による早期打ち切りは、無変更部分木の最適化で値は同じ、と読んだ）。`instantiateRange` は `subst + b` から `e - b` 個を使う（`b ≤ e ≤ size` でなければ panic。モデルは範囲外を扱わないので `b ≤ e' ≤ size` を前提にした）。`lift_loose_bvars` は既存の `liftSpec`（`LiftAgrees0` の A1 と同じ読み）を使う。`betaRev` 自体は C++ ではなく Lean の `partial def`（`Expr.lean:1593-1617`）で、その読みはソースの `go` のコピーが `betaGo` と同じ分岐になっている、というもの。**betaRev の読みは C++ の読みではなく Lean ソースの読みである**ことを明記する。
* 読みの限界: `instantiate` の `lean_internal_panic`（範囲外）は扱わない。`unsigned` へのオフセットの切り詰め（`s,d ≥ 2^32`）は範囲外（N3_EXTERN_MIN.md の記録と同じ）。`partial def` の実行時の挙動が、ソースを素直に読んだ再帰と同じであること（コンパイラが再帰をそのまま実行する、という通常の理解）は、この読みでは形式的に確かめていない。

### 2.4 既存の `Inst1Agrees` / `LiftAgrees` との重なり

| 既存 | 重なり |
|---|---|
| `Inst1Agrees`（T1L-51、`instantiate1` の等式） | **仮定としての重なりはない**。`instantiate1` と `instantiate` は別の extern（C++ の入口が別: `lean_expr_instantiate1` / `lean_expr_instantiate`）で、論理では別の opaque 定数。`instantiate b #[a]` は `inst1Spec b a 0` と等しい（モデルの上では `instSpec #[a] 0 1 b 0` と同形）が、その等式は `InstantiateAgrees` が与えるもので `Inst1Agrees` からは出ない。**モデルの重なり**: `instSpec` の 1 要素の場合は `inst1Spec` と同じ。保存補題 `inst1Spec_noPh` / `inst1Spec_bvarLt`（`Tools/ShippingGen5ReaderTraceInst1.lean:14,47`）は 1 要素の場合にだけ流用でき、一般の `subst` には使えない |
| `LiftAgrees` / `LiftAgrees0`（T1L-55） | **仮定は使わない**。`instSpec` は純粋なモデル `liftSpec` を呼ぶだけで、`Expr.liftLooseBVars`（extern）を呼ばない。純粋補題 `liftSpec_noPh` / `liftSpec_bvarLt`（`Tools/ShippingGen5ReaderTraceLift.lean:15,39`）は流用できる |
| `ZeroLitAgrees0` | U-1 一般形で導出できる（§1.2）。U-2 とは無関係 |

### 2.5 比較と推奨

| 案 | 仮定の本数 | T1 | 文の規模 | 仮定の種類 | 追加の証明（見積もり、未証明） |
|---|---|---|---|---|---|
| P0 `HeadBetaPh0` | 1 | +1 | 3 行 | 性質（保存）。合成法則の一部を仮定 | なし（`inlAbbrevs_ph` は scratch で証明済み） |
| P `HeadBetaPh` | 1 | +1 | 4 行 | 同上、`L` 全称 | なし |
| A' `HeadBetaAgrees` | 1 | +1 | 文 1 行 + モデル ~35 行（elaborate 済み） | 振る舞い（モデルとの一致）。方針に最も合う | `instSpec` の `NoPh` / `BvarLt` 保存、`betaGo` の帰納、`mkAppRevRange` の fold、`headBeta` の場合分け。~250 行の見積もり（`inst1Spec_*` / `liftSpec_*` の同形の書き直しが主）。成立の確認は未 |
| A（3 本に分割） | 3 | +3 | 上に加えて各 3〜4 行 | 振る舞い。最も小さい単位 | A' と同じ ~250 行 + 接続の補題。型は未固定 |

* **推奨案（使う向き・範囲だけの最小形）: P0 `HeadBetaPh0`。** 一方向（保存）、`L = 0`、`inlAbbrevs` の再帰の 1 箇所だけで使う。件数は A' と同じ +1 で、証明の追加が要らない。
* ただし P0 は方針（振る舞いを仮定し、法則は証明する）より弱い立場にある。方針に忠実なのは A'（同じ +1 で、`headBeta` の振る舞いそのものの仮定。代償は追加の証明 ~250 行と、モデルの読みが C++ と Lean ソースの両方に及ぶこと）。**P0 か A' かは reviewer の判断事項**で、新しい T1 の追加なのでユーザー承認も要る。推奨は P0（最小・既に合成まで証明済み）。理由は規模だけで、方針への忠実さの点では A' が上であることを併記する。
* 判断しない場合: inline 枝の `hdecl`（RT_INLINE_SURVEY §0 の 1 文）は閉じない。当面 `shapeInputs_of_direct` で進める（rev18/19 の選択）のを続けるだけで、他の枝は止まらない。

## 3. 合成: `inlAbbrevs` の `NoPh ∧ BvarLt 0` 保存（scratch で sorry なしに証明済み）

仮説: `DeclValuePh env`（N1-a、既存の候補。登録しない）、U-1 限定形（または一般形から自明に導く）、U-2 `HeadBetaPh0`。

```lean
theorem rnc_ph (f : Lean.Expr → Option Lean.Expr)      -- 汎用: 置換結果が閉じていれば replaceNoCache は NoPh ∧ BvarLt L を保つ
    (hf : ∀ x v, f x = some v → NoPh v = true ∧ BvarLt 0 v = true) :
    ∀ (e : Lean.Expr) (L : Nat), NoPh e = true → BvarLt L e = true →
      NoPh (e.replaceNoCache f) = true ∧ BvarLt L (e.replaceNoCache f) = true

theorem abbrevFn_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) :
    ∀ x v, abbrevFn env x = some v → NoPh v = true ∧ BvarLt 0 v = true

theorem inlAbbrevs_ph (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    (hr : AbbrevReplaceAgrees) (hb : HeadBetaPh0) :
    ∀ (n : Nat) (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      NoPh (inlAbbrevs env n e) = true ∧ BvarLt 0 (inlAbbrevs env n e) = true
```

* 証明の骨子: `n` の帰納。`succ` の腕で `e.replace (production のラムダ)` を `e.replaceNoCache (abbrevFn env)` に書き換え（`hr`、ラムダの等式は `funext; cases; rfl`）、`rnc_ph`（`binder` ごとに `L+1`、置換結果は `bvarLt_mono (Nat.zero_le _)` で任意の `L` に持ち上げ）で `NoPh ∧ BvarLt 0`、`if e' == e` は Bool の場合分け（`==` が `Expr.eqv` でも値に依らない）、`hb` で `headBeta`、`ih`。`abbrevFn_ph` は `userAbbrev?` の `if` を `split` で外して `DeclValuePh`。
* scratch の規模: 上の 3 定理 + 補助 1 つ（ラムダの等式）で約 140 行（`rnc_ph` の 9 構成子の腕が大半）。axioms: `propext`, `Classical.choice`, `Quot.sound`（`sorry` / 独自 axiom なし）。
* `userAbbrev?` の `!d.value.hasLooseBVars` の guard は使っていない（`DeclValuePh` が直接 `BvarLt 0` を与える）。`userAbbrev?` の他の条件（`inlUserModule`、reducibility 等）も使わず、`some` なら `env.find? c = some (.defnInfo d)` だけを取り出す。
* 一般形 `ReplaceAgrees` を仮説にするなら `hr` は `fun env e => h _ e`。
* これは条件付きの中間結果: 3 つの仮説（`DeclValuePh`、U-1、U-2）がいずれも受理するソースで成り立つことは、この文書では示していない。`userInliner` 全体の合成には `rounds` / `MachRecUnfold.pass`（S2）が別に要る。

## 4. scratch の `#check` 出力（`set_option autoImplicit false`、`kjob lake lean`、exit 0、error / sorry なし）

```
ReplaceAgrees : Prop
AbbrevReplaceAgrees : Prop
HeadBetaPh : Prop
HeadBetaPh0 : Prop
instSpec : Array Expr → Nat → Nat → Expr → Nat → Expr
betaGo : Array Expr → Nat → Expr → Nat → Expr
betaRevSpec : Expr → Array Expr → Expr
headBetaSpec : Expr → Expr
InstantiateAgrees : Prop
InstantiateRangeAgrees : Prop
BetaRevAgrees : Prop
HeadBetaAgrees : Prop
zeroLit_of_replaceAgrees : ReplaceAgrees → Tools.Assume.N3Extern.ZeroLitAgrees0
rnc_ph : ∀ (f : Expr → Option Expr),
  (∀ (x v : Expr), f x = some v → NoPh v = true ∧ BvarLt 0 v = true) →
    ∀ (e : Expr) (L : Nat),
      NoPh e = true →
        BvarLt L e = true → NoPh (Expr.replaceNoCache f e) = true ∧ BvarLt L (Expr.replaceNoCache f e) = true
abbrevFn_ph : ∀ (env : Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env →
    ∀ (x v : Expr), abbrevFn env x = some v → NoPh v = true ∧ BvarLt 0 v = true
inlAbbrevs_ph : ∀ (env : Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env →
    AbbrevReplaceAgrees →
      HeadBetaPh0 →
        ∀ (n : Nat) (e : Expr),
          NoPh e = true → BvarLt 0 e = true → NoPh (inlAbbrevs env n e) = true ∧ BvarLt 0 (inlAbbrevs env n e) = true
'S1.zeroLit_of_replaceAgrees' depends on axioms: [propext]
'S1.inlAbbrevs_ph' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(scratch 実行場所: base d68b167c の worktree、`kjob lake lean` で `Tools.ShippingGen5ReaderTraceInlineP1` と `Tools.Assume.N3Extern` を import。scratch ファイルはコミットしない。)

## 5. 台帳（登録時の T1 増減。現時点は 0/0、未登録）

FG は全案で ±0（U-1 / U-2 は C++ / core の extern・`partial def` に関する T1 側）。

| 案の組み合わせ | T1 の増減 | 内訳 |
|---|---|---|
| U-1 一般形 + U-2 P0（**推奨**） | **+1**（T1 54 → 55） | `ReplaceAgrees` +1、`ZeroLitAgrees0`（T1L-54）−1（定理に降格）、`HeadBetaPh0` +1 |
| U-1 一般形 + U-2 A' | +1 | `ReplaceAgrees` +1、`ZeroLitAgrees0` −1、`HeadBetaAgrees` +1 |
| U-1 限定形 + U-2 P0 | +2 | `AbbrevReplaceAgrees` +1、`HeadBetaPh0` +1（`ZeroLitAgrees0` は残る） |
| U-1 限定形 + U-2 A' | +2 | 同上 |
| U-1 一般形 + U-2 A（3 本） | +3 | 型未固定（§2.3 の注意） |
| 何も登録しない | 0 | inline 枝は未解消のまま |

* 数え方: 現在 FG 103 / T1 54（2026-11-01）。上の増減は本文の仮定の本数から数えたもので、既存の台帳行（T1L-nn）の番号付けや束ね方（`RecRulePh` との関係など）は未確定。登録・付け替え・束ね方は reviewer の承認事項。
* `RecRulePh`（S2、`MachRecUnfold.iota` 用）と U-3（`PassPh`）は本 freeze の範囲外。

## 6. reviewer に確認してほしい点

1. U-1: 一般形（`ZeroLitAgrees0` を降格して付け替え、T1 ±0）か、限定形（T1 +1）か。C++ の読み（§1.3）とその限界（キャッシュのポインタ同一性は読みの範囲外）で足りるか。
2. U-2: P0（保存形、最小）か A'（一致形、方針に忠実、追加の証明 ~250 行の見積もり）か。モデル（`instSpec` / `betaGo` / `headBetaSpec`）の対応づけで足りるか。
3. 登録先: 新規 `Tools/Assume/AbbrevExtern.lean`（`N3Extern.lean` の A3 を定理に降格する編集は別単位）。
4. 承認後の実装単位: 仮定の登録 + `inlAbbrevs_ph` の実装（新規ファイル、scratch 相当 ~140 行 + 仮定の登録）。

## 7. 未確認・主張しないこと

* U-1 / U-2 の仮定が**成り立つ**ことは C++ / Lean ソースの読みと有限個の実行時照合（8 式）による。証明ではなく、反例の網羅探索もしていない。「読みの限界」（§1.3 / §2.3）に書いた点は未確認。
* A / A' の保存の証明（~250 行）は見積もりで、書いていない・成立を確認していない。
* `userInliner` 全体、`relevantClosure` の真の腕（S2）、`RecRulePh`、`hdom` / `hbs` への `d.type` の影響は範囲外で未確認。
* コンパイラ・共有定義（`Tools/ShippingGen2Defs.lean`、`T1Hyp`、`T1HypND`、`Elab*.lean`）・TRUSTED 境界・law・FG は変えていない。`GenWF` は強化していない。mutant は使っていない（signature / defeq での棄却も行っていない）。
* `sorry` / `axiom` / `native_decide` は scratch にも無い。Lean はコミットしていない。
