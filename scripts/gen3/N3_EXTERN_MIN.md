# N3 extern 最小仮定: liftLooseBVars / lowerLooseBVars / instantiate1 を閉じる最小の LetOk 条件(T1L-50/51/55/56、54/57 は必要性のみ)

- Issue: `sparkle-n3-extern-min`(親 `sparkle-gen3-src-argw`)。agent `n3min1`、branch `kjob/n3min1`、base `b8a3ddb8`(`kjob/tre1`、旧 N3 freeze `scripts/gen3/TRUST_EXPR_FREEZE.md`、承認済み・未実装・未有効)。**文書のみ。Lean のソースツリーは変更していない。** Lean の探索は scratch(ソースツリー外、コミットしない)。
- 位置づけ: ユーザー指示(2026-11-01)「複合命題を丸ごと信頼せず、C++ 実装の振る舞いを小さく仮定して残りを証明する」に対する、reviewer 意見(B5 全入力は強すぎる / C++ source と照合 / B6・B7 は必要形に絞る / #5 `s=0` と `lowerSpec_ok` 一般化は証明が通るまで未確認)への回答資料。**これは仮定の追加・変更の freeze 相談で、reviewer の承認が出るまで Lean 実装・有効化には進まない。**
- coder 案 `~/git/.kjob-state/n1n3-behavior-spec.md` はこの Pod から見えなかった(読めていない)。B5/B6/B7 は brief の要約(B5 = extern を全入力で仕様と一致と仮定、B6 = `replace` を全 `f,e` で、B7 = `beta`)に従って扱った。
- 書き方の規則: 「見つからなかった」は「この調査では供給元・経路が見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant は signature / defeq での棄却で、意味的反例ではない。差分テストは検査であって証明ではない。台帳の数は数えたものだけ書く。
- 台帳: FG 102 / T1 57(今回 FG -0 +0 / T1 -0 +0、文書のみ。T1 57 に T1L-50..59 の 9 行が全て含まれるかは未計数)。

## 0. 結論(先に)

1. 4 行(T1L-50/51/55/56)のうち、reader の証明が使う形は**すでに LetOk 保存(range)か、(0,1)・(1,1) の等式**で、旧 freeze の原文より小さくできる箇所は **`n = 0` への絞り(T1L-51・54)だけ**だった。B5(全入力で仕様と等式)は**不要**で採らない。
2. **#5(T1L-55)`LiftLooseRange0`(`s = 0`)と #6(T1L-56)`LowerLooseRangeEq`(`s = d`)は、scratch で `rawNode_ok` の証明をそのまま(仮説の型と `hl _ _ _`→`hl _ _` の引数減らしだけ変えて)通した。** `sorry` なし、公理は `propext, Classical.choice, Quot.sound` のみ(§3.3)。reviewer が未確認とした「`s = 0` が証明で足りるか」は、**`rawNode_ok`(RawNodeRangeLetOk:428)については確認済み**。下流(`rawNodeRange_structEnv` ほか ArgSupply15)は base に無く、未確認。
3. `liftSpec_ok` は**すでに `(s,d)` について一般**(`ExternSpec` の `liftSpec_ok : ∀ n e s d`、scratch の `#check` で確認)。「`liftSpec_ok` の (s,d) 一般化」は不要。`lowerSpec` は**既存に無く**、等式の代替案(§3.2 の B 案)を採る場合だけ新設が要る。scratch で `lowerSpec_ok`(一般 `(s,d)`)を証明できた(§3.3)が、range の案(推奨)では不要。
4. T1L-54 は `n = 0` だけで足りる(`zeroLit_ok` の使用が 2 箇所とも `n=0`)。T1L-57 は rawNode の 1 引数 beta で、`partial def betaRev.go` が開けないため **`beta` のまま残す**以外の経路は、この調査では見つからなかった(§4)。
5. C++ source(Lean tag `v4.32.1` = commit `f054605a…`、`lean --version` の commit と一致)を取得して照合した。lift / lower / instantiate1 / replace は、**`liftSpec` / `inst1Spec` / (新) `lowerSpec` の定義と構造が一致**(§1.2)。照合は私の読み取りであって、形式的な証明ではない。

## 1. extern の正確な宣言と C++ 実装

### 1.1 Lean v4.32.1 の宣言(toolchain の `src/lean/Lean/`)

| extern | 宣言(file:line、型) |
|---|---|
| `lowerLooseBVars` | `Lean/Expr.lean:1357-1358` `@[extern "lean_expr_lower_loose_bvars"] opaque lowerLooseBVars (e : @& Expr) (s d : @& Nat) : Expr`。docstring: `bvar i`(`i >= s`)を `bvar (i-d)` に。**`s < d` なら結果は `e`** |
| `liftLooseBVars` | `Lean/Expr.lean:1362-1363` `@[extern "lean_expr_lift_loose_bvars"] opaque liftLooseBVars (e : @& Expr) (s d : @& Nat) : Expr` |
| `instantiate1` | `Lean/Expr.lean:1446-1447` `@[extern "lean_expr_instantiate1"] opaque instantiate1 (e : @& Expr) (subst : @& Expr) : Expr` |
| `instantiate`(beta が使う) | `Lean/Expr.lean:1429-1430` `@[extern "lean_expr_instantiate"] opaque instantiate (e : @& Expr) (subst : @& Array Expr) : Expr` |
| `instantiateRange`(beta の `done` が使う) | `Lean/Expr.lean:1472-1473` `@[extern "lean_expr_instantiate_range"] opaque instantiateRange (e : @& Expr) (beginIdx endIdx : @& Nat) (subst : @& Array Expr) : Expr` |
| `Expr.replace`(T1L-54 参考) | `Lean/Util/ReplaceExpr.lean:16-19` `@[extern "lean_replace_expr"] opaque replaceImpl (f? : @& (Expr → Option Expr)) (e : @& Expr) : Expr`、`@[inline] def replace f? e := replaceImpl f? e`。構造的な参照実装は `replaceNoCache`(同 :22-35) |
| `Expr.beta`(T1L-57 参考) | `Lean/Expr.lean:1624-1625` `def beta (f : Expr) (args : Array Expr) : Expr := betaRev f args.reverse`。`betaRev`(:1593)は `partial def`、内部の `let rec go` も partial |

### 1.2 対応する C++(`leanprover/lean4` tag `v4.32.1`、`src/kernel/`。ネットワークで取得。同梱 toolchain には `src/kernel` が無い)

取得したファイルの sha256 先頭: `expr.cpp` cb02c189…、`instantiate.cpp` 42527c96…、`replace_fn.cpp` 2edfa172…(照合の再現用。コミットはしない)。

| extern | C++ file:line | 計算内容の要約 |
|---|---|---|
| `lean_expr_lift_loose_bvars` | `expr.cpp:469-475`(本体 `lift_loose_bvars` :448-463) | `s`・`d` が非 scalar なら `e` を返す。`d == 0` または `s >= loose_bvar_range(e)` なら `e`。それ以外は `replace` で、深さ `offset` の位置で `bvar i`(`i >= s+offset`)を `bvar (i+d)` に。`s+offset` 桁あふれ・`loose_bvar_range` 以上の部分木は無変更。**`liftSpec` と同じ**(束縛を下るごとに `s+1`、`letE` は型・値は `s`、本体は `s+1`) |
| `lean_expr_lower_loose_bvars` | `expr.cpp:440-446`(本体 :417-434) | 非 scalar または `s < d` なら `e`。`d == 0` または `s >= range` なら `e`。それ以外は `replace` で `bvar i`(`i >= s+offset`)を `bvar (i-d)`。**(新)`lowerSpec e s d := if s < d then e else lowerGo e s d`(§3.2)と同じ** |
| `lean_expr_instantiate1` | `instantiate.cpp:44-53`(本体 `instantiate(a, s, n, subst)` :15-37) | `!has_loose_bvars(a)` なら `a`。それ以外は `replace` で深さ `offset` の位置で、`bvar i`:`i < offset` は無変更、`i == offset`(`n=1`)は `lift_loose_bvars(subst[0], offset)`(= `liftSpec subst 0 offset`)、`i > offset` は `bvar (i-1)`。**`inst1Spec b a 0` と同じ** |
| `lean_expr_instantiate`(beta の lam 経路) | `instantiate.cpp:55-82` | 配列版。`n = 1` なら instantiate1 と同じ。 |
| `lean_replace_expr` | `replace_fn.cpp:151-154`(`replace_fn` :87-146) | 各ノードにまず `f?` を適用し、`some` ならその結果、`none` なら子(`mdata`/`proj`/`app`/`lam`・`forallE` の型と本体/`letE` の型・値・本体)へ再帰。共有ノードは(`f?` が純粋なので)結果をキャッシュ。**`replaceNoCache` と同じ走査** |

要約: 4 つとも**構造的な bvar 書き換え**で、`fvar` を作らない(`instantiate1` が `fvar` を持ち込むのは `subst` 由来のみ)。この性質が LetOk(`fvar` の `_machLet j` 添字だけを見る述語)の保存を支えている。

照合の限界(この調査では確認していないもの): (a) C++ の `unsigned` 変換(`lean_unbox(s)` を `unsigned` に)で `s,d ≥ 2^32` のときの切り捨て。reader の `s,d` は小さい数なので範囲外として扱った。(b) 実行中の `lean` バイナリがこの tag のソースからビルドされたことの機械的確認(commit 文字列 `f054605a…` の一致までは確認)。(c) Lean 側 `betaRev.go` の挙動は Lean ソース(:1593-1620)を読んだもの。

## 2. callsite 表(base `b8a3ddb8`)

### 2.1 Sparkle ソース側(実際に引数が何か)

| extern | 箇所 | `(s,d)` / 引数 | 入力の条件(証明側) |
|---|---|---|---|
| lift | `Elab.lean:3993`、`Elab.lean:4158` | `ty.liftLooseBVars 0 1`、`b.liftLooseBVars 1 1`(`machConv`・`machChain`) | `LetOk 0 ty`、`LetOk 0 b` |
| lift | `MachRawSurface.lean:201`・`205`(`rootFloat`) | `(0,1)`、`(1,1)`、`(0,1)` | `LetOk 0` の `let` 値 |
| lift | `MachRawSurface.lean:100`(`k.liftLooseBVars 0 n`)、`102`(`f`/`a` に `0 i`)、`104`(`dom`/`S`/`β` に `0 i`)、`120`・`122`・`123`(`m`/`inst` に `0 i`)、`124`(`done` に `0 n`)、`148`(`regs`/`tys` に `0 j`) | **全て `s = 0`**、`d` は `n`(リスト長)・`i`(添字)・`j`(let の個数) | `rawNode_ok` の `LetOk 0` 入力 |
| lift | `MachTupleIn.lean:87` `(b.liftLooseBVars 1 1)`、`(dom.liftLooseBVars 0 1)` | (1,1)・(0,1) | **範囲外**(§6) |
| lower | `MachRawSurface.lean:142` `t.lowerLooseBVars i i` | **`s = d = i`** | pair 分岐の component 型 |
| instantiate1 | `Elab.lean:4095`(`machInstanceS` の `inst`、`forallE` 本体に引数)、`4989`(`Nat` の `let`)、`4992`(閉じた `BitVec` の `let`)、`MachRawSurface.lean:220`(`zetaAll`) | 本体 `b`、代入 `a`/`v` | 4095 の `inst`: 型 `ty` と `args` |
| instantiate1 | `Elab.lean:6206`・`7316`・`7430..7459`・`7922..7970`(`fvar` で呼ぶ)、`MachRecUnfold.lean:174`・`262` | 代入が `fvar` / `LetOk` と無関係 | **範囲外**(§6) |
| beta | `MachRawSurface.lean:100`(引数 `PUnit.unit`)・`102`・`120`(引数 `a.liftLooseBVars 0 i`) | **1 引数** | `rawNode_ok` の `LetOk 0` |
| beta | `MachRecUnfold.lean:57`・`161` | 引数の個数が可変 | **範囲外**(§6) |
| replace | `MachRawSurface.lean:212`(`zeroLit`)、呼び出しは `Elab.lean:5088` | `f?` = `BitVec.zero w` を `BitVec.ofNat w 0` に | — |

### 2.2 証明側(`kjob/g3aw-a24` 8fff703c。`git show` で読んだ)

| 仮定 | 使う補題(file:line) | 実際の引数 |
|---|---|---|
| `LiftAgrees`(T1L-50) | `liftRange_of_agrees`(ExternSpec:`liftRange_of_agrees`)→`pureFacts_of`→`readF_good`(ReaderInv:673-676・884-887 の `F.lift ty …`/`F.lift b …`)。等式のまま: `bvarLiftSpec01_of_liftAgrees`(ArgSupply10:22。**入力は `Expr.bvar j` のみ**、`s ∈ {0,1}`、`d = 1`)、`allMemSites_float`(ArgSupply11:392。`hA ty hty` の `.1`、`hA b hb` の `.2`。**入力は一般の `ty`/`b`、全体の等式**)、`memSrcKinds_of_allSites`(ArgSupply12:68) | `(0,1)` を `ty` に、`(1,1)` を `b` に |
| `Inst1Range`(T1L-51) | `instRes_ok`(ReaderInv:335。`n` は暗黙引数)。呼び出し `ReaderInv:817` は `LetOk 0`、`ArgSupply13:65` は `F.instCallS 0 …`、`NormRangeLetOk:128・130`・`NormStepModel:141・143` は `hinst 0 b v …`、`ExtReaderGlue:297・299` は `hO.inst1 0 …` | **調べた範囲で `n ≠ 0` の使用は見つからなかった**(`PureFacts.inst1` の欄は `∀ n` のまま) |
| `ZeroLitAgrees`(T1L-54) | `zeroLit_ok`(PreprocLetOk:151)の使用: `PreprocLetOk:288`、`ArgSupply13` `readSub_letOk` の `root` 分岐 | **どちらも `zeroLit_ok hz 0 _ …`(`n = 0`)** |
| `LiftLooseRange`(T1L-55) | `build_ok`(RawNodeRangeLetOk:235)の `hl regs 0 j hr`・`hl y 0 j …`(:251・:254)、`rawNode_ok`(:428)の `hl _ _ _ …`(:496〜539) | scratch で `s` を落として通った(§3.3)。**`s ≠ 0` が要る箇所は見つからなかった** |
| `LowerLooseRange`(T1L-56) | `rawNode_ok` :553 `hlo t i i ht` | `s = d = i` |
| `BetaRange`(T1L-57) | `rawNode_ok` :496・508・539 の `hb _ _ (hl …) …` | `f = (…).liftLooseBVars 0 i` または `k.liftLooseBVars 0 n`、`a` は lift 済みの式または `PUnit.unit` |

## 3. 行ごと: 最小の仮定候補・導出の筋道・未確認の補題・elaborate 結果

`LetOk` は `Tools.ShippingLetsAliasInv.LetOk`(`Tools/ShippingLetsReaderInvBase.lean:34` の定義。`fvar` の `_machLet j` が `j < n` かだけを見る)。以下の型は **scratch で elaborate した**(根拠は §3.3。コミットしていない)。

### 3.1 候補(原文)と判定

#### T1L-50 — 変更しない(`LiftAgrees`、旧 freeze #1)
```
LiftAgrees : Prop :=
  ∀ e, LetOk 0 e = true → e.liftLooseBVars 0 1 = liftSpec e 0 1 ∧ e.liftLooseBVars 1 1 = liftSpec e 1 1
```
- 等式が必要な理由: `allMemSites_float` が `ty`・`b`(一般の `LetOk 0` 式)で `lift` の**結果そのもの**を `liftSpec` に書き換える。range だけでは足りない(§2.2)。`(s,d)` は既に `(0,1)`・`(1,1)` の 2 組のみで、これ以上は絞れない。
- 「`bvar j` だけの等式」(ArgSupply10 の使い方)に絞る案は、`allMemSites_float` が使えなくなるので**採れない**(この調査では代替経路が見つからなかった)。
- 導出の筋道: 既存。`liftRange_of_agrees`(ExternSpec)。未確認の補題なし。
- 台帳: 1 行のまま。

#### T1L-51 — 旧 freeze のまま(`Inst1Range`、旧 #2)。さらに `n = 0` に絞る案は**未確認**
```
Inst1Range : Prop :=
  ∀ n b a, LetOk n b = true → LetOk n a = true → LetOk n (b.instantiate1 a) = true
```
- 候補(さらに小さい形、**未確認**):
```
Inst1Range0 : Prop :=
  ∀ b a, LetOk 0 b = true → LetOk 0 a = true → LetOk 0 (b.instantiate1 a) = true
```
  `Inst1Range → Inst1Range0` は scratch で `fun b a hb ha => h 0 b a hb ha`(通った)。**逆は言えない**。
- ただし `Inst1Range0` で reader の証明を閉じるには、`PureFacts.inst1`(ReaderInvBase:406、共有定義の欄)を `n = 0` に書き換えるか、`instRes_ok` を `n = 0` に固定して `PureFacts` を別構造に写す必要がある。`PureFacts` の編集は禁止対象に近く(共有定義)、別構造に写すと証明の書き直しが `readF_good` に及ぶ。**この調査では書き直しの規模を見積もっていない。** 採るなら別の freeze 単位で扱う。この文書の推奨は `Inst1Range` のまま。
- 導出の筋道: 既存。`inst1Range_of_agrees`(ExternSpec:128)= `inst1Spec_ok`。等式版 `Inst1Agrees` は B 案(§3.2)。

#### T1L-55 — 推奨: `LiftLooseRange0`(旧 freeze #5 と同じ。**`s = 0` の成立を scratch で確認**)
```
LiftLooseRange0 : Prop :=
  ∀ (e : Lean.Expr) (d : Nat), LetOk 0 e = true → LetOk 0 (e.liftLooseBVars 0 d) = true
```
- 導出の筋道(使う側): `build_ok`・`rawNode_ok` の `hl` を `LiftLooseRange0` に替える。scratch で通った(§3.3)。
- 導出の筋道(仮定を更に小さくする側): この range は `liftSpec_ok`(`∀ n e s d`、既存)から、**B 案**(等式 `LiftAgrees0`、§3.2)があれば `liftSpec_ok 0 e 0 d he` で出る。つまり range は等式より弱い。**range を推奨する理由は、証明が使うのが LetOk 保存だけだから**。
- 未確認: `rawNodeRange_of` を経由して `rawNodeRange_structEnv`(ArgSupply15:20、base に無い)まで通ること。ArgSupply13..15 は 8fff703c にのみあり、この worktree では elaborate していない。

#### T1L-56 — 推奨: `LowerLooseRangeEq`(旧 freeze #6 と同じ。**`s = d` の成立を scratch で確認**)
```
LowerLooseRangeEq : Prop :=
  ∀ (e : Lean.Expr) (i : Nat), LetOk 0 e = true → LetOk 0 (e.lowerLooseBVars i i) = true
```
- 導出: `rawNode_ok` の `hlo t i i ht` → `hlo t i ht`(scratch で通った)。
- B 案の等式 `LowerAgreesEq`(§3.2)+ `lowerSpec_ok` からも出る。

### 3.2 B 案(等式を仮定し range を導く)と、B5(全入力等式)を採らない理由

等式形の候補(scratch で elaborate、`LiftAgrees0` と `LowerAgreesEq` は型が通った):
```
LiftAgrees0 : Prop := ∀ (e : Lean.Expr) (d : Nat), LetOk 0 e = true → e.liftLooseBVars 0 d = liftSpec e 0 d
LowerAgreesEq : Prop := ∀ (e : Lean.Expr) (i : Nat), LetOk 0 e = true → e.lowerLooseBVars i i = lowerSpec e i i
-- lowerSpec は新設(既存に無い):
def lowerGo : Expr → Nat → Nat → Expr   -- liftSpec と同じ形で bvar i ↦ if i < s then bvar i else bvar (i - d)
def lowerSpec (e : Expr) (s d : Nat) : Expr := if s < d then e else lowerGo e s d
```
- 導出(scratch で証明済み): `liftRange0_of_agrees0 : LiftAgrees0 → LiftLooseRange0`、`lowerRangeEq_of_agrees : LowerAgreesEq → LowerLooseRangeEq`(`lowerGo_ok`・`lowerSpec_ok` を含む)。
- 採らない理由: (1) 等式は range より**強い**(range を導けるが逆は言えない)。証明が使うのは range だけ(rawNode)なので、強くする理由が証明側に無い。(2) `lowerSpec` の新設と `lowerSpec_ok` の保守が増える。(3) B5(全入力・全 `(s,d)`)は reader の `LetOk 0` 入力でも `(s,d)` が一般になり、旧 freeze の `(0,1)`/`(1,1)` や `s=0`/`s=d` への絞りを戻す。**ただし B 案の利点: 差分テストが等式を直接検査できる(§5.1)。** どちらを採るかは reviewer の判断。この文書は range(§3.1)を推奨する。
- 注意: `LiftAgrees0`(`s=0`)は T1L-50 の `(1,1)` 半分を含まない。T1L-50 を `LiftAgrees0` で置き換えて 1 行にする案は**成立しない**(`allMemSites_float` が `(1,1)` を使う)。

### 3.3 scratch での elaborate / 証明の結果(コミットしない。`kjob lake env lean`、Lean v4.32.1)

| 実験 | 結果 |
|---|---|
| 候補の型(`LiftLooseRange0`、`LowerLooseRangeEq`、`BetaRange`、`ZeroLitRange`、`ZeroLitRange0`、`Inst1Range0`、`LiftAgrees0`、`LowerAgreesEq`、`InstArr1Range`)を Sparkle の `LetOk` で elaborate | 全て通った(`ZeroLitRange`/`ZeroLitRange0` は `zeroLit inlNatLit canonicalNatLitValue?`、namespace `Sparkle.Compiler.Elab` を open) |
| `LiftLooseRange → LiftLooseRange0`、`LowerLooseRange → LowerLooseRangeEq`、`ZeroLitAgrees → ZeroLitRange`(`zeroLit_ok`)`→ ZeroLitRange0`、`Inst1Range → Inst1Range0` | 通った |
| **`build_ok` と `rawNode_ok`(RawNodeRangeLetOk:235-555 を複製)の仮説を `LiftLooseRange0`/`LowerLooseRangeEq` に替え、`hl _ _ _`→`hl _ _`、`hl regs 0 j`→`hl regs j`、`hl y 0 j`→`hl y j`、`hlo t i i ht`→`hlo t i ht` だけ変更** | **通った。エラーなし、`sorry` なし。** `#print axioms Scratch.rawNode_ok` / `Scratch.rawNodeRange_of0`: `[propext, Classical.choice, Quot.sound]` |
| `liftSpec_ok`(既存)の型 | `∀ (n : Nat) (e : Expr) (s d : Nat), LetOk n e = true → LetOk n (liftSpec e s d) = true`(**一般 `(s,d)`**、変更不要) |
| `lowerGo_ok` / `lowerSpec_ok`(新、一般 `(s,d)`)を `liftSpec_ok` と同じ帰納で証明 | 通った(`LetOk` は `fvar` だけを見るので、`bvar` の書き換えは自明。`Lean` だけを import した複製の `LetOk`/`liftSpec` で確認) |
| `betaRev` の展開 | 外側の `betaRev` は `unfold` できるが、内部の `go`(partial)は `rfl` でも開かない(`(Expr.bvar 0).betaRev #[Expr.bvar 1] = .app …` が `rfl` で失敗)。**`beta` の LetOk 保存は証明できない**ので仮定のまま(§4) |

制約: 上の `rawNode_ok` の通りは `Tools/Prototype/RawNodeRangeLetOk.lean` の複製に対するもの。`rawNodeRange_of`・`rawNodeRange_structEnv`・`siteLetOk_structEnv''` 以降は elaborate していない。

## 4. T1L-54 / T1L-57 の必要性

### T1L-54(`zeroLit`、`Expr.replace`)
- 証明の使用: `zeroLit_ok hz 0 _ …` が 2 箇所(PreprocLetOk:288、ArgSupply13 `readSub_letOk` の `root`)で、**どちらも `n = 0`**。
- 最小形の候補(旧 freeze #4 の `n` を 0 に):
```
ZeroLitRange0 : Prop :=
  ∀ (e : Lean.Expr), LetOk 0 e = true → LetOk 0 (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true
```
- `ZeroLitAgrees`(全 `e` の等式)→ `ZeroLitRange` → `ZeroLitRange0` は scratch で通った(§3.3)。**逆は言えない。**
- `replace` を「全 `f,e` で `replaceNoCache` と等しい」と仮定する(B6 の形)案は、`f` が `zeroLit` の特定の関数 1 つだけなので**一般の `f` は不要**。`zeroLit` 専用の range 形(上)で足りる。C++ 側は §1.2 の通り `replaceNoCache` と同じ走査(読み取りによる)。
- 未確認: `ZeroLitRange0` を下流(`machineShapeN_lets''` が `hz : ZeroLitAgrees` を取る形、PreprocLetOk:329 ほか)に差し込む書き直しの規模。

### T1L-57(`beta` 1 引数)
- 証明の使用: `rawNode_ok` 3 箇所。`BetaRange` は既に 1 引数(`#[a]`)、`LetOk 0` の `f`・`a`。**これ以上絞る形は、この調査では見つからなかった**(`f` が `lam` に限られることは型から出ない)。
- Lean ソース(:1593-1620)を読んだ 1 引数の挙動: `f` が `lam _ _ b _` なら `b.instantiate #[a]`(`lean_expr_instantiate`、**`instantiate1` ではない**)、`mdata _ f'` なら `f'` に再帰(`mdata` を外す)、それ以外(`letE` は `useZeta=false` なので含む)は `.app f a`。この読み取りに基づくモデル `beta1Spec` は scratch の差分テストで 0 不一致(§5.1)。
- 代替案(B 案の beta 版、**推奨しない**): `Expr.instantiate #[a]` の LetOk 保存 `InstArr1Range`(scratch で型は通った)を仮定して `beta` を導くことは、`betaRev.go` が partial で開けないため**この調査では経路が見つからなかった**。`beta` のままの `BetaRange` を維持する。
- `MachRecUnfold.lean:57・161` の `beta`(引数の個数が可変)は範囲外(§6)。

## 5. controls

### 5.1 差分テスト(検査であって証明ではない)
- 範囲(案): (a) **scratch で実施済み**: 擬似乱数(LCG、種 12345)で生成した 200000 組の `Expr`(深さ ≤ 5、`bvar` 添字 < 4、`fvar` は `_machLet j`(`j<3`)と通常名、`lam`/`forallE`/`letE`/`mdata`/`proj`/`app`/`const`/`lit`)と `(s,d,i) < 4` で、実 extern と仕様を比較。
  - `liftLooseBVars s d` = `liftSpec`(`LetOk` に関係なく全入力)、`lowerLooseBVars s d` = `lowerSpec`(`s<d` も含む)と `lowerLooseBVars i i` = `lowerSpec`、`instantiate1` = `inst1Spec b a 0`、`instantiate #[a]` = `inst1Spec b a 0`、`beta #[a]` = `beta1Spec`、`replace f` = `replaceNoCache f`(`zeroLit` 型の `f`)。
  - `LetOk 0` の入力(51771 件)のうち `LetOk 0` の `a` との組(21763 組)で、`lift (0,d)`・`lower (i,i)`・`instantiate1`・`beta` の結果が `LetOk 0`。
  - **結果: 不一致 0**(出力 `N=200000 LetOk0-inputs=51771 LetOk-pairs-checked=21763 mismatches=0`)。
- 範囲外: コーパスの実 `Expr`(reader が実際に見る `LetOk 0` 入力)。`bvar` 添字・`d` が大きい入力。`s,d ≥ 2^32`。共有ノードが多い大きな式。(b) 実コーパスでの実行は**別の単位**(未実施)。結果は「N 件で食い違いなし」の形で書き、「正しい」とは書かない。
- 実コーパス版では、`rootFloat` / `zeroLit` / `machLiftScalarN` / `machBoolMap`(コンパイラ自身の定義、T1L-52/54/58/59)の LetOk 保存も同じ枠で比べられるが、この文書では扱わない。

### 5.2 mutant(signature / defeq での棄却であって、意味的反例ではない)
scratch の `example` で、仮定を強め・弱めた形が型で弾かれるかを見た。✓ = 通る(想定どおり)、✗ = 型エラー(想定どおり棄却)。

| mutant | 結果 |
|---|---|
| `LiftLooseRange`(全 `s`)→ `LiftLooseRange0`(特殊化) | ✓ |
| `LiftLooseRange0` → `LiftLooseRange`(全 `s`)(弱い方から強い方) | ✗ 棄却 |
| `LiftLooseRange0` で `y.liftLooseBVars 1 j` を閉じる(`s=1` の呼び出し) | ✗ 棄却 |
| `LiftLooseRange0` で `y.liftLooseBVars 0 j` を閉じる(`build_ok` の形) | ✓ |
| `LowerLooseRangeEq` で `t.lowerLooseBVars i j`(`i ≠ j`)を閉じる | ✗ 棄却 |
| `LowerLooseRangeEq` で `t.lowerLooseBVars i i` を閉じる | ✓ |
| 前提を `LetOk 1 e`(結論 `LetOk 0`)にした弱め形 → `LiftLooseRange0` | ✗ 棄却 |
| 結論を `LetOk 1 (…)`(前提 `LetOk 1`)にした強め形を `LiftLooseRange0` から | ✗ 棄却 |
| `Inst1Range0`(`n=0` のみ)→ `Inst1Range`(全 `n`) | ✗ 棄却 |
| `Inst1Range` → `Inst1Range0` | ✓ |

注意: これらは**型の向き**の検査で、仮定が実際の C++ の振る舞いと合っているかは検査しない(それは §5.1 の差分テストの役割で、証明ではない)。

## 6. 台帳の差分の見込み、旧 freeze の supersede、範囲外

### 6.1 T1L 行ごと(この文書の推奨を採った場合)

| ID | 旧 freeze(b8a3ddb8) | この文書の推奨 | 台帳の動き |
|---|---|---|---|
| T1L-50 | `LiftAgrees`(元のまま) | **変更なし**(§3.1) | 行は残る。置き換わらない |
| T1L-51 | `Inst1Range` | **変更なし**。`Inst1Range0` は未確認の選択肢(§3.1) | 行は残る |
| T1L-55 | `LiftLooseRange0`(`s=0` は未確認と注記) | **同じ型。`rawNode_ok` で `s=0` を確認**(scratch) | 行は残る。置き換わる仮定の文面は旧 freeze と同じ |
| T1L-56 | `LowerLooseRangeEq`(同) | **同じ型。`rawNode_ok` で `s=d` を確認**(scratch) | 行は残る |
| T1L-54 | `ZeroLitRange`(`n` 一般) | `ZeroLitRange0`(`n=0`)へ絞る**提案**。下流の差し込み規模は未確認 | 行は残る |
| T1L-57 | `BetaRange` | **変更なし**(これ以上絞れる形は見つからなかった) | 行は残る |
| T1L-52/58/59/53 | — | この文書の範囲外(コンパイラの `partial def`、kernel fact) | 変更なし |

- **消える行は無い**(TRUSTED の仮定として残る)。**新しい仮定の追加は無い**(旧 freeze の 9 件の文面の中での絞り・確認)。B5(全入力等式)・B6(`replace` 全 `f,e`)・B7(`beta` 全般)を**採らない**ので、仮定の件数は旧 freeze の 9 のまま増えない。
- **二重計上しない**: この文書の候補は旧 freeze の同番号(#1,#2,#4,#5,#6,#7)の**言い換え・確認**であって別行ではない。T1L-50..59 の 9 行は旧 freeze が数えるものと同じ。
- FG 側: 変更なし(この調査では対応する FG 行は見つからなかった)。FG 102 → 102 (-0 +0)。T1 57 → 57 (-0 +0)。T1 57 に 9 行が全て含まれるかは旧 freeze と同じく未計数。

### 6.2 旧 freeze(`TRUST_EXPR_FREEZE.md`)のどの節を supersede するか
- §1 #5 の「注意(次段で確認すべき点)」と §8 の「`rawNode_ok` の `hl _ _ _` の全使用箇所が `s = 0` か」の未確認: **`rawNode_ok` については確認済み**(scratch、§3.3)に更新。ただし ArgSupply15 以降は未確認のまま。
- §1 #6 の同様の記述: 同上(`s = d`)。
- §1 #4 の「`n` を 0 に絞れるかは未確認」: **`n = 0` で足りる使用を確認**(`zeroLit_ok` 2 箇所)。`ZeroLitRange0` を採るかは reviewer の判断。採れば #4 の原文だけを置き換える(§4 の差し込み規模が未確認)。
- §1 #2 の「`n = 0` で足りるかは未確認」: **使用側は `n = 0` だけ見つかった**が、`PureFacts.inst1` が `∀ n` なので採る場合は別の単位(§3.1)。**この文書は #2 の原文を変えない**。
- §1 #1, #3, #7, #8, #9 と §2(版固定)・§3(差分テスト範囲)・§4 の U2〜U5・§5 の台帳表: **supersede しない**(そのまま有効)。§4 U1 の「唯一元の証明がそのまま通らない可能性のある単位」は、`rawNode_ok'` の証明が引数を減らすだけで通ることが scratch で分かった(§3.3)ので、リスクは下がった(ただし scratch の複製で、コミットされた単位ではない)。
- 旧 freeze 全体は、この文書が reviewer に採用された**範囲(上の #4・#5・#6 の注記と、B5/B6/B7 を採らない判断)だけ**を supersede する。採用されなければ旧 freeze が有効なまま。

### 6.3 範囲外(この文書が閉じないもの)
1. `MachTupleIn.lean:87`(`packTupleInputs`、`liftLooseBVars` (1,1)・(0,1))の入力が `LetOk 0` か。
2. `MachRecUnfold.lean:57・161` の `beta`(引数可変)、`:174・262` の `instantiate1`。
3. elaboration 側の `instantiate1`(`Elab.lean:6206` ほか。`fvar` で呼ぶ)。T1L-51 は reader 側の呼び出しだけを覆う。
4. `ReadTyped` の残り 3 要素(`ConvKind`、`LetSrcKinds`、`CallSrcKinds`)と `argWidthAt_of_closingRun` までの組み立て。
5. `Inst1Range0`(`n = 0`)を実際に使うための `PureFacts` 側の書き換え。
6. `rawNodeRange_structEnv` 以降(ArgSupply15)の elaborate。

## 7. reviewer への質問
1. T1L-55/56 は旧 freeze と同じ range の型(`LiftLooseRange0`・`LowerLooseRangeEq`)で進めてよいか(B 案の等式 + `lowerSpec` 新設は採らない)。
2. T1L-54 を `ZeroLitRange0`(`n = 0`)に絞る提案を採るか。採る場合、下流の差し込みを別の単位として出してよいか。
3. T1L-51 の `n = 0` への絞り(`Inst1Range0`)は、`PureFacts.inst1` の扱いが共有定義に近いので、**この文書では採らず**別の判断に回す、でよいか。
4. 実コーパスでの差分テスト(§5.1 b)を別の単位として出すか。

## 8. この文書が確認したこと / していないこと
- 確認した(コマンドで確かめた): toolchain `leanprover/lean4:v4.32.1`(commit `f054605aea4b840552cca2e725580bffd1e1b704`)、extern の宣言行(§1.1)、Lean tag `v4.32.1` の C++ を取得して読んだ内容(§1.2)、callsite の行(base `b8a3ddb8` の `grep`)、8fff703c の証明側の使用箇所(`git show`/`git grep`)、scratch での elaborate・証明・差分テスト・mutant(§3.3・§5)。`Tools.Prototype.RawNodeRangeLetOk` の `kjob lake build` が成功(510 jobs)したことを scratch の前提にした。
- していない: coder 案の読み取り(Pod から見えなかった)、`rawNodeRange_structEnv` 以降の elaborate、`PureFacts` の `n=0` 書き換えの見積もり、実コーパスでの差分テスト、C++ の `unsigned` 切り捨ての影響、バイナリとソースの機械的同一性、T1 57 の内訳の計数。
