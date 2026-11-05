# RT pass_ph: memo (`Std.HashMap Expr Expr`) と `EquivBEq Expr` / `LawfulHashable Expr` の調査（rt120）

調査のみ。Lean ソース未編集。台帳: FG 94 / T1 54（今回 0 / 0）。base は par/rt-pass-ph-int2 62d487e1。
scratch は `scripts/gen5/RT_PASS_PH_MEMO_scratch.lean.txt`（`kjob lake env lean` で elaborate、`#synth` 3 行以外はエラーなし、sorry / axiom なし）。

## 1. 事実

- memo の型は `PM := ExceptT String (StateM (Std.HashMap Expr Expr))`（`Sparkle/Compiler/MachRecUnfold.lean:327`）。`passM` は `(← get).get? e` の hit なら返し、miss なら `passStep` の後で `modify (·.insert e r)`。
- `MemoGoodL s := ∀ k v, s.get? k = some v → ∀ L, GL L k → GL L v`（`Tools/PassPh/Defs.lean`）。
- `Expr` の `BEq` は extern の `Expr.eqv`（alpha 同値、binder 名は無視）。`#synth EquivBEq Expr` / `LawfulHashable Expr` / `PartialEquivBEq Expr` は **すべて失敗**（core にインスタンスがない）。
- Std の補題（Lean v4.32.1）: `getElem?_insert`、`toList_insert_perm`、`mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some`、`getElem?_eq_some_iff_exists_beq_and_mem_toList` はいずれも `[EquivBEq α] [LawfulHashable α]` を要る。`mem_toList_insert` と `get?_eq_some_iff` は存在しない。`toListModel_expand`（insert が内部で呼ぶ rehash）も `PartialEquivBEq` を要る。

## 2. 結論 1: 「`EquivBEq` / `LawfulHashable` だけ」では足りない

rt114 の STOP コメントは `EquivBEq` / `LawfulHashable` を挙げたが、それだけでは `MemoGoodL` は `insert` で保てない。`get? k (s.insert e r)` は `e == k` なら `some r`。必要な含意は `GL L k → GL L r` だが、手元にあるのは `GL L e → GL L r`。したがって **`e == k` から `GL L k → GL L e` を得る** 必要があり、これは `Expr.eqv` が不変量を保つという別の事実（`EquivBEq` は `==` の反射・対称・推移だけを言い、`GL` には触れない）。

この点は memo の形を変えても避けられない。hit 側も同じ: `get? e = some v` は「ある entry (k, v) で `e == k`」を意味し、不変量は `GL L k` についてしか何も言わないので `GL L e → GL L k` が要る。entry の値だけを使う形（「get? の結果はどれかの entry の値」）でも、その entry と入力 `e` を結ぶ事実が `e == k` だけなので同じ。任意の `BEq` では `e == k` が全ての `k` で成り立ち得て、`passM` の結果と入力 `e` に関係がなくなる（検査の失敗ではなく、定理の文が偽になり得る）。

既存の T1L-72 `ExprEqvAtom`（`a == b = true`、`b` が fvar / const の atom → `a = b`）は **atom の `b` にしか効かない**ので、一般の `e == k` には使えない（この調査では、そこから出す経路は見つからなかった）。`KeySound`（`a == b → a = b`、`Tools/ShippingCacheSoundness.lean`）は `Expr.eqv` が binder 名を無視するため偽の見込みで、使わない。

## 3. 結論 2: 要らない形（探索結果）

| 形 | 結果 |
| --- | --- |
| `MemoGoodL` を `∀ (k,v) ∈ s.toList` の形にする | `toList` の挿入補題が全て `EquivBEq` + `LawfulHashable` を要る。素の `BEq` で手で証明するには `Raw₀.insert` / `expandIfNecessary` の内部を直接扱う必要がある。`exists_bucket_of_update` は法則なしだが、`toListModel_expand` が `PartialEquivBEq` を要る。この調査では実施せず（可能かどうかは未確認）。しかも hit 側の `GL L e → GL L k` は残る |
| `get?` の結果が「どれかの entry の値」であることだけを使う | §2 の理由で、`e` と entry を結ぶ事実が要るため不可 |
| 法則なしの `get?_insert` | 任意の `BEq` では偽（bucket 内の置換で古い entry が見え始める）。rt114 の指摘どおり |

## 4. 結論 3: 最小の追加仮定

`P L e := GL L e`（`NoPh e ∧ BvarLt L e`）として、次の 3 つの事実で `MemoGoodL` の保存が通る（scratch で elaborate 済み）。

```lean
-- (a) [EquivBEq Expr]   (b) [LawfulHashable Expr]
def EqvPres : Prop := ∀ a b : Lean.Expr, (a == b) = true → ∀ L, GL L a → GL L b   -- (c)
theorem memoGoodL_insert [EquivBEq Expr] [LawfulHashable Expr] (hE : EqvPres)
    {s} (hs : MemoGoodL s) (e r) (hr : ∀ L, GL L e → GL L r) : MemoGoodL (s.insert e r)
theorem memoGoodL_hit (hs : MemoGoodL s) (h : s.get? e = some v) : ∀ L, GL L e → GL L v   -- 定義そのもの
theorem memoGoodL_empty : MemoGoodL ∅
```

`EqvPres` は片方向で足りる（対称性は `EquivBEq` から）。(c) が成り立つ理由: `Expr.eqv` は binder 名・binder info を除いて構造が一致する alpha 同値で、`NoPh`（fvar id の tag）と `BvarLt`（bvar 番号と binder の深さ）はどちらも binder 名に依存しない。ただしこれは `Expr.eqv` の extern 実装についての文で、Lean の論理内では導けない。

台帳への影響（reviewer が判断）: (a)(b)(c) を **1 行に束ねて T1 +1**（案 A: 「`Expr.eqv` は `GL` を保つ alpha 同値で、`hash` と整合する」）、または 3 行で T1 +3（案 B）。推奨は案 A（同じ extern `Expr.eqv` についての 1 つの性質の束で、使い道が `MemoGoodL` の保存だけ）。条件付き台帳は T1 55（案 i）から 56 になる。reviewer 承認が要る freeze の材料として、`passM_goodL` / `passStep_goodL` / `passSpine_goodL` / `passWith_ph` / `pass_ph` の仮説に `[EquivBEq Expr] [LawfulHashable Expr] (hE : EqvPres)`（または束ねた 1 つの Prop）を足す提案になる。型や意味の変更なので、freeze 改訂（rev3）を reviewer に出す必要がある。

## 5. 代替（仮定を増やさない案、未検証）

- `passM` が使う memo を別実装に差し替えることは不可（コンパイラ本体は編集禁止）。
- `Expr.eqv` を使わず、`Expr.equal`（構造等価）の `KeySound` 型の仮定にすることも、同様に extern の仮定で、T1 +1 の別形にすぎない。
- (c) を `GL` に限らず `NoPh` と `BvarLt` に分けても数は変わらない。

## 6. 次

reviewer / coder: 案 A / B の選択と freeze rev3 の要否。承認があれば、`memoGoodL_insert` を `Tools/PassPh/Defs.lean` 相当の新規ファイルに置き、joint 帰納（`passM_goodL` の insert 腕）で使う。mutant の扱い: 本調査に mutant はない。
