# AC9KIT: C.AC-9 の組み立て（Acc の kit を `mkKit (dataOfAt lvl) …` に固定する）

Issue: `sparkle-ledger-ac9`（親 `sparkle-ledger-shorten`）。base: 9a63e144（par/ac9）。計画: aa638b35 の `scripts/gen5/ASSEMBLY_COST.md` §1（reviewer 承認済み）。
実装: `Tools/ShippingGen5AccKit.lean`。検査: `Tests/Gen5/AC9KitCheck.lean`。台帳（受入済み）: FG 85 / T1 57。この文書は台帳の数を変えない。
状態: 未 build（この文書の時点）。build 結果は Issue の note に書く。

## 0. 減算表

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | C.AC-9（`hDS : DataOfShape K`、リーフ）。受理されたときだけ |
| 入る束縛変数 | `lvl`（非 Prop）、`initsOf`（非 Prop）、`hs : DataOfSound (dataOfAt lvl) initsOf`（**既存行 C.SM-1**）、`genData₀`（非 Prop の carrier） |
| 消える束縛変数 | `K`（固定される）、`hDS`。`hK` は束縛変数にならない（`mkKit_dataOf` で `rfl`） |
| 残る条件 | `hcl`、`ReachCover`（C.AC-4）、`GatesNoneAt`（C.AC-5）、`ClosesOfShape`（C.AC-6）、`ReadsSupplyAt`（C.AC-7）、`hs`（C.SM-1） |
| 新しい TRUSTED / law / 台帳の行 | なし。`hs` は既存の C.SM-1 と同じ型（§3）。数えて純差分は FG −1（C.AC-9）、T1 0、新規行 0 の見込み。受理は reviewer |
| 台帳への効果 | 条件付き台帳: FG 84 / T1 57。受入済みの台帳は変えない |

## 1. 凍結する文

`K` は次の項（ASSEMBLY_COST §1.1。`GenData` の kit の 4 定理は `Tools/ShippingGen5AccGenDataKit.lean`、`ordCallees₀_mem` は `AccOrdCallees.lean`）。Lean では `local macro accKit%` で書く（展開後の項は同じ）。

```lean
mkKit (dataOfAt lvl) (fun E => GenData (dataOfAt lvl) E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
  (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
  (genData_gdEvidence _) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)

theorem accServed0_of_cover_gatesK (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (dataOfAt lvl) initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env₀)))
    (L : Laws mref cref) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge (accKit%) X c → Reach c)
    (hcov : ReachCover (accKit%) Reach) (hG : GatesNoneAt env₀ Reach)
    (hC : ClosesOfShape env₀ L Reach) (hRS : ReadsSupplyAt env₀ L Reach) :
    AccServed0Stmt (accKit%) L Reach
```

証明: `accServed0_of_cover_gatesR (accKit%) L Reach lvl hcl hcov (mkKit_dataOf …) hG hC hRS`（`hK` は `mkKit_dataOf`）。

## 2. 束縛変数の差分（元の `accServed0_of_cover_gates` との比較）

| 束縛変数 | 元 | 新 |
|---|---|---|
| `K` | あり | なし（`mkKit …` に固定） |
| `hDS` | あり | なし |
| `hK` | （R 版にあり） | なし |
| `lvl`, `initsOf`, `hs`, `genData₀` | なし | 追加 |
| `L Reach hcl hcov hG hC hRS` | あり | 同名（型は `K := mkKit …` を代入すると `==`） |
| 結論 | `AccServed0Stmt K L Reach` | `AccServed0Stmt (mkKit …) L Reach` |

## 3. `hs` と C.SM-1

`hs : DataOfSound (dataOfAt lvl) initsOf` は、`factsOf_genS_assembled''`（`AccGenDataKit.lean`）の `hs : DataOfSound dataOf initsOf` を `dataOf := dataOfAt lvl` としたものと同じ型（Check で `==`）。CKIT_FREEZE と CANDA_FREEZE はこれを C.SM-1 として数えている。
注意: `DataSoundAt f`（`AccDataAgree.lean`）は `DataOfSound` の最初の 3 conjunct だけ（`initOk` が無い）。同じ型ではないので、Check は `hs` が `DataSoundAt (dataOfAt lvl)` ではないことを対照に入れる。

## 4. 検査（AC9KitCheck）

(1) `K`・`hDS`・`hK` が新しい束縛変数に無い。(2) 追加は `lvl initsOf hs genData₀` だけ、除去は `K hDS` だけ。(3) 共通の束縛変数の型は、`K := 結論中の mkKit 項` と古い束縛変数を同名の新しい束縛変数に置き換えると `==`。(4) 結論は `AccServed0Stmt (mkKit …) L Reach`、古い結論を同じ置き換えにかけたものと `==`。(5) `hs` の型が `factsOf_genS_assembled''` の `hs` と `==`。対照: `K` を置き換えない比較は不合格、`hs` は `DataSoundAt` ではない。(6) AXIOMS（標準 3 つ）。
mutant は signature / `==` による棄却で、意味的な反例ではない。

## 5. 主張しないこと

* `genData₀`・`ReachCover`・`GatesNoneAt`・`ClosesOfShape`・`ReadsSupplyAt`・`hs` の供給（この調査では供給元・経路が見つからなかったものは束縛変数のまま）。C.AC-7 の `L'` は扱わない。
* 台帳の数の変更、FG の縮小、新しい law / TRUSTED。`hK` を行と数えるかは reviewer の裁定（承認済み: carrier 固定で、行ではない）。
* build 前は何も elaborate していない。
