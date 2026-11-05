# C.AC-9 と C.CV-5: carrier を `dataOfAt` に固定し、`hDS` と `hsp/hss/hls/hn` を証明の中で出す

Issue: `sparkle-ledger-ac9cv5`（親 `sparkle-ledger-shorten`）。base: 0d9da1ce。
台帳（受入済み）: FG 87 / T1 57。この文書は台帳を変えない。コーダー指示により freeze と実装を続けて出す（review にしない）。
実装: `Tools/ShippingGen5Cover5R.lean`（CV-5）、`Tools/ShippingGen5AccServedR.lean`（AC-9）。検査: `Tests/Gen5/CV5RCheck.lean`、`Tests/Gen5/AC9RCheck.lean`。
既存ファイル・共有定義は変えない（新しいファイルに「固定した版」を置く）。

## 0. 減算表

| 項目 | C.CV-5 | C.AC-9 |
|---|---|---|
| 消える ID | C.CV-5（`hsp` `hss` `hls` `hn`） | C.AC-9（`hDS : DataOfShape K`） |
| 消える条件 | §2 の文の受理と clean build。BINDERS で 4 つの束縛変数が消えていること | §3 の文の受理と clean build（**この base では未ビルド**、§5） |
| 入る束縛変数 | `hd : dataOfAt lvl E senv sp = some d`（入力の事実 (b)） | `hK : K.dataOf = dataOfAt lvl`（carrier の固定。下の注） |
| 残る条件 | `hs`（state 側 4 事実。`StateSideWitness` から出せる: `shapeAgree_of_witness`）、C.CV-4（`hbr`） | `hcl`、`MachineRouteAt`、`ReachCover`（C.SM-1）、`ReadsSupplyAt` |
| 台帳への効果 | FG −1（見込み）。受理前なので「台帳:」行は動かさない（条件付き台帳: FG 86 / T1 57。AC-9 の −1 は未ビルドのため見込みに含めない） | 同左（未ビルド） |
| 新しい TRUSTED / law / コンパイラ変更 | なし | なし |
| 新しい前提の行 | なし。`hd` は `dataOfAt` の結果という入力の事実 | `hK` は kit の `dataOf` 欄が `dataOfAt lvl` であるという等式で、`mkKit (dataOfAt lvl) …` で作った kit では `rfl`（`mkKit_dataOf`）。台帳の行ではないと読んだが、行として数えるかは reviewer が判断（数えるなら AC-9 は純差分 0） |

## 1. 何をするか

* CV-5: `d` 側の 4 事実は `dataOfAt_dims`（`dims_of_dataOfAt` と同内容）の結論そのもの。`hd` から出して `shapeAgree_of_sides`（Cover5 T4）に渡す。
  調査の読み（`st` は `readerTrace_final` の結論の ∃ 変数）に沿い、`shapeAgree_of_witness` は `StateSideWitness` の `st` をそのまま使う（新しい ∃ を作らない）。
* AC-9: `DataOfShape K` は `K.dataOf E se s = some d → d.shape = s`。`K.dataOf = dataOfAt lvl` なら `dataOfAt_dims` の `.1`。`accServed0_of_cover` にそのまま渡す。
  `DataSound` / `mkKit_dataSound` は使わない（`d.shape = s` だけで足りる）。`RunDataLink` は cover 形の前提ではない（route 形 `accServed0_of_route` のみ）。

## 2. 凍結する文: C.CV-5（`Tools/ShippingGen5Cover5R.lean`）

```lean
theorem shapeAgree_of_sidesR {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    {lvl : Lean.Expr → Nat} {E : ConstantInfo} {senv : StructEnv}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d) :
    ShapeAgree d st

theorem shapeAgree_of_witness {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat}
    {p : ShapePre} {en : Lean.Expr} {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (w : StateSideWitness E senv sp n p en st0 env st1 st v)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d) :
    ShapeAgree d st
```

対応: `shapeAgree_of_sides` の Prop 束縛 `[hs, hsp, hss, hls, hn]` → `[hs, hd]`（`hsp hss hls hn` が消え `hd` が入る）。結論は同じ `ShapeAgree d st`。

## 3. 凍結する文: C.AC-9（`Tools/ShippingGen5AccServedR.lean`）

```lean
theorem dataOfShape_of_dataOfAt (K : AssignKit ι dom env₀) (lvl : Lean.Expr → Nat)
    (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl) : DataOfShape K

theorem accServed0_of_coverR (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop)
    (lvl : Lean.Expr → Nat)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hcov : ReachCover K Reach)
    (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl)
    (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach
```

対応: `accServed0_of_cover` の `[hcl, hRoute, hcov, hDS, hRS]` → `[hcl, hRoute, hcov, hK, hRS]`（`hDS` が消え `hK` が入る）。結論は同じ `AccServed0Stmt K L Reach`。

## 4. 検査

* CV-5（`CV5RCheck`、**agent の target build exit 0、737 jobs**）: TYPE 2、MUTANT 3（`hd` なし／`hs` なし／`hd` を `d.shape = sp` だけに弱めた版。いずれも signature / defeq での棄却であって意味的反例ではない）、BINDERS 1（`[hs, hsp, hss, hls, hn]` − 4 + `[hd]` = `[hs, hd]` を機械比較）、AXIOMS 2（標準 3 つ）。
* AC-9（`AC9RCheck`、**未ビルド**）: TYPE 2、MUTANT 3（`hK` なし／`hcl` なし／`hDS` を残した版）、BINDERS 1、AXIOMS 2 を同じ形で書いたが、一度も elaborate していない。

## 5. 未ビルドの理由（AC-9）

`kjob lake build Tools.ShippingGen5AccServedR` は import 先の `Tools.ShippingGen5AccKeep` で失敗した。最初の失敗は `AccKeep.lean:199` の `whnf` の heartbeat 超過、`maxHeartbeats 0` を一時的に足して（コミットしていない）再実行すると `AccKeep.lean:200:4: Type mismatch`。
`AccKeep` の旧ビルド（5c38c6fc）以降に `Tools/ShippingGen2KeepChild.lean` が変わっており（00c93ab7 rt87: `entryInlinerError?` の分岐と `Triple.ite` を追加）、この調査では `AccKeep` がこの base で通らない原因はこの変更だと読んでいるが、確認はしていない。
既存ファイルは編集できないため、AC-9 のビルドと Check は coder の判断待ち（`AccKeep` の修正、または AccServed を使わない経路）。AC-9 の Lean は未検証で、証明が通るとは主張しない。

## 6. 主張しないこと

* `dataOfAt` が実際の run で `some` であること、`hd` の `E` `sp` が run の `entryConst` と `shapeEq` に一致すること（この調査では供給元・経路を確認していない）。
* `K.dataOf = dataOfAt lvl` を満たす実際の kit の構成（`GDEvidence`、`genData₀` など）、`ReachCover`、`ReadsSupplyAt`、C.CV-4（`hbr`）。
* FG 台帳の数の変更、非空虚性（`hd` `hK` を満たす具体例の構成）。
