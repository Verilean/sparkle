# AC9: C.AC-9（`hDS : DataOfShape K`）を Acc 系の最上位で除く

Issue: `sparkle-ledger-ac9`（親 `sparkle-ledger-shorten`）。base: 3cd32441（par/cv56 = rad + CV6/CV5/CV56）。
実装: `Tools/ShippingGen5AccKeep.lean` の修正（4191960a）、`Tools/ShippingGen5AccServedR.lean`（rt184）、`Tools/ShippingGen5AccRouteR.lean`（545d2b46）。
検査: `Tests/Gen5/AC9RCheck.lean`、`Tests/Gen5/AC9TopCheck.lean`。台帳（受入済み）: FG 85 / T1 57。この文書は台帳を変えない。

## 0. 減算表

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | C.AC-9（`hDS : DataOfShape K`、リーフ） |
| 消える条件 | `accServed0_of_cover_gatesR` の受理（reviewer: 前提の除去と、`hK` の数え方） |
| 入る束縛変数 | `hK : K.dataOf = dataOfAt lvl`（kit の `dataOf` の欄を reader の `dataOfAt lvl` に固定する等式）と、非 Prop の `lvl` |
| 残る条件 | `hcl`、`ReachCover`（C.AC-4 / C.SM-1）、`GatesNoneAt`（C.AC-5）、`ClosesOfShape`（C.AC-6 = A.P-07）、`ReadsSupplyAt`（C.AC-7） |
| root theorem | `accServed0_of_cover_gatesR`。元の `accServed0_of_cover_gates`（`Tools/ShippingGen5AccRoute.lean`）は他の定理から使われていない、Acc 系の最上位 |
| 台帳への効果 | (a) `hK` を carrier の選択とみる（行ではない）なら リーフ −1（85 → 84）。(b) `hK` を新しい行と数えるなら 0 |
| 新しい TRUSTED / law | なし |

`hK` について: `mkKit (dataOfAt lvl) …` で作った kit では `rfl`（`mkKit_dataOf`、`Tools/ShippingGen5AccMkKit.lean:41`）。FG の組み立てで kit を `mkKit (dataOfAt lvl) …` に決めれば、`hK` は証明の中で `rfl` で消える。調査（BINDER_EXIT_CENSUS §2.4）は「carrier を `dataOfAt` に固定する」ことを候補 ④ とし、C.CV-5 と C.CV-6 は reader の root（`dataOfAt` を使う）で既に受理された。

## 1. 前提の修正（文は変えない）

`Tools/ShippingGen5AccKeep.lean` は rad（aab355f2）で elaborate しなかった（`acck-aab355f2` exit 1、199 行で heartbeat 切れ）。
原因: rt83（9fbe5e2a）で `doSynth` に燃料切れの `entryInlinerError?` の throw が入った。00c93ab7 は `ShippingGen2KeepChild.core_tripleAInv` を合わせたが、その写しの AccKeep は直されていなかった。
同じ 6 行（プログラムの字面に `if … then throwError … else`、証明に `Triple.ite` と `tripleA_throwErr`）を足した。定理の文は変わらない。
rad の Acc 系の受理済みの結果は、この修正の前は build できない状態だった。

## 2. 凍結する文

```lean
theorem dataOfShape_of_dataOfAt (K : AssignKit ι dom env₀) (lvl : Lean.Expr → Nat)
    (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl) : DataOfShape K

theorem accServed0_of_cover_gatesR (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop)
    (lvl : Lean.Expr → Nat)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hcov : ReachCover K Reach) (hK : K.dataOf = Tools.ShippingGen5DataOf.dataOfAt lvl) (hG : GatesNoneAt env₀ Reach)
    (hC : ClosesOfShape env₀ L Reach) (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach
```

## 3. 検査

* AC9TopCheck: 新旧の telescope を同時にたどり、`lvl` を飛ばし、`hDS` の位置に `hK` があることだけを例外として、他の束縛変数（名前・info・型）と結論を `==` で比べる。`hDS` は新しい定理の束縛変数に無い。対照: 例外なしの比較は不合格。AXIOMS（標準 3 つ）。
* AC9RCheck（rt184）: `dataOfShape_of_dataOfAt`・`accServed0_of_coverR` の TYPE / MUTANT / BINDERS / AXIOMS。

## 4. 主張しないこと

* kit の具体的な構成（`GDEvidence` など）、`ReachCover`・`GatesNoneAt`・`ClosesOfShape`・`ReadsSupplyAt` の供給、FG。
