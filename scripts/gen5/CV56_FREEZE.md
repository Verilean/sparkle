# CV56: C.CV-5 と C.CV-6 を reader の root で除く

Issue: `sparkle-ledger-ac9cv5`（C.CV-5）。C.CV-6 の差し戻し（`sparkle-ledger-cv6`、reviewer 2026-11-05「hms・hd を reader/run の shapeEq と C.SM-1/DataOf の被覆から同じ E・sp で得て、最終定理の束縛変数の差分を Check で示す」）への回答を兼ねる。
base: 614f37be（kjob/rt184 = par/cv6 0d9da1ce + rt184 の Cover5R）。実装: `Tools/ShippingGen5ReaderTraceFinalB1.lean`、検査: `Tests/Gen5/ReaderTraceFinalB1Check.lean`。
台帳（受入済み）: FG 87 / T1 57。この文書は台帳を変えない。

## 0. 減算表

| 項目 | C.CV-5 | C.CV-6 |
|---|---|---|
| 消える束縛変数 | `hsp hss hls hn`（reader state と `d` の寸法の 4 事実） | `hcb`（call binder の kind） |
| root theorem | `readerTrace_final`（`Tools/ShippingGen5ReaderTraceFinal.lean`、§12.8 で前提を台帳に数えた root、378f8e31） | `readerTrace_final_b1`（新規。束縛変数は `readerTrace_final` と同じ） |
| 消える根拠 | root が自分の `hd` から `dims_of_dataOfAt` で出している（既存の証明。束縛変数に無い） | `rowB1_of_dataE` に root の `h`（`machineShape? false [] E (structEnv env) = some sp`）と `hd`（`dataOfAt lvl E (structEnv env) sp = some d`）を渡す。同じ `E`・`sp` |
| 新しい束縛変数 | なし | なし（`readerTrace_final` と同じ列） |
| 残る条件 | `readerTrace_final` の仮定（§12.8 で計上済み）。`hd`・`h` は root の入力（C.SM-1 の被覆半分と G3-SHAPE の側） | 同左。GenWF の他の行（a1〜a4、b23、c）は C.SM-6 に残る |
| 台帳への効果 | リーフ −1 | リーフ −1 |
| 新しい TRUSTED / law | なし | なし |

合計の見込み: FG 87 → 85（リーフ）。受理されるまで台帳は変えない。

## 1. 凍結する文

```lean
theorem readerTrace_final_b1
    -- readerTrace_final の束縛変数の列そのまま（hE hla hi1 hr hh hbt hEq env hK hC hD hv hbr hraw hnode hrr hfb
    --   {ci0 E} hci hbranch {dd} hEd {sp} h {lvl d} hd）
    : (readerTrace_final の結論) ∧ (∀ k, k < d.shape.insts.length → callKind d k ≠ .domain)
```

字面は `Tools/ShippingGen5ReaderTraceFinalB1.lean`。束縛変数は `readerTrace_final` の source から機械的に写し、Check で一致を確かめる。

## 2. 検査

* BINDERS: `readerTrace_final_b1` と `readerTrace_final` の telescope を同時にたどり、名前・binder info・型を `==` で比べる（全部一致）。結論は `C ∧ B1` で、`C` は root の結論と `==`。
* 消えた行の名前（`hcb`、`hsp`、`hss`、`hls`、`hn`）がどちらの束縛変数にも無い。
* 対照: `rowB1_of_dataE`（違う telescope）との比較は不一致。結論が root の結論と等しい場合は不合格にする。
* AXIOMS: 標準の 3 つだけ。

## 3. 主張しないこと

* GenWF 全体の組み立て（C.SM-6）、`readerTrace_final` の仮定の供給、FG。
* C.AC-9（`Tools.ShippingGen5AccKeep` が base で elaborate しないため未実施。別の単位）。
