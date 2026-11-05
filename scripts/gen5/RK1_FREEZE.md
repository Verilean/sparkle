# RK1: FG の前提の文から C.RK-1（`h_C_RK1 : ReadKeeps cref`）を除く

Issue: `sparkle-ledger-rk1`（親 `sparkle-ledger-shorten`。調査 `scripts/gen5/BINDER_EXIT_CENSUS.md` §2.1、reviewer 承認 2ce38c69）。
base: 2ce38c69（par/binder-census）。実装: `Tools/ShippingGenFGLedgerPremisesR.lean`、検査: `Tests/Gen5/FGLedgerPremisesRCheck.lean`。
台帳（受入済み）: FG 88 / T1 57。この文書は台帳を変えない。

## 0. 減算表

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | C.RK-1（リーフ） |
| 消える条件 | 下の 3 つの文の受理（reviewer: 前提の除去）と exact-head build exit 0 |
| 残る条件 | C.EN-4（`CellPrem`）。C.EN-4 が TRUSTED かどうかの A/B/C 判断（DG_ENV_FREEZE §4）は動かない。C.EN-4 が採用されない場合は C.RK-1 の支払い元も無くなる |
| root theorem | `fgLedgerPremisesStmtR_iff : FGLedgerPremisesStmtR ↔ FGLedgerPremisesStmt` |
| 台帳への効果 | 一般 FG のリーフ −1（88 → 87）。新しい行なし。T1 は変わらない |
| 新しい TRUSTED / law / コンパイラ変更 | なし |

## 1. 根拠

* `CellPrem MkRefd mref cref`（`Tools/ShippingGen5EnvFrame3.lean:58`）の 9 番目の連言は `ReadWorld cref`。
* `ReadWorld.readKeeps : ReadWorld r → ReadKeeps r`（`Tools/ShippingStRefCorrespondence.lean:31`、証明済み）。
* よって `h_C_EN4` から `h_C_RK1` が出る。FG の前提の文 `FGLedgerPremisesStmt`（`Tools/ShippingGenFGLedgerPremises.lean:30`）で、`h_C_RK1` は `h_C_EN4` から導ける冗長な束縛変数。

## 2. 凍結する文

```lean
theorem readKeeps_of_cellPrem {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (h : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref) :
    Tools.ShippingStRefCorrespondence.ReadKeeps cref

-- FGLedgerPremisesStmtR: FGLedgerPremisesStmt の字面から
--   (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)                                 -- C.RK-1
-- の 1 行を除いたもの（他の束縛変数・順序・名前・結論は同じ）

theorem fgLedgerPremisesStmtR_iff : FGLedgerPremisesStmtR ↔ FGLedgerPremisesStmt
```

## 3. 検査

* BINDERS: 2 つの文の telescope を同時にたどり、旧の `h_C_RK1` だけを飛ばして、名前・binder info・型・結論を `==` で比べる。飛ばした束縛変数が後で使われていないことも確かめる。対照: 飛ばさない場合と、`h_C_EN4` を代わりに飛ばす場合は不一致になる。
* TYPE 2（`readKeeps_of_cellPrem`、`fgLedgerPremisesStmtR_iff`）、AXIOMS 2（標準の 3 つだけ）。

## 4. 主張しないこと

* FG の証明、C.EN-4 の供給、C.EN-4 が TRUSTED かどうか。`FGLedgerPremisesStmt` 自体と同じく条件付きの文の整理。
* リーフ以外の行の変化。
