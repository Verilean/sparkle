# D.T-2（`CallOutRange`、PA 非リーフ）: CallTie の root に `CallOutRange` の束縛変数が無いことの確認

Issue: `sparkle-ledger-dt2`（親 `sparkle-ledger-shorten`）。base: kjob/flow1-b e6d8e55b（U1・U2 承認済みの tree。`Tools/ShippingGen5T1ND.lean` を含む）。
検査: `Tests/Gen5/DT2Check.lean`。新しい定理は無い（既存の定理の束縛変数を調べるだけ）。台帳（受入済み）: FG 84 / T1 57。この文書は台帳を変えない。

## 0. 減算表

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | D.T-2（`hDG_SEM_range : CallOutRange p q k hk`、PA、非リーフ） |
| 消える条件 | `CallTie` を出す root の束縛変数に `CallOutRange` が無く、`callOutRange_of_widths`（`Tools/ShippingGen5T2Range.lean:162`）の材料が既存の行（下の表）で Lean の中で供給されていること。reviewer の承認 |
| 旧 | `callTie_of_served`（`Tools/ShippingGen5T2Tie.lean:276`）の `hDG_SEM_range`。Check の対照で、この定理だけが `CallOutRange` の束縛変数を持つことを確かめる |
| root | ND root `callTie_of_served_oneOut_t1ND`・`callTie_of_served_kidW_closing_t1ND`（`Tools/ShippingGen5T1ND.lean:90,107`、built g5nd2-b1e4bdbf）。run 側の U1 root `callTie_of_run_one_ex`・`callTie_of_run_group_kidW`（`Tools/ShippingGen5Flow1Tie.lean`、承認済み、D.T-8/D.T-9 の解消に使った定理） |
| 入る束縛変数 | 新しいものはない。下の表のとおり、どれも既存の行 |
| 台帳への効果 | 非リーフ −1（FG 84 → 83、リーフ 58 は不変）。A.P-24（FG 台帳 §12.11）と同じ「束縛変数が Lean で既存の行に置き換わった」型 |
| 新しい TRUSTED / law | なし |

## 1. root の束縛変数と台帳の行

ND root（one-output / group）:

| 束縛変数 | 台帳の行 |
|---|---|
| `L`、`P`、`p q k hk`、`Reach`、`DataOk` | A.P-01（`Laws`）、carrier と入力（数えない値） |
| `H : T1HypND` | C.CR-4 / D.T-6（T1 側。`houtTy` は `houtTy_of_closingND` が `H.defines` と closing の witness から出す = D.T-9、解消済み） |
| `hRp`、`hPp` | `Reach p.decl`、`P p.decl = some p`（T1Hyp.pkg の入力） |
| `hord`（その `k` が ordinary call） | C.SM-7 と同じ guard（PA。`h_D_T1` の前件にもある） |
| `hDG_GENP` | D.T-7（`calleePkg_of_t1ND` で T1 の `pkg` に帰着） |
| `hDG_CLOSINGRUN` | ClosingRun の行（D.T-5 は §4 で ClosingRun に統合。C.CR-2 ほか） |
| `hDG_SEM` | D.T-1 |
| `h1`、`hOW`（one-output） | `instFields = []` の場合分け、A.P-25 / D.T-3（`OneOutWidth`、T1L-14） |
| `hG`、`hkidW`（group） | `instFields ≠ []` の場合分け、D.T-4 |

U1 root は ND root の `hDG_CLOSINGRUN` を run 側の前提（`hs hd0 hIH hKI hrun Gen hGen` と `hord`）に置き換えた定理。この tree の U1 は旧 `closingRun0_of_run` を使っていて、全パッケージの `hord`（A.P-26）を束縛変数に持つ。A.P-26 は `closingRun0_of_runR`（par/hord-run bb050d37）で既に除いた行で、この tree には hord-run が無い。D.T-2 の判断は ND root で足り、U1 は「run 側の root にも `CallOutRange` が無い」ことの補足として載せる。

## 2. 検査（`Tests/Gen5/DT2Check.lean`）

* 束縛変数の型が使う定数（`Expr.getUsedConstants`）で調べる。文字列の比較ではない。
* 対照: `callTie_of_served` では `CallOutRange` を使う束縛変数がちょうど `[hDG_SEM_range]`。
* 4 つの root の束縛変数は `CallOutRange` も `CallOutWidthAt` も使わない。結論は `CallTie` の文。束縛変数の名前を印字する（上の表と照らす）。
* AXIOMS: 4 root を印字する（標準の 3 つ以外が出ないことを build log で確かめる）。

## 3. 主張しないこと

* D.T-1 / D.T-3 / D.T-4 / ClosingRun の行の供給、`T1Hyp.dec`（A.P-17）の組み立て、FG。
* リーフの変化（無い）。
