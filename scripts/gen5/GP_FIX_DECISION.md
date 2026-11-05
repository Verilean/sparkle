# 判断資料: FG のパッケージ carrier `GP` を生成器の表 `genP` に固定するか（D.T-1 / C.SM-7 / D.D-3）

Issue: `sparkle-ledger-gpfix`（親 `sparkle-ledger-shorten`）。台帳（受入済み）: FG 83 / T1 57（FG 台帳 §12.15、36484663）。この資料は台帳を変えない。Lean は書いていない。

## 1. 前提知識なしの説明

* FG の前提の文 `FGLedgerPremisesStmtR`（par/rk1 `Tools/ShippingGenFGLedgerPremisesR.lean`）は、パッケージの表 `GP : Environment → Pkgs` を**任意の carrier**として全称で取る（台帳 D.D-3）。
* そのため「呼び出しの先のパッケージが生成器の意味と合う」ことを、仮説 `h_D_T1 : … → GenExtAtCall p q k hk`（台帳 D.T-1）として取っている。その中の「ordinary な呼び出しである」ことの guard は C.SM-7。
* 生成器の側には、表 `genP K hF`（`Tools/ShippingGen5AccGenP.lean:26`、par/ac9）と、その表のどのパッケージも生成器から作られたことを示す `genP_generated`（同 :96、証明済み）がある。kit `K` は AC9KIT（04db3763、§12.14 で受理）で `mkKit (dataOfAt lvl) …` に固定済みで、その `genSem` は定義で `genSemI Q X (g.toIn hs)`（`Tools/ShippingGen5SemGenData.lean:40-44`）。
* よって `GP env := genP (accKit env) hF` と固定すれば、`h_D_T1` は既存の証明済み定理（`genP_generated`、`genExtAtCall_of_genSem` `Tools/ShippingGen5SemExtPkg.lean:17`、`semOf_genP`）から証明の中で出る見込み。`hF : GenSFacts K` は C.SM-1 の `hs : DataOfSound (dataOfAt lvl) initsOf` から（AC9KIT と同じ `factsOf_genS_assembled''` の経路）。

## 2. Project / Milestone への影響

* 目標「FG 台帳を 0 にする」に対して、この固定がないと D.T-1 / C.SM-7 / D.D-3 は**現時点では一般定理から支払い不可**のまま残る（D.T-1 の `GenExtAtCall` を任意の `GP` から出す道は無い）。
* 止まる後続: FG の組み立て（A.P-17 `T1Hyp.dec` の `stepDec_of_ties` は `hT2_TIE` に `GenExtAtCall` を要る）。

## 3. 選択肢

| 案 | 内容 | 台帳の見込み | 利用者に見える影響 | コスト・リスク |
|---|---|---|---|---|
| A（推奨） | FG の文で `GP := fun env => genP (accKit env) (hF env)` に固定する。`lvl`・`initsOf`・`genData₀`（非 Prop の値）と `hs`（C.SM-1、既存の行）を束縛変数に足し、`h_D_T1` を除いた文 `FGLedgerPremisesStmtG` と、`h_D_T1` をその中で証明する定理を作る | D.T-1（リーフ）、C.SM-7（PA 非リーフ）、D.D-3（carrier、リーフ）で −3。C.DG-1（`P = genP env₀`）が定義で成り立つ分は reviewer 判断（0〜−1） | FG の結論のパッケージが「生成器が作った表」になる。任意の `GP` についての文ではなくなるが、O2（`∃ p, GP env declName = some p`）は任意の `GP` では成り立たないので、最終の FG はもともとどこかで `GP` を選ぶ必要がある | Lean 100〜200 行（推定）、Check、build。新しい TRUSTED / law なし。kit の `env` 依存（`accKit` は section 変数 `env₀` 上）を `env` の関数にする作業が要る |
| B | `GP` を任意のまま残す | 0 | なし | D.T-1 / C.SM-7 / D.D-3 は支払い不可のまま |

* データ損失はない。後から戻せる（新しい文は別の定義として足す。既存の文と定理は変えない）。
* 判断しない場合: B のまま。D.T-1 / C.SM-7 / D.D-3 は減らない。他の候補の調査は続ける。

## 4. 推奨と理由

A。carrier の固定は AC9KIT の kit 固定（`mkKit (dataOfAt lvl) …`、reviewer 受理）と同じ種類の選択で、新しい前提を足さず、既存の証明済み定理だけで `h_D_T1` を消せる見込み。FG を「生成器が作った表について述べる」形にすることは、生成器の健全性（DG-SEM）の結果を FG に使うための自然な接続でもある。

## 5. 根拠

* `genP`・`GenSFacts`・`genP_generated`・`GenPGeneratedStmt`（`Tools/ShippingGen5AccGenP.lean:23,26,36,96`、par/ac9 9a63e144）。
* `GenData.genSem hs Q X g := genSemI Q X (g.toIn hs)`（`Tools/ShippingGen5SemGenData.lean:40-44`）。
* `genExtAtCall_of_genSem`（`Tools/ShippingGen5SemExtPkg.lean:17`、束縛変数 `hp hq hord`。`hq` と `hord` は `h_D_T1` の前件そのもの）。
* `accServed0_of_cover_gatesK`（`Tools/ShippingGen5AccKit.lean:28`、kjob/rt187 04db3763）の `accKit%`。
* 調査 `scripts/gen5/BINDER_EXIT_CENSUS_DETAIL.md` の out_5 候補 2、§3 候補 5（par/binder-census 2ce38c69）。
