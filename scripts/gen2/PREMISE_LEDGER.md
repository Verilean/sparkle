# 前提台帳（FG 側）— 段 1

Issue: `sparkle-fg-final`（job `fg-ledger1`、ブランチ kjob/fg-ledger1）。base: par/gen2-spec d0ddc50b。
状態: **段 1 文書のみ。Lean は書いていない。**（段 1 は承認済み: dd624a27。）段 2（全前提を明示仮説にした文の Lean 計画）は **§8**（文書のみ、Lean なし、再 review 待ち）。
版の履歴: 段 1 基準件数 146 / 110（dd624a27）→ 段 2 計画（62aef763、approved）→ 型付け 7 仮説の文と Check（13c7d5a3、条件付き設計確認として approved）→ **本版（fgreg1、文書のみ）: 流れ 1 の前提解消（e6d8e55b）を反映して現在値 FG 107、registry 69 行の owner / 型の確認（§9.2）、T1 crosswalk 16 行の確認（§9.3）、次の候補の流れ（§9.4）。基準件数 146 / 110 は版の履歴として残し、現在値と区別する（§2）。**

## 0. 範囲・方法・読み方

- 対象: FG schema（GENERAL_SPEC.md §1.1）の各 binder・前提に効く、M2 / M4 / M5 の Issue が残している前提。T1 側（M3、gen3-*）は sparkle-gen3-t1-assembly の別 agent が作る。M3 由来の前提は各行で「T1 台帳を参照」の 1 行にした。
- 材料: `managerctl plan history`（各 Issue の最新 approved note の対象SHA・残り）、各 freeze 文書、各 branch の Tools ファイルの定理の型（`git show <branch>:<path>` で読んだ。checkout・merge はしていない）。履歴 JSON は調査用に作業領域へ保存しただけで、リポジトリには入れていない。
- **前提行の本体（完全な型・定義元 branch@SHA と path・仮定している定理・効く binder・別名・支払い予定・実run可否・分類）は 4 つの部分ファイルにある**（下の §1）。この文書は索引・重複整理・総数・推奨を持つ。型の本文は部分ファイル内で `git show` の原文を貼ってあり、手で書き写していない。長い補題で定義元の path:行のみを書いたものは、各部分ファイルにそう明記されている。
- 数え方: 「ブロック」は部分ファイルの前提見出し 1 つ。**1 ブロックは複数の Lean binder を束ねることがある**（例: C.RR-1 は `hA`/`hw`/`hc` の 3 つ）。したがって総数は「ブロック数」であり、Lean の binder 数ではない。
- 書いていないこと: 推測の数、「不可能」「導出不能」。供給元・経路が見つからなかったものは「この調査で辿った候補経路では未供給」の意味で書いてある。mutant の棄却は signature/defeq での棄却であって、意味的反例ではない。
- **未 review の実装の扱い**: 履歴に「agent の増分ビルドのみ」「clean build は coder」とある Lean（例: dc-connect U-CORENR 74343ad8、dg-env U9 b6b3206b、dg-sem kjob/g5sm-u23 7af6c7cc、dg-dataof row 6b 063056d6）は、承認済みとは数えず、各行に未 review と書いてある。
- 4 段の進捗（設計承認 / 条件付き部品 / 前提解消 / 最終受理）のうち、この台帳が示すのは「前提解消」の分母だけである。**FG の最終受理はまだ何も満たしていない。**

## 1. 部分ファイルと Issue の対応

| ファイル | 対象 Issue | ブロック数（見出しを機械的に数えた値） |
|---|---|---|
| premise_ledger/A_M2.md | gen2-u0-types, gen2-uadapt, gen2-loop-pkg, gen2-calldec, gen2-step-mem, gen2-leaf, gen2-gencall-plan, gen2-callfield, gen2-step, gen2-top-contract, gen4-oneout-probe（＋ FG binder 一覧 §2） | 28（P-01…P-28） |
| premise_ledger/B_M4.md | gen4-gate-supply（G-1…G-10）, gen4-fallback-supply（F-1…F-8）, gen4-parametric-supply（P-1…P-8）。gen4-routes は固有の binder なし（gate-leaf の G-1…G-7 を使う）。gen4-fg-assembly は履歴が created / dependencies のみで、この調査では branch・Lean が見つからなかった | 26（F-9 は未供給項目の列挙で、ブロックに数えない） |
| premise_ledger/C_M5dg.md | gen5-dg-runreads(RR), closingrun(CR), env(EN), readkinds(RK), dataof(DO), sem(SM), acc(AC), cover(CV, DG), readertrace(RT), dgen。dg-audit は created / dependencies のみ（note・SHA なし） | 55 |
| premise_ledger/D_M5t2.md | gen5-t2probe(P1-P3), t2-tie(T-1…T-12), dc-connect(D-1…D-9), boundary-audit(E-1…E-13)。t2cover は設計のみ（Lean なし）。t2-emit, gencall-proof, package-coverage, decl-bridge, reader-bridge は Lean も approved note もなく、前提行なし | 37 |

ID は `<ファイル記号>.<部分ファイル内の見出しID>`（例: `C.RK-5`、`A.P-07`）。

## 2. 総数

- **重複整理前: 146 ブロック**（28 + 26 + 55 + 37）。
- **重複整理後: 110 ブロック**（146 − 36）。整理の規則と一覧は §4。整理は「部分ファイルの別名欄または同じ型と明記されているもの」に限った保守的な統合で、型の同値は Lean では確認していない。
- **基準件数と既知の差分は別**: 146 / 110 は段 1 の基準件数で書き換えない。基準日以降に承認済みの unit6 F3（parametric-supply, 50d22e3b）の差分は B.P-8 に別記した: `LegalBinding` を前提に B.P-1 `AllPos θ` と宣言 parameter coverage の 2 項目を条件付きで導出、`requirePositive` 実装/model 一致 1 項目を解消、追加前提 0、`LegalBinding` は入力として残る。この差分は 146 / 110 に反映していない。広い残余（B1-B3、T、FG）は未供給のまま。
- **現在値の定義（唯一の定義。他の箇所はこれを参照する）**: 現在値 = 「§8.2 の 110 行表のうち、未解消の行数」。元の 110 行表に含まれる解消印の行は C.RK-5、D.T-8、D.T-9 の **3 行だけ**なので、現在値は **FG 107**（110 − 3）。流れ 1 の U1 / U2（kjob/flow1-b e6d8e55b、reviewer 承認 seq 5756、clean build f1v-e6d8e55b exit 0）の解消対象 4 ID のうち D.T-5 は §4 で 110 表から除外済みの指し示し行なので、現在値からは引かない。条件付き部品であり、FG の完了ではない。**基準件数 146 / 110 とは別の欄**で、146 / 110 は段 1・段 2 の版の記録として書き換えていない。詳細は §9.1。
- 分類の内訳は部分ファイルごとにある（A は §4 の集計に、他は各ブロックの分類欄）。この台帳全体での分類別の合算は、各ファイルの分類欄の書式が揃っていないので行っていない（数えていない値は書かない）。
- TRUSTED 境界として**明示された**前提: 確定した TRUSTED 宣言はこの調査では見つからなかった。候補として挙がっているのは A.P-01（Laws。GENERAL_SPEC §5 は「model または明示 TRUSTED」）、D.E-10（Laws の 14 フィールド。boundary-audit は CONTRACT と分類）、D.E-13（G7-c 印字。boundary-audit §3 が「TRUSTED by design」）。C 群は「新 TRUSTED / 新 law なし」と記録し、DG_ENV_FREEZE §4 の A/B/C 判断へのユーザ決定の記録は見つからなかったと報告している。
- 実run から払える根拠の補題名が履歴・freeze にあるもの（各行の「実runから払えそうか」が「はい」または「条件付きではい」）: A.P-07（条件付き、`machineRunJQC_of_closesA`）、A.P-13（`memOrigin_of_memDec`、`Nonempty ι` の下）、B.G-2（`RealChildA` は成功 run から）、C.RK-5（`runReads_of_run`）、C.SM-5（`srcCausal_of_acc_unfold`、`hunf` と `Acc` が前提）、D.P2（decoded 版 `letTie_dec`）、D.T-7（存在形 `calleePkg_of_t1ND`）、D.T-8, D.T-9（組み立て済み、末端は D.T-5/T-6）、D.D-2（default route のみ `synthesizeCombinational_postEntry`）、D.D-8（`postEntry_lookup_ne`）。これは各行を読んで拾った一覧で、いずれも前提つきである。
- 支払い予定の Issue が履歴に書かれているもの: 部分的（C 群の多くは dg-* 内の後続単位、D.T-5 は dg-closingrun、D.T-1 は dg-sem P4e）。**gen5-gencall-proof / package-coverage / reader-bridge / decl-bridge / boundary-audit / gen4-fg-assembly は履歴上は担当する前提の割当を持たない**（todo で、台帳待ちで一時停止とされているものもある）。

## 3. 全体で目立つ点（各部分ファイルの報告から。数えた事実のみ）

1. **StepStmt 本体は未証明。** 承認済みなのは `StepStmtCases`（3 形に case 制限、4 つの row 前提つき）と部品。group 親の `TopShips`、case S の slotless top、instFields = [] の closing 内 memory call、one-output slotless の実 Pkg は、STEP_ROUTE_FREEZE.md に「供給元なし」と記録されている（A.P-14, P-20, P-25）。
2. **`TopShips` に 2 世代ある。** par/gen2-spec 先端（d0ddc50b）は旧形。R-G 形と `InstClosed` は kjob/g2tc-s2（fa84af5d）にのみある。承認済みの oneOut_topShips は旧形に対する証明。非空虚性（P-TOP）は未完（A.P-27）。
3. **具体 run の存在を供給した Issue が見つからなかった**（A.P-28）。`lawsQuietFalse` では `PbhRunEx` が偽であることだけが証明済み。非空虚な `Laws` の値は、この調査では見つからなかった（A.P-01）。
4. **`ReflectsAll` と `Pk` は Lean 定義が見つからなかった**（A の調査、D.D-1）。FG の仮定として残る。
5. **反射 Prop（gate の `entry`/`old`/`peel`/`he`/`hb`/`hv`、first-gate の `EntryDefines`）はどの Issue も一般の供給元を持たない**（B.G-1, G-3…G-6, G-8, F-6）。
6. **fallback の `hS`（FB-22）と parametric の B1–B4 / `SpecSuccessAllPositive` は未供給で、割当もない**（B.F-4, B.P-4, B.P-5）。parametric の I3c keeps 定理は FG の `Laws` ではなく旧 `RefLaws` を使い、`Start` から `Out0` への補題は freeze に記録がない（B.P-7）。
7. **dc-connect の `FG_CONNECT` は条件付きの schema** で、`Post := False`、`GP := none`、`CV := ∅` でも成り立つ（D.D-1…D-4）。U-CORENR 実装（74343ad8）は agent の増分ビルドのみで未 review。
8. **dg-env / dg-sem / dg-dataof の最新実装は未 review**（上の §0）。dg-acc A13 は着手中で kjob/g5ac-r27 は freeze コミット cff12a48 のまま。

## 4. 重複整理（統合した組と除いた数）

統合の根拠は、各部分ファイルの「別名」欄または同じ型・同じ役割の明記。除いた数 = 組のメンバー数 − 1。

| 統合先（残す行） | 統合した行 | 除いた数 | 根拠（部分ファイルの記載） |
|---|---|---|---|
| Laws | A.P-01, B.F-3, D.E-10 | 2 | 同じ `L : Laws`（D.D-6 の Laws 部分も同じ。D.D-6 自体は下の Start 側に数える） |
| Start（AdmCtx ∧ JQC） | A.P-02, A.P-03, C.RR-1, B.F-2, D.E-11, D.D-6 | 5 | `Start := AdmCtx ∧ JQC`（GENERAL_SPEC §1.2）。D.E-11 の別名欄は D.D-6 と同じと記載。B.F-2 の `entry` 部分は下の machine 側にも関わる |
| 核 run（RunsTo） | A.P-04, B.F-5, B.G-2, C.CR-5, D.T-12 | 4 | A.P-04 の別名 `hr`、B.G-2 の別名欄「fallback では `hr : RunsTo …`（F-5）」、D.T-12 の別名「dg-closingrun の同名 binder」 |
| gate/first-gate の entry | B.G-1, B.G-8, B.F-6, B.F-7 | 3 | B.G-1 と B.G-8/F-6 は別名、B.F-7 は「型は G-8 と同じ」 |
| MachineDefines（machine 側 entry） | A.P-06, C.RR-3, D.D-9 | 2 | A.P-06 の別名 `entry`/`MachineDefines`、C.RR-3 は `T1HypND.defines`、D.D-9 は T1Hyp の同名フィールド |
| MachineTaken / closes | A.P-07, C.AC-6 | 1 | C.AC-6 の別名 `T1HypND.closes`、`MachineRouteAt` |
| 後処理関係 | A.P-05, B.P-6, D.D-2 | 2 | A.P-05 の別名 `hpost`、D.D-2 の別名 `PostT1`／B.P-6 `PostTransfer` |
| package 割当 GP | D.P1, D.T-7, D.D-3 | 2 | D.P1 の別名 `hDG_GENP`（＝T-7）、D.D-3 の別名「t2probe の `P`」 |
| call 生成残差 t1/t2/t3 | A.P-18, D.P2, D.P3 | 2 | A.P-18 の別名 G3-GEN-CALL t1/t2/t3 |
| ChildKeepsInv（G-KEEP-CHILD） | A.P-24, B.F-1, C.CR-3, C.AC-8 | 3 | A.P-24 の別名 G-KEEP-CHILD、C.CR-3 の別名 `AccIHAt`/`AccChildKeeps`、C.AC-8 の別名 `ChildKeepsInv` |
| OneOutWidth（G-ONEOUT-WID） | A.P-25, D.T-3 | 1 | D.T-3 の別名「M3 側の G-ONEOUT-WID」 |
| G-DATA-CALL | A.P-19, D.T-10 | 1 | D.T-10 の別名「GENERAL_SPEC §4.4 の DataOk の Bool 行」、A.P-19 の別名 G-DATA-CALL |
| G-MEMCALLS | A.P-16, D.T-11 | 1 | 両方 `hG_MEMCALLS` |
| DeclConnect | C.DG-2, D.D-5 | 1 | 両方 DeclConnect（G3-DECL） |
| T1Hyp | C.CR-4, D.T-6 | 1 | 両方 `T1Hyp`／`T1HypND` |
| ClosingRun の行 | C.CR-1, C.CR-2, C.CR-3, D.T-5 | 1（D.T-5） | D.T-5 は「各 binder は dg-closingrun の台帳を参照」と書く指し示しの行 |
| DataOfSound | C.DO-1, C.SM-1, C.AC-1 | 2 | C.DO-1 と C.AC-1 の別名欄が `DataOfSound`/`DataSoundAt` |
| C0（環境等式） | C.EN-6, C.RK-3 | 1 | C.RK-3 の別名「DG-ENV の C0（EN-6）」 |
| DataOk の束 | A.P-20 と A.P-10/P-11/P-12/P-25 | 1（A.P-20） | A.P-20 の別名欄「4 前提を束ねたもの」 |
| **合計** |  | **36** | |

統合しなかったが関係の深い組（今後の確認対象、数からは引いていない）: A.P-09/P-10/P-11（DataOkB の行が重なる）、A.P-08 と D.P1（GenFacts と `hP`）、C.RK-5 と C.CR 系の `RunReadsAt`、C.CV-5 と C.DO-3（row 6b）、D.T-1 と C.SM-7。

## 5. 推奨: 実 run から払える前提を持つ流れ（2〜3 本）

選び方: §2 の「実run から払える根拠の補題名がある」前提を含み、かつ同じ接続に属する複数の行を同時に動かせるもの。**消える予定の台帳 ID は、各行に書かれた補題が、その行の前提を満たすことを freeze で型として示せたときの候補であり、消えたとはまだ言えない。増える前提は、この段階では数えていない。各単位の freeze に「台帳の前提がいくつ消え、いくつ増えるか」を数えて書くことを必須にする**（ユーザー了承の条件）。

- **流れ 1: 実 run の読み → ClosingRun（dg-runreads → dg-closingrun）。** 根拠: `runReads_of_run`（C.RK-5, C.RR-2, C.RR-3）、`closingRun0_of_run`/`closingShared_of_run`（D.T-5 が built と記載、kjob/g5cr-r6@f3a29dbb）。消す予定の ID: C.RK-5、D.T-8、D.T-9 の末端（110 表の 3 行）。D.T-5 は §4 で 110 表から除外済みの指し示し行なので 110 表の数には入らない。残る/増える候補（数えていない）: C.CR-1（`hrow`/`hord`、`DataOk` の具体化が先）、C.CR-2（`hGen`、供給の経路未発見）、非空虚性、depth0 stop。つまりこの流れだけでは `ClosingRun` の前提は全部は消えない。
- **流れ 2: DataOf の健全性（dg-sem → dg-acc の Acc 帰納）。** 根拠: `ordCallees₀_mem`（C.SM-2、kjob/g5ac-r26@cff12a48 で証明済み）、`srcCausal_of_acc_unfold` と `acc_top_of_run`/`hacc_of_top_runs`（C.SM-4, C.SM-5）、`dataOfAt_sound`。消す予定の ID: C.SM-2、C.SM-5、C.SM-4、およびそれらに束ねられる DataOfSound の統合行（C.DO-1/SM-1/AC-1）の一部。残る候補: C.SM-3（`hinv`/`hunf`）、C.AC-3, C.AC-4。dg-sem の実装 7af6c7cc は未 review。
- **流れ 3: default route の post / entry 接続（dc-connect）。** 根拠: `synthesizeCombinational_postEntry`（D.D-2 の default route）、`postEntry_lookup_ne`（D.D-8）。消す予定の ID: D.D-8、D.D-2 の default route 部分。注意: D.D-2 の parametric route、D.D-1（ReflectsAll）、D.D-3（GP）、D.D-4（CV）、D.D-5（DeclConnect の rows）は未供給のまま。U-CORENR（74343ad8）は未 review なので、承認後でなければ「条件付き部品」止まり。

流れ 1〜3 のどれが最小の追加前提で最大の削減になるかは、この調査では数えていない。選定は reviewer / ユーザーの判断（段 1 の承認事項）。

## 6. 次（段 2、この台帳の承認後）

全前提を明示仮説に並べた FG 定理の文を Lean で書く計画を、この台帳の ID を使って freeze に追記する（import する branch、局所統合が必要な branch と SHA、統合の手順の列挙）。局所統合は coder の担当なので、列挙して止まる。

## 7. 索引（各ブロックの 1 行要約。全文は部分ファイル）

書式: 支払い予定・実run・分類は部分ファイルの該当欄の先頭を機械的に切り出したもの。切れている場合は部分ファイルを正とする。

| 台帳ID | 前提 | 支払い予定（抜粋） | 実runから払えそうか（抜粋） | 分類（抜粋） |
|---|---|---|---|---|
| A.P-01 | Laws（実行時法則 G5） | GENERAL_SPEC.md §5 M5「G5: a model of `Laws`, or an | いいえ（run から払う対象ではない。一様な法則）。履歴上の事実: `Laws` | TRUSTED境界（候補）。GENERAL_SPEC §5 は「model また |
| A.P-02 | AdmCtx（許容コンテキスト） | 最外は FG の Start 前提として残る。内側の run は T1 台帳を参照。 | 不明。`AdmCtx` は `mctx.canUnfold?` が inert | 入力条件（Start）。 |
| A.P-03 | JQC（深さ付きキャッシュ不変量） | 最外は Start。内側（InvAt / G-START: depth 0 でコアが sparkle | 不明（上記 G-START は GENERAL_SPEC §3.2 の T1 側 | 入力条件（Start）。 |
| A.P-04 | core run（RunsTo） | FG の入力そのもの。entry→core の橋は M4（sparkle-gen4-fg-assem | 入力そのもの（払う対象ではない）。 | 入力条件。 |
| A.P-05 | hpost（b と raw の後処理関係） | GENERAL_SPEC §1.1 は「`b ↔ raw` of the default entry | 不明。entry の 2 つの後処理が 2 択の disjunction になる | 入力条件（M4 で固定される関係）。 |
| A.P-06 | MachineDefines（shape 反映 G3-SHAPE） | GENERAL_SPEC §5 M5 G3-SHAPE（reader soundness: `rea | 不明。GENERAL_SPEC §5 の M5 Risk に「`partial` | 未供給の義務。 |
| A.P-07 | MachineTaken（route 証拠）と MachineClosesAtA | G-CLOSES。GEN2_DEFS.lean.txt:201-204 のコメント: 「memory | 条件付きで「はい」: `machineRunJQC_of_closesA`（To | 未供給の義務（T1Hyp.closes）。 |
| A.P-08 | パッケージの存在と生成事実（G3-GEN / G3-DECL） | GENERAL_SPEC §5 M5 G3-GEN（生成器の健全性）/ G3-DECL。Issue | いいえ（現状）。GenFacts の注記: 「NOT derived gener | 未供給の義務（G3-GEN、G3-DECL）。 |
| A.P-09 | DataOkB の行（U0 の具体 DataOk）と callDec 系の `hok` / `hco` / `hslot | G-DATA coverage（GENERAL_SPEC §4.3: M2 per check）— | 行ごとに異なる（`outHead` は「いいえ（被覆リスクあり）」、`outNa | 入力条件（decidable row）。coverage は未供給の義務（`ou |
| A.P-10 | MemParentDataOk（5 行） | coverage = G-DATA（MEMPARENT_RESULT.md: 「DATA (5 Bo | 不明。instance 側は `decide`（lm_dataOk、q_data | 入力条件（decidable row）、coverage は未供給の義務。 |
| A.P-11 | LeafDataOk（4 行） | LEAF_RESULT.md「No generic supply of `ExtInS`/`Leaf | 不明。instance は `decide`（leaf16、pbhC: `pbh | 入力条件（decidable row）、coverage は未供給の義務。 |
| A.P-12 | ExtInS（package の入力延長が恒等） | MEMPARENT_RESULT.md: 「generic supply D-GEN/M5」。G3G | 不明。instance は `rfl`（leaf16、pbhC）、`q_extI | 未供給の義務。 |
| A.P-13 | MemOrigin（memory 起源 + 宣言幅） | P-16（MemDec）と同じ。履歴 seq 2211: 「MemOrigin は宣言幅も主張するの | はい（`Nonempty ι` と P-16 の下で `memOrigin_of | 入力条件（case）。coverage は未供給の義務。 |
| A.P-14 | case 前提（insts / instFields / slots / Nonempty ι / StepCaseOK | 被覆は sparkle-gen2-step の未了部分。STEP_ROUTE_FREEZE.md § | いいえ（現在）。上の行は未供給。 | 入力条件（case 制限）。被覆は未供給の義務。 |
| A.P-15 | hrst（rst が b の入力でない）と hnoRst / hnoClk | case S（`rst ∈ b.inputs`）は C5S が見つからない（P-14）。 | S5_SLOTLESS_FREEZE.md: 「Reset absence co | 入力条件（case）。 |
| A.P-16 | MemDec（memory 呼び出しの分解 G-MEMCALLS） | GENERAL_SPEC §4.3: G-MEMCALLS は「`MemDec` from the | 不明。履歴上の供給は宣言ごとの kernel チェック: `leafM_memc | 未供給の義務。 |
| A.P-17 | CallDec（ordinary 呼び出しの分解 G-CALLDEC） | G-CALLDEC は generic には未供給（calldec seq 2155 done no | 不明。GENERAL_SPEC §4.2: 「producer-export g | 未供給の義務（G-CALLDEC）。 |
| A.P-18 | HPointAt / HPointG / CallFactF（呼び出しごとの生成残差 G3-GEN-CALL） | G3GEN_CALL_PLAN.md §4: 「G3-GEN-CALL t1/t2/t3 — M5」 | 不明。CALLDEC_PROBE_RESULT.md (iii): 「gener | 未供給の義務。 |
| A.P-19 | 呼び出し対 data（`callArgsOkAt` / arity、および global の `widths` `har | G3GEN_CALL_PLAN.md §4: G-DATA-CALL は M3（T1 台帳を参照）、 | 不明。計画は run-local（`ClosingRun` + `PortTie | 未供給の義務（D 行、coverage 未了）。 |
| A.P-20 | `stepStmtCases_of_rows` の 4 つの row 前提（DataOk placeholder の強化 | sparkle-gen3-data-supply（STEP_ROUTE_FREEZE.md §4: | 不明。STEP_ROUTE_FREEZE.md §7 row 6 の通り Dat | 入力条件（DataOk の強化）。供給は未了。 |
| A.P-21 | `hseq`（served module が clk 入力を持つ） | S3（sparkle-gen2-step）で hseq の代わりに分岐する形に置換済み（d603ac | 不要（置換済み）。 | 未供給の義務（seqFactsRN_of_callDec 単体として）。S3 の |
| A.P-22 | G-SERVED の trace（`ServedP (ShipsRes L P)`） | T1 台帳を参照（sparkle-gen2-step の note seq 2564: 「G-SER | T1 台帳を参照。 | 未供給の義務（T1 側）。 |
| A.P-23 | G-LIFT（`LiftShips`）と `ShipsAt` 版の trace | 未割当（STEP_ROUTE_FREEZE.md §7 row 1: 「`ChildShips q | 不明（上記。この調査では見つからなかった）。 | 未供給の義務（G-LIFT）。 |
| A.P-24 | ChildKeepsInv（G-KEEP-CHILD） | T1 台帳を参照（M3）。 | (記載なし) | T1 台帳を参照（M3）。 |
| A.P-25 | `hW : ∀ k, OneOutWidth P p k`（G-ONEOUT-WID） | sparkle-gen3-data-supply（STEP_ROUTE_FREEZE.md §4: | 不明。DataBridge の `oneOutWidth_of_strict` | 未供給の義務（G-ONEOUT-WID）。 |
| A.P-26 | `hnomem`（名前半分を含む）と `hord`（起源半分）— P-MEM | hord row = sparkle-gen3-data-supply（STEP_ROUTE_FRE | 名前半分は不要（chain は起源半分しか使わない: S4_PMEM4_FREE | 入力条件（row）。coverage は未供給の義務。 |
| A.P-27 | `TopShips` 結論内の実行前件（R-G）と `PTopPrem` | sparkle-gen2-top-contract（本 Issue。seq 5569 todo）。 | 一部のみ（履歴の証明済み条件付き補題）。`ss = []` で c2/c3（pt | 入力条件（保証の前件）。供給は未供給の義務（P-TOP 未完: 履歴 seq 5 |
| A.P-28 | 具体 run の存在と共同充足性（`PbhRunEx L` / `PbhRunAt`） | sparkle-gen2-top-contract（P-TOP）。再開条件は seq 5569（前提 | **この調査では見つからなかった**（seq 5357 以降の各 note: 「 | 未供給の義務。 |
| B.G-1 | 前提: `entry`（gate 版） | 未割当。 | 不明。履歴（seq 2379, 3500, 4376, 4578）は「entry | 未供給の義務（反射 premise）。 |
| B.G-2 | 前提: `h : RealChildA` | T1 側 IH（`IHAt`/`ShipsRes`）の領域。T1 台帳を参照。 | はい（`IHAt` の定義上 `RealChildA` は成功 run から作ら | 入力条件。 |
| B.G-3 | 前提: `GateLeaf.old` | 未割当。 | 不明。`GateDefines` の `certifiedShape? fals | 未供給の義務（反射）。 |
| B.G-4 | 前提: `GateLeaf.peel` | 未割当。**実runから払えそうか**: 不明（供給元はこの調査では見つからなかった）。**分類** | 不明（供給元はこの調査では見つからなかった）。**分類**: 未供給の義務（反射 | 未供給の義務（反射）。 |
| B.G-5 | 前提: `GateLeaf.he` | 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務。 | 不明。**分類**: 未供給の義務。 | 未供給の義務。 |
| B.G-6 | 前提: `GateLeaf.hb` / `GateLeaf.hv`（2フィールド） | 未割当。**実runから払えそうか**: 不明。ただし pick の個別インスタンスでは `old/ | 不明。ただし pick の個別インスタンスでは `old/peel/he/hb/ | 未供給の義務。 |
| B.G-7 | 前提: `hw1 : g.srt.width ≠ 1` | 未割当（seq 3500「幅1は未供給義務として調査継続」）。**実runから払えそうか**: 幅≠ | 幅≠1 側は `gate_full_outputs`（`Tools.Shippi | 未供給の義務。 |
| B.G-8 | 前提: `FirstLeaf` のデータ＋`entry`（first-gate 版） | 未割当。**実runから払えそうか**: 不明（freeze/履歴は「entry/RealChild | 不明（freeze/履歴は「entry/RealChildA/Q/正幅は前提」s | 未供給の義務。 |
| B.G-9 | 前提: `Q`（route table）と `hQ` | 未割当（theorem 内コメントは「Q の supplier は route table の as | 不明。**分類**: 入力条件（これを組み立てる側が未供給）。 | 入力条件（これを組み立てる側が未供給）。 |
| B.G-10 | U-G7a（instance 付き gate 親）— 未承認 | 未割当。分類: 未供給の義務。承認前のため FG への対応は記録しない。 | (記載なし) | 未供給の義務。承認前のため FG への対応は記録しない。 |
| B.F-1 | 前提: `hC : ChildKeepsInv L P Reach (D + 1)`（D=0 の Fin0 系は `Ch | (記載なし) | (記載なし) | T1 台帳を参照（`KeepChildStmt`、Defs:192 が供給文）。 |
| B.F-2 | 前提: `hI : InvAt L P Reach D w`、`hA : AdmCtx L.O.quiet mctx c | (記載なし) | (記載なし) | (記載なし) |
| B.F-3 | 前提: `L : Laws`（`legacyTail_keepsInv` 等） | (記載なし) | (記載なし) | (記載なし) |
| B.F-4 | 前提: `hS`（FB-22）— package の `S` と `firstFn` の対応 | 未割当（seq 5568: 「前提台帳で支払い先に割り当てられたとき再開」）。 | 不明（履歴 seq 5529「S の hS 対応は未供給」）。 | 未供給の義務。 |
| B.F-5 | 前提: run `hr` / `h` | (記載なし) | (記載なし) | 入力条件。 |
| B.F-6 | 前提: `entry`（first-gate fragment） | 未割当。**実runから払えそうか**: 不明（seq 5174, 5529「EntryDefine | 不明（seq 5174, 5529「EntryDefines/WF は前提」）。 | 未供給の義務。 |
| B.F-7 | 前提: `hwf : fe.WF names.length n`、`hn : 0 < n` | 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務。 | 不明。**分類**: 未供給の義務。 | 未供給の義務。 |
| B.F-8 | 前提: 実 run が走った core モジュールの `ChildRunN`（clean-up 輸送の入力） | 未割当。**分類**: 未供給の義務。 | (記載なし) | 未供給の義務。 |
| B.P-1 | 前提: `AllPos θ` | 未割当。履歴 seq 3648/5358: 「B1-B3/T/FG 未供給」。 | 不明。`specializeDesign_ok_legal`（ParamIfac | 未供給の義務（Layer A のモデル側条件）。 |
| B.P-2 | 前提: `Bound θ d`、`PosDim d`、`NonNegDim s`、`SliceOK hi lo` | 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務。 | 不明。**分類**: 未供給の義務。 | 未供給の義務。 |
| B.P-3 | 前提: `ExprOK θ e`、`TyPos t` / `TyBound θ t` | (記載なし) | (記載なし) | P-2 と同じ（未割当／不明／未供給の義務）。 |
| B.P-4 | 前提: B1〜B4（production との橋、binder ではなくギャップ） | 未割当（決定資料 §5「決定が無ければ B1-B3 は未供給のまま」）。**実runから払えそうか* | 不明（「この調査で経路未発見」と書かれている）。**分類**: 未供給の義務（o | 未供給の義務（option 3 を採れば TRUSTED境界になるが、現時点では |
| B.P-5 | 前提: `T = SpecSuccessAllPositive b D` | 未割当（D3 の判断待ち）。**実runから払えそうか**: 不明。**分類**: 未供給の義務。 | 不明。**分類**: 未供給の義務。 | 未供給の義務。 |
| B.P-6 | 前提: `SrcAt`、`PostTransfer raw b Dr D I` | 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務。 | 不明。**分類**: 未供給の義務。 | 未供給の義務。 |
| B.P-7 | 前提: `RefLaws` 系（I3c, ParamKeeps.lean） | 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務（対応する M3 側の | 不明。**分類**: 未供給の義務（対応する M3 側の IH は T1 台帳を | 未供給の義務（対応する M3 側の IH は T1 台帳を参照）。 |
| B.P-8 | 承認済み unit6 F3（50d22e3b）の `LegalBinding D θ` | 未割当（`LegalBinding` を実 run から払う経路はこの調査では見つからなかった） | 不明 | 入力条件。F3 の既知差分: `LegalBinding` を前提に B.P-1 `AllPos θ` と宣言 parameter coverage の 2 項目を条件付き導出、`requirePositive` 実装/model 一致 1 項目を解消、追加前提 0（基準件数 146/110 とは別。B_M4 §4 P-8） |
| C.RR-1 | `hA` / `hw` / `hc` | 履歴に割当の記載なし（外側ランは `Start`＝FG の仮説、内側ランは T1 の IH）→ 未割 | depth 0 の外側ランでは `Start` が `AdmCtx` と `JQ | 入力条件 |
| C.RR-2 | `hr` | FG の仮説そのもの | はい（FG の `RunsTo` 仮説が定義上これ）。ただし FG の `Run | 入力条件 |
| C.RR-3 | `entry` / `closes` | T1 側（G3-SHAPE / G-CLOSES）。DG-ENV は all-world `defi | 不明（RR は T1 の field をそのまま取る） | 入力条件（T1 台帳の field） |
| C.CR-1 | `hrow`（`closingRun0_of_run` では `hord`） | 割当の記載なし → 未割当（R6 freeze §2: 「`DataOk` は抽象 Prop パラメ | 不明。履歴・freeze に支払う補題の記載なし | 未供給の義務（`DataOk` の具体化＝M2 U0 に依存） |
| C.CR-2 | `hGen` | R6 freeze §2: DG-COVER + DG-WFCOVER + `genP_genera | 不明（R6 freeze: `Gen := GeneratedAt …` の供給 | 未供給の義務 |
| C.CR-3 | `hIH` / `hKI`（`hst` / `h1`） | R6 freeze §2: 名前付き producer の形は `Tools.ShippingGen | 不明（R6 freeze: 「供給元・経路が見つからなかった」） | 未供給の義務（T1 台帳側の IH） |
| C.CR-4 | `hT` | T1 側 | T1 台帳を参照 | 入力条件（T1 台帳） |
| C.CR-5 | `hs` / `hd0` / `hA` / `hR` / `hP` / `hrun` | FG の仮説／T1 台帳 | `hs`, `hrun` は FG の仮説として与えられる。`hd0`, `hR | 入力条件 |
| C.EN-1 | `QuietStrength L L' env₀`（`hq`） | DG-ENV（履歴 5467/5476 の残り: 「L′/QuietStrength 未供給」）。具 | いいえ、とは書けない。履歴 3071/5476 に「QuietStrength/ | 未供給の義務 |
| C.EN-2 | `AdmDown L L'`（`hd`）と `hA′` | DG-ENV（未供給） | R3 freeze §1: 「`AdmCtx`/`InertUnfold` は | 未供給の義務 |
| C.EN-3 | 開始 cache: `hC` / `hE` / `hN` | DG-ENV（5476: 「実 start cache hN、非空例 未供給」） | `hE` 形（開始時 `cv w₀ = {}`）は `hE` として仮説。実 r | 未供給の義務 |
| C.EN-4 | `CellPrem`（セルの ReadWorld/SetFrame 前提） | DG-ENV（R3 freeze: 「セル前提は runtime で未供給（fit は open）」 | 不明（R3 freeze §1.1: B 13 は cell premise か | 未供給の義務（これらを TRUSTED とするかの決定は DG_ENV_FREE |
| C.EN-5 | `¬ DRow p` | DG-ENV（履歴 5476: 「¬DRow 未供給」） | 不明（R3 freeze §1.1: D 13 は「経路未発見」、HeapPro | 未供給の義務 |
| C.EN-6 | `hall`（C0: 全 world の `ReadsAt`）とゲート／shape 事実 | DG-ENV（C0 は履歴の全 note で「未供給」） | `hall`（全 world）は不明。run 側の `ReadsAt` は `r | 未供給の義務 |
| C.EN-7 | `hentry`（入れ子 core run 終端の保存） | 割当の記載なし（U9 freeze §0: 「rows owned by G-REACH / DG- | 不明（U9 freeze: 「候補経路では未供給」） | 未供給の義務 |
| C.EN-8 | `hn` | 記載なし → 未割当 | 不明 | 入力条件（Meta.Context の条件） |
| C.RK-1 | `hk` | 未割当（U13 freeze §1） | いいえ、とは言えない。U13 freeze §2: 「`ST.Ref.get` | 未供給の義務 |
| C.RK-2 | `hHead` | 未割当 | 不明（U13 freeze §2: 「run が return したと言うだけ。 | 未供給の義務 |
| C.RK-3 | `h0s` | sparkle-gen5-dg-env（U13 freeze 表） | いいえ、とは言えない。U13 freeze §2: 「`ReadsAt.of_e | 未供給の義務 |
| C.RK-4 | `hrun`（readMachine）と `hX` | 履歴・U13 freeze 表: `sparkle-gen5-dg-runreads` / `-cl | 不明（`hX` は命名の等式で U13 freeze は gap に数えない） | `hrun` 未供給の義務、`hX` 入力条件（trivial） |
| C.RK-5 | `R : RunReadsAt …` | sparkle-gen5-dg-runreads（RR3 が `O, hA, JQ/cache, M | はい（`runReads_of_run`、ただし RR-1/RR-3 の前提つき | 入力条件（RR-1..RR-3 に帰着） **【前提解消（e6d8e55b、reviewer 承認 seq 5756）。条件付き部品。§9.1】** |
| C.RK-6 | `hag : ReflExprAgree` | 未割当（記載なし） | 不明（記載なし） | 未供給の義務 |
| C.RK-7 | U14 の置換前提 `hM` / `hC`（freeze 承認、Lean は未実装） | RK-1/RK-2 と同じ未割当 | 不明 | 未供給の義務 |
| C.RK-8 | reader 完全性の前提（`readN_quote` 系、U1-U4 の成果） | DATAOF freeze: C-QWIT は「供給元未発見」 | 不明 | 未供給の義務 |
| C.DO-1 | `h : dataOfAt lvl E senv s = some d`（coverage の行） | DG-COVER（行 8 の `S-OK`、DATAOF freeze §11.2）。他の行は記載な | いいえ、とは言えない。§11.2 の行 1,2,3,4,5,6,8 が未供給、行 | 未供給の義務（成功 run 全部での `dataOfAt = some` という |
| C.DO-2 | 実 reader との一致（Rdr）と `s = sp` | DG-COVER / DG-READKINDS（freeze 本文） | 不明 | 未供給の義務 |
| C.DO-3 | row 6a, C-CMP, C-QWIT, S-OK, S-COV-FLOAT, `dataOf at exprSiz | S-OK は DG-COVER／DG-WFCOVER。他は記載なし | (記載なし) | 未供給の義務 |
| C.SM-1 | `hs : DataOfSound dataOf initsOf` | DG-DATAOF（5492 note: 「実 dataOf/DataOfSound(DG-DATA | いいえ、とは言えない。`dataOfAt_sound`（DO-1）が 4 連言と | 未供給の義務 |
| C.SM-2 | `hmem`（ordC の membership） | DG-ACC A12 で `ordCallees₀`＋`ordCallees₀_mem` として具体 | はい（`ordCallees₀_mem` は kjob/g5ac-r26 で証明 | 未供給の義務（SEM 側への接続） |
| C.SM-3 | `hinv`（kit の invariant）／`hunf` | DG-ACC（`genS` が `hunf`／`hinv` を満たす構成）。5492: 「実 kit | 不明（DG-ACC の `genS_unfold`（Acc.lean）が候補。S | 未供給の義務 |
| C.SM-4 | `hacc` | DG-ACC（AC-8） | AC-8 に記載 | 未供給の義務 |
| C.SM-5 | `hQ : CalleesCausal Q g.d` | SM-3/SM-4 の Acc 帰納（`srcCausal_of_acc_unfold`）が与える形 | はい（`srcCausal_of_acc_unfold`、`hunf` と `A | 未供給の義務（SM-3/SM-4 に帰着） |
| C.SM-6 | `GenWF d = true`（`GenData.wf`／`GenIn.wf`） | DG-COVER（`rowC_of_reader`, `rowA3_of_inv` 等、CV 節）／ | CV 節参照（hq, hnl, FullInv が未供給） | 未供給の義務 |
| C.SM-7 | `hord`（`genExtAtCall_of_genSem`） | 記載なし → 未割当 | 不明 | 入力条件（k が ordinary 呼び出しであること） |
| C.AC-1 | `hf : DataSoundAt f` | DG-DATAOF（`dataOfAt_sound` が候補、5124 note）。kjob/g5d | いいえ、とは言えない（DO-1 の被覆が未供給） | 未供給の義務 |
| C.AC-2 | `hev : GDEvidence f GD dOf env₀` | DG-SEM の実 `GenData`（5456: 「実 GenData/genSem/laws/h | 不明。A13（`GDf`, `genDataF`; freeze approve | 未供給の義務 |
| C.AC-3 | `hloc` / `hdecl` / `hd` | DG-SEM（実 `genSem` から）。接続は別ブランチ | 不明（SEM 側に該当補題名があるが、ACC branch から import | 未供給の義務 |
| C.AC-4 | `ReachCover K Reach` と `hcl` | DG-COVER／DG-DATAOF（A13: 「genData₀ が成功する条件」） | 不明（5505: 「実データ成功 coverage は未供給」） | 未供給の義務 |
| C.AC-5 | `GatesNoneAt env₀ Reach` | 記載なし → 未割当 | 不明 | 未供給の義務 |
| C.AC-6 | `ClosesOfShape env₀ L Reach`（= `ClosesData` ∧ `ClosesCalls`） | 記載なし → 未割当 | 不明。`closesData_of_sound` は `hL : ∀ c d, | 未供給の義務 |
| C.AC-7 | `ReadsSupplyAt e L Reach` | DG-ENV | 不明（EN-1/EN-6 に帰着） | 未供給の義務 |
| C.AC-8 | `hI : AccIHAt K L Reach 1`, `hKI : AccChildKeeps K L Reach 1 | `acc_of_run`（AccInd.lean、`AccOfRunStmt`）が `LimitSt | 部分的（`accKeepBody`/`accKeepChild_proved` | 未供給の義務 |
| C.AC-9 | `RunDataLink` / `hDS : DataOfShape K` | DG-DATAOF（`DataSound`／`dataOfAt_sound`） | AC-1 に記載 | 未供給の義務 |
| C.CV-1 | `hq : LetQuoteEq d st` | 履歴 4246: 「担当: R-trace/R-in/R-nl/R-dom/readF⇒FReach | 不明（REV7: 「`LetQuoteEq`, `FullInv` for a | 未供給の義務 |
| C.CV-2 | `hnl : LetsNoLoose st`（R-nl） | dg-readertrace（4246 note）。REV7 §6 は当初「new Issue」、後 | 不明（REV7 S5: `machClose_bvar` は root bvar | 未供給の義務 |
| C.CV-3 | `hi : FullInv nDecl st`／`FReachC`（readF の trace） | dg-readertrace（RT 節） | 不明。REV7 §0 行 1: 「R-trace for `readF` cal | 未供給の義務 |
| C.CV-4 | `hbr : ShapeFuelBridge` | `sparkle-gen5-reader-bridge`（REV7 §6 の割当表）。本グループ外 | 不明（REV7: reader-bridge の goal に「fuel 版の正 | 未供給の義務 |
| C.CV-5 | shape 側の同一視 `hsp` / `hss` / `hls` / `hn` | dg-dataof（4246: 「row 6b/nDecl = dg-dataof」） | `hsp`/`hss`/`hls`/`hn` の d 側は `dataOfAt_ | 未供給の義務 |
| C.CV-6 | `hcb`（`rowB1_of_inv`）, R-in, R-dom | `hcb` は 4246 note の「B3 = src-argw」、R-in／R-dom／R-nl | 不明（未供給と REV7 に記載） | 未供給の義務 |
| C.RT-1 | `hT : TraceGood senv nDecl (readF senv n)`（帰納仮定） | 本 Issue 自身（全 arm の `hstep` が揃えば `readF_traceGood_o | いいえ、とは言えない。5560/5577: 「hT/成功run、他arm、全体 | 未供給の義務 |
| C.RT-2 | `hpre : TracePre senv nDecl (Call.…)` | REV7: `ShapeInputs`（R-in）は dg-readertrace の担当 | 不明 | 未供給の義務 |
| C.RT-3 | `hv`（成功 run） | 記載なし（5560: 「hT/成功run」） | 不明 | 入力条件（成功 run の仮定） |
| C.RT-4 | `hstep`（全 arm） | 本 Issue。REV4 §0 は未供給の arm を列挙: `chainStep` の `.let | 不明（上記 arm は「候補経路では未供給」） | 未供給の義務 |
| C.DG-1 | 被覆 (i) `dataOf` 成功、(ii) `GenWF d = true`、(iii) `P = genP env | (i) DG-COVER, (ii) DG-WFCOVER, (iii) DG-PKGASSIGN（ | いいえ、とは言えない。DGEN_FREEZE 自身が「(i)(ii) は M5 | 未供給の義務 |
| C.DG-2 | `DeclConnect`（G3-DECL） | DC-FORM／DC-SUPPLY の study unit（dgen の done note 28 | 不明（2698/2702 の R6: 実宣言に対する存在・適切性の一様供給なしに | 未供給の義務 |
| D.P1 | hP | 後続の t2-tie（`calleePkg_of_t1ND`、条件付き）と dg-acc | 不明。この Issue の履歴・結果文書に根拠は書かれていない | 入力条件 |
| D.P2 | h2（LetTie、t2） | t2-tie（decoded family 経由で証明済み）。生成器の family に対する ti | decoded family 版は はい（`letTie_dec`）。生成器の | 未供給の義務（生成器の family 版）。decoded family 版は証 |
| D.P3 | h13（CallOut、t1+t3） | t2-tie / T2-DEC（`hPointG_iff_callOutG`、`hPointG_if | 不明。2 呼び出しの個別検証（`tm2_callOut`、`wQ_callOut | 未供給の義務 |
| D.T-1 | hDG_SEM（GenExtAtCall） | sparkle-gen5-dg-sem の P4e（`genExtAtCall_of_genSem` | この調査では見つからなかった。T2TIE_NEXT_FREEZE_R0 §1 r | 未供給の義務 |
| D.T-2 | hDG_SEM_range（CallOutRange） | 置換版 `callOutRange_of_widths`（T2Range.lean:162）が `P | `Pkg.src_range`、`callOutRange_of_widths` | 未供給の義務（組み立て済み、末端は T-3/T-4） |
| D.T-3 | hOW（OneOutWidth） | sparkle-gen3-data-supply（G-ONEOUT-WID / G-DATA）。T2 | 補題 `oneOutWidth_of_strictP`（Tools/Shippi | 未供給の義務（M3/gen3 側。T1 台帳を参照） |
| D.T-4 | hkidW（group parent の幅） | sparkle-gen3-data-supply（T2TIE_NEXT_FREEZE_R0 §1 r | この調査では見つからなかった。候補 `hkidW_of_data`（CallWi | 未供給の義務（M3/gen3 側。T1 台帳を参照） |
| D.T-5 | hsh / hDG_CLOSINGRUN（ClosingShared、ClosingRun0） | sparkle-gen5-dg-closingrun（非空虚性、depth0 `stop`） | 履歴は、`ClosingShared` が `ClosingRun.shared | 未供給の義務（dg-closingrun 側。各 binder は dg-clo **【前提解消（e6d8e55b、reviewer 承認 seq 5756）。条件付き部品。§9.1】** |
| D.T-6 | hT（T1HypND） | T1 側 | T1 台帳を参照 | T1 台帳を参照 |
| D.T-7 | hDG_GENP | `_one_ex` と `_group_kidW` では `calleePkg_of_t1ND`（T | 存在形は はい（`calleePkg_of_t1ND`、built）。T1 の | 入力条件（T1 の `pkg` に帰着） |
| D.T-8 | hT2_FIELD（CallField の per-i 存在）と FieldRowAt | 一人出力は `fieldRow_one_of_callStmt`（T2Tie.lean:178）が | はい（上記 2 補題）。ただし `hsh`（T-5）が前提 | 組み立て済み。末端は T-5 **【前提解消（e6d8e55b、reviewer 承認 seq 5756）。条件付き部品。§9.1】** |
| D.T-9 | houtTy | T2-OUTTY H1-H4（`houtTy_of_realChildND`、`reach_call | はい。`hT.defines`/`hT.closed` と closing wi | 組み立て済み。末端は T-5 / T-6 **【前提解消（e6d8e55b、reviewer 承認 seq 5756）。条件付き部品。§9.1】** |
| D.T-10 | hG_DATA_CALL_*（4 個） | 未割当（この調査の履歴・文書には支払い先が書かれていない） | この調査では見つからなかった | 未供給の義務 |
| D.T-11 | hG_MEMCALLS | GENERAL_SPEC.md:364 の表で「G-MEMCALLS: `MemDec` from | この調査では見つからなかった | 未供給の義務（M2/gen2 側。T1 台帳を参照） |
| D.T-12 | closingRun0_of_run 系の statement-level binder | R0 §1 の owner 列による。`hord`/`hrow`/`hrows`/`hIH` は s | `hs`、`hd0`、`hrun` は FG の仮定そのもの。他は、この調査では | 入力条件（`hs`、`hd0`、`hrun`）。未供給の義務（`hord`、`h |
| D.D-1 | ReflectsAll | boundary-audit §4 の表（kjob/g5ba-r16@96e862fe、script | この調査では見つからなかった | 未供給の義務（FG の仮定として残る）。`ReflectsAll = False |
| D.D-2 | Post | default route は証明済み（`synthesizeCombinational_postE | default route は はい（`synthesizeCombinatio | default route は入力条件（RunsTo）のみ。parametric |
| D.D-3 | GP（package 割り当て） | package-coverage（todo、未割当の設計）、dg-acc の `genP_pkg`（ | この調査では見つからなかった。`nv_gp` は、EntryWitness があ | 未供給の義務 |
| D.D-4 | CV（ConstValueRel）と ConstValueFunctional | decl-bridge（todo）。`seq3553` は「新 TRUSTED 採用は未承認」。DC | この調査では見つからなかった | 未供給の義務（TRUSTED 境界としては明示されていない。「no TRUSTE |
| D.D-5 | DeclConnect の rows 前提（hAcc / hclosed / hstep、順序 R） | decl-bridge（todo。設計のみ）、dg-sem、dg-dataof、dg-acc | この調査では見つからなかった | 未供給の義務 |
| D.D-6 | Start / Laws（EntryWitness の条件） | boundary-audit §2 の分類による（下記 E-11/E-12） | boundary-audit の記述では `AdmCtx` は `Command | 入力条件（Start）、CONTRACT 境界（Laws）。boundary-a |
| D.D-7 | NoRawBelow（hno） | U-CORENR（74343ad8。freeze 28f2627c は seq5327 で承認、実装 | 承認済みの根拠は `noRawBelow_of_closeInsts`（実 ru | 未供給の義務（実供給は 74343ad8 待ち。leaf と (a3) は未） |
| D.D-8 | hlk（D と D′ の lookup 同一） | 証明済み。`postEntry_lookup_ne`（DCEntryN.lean:84、承認 seq | はい（`postEntry_lookup_ne` は承認済み）。`PostEnt | 入力条件（default route では証明済み） |
| D.D-9 | MachineDefines / MachineClosesAtA（hdef / hcl） | T1 側 | T1 台帳を参照 | T1 台帳を参照 |
| D.E-1 | hmemSame | `MemTagsNamed` は U4 の `hmem_of_machineShapeF`（E-5 | 文書によると mem 同士の `insts[k].1 = insts[k'].1 | 未供給の義務（`MemTagsNamed` に帰着） |
| D.E-2 | hself | U3 の `hself_all_reached` は `hin : InClass g B top | 文書によると「無条件の定理は見つからなかった」。条件付きで U2/U3 が bu | 未供給の義務（E-6〜E-9 に帰着） |
| D.E-3 | hn（kid モジュール名） | 文書は「synthesis run についての事実」とし、供給元は不明 | `hn_kidNames`（kidNameAt の定義による）は はい（buil | 未供給の義務（B7 部分） |
| D.E-4 | B3 hparentD / B4 hdisjD / B5 hfresh（残余） | B3/B4 は call-graph/rank 系。B5 は文書が「FG がそのような設計を覆うべき | この調査では見つからなかった。B5 は出力名が `inst{gi}_…` と衝突 | 未供給の義務 |
| D.E-5 | U3 の GraphAgrees / ReachSpans / InClass / hmem | `hmem` は U4（`hmem_of_machineShapeF`、NameKids4.lean | 上記 U4〜U6 は built。ただし `ReachSpans`、produc | 未供給の義務 |
| D.E-6 | U4 の hF（machineShapeF） | reader-bridge（`machineDefines_of_readsAll`、boundar | この調査では見つからなかった。production bridge は未供給（se | 未供給の義務 |
| D.E-7 | U5 の hfo（FirstOcc） | 未割当（production の `ds`/`Reach`/`S` が未供給） | この調査では見つからなかった | 未供給の義務 |
| D.E-8 | U6 の hnd / hr | 未割当。production の `hnd`/`hr` は、この調査では見つからなかった（seq50 | この調査では見つからなかった | 未供給の義務 |
| D.E-9 | U7 の hg（OrdPath 上の GraphAgrees） | U8（`graphAgrees_of_mem`）の freeze のみ承認。実装は無い（seq508 | この調査では見つからなかった。`Reach` が `OrdPath` と一致する | 未供給の義務 |
| D.E-10 | Laws の 14 フィールド（G5） | 未割当。GENERAL_SPEC §5 M5 は「G5: a model of `Laws`, or | この調査では見つからなかった。フィールドごとの使用トレースは未実施（FG の閉じ | boundary-audit は CONTRACT と分類（「approved |
| D.E-11 | Start の 2 conjunct | 未割当 | `Start.1` は `Command.mkMetaContext` に対して | 入力条件（CONTRACT。start-world invariant at d |
| D.E-12 | G7 の hno / htop | 未割当 | `hno`/`htop` が全成功 run で成り立つかは、この調査では見つから | 未供給の義務（G7-a/b） |
| D.E-13 | G7-c 印字（printer） | なし | 対象外 | TRUSTED 境界（boundary-audit §3 が「TRUSTED b |

## 8. 段 2 計画（文書のみ。Lean は書いていない。agent `fg-ledger4`、branch `kjob/fg-ledger4`、base `kjob/fg-ledger3` dd624a27 = 段 1 承認済み）

### 8.0 これは何で、何ではないか

- 台帳の 110 ブロック（重複整理後。§2, §4）を分類し、**型が今書けるものを 1 つの Lean `Prop` 定義に仮説として並べ、書けないものは理由つきで registry に残す**計画。T1 側の段 2 計画（`scripts/gen3/PREMISE_LEDGER.md` §11、`kjob/t1-ledger3` ce79afd0 を読んだ）と同じ形にした。**T1 側の計画は reviewer の changes_requested（seq 5659）を受けて `kjob/t1-ledger4` で改訂中なので、T1 の数・ID・束縛名は変わりうる。** この計画は seq 5659 の回答（非空虚性行を仮説から分ける、閉包は T1Hyp の量化に合わせる）だけを取り入れた。
- **これは「全前提を仮説にした文」であって前提の供給ではない。** この計画も、計画が書く文も、**台帳の前提差分は 解消 0 / 追加 0**。どの行も「消えた」とは書かない。
- **全 110 ブロックを型つき仮説にはできていない。** 型つきで書けるのは 7 仮説（外側 4、内側 3）。FG 側のリーフ 76 行のうち 69 行は、型の本文が文書にしかない／閉包が未固定／搬送体（carrier）が未固定のため registry に残る（§8.4）。したがって Lean に書く文は **「型付けできた部分」であり、「全前提を並べた文」の完成形ではない**。完成には §8.4 の各 freeze が要る。
- 定理ではなく `Prop` 定義にする（証明はない。主張しない）。定理名 `fg_of_ledger_premises` は予約するだけで宣言しない。
- Lean／build なし。sorry・axiom・native_decide なし。merge・push なし。局所統合は §8.6 に列挙して止まる（coder の担当）。
- 調べ方: `git show` / `git cat-file` / `git grep` / `git rev-parse` / `git merge-base --is-ancestor` / `git merge-tree --write-tree --name-only`。**`git merge-tree --write-tree` は object database に tree object を書くが、ref・index・作業ツリーは変えない。** checkout も merge もしていない。

### 8.1 110 ブロックの数え方と分類

**どの行を残すか（重複整理 §4 の 36 件）。** §4 の表は「残す行」を名前でしか示さないので、ここで固定する（総数 110 は変わらない）。除く 36 行は 19 組の重複で、組ごとの残す行は次のとおり。

| 組（§4） | 残す行 | 除く行 |
|---|---|---|
| Laws | A.P-01 | B.F-3, D.E-10 |
| Start | A.P-02 | A.P-03, C.RR-1, B.F-2, D.E-11, D.D-6 |
| 核 run | A.P-04 | B.F-5, B.G-2, C.CR-5, D.T-12 |
| gate/first-gate entry | B.G-1 | B.G-8, B.F-6, B.F-7 |
| MachineDefines | A.P-06 | C.RR-3, D.D-9 |
| MachineTaken / closes | A.P-07 | C.AC-6 |
| 後処理関係 | A.P-05 | B.P-6, D.D-2 |
| package 割当 GP | D.D-3 | D.P1, D.T-7 |
| call 生成残差 | A.P-18 | D.P2, D.P3 |
| ChildKeepsInv | A.P-24 | B.F-1, C.CR-3, C.AC-8 |
| OneOutWidth | A.P-25 | D.T-3 |
| G-DATA-CALL | A.P-19 | D.T-10 |
| G-MEMCALLS | A.P-16 | D.T-11 |
| DeclConnect | D.D-5 | C.DG-2 |
| T1Hyp | C.CR-4 | D.T-6 |
| ClosingRun の行 | C.CR-1, C.CR-2 | D.T-5 |
| DataOfSound | C.SM-1 | C.DO-1, C.AC-1 |
| C0 | C.EN-6 | C.RK-3 |
| DataOk の束 | A.P-10, A.P-11, A.P-12, A.P-25 | A.P-20 |

除く行は 2+5+4+3+2+1+2+2+2+3+1+1+1+1+1+1+2+1+1 = 36（全て別の ID。作業用 script で `146 − 36 = 110` と、残す 110 行の全てに分類があることを確認した）。C.CR-3 は ChildKeepsInv の組で除かれるので、ClosingRun の組で残るのは C.CR-1, C.CR-2。

**区分（この計画の読み。定義は reviewer が確認する）。**

| 区分 | 意味 | 文の中での扱い |
|---|---|---|
| CTX | 文の文脈 binder | binder として現れる（仮説ではない） |
| ANT | 結論 `FG_CONNECT` の前件（`EntryWitness`）の中 | 前件として現れる |
| TY-O / TY-I | 型が今書けた仮説。O = 外側（閉じた Prop）、I = 内側（run ごとの前件） | 仮説として現れる |
| UN-x | 型付けできなかった（registry）。x は理由コード（§8.4） | 文に現れない。registry に ID を残す |
| T1 | T1 台帳の行と同じ前提（または T1 側で解消済み） | **文に入れない**（二重に数えない）。T1 台帳の行 ID を参照 |
| PA | 親行または導出される行。リーフ行に分解されている | 文に入れない（リーフを入れる） |
| AU | 非空虚性の監査項目 | 文に入れない。別の Check（§8.5） |
| XC | 文から除く（廃止・未承認・保証の外）。理由を書く | 文に入れない。ブロックは 110 に数えたまま |

**数（機械的に数えた値）。**

| 区分 | ブロック数 |
|---|---|
| CTX | 1 |
| ANT | 2 |
| TY-O | 4 |
| TY-I | 3 |
| UN（理由コード別は §8.4） | 69 |
| T1 | 16 |
| PA | 10 |
| AU | 2 |
| XC | 3 |
| **合計** | **110** |

- 文（§8.3）に現れる台帳行: CTX 1 + ANT 2 + TY 7 + carrier の 4（A.P-05 `Post`、D.D-1 `ReflectsAll`、D.D-3 `GP`、D.D-4 `CV`。binder として現れるが、その性質を述べる仮説は registry）= **14**。残り 96 = UN 65 + T1 16 + PA 10 + AU 2 + XC 3。
- **FG 側のリーフ行 = TY 7 + UN 69 = 76。** うち文に型つきで入るのは 7。
- **T1 台帳と同じ前提とみなした 21 行**（CTX/ANT 3 = A.P-01, A.P-02, A.P-04、AU 1 = A.P-28、TY 1 = C.CV-4、T1 区分 16）: A.P-01, A.P-02, A.P-04, A.P-07, A.P-08, A.P-09, A.P-10, A.P-11, A.P-12, A.P-14, A.P-15, A.P-16, A.P-19, A.P-22, A.P-23, A.P-24, A.P-25, A.P-26, A.P-28, C.CR-1, C.CV-4。対応は、FG 台帳の部分ファイルの本文または T1 台帳の「same premise under other names」欄・§8 に、名前の一致（G-MEMCALLS、G-DATA-CALL、LiftShips、hrow、ShapeFuelBridge など）があるものを **この計画が読んで結んだ**もので、T1 側の agent の確認は受けていない（A.P-09、A.P-14、A.P-15、A.P-22 は特に読みが入る。Q-F1 で確認を求める）。T1 ID が親（T1L-03, 07, 08, 09, 10）の行は、親の下のどのリーフと同じかを台帳が示さないところは親 ID のままにした。
- **T1 と FG の合算の総数はここでは出さない。** T1 台帳は「71 行／リーフ 62」、この台帳は「ブロック 146／重複整理後 110」で数え方が違う。重複なしの合算が要るときは、上の 21 行の対応表を使って ID 単位で別に数える。


### 8.2 110 ブロックの一覧（台帳 ID は §7 の索引と同じ。仮説名は文 §8.3 の binder 名）

「型の根拠」は、TY の行は §8.6 の表の定義元。UN の行は理由コード（§8.4）と、本文が載っている部分ファイルのブロック（`premise_ledger/<A_M2|B_M4|C_M5dg|D_M5t2>.md` の同 ID。`git show` の原文が貼ってある）。T1 区分は T1 台帳（`kjob/t1-ledger3` ce79afd0 の `scripts/gen3/PREMISE_LEDGER.md` §3）の行 ID。

| 台帳ID | 仮説名 | 区分 | 内容・根拠・型の出どころ |
|---|---|---|---|
| A.P-01 | `L` | CTX | context binder `L : Laws mref cref`; = T1L-01 (shared). TRUSTED candidate (ledger class). merged: B.F-3, D.E-10 |
| A.P-02 | `Start` | ANT | inside `EntryWitness` (1st conjunct); = T1L-02 (shared). merged: A.P-03, C.RR-1, B.F-2, D.E-11, D.D-6 |
| A.P-04 | `run` | ANT | inside `EntryWitness` (2nd conjunct, the two-route disjunction); core-run part = T1L-02 (shared). merged: B.F-5, B.G-2, C.CR-5, D.T-12 |
| A.P-05 | `Post` | UN-K | carrier `Post`; default route PostEntry is proved (`synthesizeCombinational_postEntry`); parametric-route post-processing and adoption of `Post` unapproved (seq 4318). merged: B.P-6, D.D-2 |
| A.P-06 | `h_A_P06` | TY-I | `T1Hyp.defines` closure over `TgtRun` reach (R-clo, Q-F2). merged: C.RR-3, D.D-9. T1L-07 is a T1 parent with no binder, so no double count |
| A.P-07 | - | T1 | T1L-08 (parent) -> 20-25, 21. merged: C.AC-6 |
| A.P-08 | - | T1 | T1L-06 (shared, typed there as h_T1L_06). FG-side payers: C.CR-2, D.D-3 |
| A.P-09 | - | T1 | T1L-32, 39, 40 (DataOkB rows; payer includes DG-DATAOF/COVER) |
| A.P-10 | - | T1 | T1L-12 |
| A.P-11 | - | T1 | T1L-11 |
| A.P-12 | - | T1 | T1L-11, 12 (ExtInS conjunct) |
| A.P-13 | - | PA | derived from `MemDec` (A.P-16 = T1L-26) by `memOrigin_of_memDec`, needs `Nonempty ι` (T1L-41) |
| A.P-14 | - | T1 | T1L-15..18 (uncovered cases) and T1L-03 (StepCaseOK scope) |
| A.P-15 | - | T1 | case restriction of `StepStmtCases`; complement is T1L-17 |
| A.P-16 | - | T1 | T1L-26. merged: D.T-11 |
| A.P-17 | - | PA | = `T1Hyp.dec` (T1L-09 parent); leaves: A.P-16, A.P-18, A.P-19, D.T-1, D.T-4 |
| A.P-18 | - | UN-C | G3-GEN-CALL: `LetTie`/`CallOut` (par/gen5-t2@0bb53938) over generator families `ArgFamB`/`ArgFamV`; family not fixed. T1 ledger §8 assigns HPointAt to FG. merged: D.P2, D.P3 |
| A.P-19 | - | T1 | T1L-27. merged: D.T-10 |
| A.P-21 | - | XC | retired: `group_childShips` has no `hseq` binder (seq 2713) |
| A.P-22 | - | T1 | T1L-03 (parent, `hStep`); no leaf of its own in the T1 ledger |
| A.P-23 | - | T1 | T1L-19 |
| A.P-24 | - | T1 | resolved on the T1 side: `keepChild_proved` (T1 ledger §6); IHAt part is the T1 conclusion. merged: B.F-1, C.CR-3, C.AC-8 |
| A.P-25 | - | T1 | T1L-14. merged: D.T-3 |
| A.P-26 | - | T1 | T1L-04 |
| A.P-27 | - | AU | non-vacuity of the conclusion `TopShips` (P-TOP, `PTopPrem`); T1 ledger rows 69-71 are the sibling audit |
| A.P-28 | - | AU | concrete run + non-vacuous `Laws` (`PbhRunEx L`); = T1L-70 (shared) |
| B.G-1 | - | UN-R | component of `ReflectsAll` (gate route): gate/first-gate `entry` (`EntryDefines`). merged: B.G-8, B.F-6, B.F-7 |
| B.G-3 | - | UN-R | component of `ReflectsAll` (gate route): `GateLeaf.old` |
| B.G-4 | - | UN-R | component of `ReflectsAll` (gate route): `GateLeaf.peel` |
| B.G-5 | - | UN-R | component of `ReflectsAll` (gate route): `GateLeaf.he` |
| B.G-6 | - | UN-R | component of `ReflectsAll` (gate route): `GateLeaf.hb`/`hv` |
| B.G-7 | - | UN-C | `hw1 : g.srt.width ≠ 1` (width 1 has no supplier); depends on `g : GateLeaf` |
| B.G-9 | - | UN-D | route table `Q`/`hQ`; assembler (gen4-fg-assembly) has no Lean |
| B.G-10 | - | XC | U-G7a: Lean not reviewed, no FG correspondence recorded (ledger B.G-10) |
| B.F-4 | - | UN-C | `hS` (FB-22): Lean text exists (FbFragRun), over `S`, `dn names n fe`; closure not fixed |
| B.F-8 | - | UN-C | `ChildRunN` of the core module (clean-up transport input); closure not fixed |
| B.P-1 | - | UN-C | `AllPos θ` (PA: ParamLayerA:43); closure needs the route guard and `θ := parameters` (Q-F3) |
| B.P-2 | - | UN-C | `Bound`/`PosDim`/`NonNegDim`/`SliceOK`: conditions on DimExprs of the design; closure not fixed |
| B.P-3 | - | UN-C | `ExprOK`/`TyPos`/`TyBound`; same |
| B.P-4 | - | UN-B | B1-B4 production<->model bridges (`evaluate`, `specializeType`, `specializeExpr`, `validateBindings`). B1 has a verbatim closed type in the ledger; B2-B4 are prose. Splitting the block would change 110, not done here (Q-F4) |
| B.P-5 | - | UN-U | `SpecSuccessAllPositive`: whether T is part of FG is a user decision (D3, PARAMETRIC_SPECSUCCESS_DECISION.md) |
| B.P-7 | - | UN-B | I3c is stated on the old `RefLaws`; no `Start` -> `Out0` lemma found (PARAMETRIC_FREEZE F1 row) |
| B.P-8 | - | UN-C | `LegalBinding D θ` (PA ParamIface:91); which `D` (`D` or `D.addModule b`) is not fixed by the ledger (Q-F3) |
| C.RR-2 | - | UN-B | entry run -> core run bridge (`hr`); no statement found |
| C.CR-1 | - | T1 | T1L-04 (hrow) |
| C.CR-2 | - | UN-D | `hGen`/`GeneratedAt`: design text only (DGEN_FREEZE, par/gen5-t2@c398021c); `Gen` is a parameter |
| C.CR-4 | - | PA | = `T1Hyp`/`T1HypND` (T1L-06..10 parents); fields are paid by leaf rows. merged: D.T-6 |
| C.EN-1 | - | UN-C | `QuietStrength L L' env₀`; second Laws `L'`/`env₀`/per-run variables not fixed |
| C.EN-2 | - | UN-C | `AdmDown L L'`, `hA'`; second Laws `L'`/`env₀`/per-run variables not fixed |
| C.EN-3 | - | UN-C | start cache `hC`/`hE`/`hN`; second Laws `L'`/`env₀`/per-run variables not fixed |
| C.EN-4 | `h_C_EN4` | TY-O | `CellPrem MkRefd mref cref` (closed). TRUSTED-or-not is the A/B/C decision of DG_ENV_FREEZE §4 (no record found); typing it decides nothing |
| C.EN-5 | - | UN-C | `¬ DRow p`; second Laws `L'`/`env₀`/per-run variables not fixed |
| C.EN-6 | - | UN-C | C0: `hall` is a closed Prop (`∀ u, ReadsAt env₀ cref u`) but `hc hg1 hg2 hsh` need `c ci₀ shape`; block not typed as a whole. merged: C.RK-3; second Laws `L'`/`env₀`/per-run variables not fixed |
| C.EN-7 | - | UN-C | `hentry`; second Laws `L'`/`env₀`/per-run variables not fixed |
| C.EN-8 | - | UN-U | `mctx.canUnfold? = none`: narrower than `Start`'s `AdmCtx`; adopting it in FG would be a scope shrink (prohibited): user decision |
| C.RK-1 | `h_C_RK1` | TY-O | `ReadKeeps cref` (closed) |
| C.RK-2 | - | UN-C | `hHead`: `EnvFrame (coreHead X) …` per X, mctx, cctx |
| C.RK-4 | - | UN-C | `hrun` of `readMachine` (auxiliary command run, not a FG hypothesis) and `hX` |
| C.RK-5 | - | PA | `RunReadsAt` object, built by `runReads_of_run` from the start/run/defines/closes rows **【前提解消（e6d8e55b、reviewer 承認 seq 5756）。条件付き部品。§9.1】** |
| C.RK-6 | `h_C_RK6` | TY-O | `ReflExprAgree` (closed) |
| C.RK-7 | - | UN-D | U14 `hM`/`hC`: freeze text only, Lean not implemented |
| C.RK-8 | - | UN-C | reader completeness (`Complete cfg`, `hb hv hw hwf hdom` per `d`) |
| C.DO-2 | - | UN-N | reader agreement `Rdr`, `s = sp`: no Lean proposition (DATAOF freeze §11.3) |
| C.DO-3 | - | UN-N | row 6a, C-CMP, C-QWIT, S-OK, S-COV-FLOAT: names only |
| C.SM-1 | - | UN-C | `DataOfSound dataOf initsOf` and the coverage `dataOfAt = some d`; concrete `dataOf`/`initsOf` and the coverage closure not fixed. merged: C.DO-1, C.AC-1 |
| C.SM-2 | - | UN-C | `hmem` (ordC); proved for `ordCallees₀` on g5ac-r26, which is not in the g5sm line |
| C.SM-3 | - | UN-C | `hinv`/`hunf` (kit) |
| C.SM-4 | - | UN-C | `hacc` |
| C.SM-5 | - | PA | `CalleesCausal`, built by `srcCausal_of_acc_unfold` from C.SM-3, C.SM-4 |
| C.SM-6 | - | UN-C | `GenWF d = true` |
| C.SM-7 | - | PA | guard `child? = none` (ordinary call) that R-clo already carries |
| C.AC-2 | - | UN-C | `hev : GDEvidence`; kit `K` / `Reach` carrier not fixed |
| C.AC-3 | - | UN-C | `hloc hdecl hd`; kit `K` / `Reach` carrier not fixed |
| C.AC-4 | - | UN-C | `ReachCover K Reach`, `hcl`; kit `K` / `Reach` carrier not fixed |
| C.AC-5 | - | UN-C | `GatesNoneAt env₀ Reach`; kit `K` / `Reach` carrier not fixed |
| C.AC-7 | - | UN-C | `ReadsSupplyAt e L Reach`; kit `K` / `Reach` carrier not fixed |
| C.AC-9 | - | UN-C | `RunDataLink`, `hDS : DataOfShape K`; kit `K` / `Reach` carrier not fixed |
| C.CV-1 | - | UN-C | `LetQuoteEq d st`; reader state `st` is run-local |
| C.CV-2 | - | UN-C | `LetsNoLoose st`; reader state `st` is run-local |
| C.CV-3 | - | UN-C | `FullInv nDecl st`, `FReachC`; reader state `st` is run-local |
| C.CV-4 | `h_C_CV4` | TY-O | `ShapeFuelBridge` as the inline closed Prop of `shapeAgree_of_production` (`hbr`). Same premise as T1L-43 `OSH` (T1 registry, untyped there): shared; FG types it first |
| C.CV-5 | - | UN-C | `hsp hss hls hn`; reader state `st` is run-local |
| C.CV-6 | - | UN-N | `hcb`; R-in, R-dom are names only (`ShapeInputs`, `RootFloatPh`...) |
| C.RT-1 | - | UN-C | `hT : TraceGood`; reader-internal induction data |
| C.RT-2 | - | UN-C | `hpre : TracePre`; reader-internal induction data |
| C.RT-3 | - | UN-C | `hv` (success of a reader step); reader-internal induction data |
| C.RT-4 | - | UN-C | `hstep` (all arms); reader-internal induction data |
| C.DG-1 | - | UN-D | coverage (i) `dataOf` success, (ii) `GenWF`, (iii) `P = genP env₀`; `GeneratedAt` is design text only |
| D.T-1 | `h_D_T1` | TY-I | `GenExtAtCall` over reached ordinary calls (R-clo, Q-F2). T1 ledger §8 assigns hDG_SEM to the FG ledger |
| D.T-2 | - | PA | `CallOutRange`, built by `callOutRange_of_widths` from A.P-25/T1L-14, D.T-4, houtTy (D.T-9) |
| D.T-4 | `h_D_T4` | TY-I | `hkidW` group-parent width (R-clo, Q-F2). T1 ledger §8 assigns it to the FG ledger |
| D.T-8 | - | PA | `CallField`/`FieldRowAt`, built by `fieldRow_one_of_callStmt`, `servedCall_of_closingShared_group` from the ClosingRun row (C.CR-2 chain) **【前提解消（e6d8e55b、reviewer 承認 seq 5756）。条件付き部品。§9.1】** |
| D.T-9 | - | PA | `houtTy`, built by `houtTy_of_closingND` from T1Hyp fields and the ClosingRun row **【前提解消（e6d8e55b、reviewer 承認 seq 5756）。条件付き部品。§9.1】** |
| D.D-1 | `ReflectsAll` | UN-R | carrier `ReflectsAll : Laws mref cref -> Name -> List (String × Nat) -> Prop` (FG.lean:30); its definition = the per-route rows B.G-*, B.F-4, B.P-*, A.P-06, ... ; no Lean definition found |
| D.D-3 | `GP` | UN-K | carrier `GP : Environment -> Pkgs ι dom`; package assignment. merged: D.P1, D.T-7. dg-acc `genP_pkg` is conditional |
| D.D-4 | `CV` | UN-K | carrier `CV : ConstValueRel`; ConstValue definition not written (DCF unit); `ConstValueFunctional CV` is a conclusion conjunct of `FG_CONNECT` |
| D.D-5 | - | UN-C | `hAcc hclosed hstep` and the order `R` of `declConnect_of_rows`; `DeclConnect` itself is a conclusion conjunct. merged: C.DG-2 |
| D.D-7 | - | UN-C | `NoRawBelow` (`hno`); per-run, `raw` is existential |
| D.D-8 | - | PA | `hlk`, proved for the default route (`postEntry_lookup_ne`, approved seq 4700) |
| D.E-1 | - | UN-C | boundary-audit `hmemSame`; call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-2 | - | UN-C | boundary-audit `hself`; call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-3 | - | UN-C | boundary-audit `hn` (kid module names); call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-4 | - | UN-C | boundary-audit B3/B4/B5 residue (B5 may be a user decision); call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-5 | - | UN-C | boundary-audit `GraphAgrees`/`ReachSpans`/`InClass`/`hmem`; call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-6 | - | UN-C | boundary-audit `hF` (`machineShapeF`) over carrier `S`; call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-7 | - | UN-C | boundary-audit `hfo` (`FirstOcc`) over `ds`, `S`; call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-8 | - | UN-C | boundary-audit `hnd`/`hr` over `ds`; call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-9 | - | UN-C | boundary-audit `hg` on `OrdPath`; call-graph carriers `g`, `ds`, `S` not fixed |
| D.E-12 | - | UN-C | G7-a `hno`/`htop` over `D`, `raw` |
| D.E-13 | - | XC | G7-c printer: TRUSTED by design, outside the guarantee (boundary-audit §3) |

### 8.3 文の名前と完全な型

ファイル: `Tools/ShippingGenFGLedgerPremises.lean`（新規。module `Tools.ShippingGenFGLedgerPremises`）。文の名前: `Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmt`。値は閉じた `Prop`（自由変数なし）。結論は承認済みの `FG_CONNECT`（`Tools/ShippingGen5FG.lean`、kjob/g5dc-r23@**0fcce4e7**）の本体を展開した形に、内側の 3 仮説を挟んだもの。

**読み方（先に）。**
- 4 つの carrier（`ReflectsAll` `Post` `GP` `CV`）は **仮説ではなく binder** として全称にする。`FG_CONNECT` 自身がこの 4 つを引数に取る（FG.lean:30,42,54）。これらの性質を述べる仮説は registry（§8.4 の K / R）にあり、文には入らない。**したがって、この文は条件付き schema である**（`fgCond_trivial`、FG.lean 末尾が、`Post := False`、`GP := none`、`CV := ∅` で `FG_COND` が成り立つことを示している）。carrier が固定されるまで、「文が真」は FG の主張にならない。
- 内側の 3 仮説では、パッケージ割当を `P := GP (envAt cref w)`、到達述語を `Reach := TgtRun P declName`（`FG.lean` の最小述語 `TgtRun`。`FG_CONNECT` の `DeclConnect` が使うものと同じ）とした。これは **この計画の閉包の読み（Q-F2）** で、台帳が与える文ではない。T1 計画 §11.3 Q2（reviewer の回答 seq 5659 が採用した読み）と同じ方針: T1Hyp の field が使う `∀ c, Reach c → ∀ q, P c = some q → …` とガード `(origins.getD k .ord).child? = none` に合わせた。
- **T1 台帳と同じ前提（T1 区分 16 行）はこの文に入れていない。** T1 の前提を FG の run ごとに束ねる方法は Q-F1。入れるまで、この文は T1 側の前提について **仮説なしの（強い）文** になる。つまり **「全前提の文」ではない**。

```lean
import Tools.ShippingGen5FG                  -- kjob/g5dc-r23@0fcce4e7 (EntryWitness, TgtRun, FG_CONNECT, ConstValueFunctional; DeclConnect)
import Tools.ShippingGen5EnvFrame3           -- kjob/g5env-r22@b42ce414 (CellPrem)
import Tools.ShippingGen5T2Tie               -- base f514d08d (GenExtAtCall)
import Tools.ShippingReaderFuelShape         -- base (machineShapeF)
import Tools.ShippingStRefCorrespondence     -- base (ReadKeeps)
import Tools.Prototype.DGenStored2           -- base (ReflExprAgree)
set_option autoImplicit false

namespace Tools.ShippingGenFGLedgerPremises
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)

def FGLedgerPremisesStmt : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    -- carriers (binders, NOT hypotheses; their characterizing rows are in the registry)
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)        -- D.D-1
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)             -- A.P-05
    (GP : Environment → Pkgs ι dom)                                           -- D.D-3
    (CV : ConstValueRel)                                                      -- D.D-4
    (L : Laws mref cref)                                                      -- A.P-01  (= T1L-01)
    -- outer hypotheses (closed Props)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)   -- C.EN-4
    (h_C_RK1 : Tools.ShippingStRefCorrespondence.ReadKeeps cref)                                 -- C.RK-1
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)                                        -- C.RK-6
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),                      -- C.CV-4 (= T1L-43)
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)),
    ConstValueFunctional CV ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →     -- A.P-02 Start, A.P-04 run, D.D-1 ReflectsAll
      -- inner hypotheses; P := GP (envAt cref w), Reach := TgtRun P declName  (Q-F2)
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ q : Pkg ι dom, GP (envAt cref w) c = some q →      -- h_A_P06
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →      -- h_D_T1
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
          (p.d.shape.instOrigins.getD k .ord).child? = none →
          ∀ q : Pkg ι dom, GP (envAt cref w) (p.d.shape.insts[k]).1 = some q → GenExtAtCall p q k hk) →
      (∀ c, TgtRun (GP (envAt cref w)) declName c → ∀ p : Pkg ι dom, GP (envAt cref w) c = some p →      -- h_D_T4
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      -- conclusion: the tail of the FG_CONNECT body (FG.lean), unchanged
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
end Tools.ShippingGenFGLedgerPremises
```

- 名前の出どころは §8.6 の表。`Pkg` `Pkgs` `Laws` `TopShips` は `Tools/ShippingGen2Defs.lean`（namespace `Tools.ShippingGen2`）、`GenExtAtCall` は `Tools/ShippingGen5T2Tie.lean:238`（同 namespace）、`machineShapeF` は `Tools/ShippingReaderFuelShape.lean:256`（`namespace Tools.ShippingReaderFuel`、同ファイル 54 行）、`machineShape?` は `Sparkle/Compiler/Elab.lean:5072`（いずれも `kjob/g3pt-s3b` f514d08d で `git show` により確認）。`MkRefd` の完全修飾名 `Tools.ShippingChildFresh.MkRefd` は GEN2_DEFS（Laws の定義）の写しで、`namespace` 行は読んでいない。名前解決は Check の `#check` が裁定し、rename はコメント／名前の修正であって前提の追加ではない（T1 計画 §11.2 と同じ扱い）。
- **束縛数**: 暗黙 4（`ι dom mref cref`）、carrier 4、`L` 1、外側仮説 4、run の ∀ の内側に仮説 3。台帳行に対応する仮説 binder は外側 4 + 内側 3 = **7**。
- `h_C_CV4` の本文は `shapeAgree_of_production` の binder `hbr`（`Tools/ShippingGen5Cover5.lean:97`、kjob/g5cv-r13@44d72eaf）の写し。`ShapeFuelBridge` という名前は T1 台帳 T1L-43 にあるが、この本文を持つ名前付き Lean 定義は探した branch には無く、binder の本文が Lean にあるだけ。**そのためこの文では inline で書く。** T1L-43 は T1 の registry で未型付けなので、T1 側とこの文での重複の扱いは Q-F1 に含める。
- `h_C_EN4`（`CellPrem`）を仮説に置くことは、`DG_ENV_FREEZE.md` §4 の A/B/C（TRUSTED にするか）を決めることではない。その決定の記録はこの調査では見つからなかった（台帳 C.EN-4）。
- B.P-1（`AllPos`）と B.P-8（`LegalBinding`）を仮説にしていない理由は Q-F3。

### 8.4 registry: 型付けできなかった 69 ブロック

仮説を `(P : Prop) (h : P)` の形で文に入れることはしない（`∀ P, P → X` は `P := True` で `X` と同値になり、前提を述べずに落とす）。型が無い行は ID を数えて registry に置く。**「型が見つからなかった」であって、「型が存在しえない」ではない。**

| コード | 意味（型の本文の所在） | 数 | ブロック |
|---|---|---|---|
| C | Lean の述語は部分ファイルに原文で貼ってあるが、**閉包**（どの reach・どの run・どの carrier の上の全称か）が台帳にも freeze にも固定されていない | 48 | A.P-18, B.G-7, B.F-4, B.F-8, B.P-1, B.P-2, B.P-3, B.P-8, C.EN-1, C.EN-2, C.EN-3, C.EN-5, C.EN-6, C.EN-7, C.RK-2, C.RK-4, C.RK-8, C.SM-1, C.SM-2, C.SM-3, C.SM-4, C.SM-6, C.AC-2, C.AC-3, C.AC-4, C.AC-5, C.AC-7, C.AC-9, C.CV-1, C.CV-2, C.CV-3, C.CV-5, C.RT-1, C.RT-2, C.RT-3, C.RT-4, D.D-5, D.D-7, D.E-1, D.E-2, D.E-3, D.E-4, D.E-5, D.E-6, D.E-7, D.E-8, D.E-9, D.E-12 |
| R | `ReflectsAll` の構成要素（route ごとの反射）。`ReflectsAll` 自体の Lean 定義が見つからなかった（GENERAL_SPEC §1.1, §6 の文のみ。`FG.lean:30` は型だけ） | 6 | B.G-1, B.G-3, B.G-4, B.G-5, B.G-6, D.D-1 |
| D | 型が文書（freeze／設計文）にしか無く、Lean 定義が探した branch に無い | 4 | B.G-9, C.CR-2, C.RK-7, C.DG-1 |
| N | 名前だけ（Lean も文書も命題を固定していない） | 3 | C.DO-2, C.DO-3, C.CV-6 |
| B | production 関数とモデル、または entry run と core run の橋の文が固定されていない | 3 | B.P-4, B.P-7, C.RR-2 |
| K | carrier（`Post` `GP` `CV`）。性質を述べる仮説の型が無い | 3 | A.P-05, D.D-3, D.D-4 |
| U | 採るか採らないかがユーザー判断の範囲の行（この計画は決めない） | 2 | B.P-5, C.EN-8 |

carrier の 4 行は D.D-1（R）、A.P-05・D.D-3・D.D-4（K）。文では binder として現れる（§8.3）。registry 69 行のうち 4 行が binder として文に現れるので、文に現れないのは 65 行。

**どの freeze が来ると型付けできるか（owner は台帳の支払い予定欄の Issue 名。台帳に無いものは書かない）。**

| 要る freeze | 型付けに効く行 | owner（台帳の記載） |
|---|---|---|
| `ReflectsAll` の定義（route 別: gate／first-gate／fallback／parametric／machine。到達宣言ごと） | R の 6 行、D.D-1。B.G-7 / B.F-4 / B.F-8 / B.P-2 / B.P-3 / B.P-8 / B.P-1 の閉包 | 台帳では未割当（B.G-1…G-9 は「未割当」、fallback は seq 5568 で台帳待ち）。`sparkle-gen4-fg-assembly` の goal に「route 別の未供給契約を隠さない」とあるが、履歴に Lean は無い |
| `GeneratedAt` / `GenData` を実 run の上に置く閉包（`ClosingRun` の `Gen`、DG-COVER 被覆 (i)(ii)(iii)） | C.CR-2, C.DG-1, C.SM-1, C.SM-6, C.AC-2, C.AC-4, C.AC-9, D.D-3 | `dg-cover` / `dg-wfcover`（本グループ外）/ `dg-pkgassign` / `dg-env` / `dg-acc`（C.CR-2, C.DG-1 の支払い予定欄） |
| 第 2 の `Laws`（`L'`）と `env₀` の導入（DG-ENV の持ち上げ） | C.EN-1, C.EN-2, C.EN-3, C.EN-5, C.EN-6, C.EN-7, C.AC-7 | `dg-env`（台帳 C.EN の支払い予定欄） |
| reader の run-local 状態 `st` と trace の閉包 | C.CV-1, C.CV-2, C.CV-3, C.CV-5, C.RT-1…RT-4, C.RK-2, C.RK-4, C.RK-8 | `dg-readertrace` / `dg-readkinds` / `dg-dataof` |
| DG-SEM と DG-ACC を 1 本の木に置く（kit `K` の carrier を固定） | C.SM-2, C.SM-3, C.SM-4, C.AC-3, C.AC-5 | `dg-acc` / `dg-sem`（台帳 C.SM, C.AC） |
| 呼び出しごとの生成残差の family（`ArgFamB` / `ArgFamV`）の閉包 | A.P-18 | `gencall-proof`（履歴は created と dependencies のみ） |
| 呼び出しグラフ・`ds` の carrier（boundary-audit） | D.E-1…E-9, D.E-12 | `boundary-audit`（台帳 D.E、seq 5572 todo で台帳待ち） |
| `DeclConnect` の rows（`R`, `Tgt`）と `ConstValue` の定義 | D.D-5, D.D-4 | `decl-bridge`（todo）、DC-FORM / DC-SUPPLY |
| パラメータ route の post-processing と `Post` の採用 | A.P-05（K） | 台帳 D.D-2: parametric route は未供給、`Post` の最終採用は未承認（seq 4318） |
| ユーザー判断 | B.P-5（`SpecSuccessAllPositive` が FG の一部か。D3、`PARAMETRIC_SPECSUCCESS_DECISION.md`）、C.EN-8（`canUnfold? = none` は `Start` より狭い） | この計画は決めない。新しい判断資料は作っていない（既存の行を分類しただけで、範囲を変えていない） |

registry の ID 一覧（コード別）:

各コードの ID は上の表の「ブロック」列と同じ（重複して書かない）。

### 8.5 非空虚性の監査項目（仮説ではない。別の Check 項目）

T1 台帳の reviewer 回答（`managerctl plan history sparkle-gen3-t1-assembly` seq 5659、Q1）に合わせ、**非空虚性は証明仮説にしない。** 次を「監査項目」として分け、文の仮説にも registry にも入れない。

| 監査 | 内容 | 対応する台帳行／T1 台帳 | この計画での扱い |
|---|---|---|---|
| N1 | 非空虚な `Laws` の値の存在（`∃ w, L.O.quiet w` を持つ `L`） | A.P-01 の非空虚性（`lawsQuietFalse` では `PbhRunEx` が偽、A.P-28）。**T1L-69 と同じ監査（T1 側が持つ。二重に数えない）** | 文に入れない。T1 の監査項目を参照 |
| N2 | 具体 run の存在と共同充足性（`PbhRunEx L`） | **A.P-28 = T1L-70** | 同上 |
| N3 | `TopShips` の実行前件（R-G、`PTopPrem`）の非空虚性（P-TOP） | **A.P-27**（AU） | 文に入れない。top-contract Issue の監査 |
| N4 | carrier の自明な値で文が成り立つこと（`Post := False`、`GP := none`、`CV := ∅` で `FG_COND` が成り立つ: `fgCond_trivial`。`FG_CONNECT` は `nv_post` `nv_gp` `nv_cv` で、`EntryWitness` が与えられたときに反駁できる） | 台帳行ではない（FG.lean のヘッダの記載） | Check に「carrier が自明なとき、この文は仮説なしで成り立つ形のままである」ことを述べるコメントとして残す。**非空虚性を示すものではない** |
| N5 | `EntryWitness`（Start・run・`ReflectsAll`）を満たす実在の run と実在の `ReflectsAll`（FG の前件の非空虚性） | 台帳行ではない（T1L-71 の FG 版） | 供給元はこの調査では見つからなかった（台帳 A.P-28、D.D-1）。数えない |

N4, N5 は新しい台帳行ではない（110 を変えない）。N1, N2, N3 は A.P-01 の一部・A.P-28・A.P-27 に対応する（A.P-28 と A.P-27 が AU 区分の 2 行）。

### 8.6 各定義の出どころ（branch@SHA と path）と局所統合

**型付けできた 7 仮説と結論が使う定義。** 「base」は T1 計画 §11.5 の統合木の base `kjob/g3pt-s3b` **f514d08d**（`git merge-base --is-ancestor` で par/gen3-induct・par/gen3-combined・kjob/g2tc-s2 を含むことを T1 計画が確認している。この計画でも kjob/g2tc-s2 fa84af5d を含むことを確認した）。

| 定義 | 行 | branch@SHA : path | 統合 |
|---|---|---|---|
| `Laws` `Start` `Pkg` `Pkgs` `TopShips` | A.P-01, A.P-02 ほか | base : `Tools/ShippingGen2Defs.lean`（46, 52, 41, 288 付近） | 不要 |
| `AdmCtx` `RealChildA` | A.P-06, D.T-4 | base : `Tools/ShippingChildInvA.lean:77`、`Tools/ShippingChildCacheA.lean:105` | 不要 |
| `MachineDefines` `kindTy` | A.P-06, D.T-4 | base : `Tools/ShippingMachineEntry.lean:2345`, `:232` | 不要 |
| `GenExtAtCall` | D.T-1 | base : `Tools/ShippingGen5T2Tie.lean:238`（base の blob は aa5c8e…、kjob/g5tt-sync 632f365d の blob は 2ead5f…。**定義は両方にある。本体の差はこの計画では見ていない**） | 不要（`GenExtAtCall` は base にある） |
| `ReadKeeps` | C.RK-1 | base : `Tools/ShippingStRefCorrespondence.lean:38`（blob 0a8561…、base／gen2-spec／g5rk-r23／g5env-r22／g5tt-sync で同一） | 不要 |
| `ReflExprAgree` | C.RK-6 | base : `Tools/Prototype/DGenStored2.lean:646`（blob 64460c…、同上で同一） | 不要 |
| `machineShape?` `machineShapeF` | C.CV-4 | base : `Sparkle/Compiler/Elab.lean:5072`、`Tools/ShippingReaderFuelShape.lean:256`（blob 03be31…） | 不要 |
| `CellPrem` | C.EN-4 | **kjob/g5env-r22@b42ce414** : `Tools/ShippingGen5EnvFrame3.lean:58`（blob 71ad31…。base に無い。b42ce414 は Lean 本体 b6b3206b にコメントのみの 1 commit を足したもの） | **G-ENV（要）** |
| `EntryWitness` `TgtRun` `FG_CONNECT` `ConstValueFunctional` | 結論、A.P-02, A.P-04, D.D-1 | **kjob/g5dc-r23@0fcce4e7** : `Tools/ShippingGen5FG.lean`（blob 0cc900…。base に無い） | **G-FG（要）** |
| `DeclConnect` `ConstValueRel` `DeclConnectAt` | 結論、D.D-4, D.D-5 | **kjob/g5dc-r23@0fcce4e7** : `Tools/ShippingGen5DeclConnect.lean:267, :274, :277`（blob 447d13…。base に無い）。`FG.lean` が `DeclConnectAbs` などの依存を持つ | **G-FG（要）** |

**統合する SHA の取り方。** kjob/g5dc-r23 の先端は **74343ad8**（U-CORENR、agent の増分 build のみで未 review。台帳 §0）。承認済みの FG.lean／DeclConnect.lean は **0fcce4e7**（先端の祖先であることを `git merge-base --is-ancestor` で確認した）。**統合するのは先端ではなく 0fcce4e7 の commit。** 先端との差は `lakefile.lean` と DCEntryU 系などの 7 ファイル（`git diff --stat`、873 行追加）。kjob/g5env-r22 の先端 b42ce414 は、台帳が引く b6b3206b（U9 の Lean 本体、clean build は coder が記録）の直接の子で、コメントのみ。

**本計画が見た branch の一覧（型付けの進み具合によって、将来これらの統合が要る）。** Defs 欄は `Tools/ShippingGen2Defs.lean` の blob（先頭 7 桁）。「試行」は `git merge-tree --write-tree --name-only f514d08d <branch>` の結果で、**ファイル名の衝突だけを見たもの**（merge の結果が build できるかは見ていない）。

| branch@SHA（先端） | Defs blob | base との試行 | 台帳で必要になる行 |
|---|---|---|---|
| kjob/g5env-r22 b42ce414（承認済み Lean は bb49da59 まで、U9 は b6b3206b で未 review） | 2fddf79 | 衝突なし | C.EN-*（G-ENV）、C.AC-7 |
| kjob/g5tt-sync 632f365d | 2fddf79 | 衝突なし | D.T-1 の本体差を見るとき（base に定義はある）、D.T-4 の定理側 |
| kjob/g5ba-r16 96e862fe | 2fddf79 | 衝突なし | D.E-1…E-9, D.E-12 |
| kjob/g5cr-r6 f3a29dbb | 2fddf79 | （g5env-r22 / g5tt-sync / g5ba-r16 の祖先） | C.CR-1, C.CR-2, C.RR-* |
| kjob/g5dc-r23 0fcce4e7（先端 74343ad8 は不可） | fe85507 | `lakefile.lean` のみ | 結論、D.D-4, D.D-5, D.D-7（D.D-7 は 74343ad8 が要るが未 review） |
| kjob/g5sm-u23 7af6c7cc | fe85507 | `lakefile.lean` のみ（`Tools/ShippingGen5T2Tie.lean` は自動 merge） | C.SM-* |
| kjob/g5ac-r26 cff12a48 | fe85507 | `lakefile.lean` のみ | C.AC-* |
| kjob/g5cv-r13 44d72eaf → kjob/g5rt-r10 6e6c880f | fe85507 | `lakefile.lean` のみ | C.CV-*, C.RT-* |
| kjob/g5do-r6 063056d6 | fe85507 | `lakefile.lean` のみ | C.DO-*, C.SM-1 |
| kjob/g5rk-r23 221d590a | 2cb123c | `lakefile.lean` のみ | C.RK-2, C.RK-4, C.RK-7, C.RK-8 |
| kjob/g4gate-g3c 59b68658 | 2cb123c | `lakefile.lean` のみ | B.G-* |
| kjob/g4fb-fb25 4519e2fb | 2fddf79 | 衝突なし | B.F-4, B.F-8 |
| kjob/g4par-r23 50d22e3b | 2cb123c | `lakefile.lean` のみ | B.P-* |
| kjob/g2st-r5 2be39bc4 / kjob/g2tc-ptop21 22862066 | 2fddf79 | 衝突なし | A.P-27, A.P-28（監査） |

- Defs の blob は 4 種類: 2cb123c = par/gen2-spec d0ddc50b、fe85507 = par/gen3-combined、2fddf79 = kjob/g2tc-s2 fa84af5d、5d93a18 = 統合木の base（2fddf79 に 6 行の挿入。`git diff` の stat）。**共有定義（Defs）は編集禁止なので、各 branch の Lean は base の Defs の上で build できるかを coder が確かめる。** `TopShips` `Laws` `Start` `Pkgs` の宣言行の見出しは fe85507 と base で同じ（読み取り確認）。`ChildShips` `ShipsRes` は行番号が違う（変更あり）。semantic な互換は計算していない。
- この調査での試行は、(a) base と各 branch の組（上表）、(b) 上の枝同士の全ての組（15 枝、105 組のうち衝突を報告した組は全て `lakefile.lean`）。**連続した merge の列は試していない。**

**統合の順序と手順（提案。coder が行う。この計画は何も merge しない）。**
1. T1 計画 §11.5 の統合木（base f514d08d、提案名 `kjob/t1-ledger-int`）を **共用する**。T1 の統合 G1（kjob/g3aw-a24 8fff703c）・G2（`Tools/ShippingGen2StepLift.lean`）が先に入っていてよい。ここでは触れない。
2. **G-ENV**: `git merge kjob/g5env-r22`（b42ce414）。衝突は出ない見込み（試行）。`kjob lake build Tools.ShippingGen5EnvFrame3` を 1 つだけ実行（ログはソースツリーの外）。失敗したらエラーを記録して止まる（共有定義は直さない）。
3. **G-FG**: `git merge 0fcce4e7`（先端の 74343ad8 ではない）。衝突は `lakefile.lean` のみの見込み。2 つの枝の `lean_lib` の和を残し、他は編集しない。`kjob lake build Tools.ShippingGen5FG`。**g5dc-r23 は Defs が fe85507（gen3-combined）の上で build された枝で、base の Defs（5d93a18）の上での build は未確認。**
4. この台帳（docs のみ）を統合木に持ち込む（Check から参照するため）。
5. 新規 2 ファイル（Tools と Check、`lakefile.lean` に `lean_lib` を追加）を書く。build は Tools → Check の順に 1 つずつ。成功した SHA を NOT BUILT ヘッダにコメントのみの commit で反映する。
6. 型の確認結果（Check の出力）を Issue の note に、統合木の SHA と一緒に書く。**Lean を含む commit を出したら、自分で `review` にしない**（共通ルール 12）。

### 8.7 Check の計画（`Tests/Gen5/FGLedgerPremisesCheck.lean`、新規。`Tools.ShippingGenFGLedgerPremises` と `Tests.Gen3.ExpectedType` を import）

`Tests/Gen3/ExpectedType.lean` は base f514d08d にある（T1 計画 §11.5 が `checkExpected` `checkMutant` `checkAxioms` の所在として示したもの。この計画では中身を読んでいない）。

1. **独立 Expected。** `ExpectedFGLedgerPremisesStmt : Prop` を、承認された §8.3 の型の文から Check の中に別に書く（Tools の定義をコピーしない。両方を生成するマクロを使わない）。`checkExpected ``FGLedgerPremisesStmt ``ExpectedFGLedgerPremisesStmt` で binder ごとに（名前・binder info・型・universe）比較する。Expected の著者は reviewer。coder が両方を書くときは reviewer が両方を読む。
2. **数の assert（見積りではなくカーネルレベルの事実）。**
   - A1: `∀` の telescope を歩いて、外側 `h_` で始まる binder が **4**（`h_C_EN4 h_C_RK1 h_C_RK6 h_C_CV4`）、`EntryWitness` の後ろの内側の含意が **3**（`h_A_P06 h_D_T1 h_D_T4` の順）。carrier の binder が **4**、`L` が **1**。台帳行に対応する仮説 binder は 4 + 3 = **7**。
   - A2: 結論の尾（内側含意の後ろ）が `FG_CONNECT` を展開した本体の尾（O1, O2, O3, `DeclConnect`）と一致し、`EntryWitness` の前件が `FG_CONNECT` のものと一致する（`FG_CONNECT` の定義を unfold して `Expr` で比較する。`ConstValueFunctional CV ∧` の位置も含む）。
   - A3: 台帳の行数。Check に次の 8 つの ID リストをリテラルで持つ: CTX(1)、ANT(2)、TY(7)、UN(69)、T1(16)、PA(10)、AU(2)、XC(3)。**計算する**: (i) 8 リストは互いに素で、和は 110、(ii) 台帳 §7 の索引の行数 146（§7 の範囲だけを数える。§8.2 の表も `| A.P-01 |` の形の行を持つので、全文への `grep -c` は使わない: `sed -n '/^## 7\./,/^## 8\./p' scripts/gen2/PREMISE_LEDGER.md | grep -c '^| [A-D]\.'`）から §4 の除く 36 件（リテラル）を引いた集合 = 110 と一致、(iii) 文に現れる行（CTX+ANT+TY+carrier 4 = **14**）と TY の仮説数（7）が一致する。
   - A4（Lean の外。coder が実行して note に引用）: §7 の索引行数 = 146、§8.2 の表の行数 = 110（`sed -n '/^### 8\.2/,/^### 8\.3/p' scripts/gen2/PREMISE_LEDGER.md | grep -c '^| [A-D]\.'`）。Check のリテラル（146, 36, 110）との不一致で失敗する。
3. **空虚な binder が無い。** 各 `h_` binder の型 `T` について、`T` が `False` でも `True` でもなく、`isDefEq T False` と `isDefEq T True` が失敗すること。**これは文の形の検査で、仮説が共同充足可能であることは示さない**（非空虚性は §8.5 の監査項目）。
4. **mutant（署名／`isDefEq` での棄却。意味的反例ではない）。** `checkMutant` で Expected に対して失敗することを確かめる: (m1) `h_D_T1` から `child? = none` のガードを外す、(m2) `h_A_P06` から `AdmCtx` を外す、(m3) `h_D_T4` の `= some pt.ty.bitWidth` を `= some pt.width` にする、(m4) 結論の `∃ raw, Post b raw` を落とす、(m5) 内側の含意を 1 つ落とす（3 → 2）、(m6) `h_C_EN4` の `Fresh` を別の述語にする、(m7) `TgtRun` を `fun _ => True` にする。棄却は、文のその箇所に Check が感度を持つことしか示さない。
5. **axioms。** `checkAxioms` を `FGLedgerPremisesStmt` と `ExpectedFGLedgerPremisesStmt` に対して実行（`Lean.collectAxioms ⊆ {propext, Classical.choice, Quot.sound}`、`sorryAx` を拒否）。ログ用に `#print axioms`。Tools ファイルと Check に `sorry` `axiom` `native_decide` が無いこと（grep を coder が実行して note に引用）。
6. **Check に入れないと明記する:** この文の証明、registry 69 行のいずれかが偽・導出不能であるという主張、型付けした 7 仮説の共同充足可能性、carrier が実在すること、T1・M3・FG の完成についての主張。

### 8.8 reviewer への質問（それぞれ文の字面が変わる。前提は増えない）

- **Q-F1（T1 の前提との結合）。** T1 の前提を FG 文に入れる方法。推奨: T1 側の段 2 計画が `T1LedgerPremisesStmt` を **`structure T1LedgerPremises … : Prop` と、それを前件に取る文**の 2 つに分けてくれるなら、FG 文は run の内側の仮説に `T1LedgerPremises L (GP (envAt cref w)) (TgtRun …) DataOk HK SK env₀` を 1 つ足せば、T1 の前提を ID 単位で重複なく取り込める。ただし `DataOk`（T1 の placeholder Prop）を FG 側で具体化する必要がある（台帳 C.SM-1 / DG-DATAOF が担当、**今は registry**）。結論: 結合は `DataOk` の具体化が決まるまで書けない。また §8.1 の T1 対応 21 行は FG 側の読みなので、T1 の agent による確認も要る。それまで、この文は T1 の 16 行と T1 の葉 62 行について仮説を持たない。T1L-43 は T1 では未型付け、この文では C.CV-4 として型付けしたので、どちらの文が持つかも決める必要がある（推奨: FG 文が持つ。T1 の registry からは参照に変える）。
- **Q-F2（内側の閉包）。** `P := GP (envAt cref w)`、`Reach := TgtRun P declName` で、ガードは `(origins.getD k .ord).child? = none`（ordinary 呼び出し）。T1 計画の Q2（reviewer 回答 seq 5659: T1Hyp の field の実際の量化とガードに合わせ、最終 Check で照合）と同じ方針の読み。`h_A_P06` は `T1HypND.defines` と同じ量化（`Tools/ShippingGen5T1ND.lean:35-50`、kjob/g5cr-r6@f3a29dbb）。`h_D_T4` のガードは台帳の本文（`hkidW`）に無い（原文は `p` の上で `RealChildA`）ので、reach と `P c = some p` だけ足した。
- **Q-F3（B.P-1 `AllPos θ` と B.P-8 `LegalBinding D θ` を仮説にしない理由）。** (1) `LegalBinding D θ` の `D` が `D` か `D.addModule b` か、台帳が固定していない（`SpecSuccessAllPositive` は `D.addModule b`、`legal_facts` などは `D` と書かれている）。(2) これらをパラメータ route の前件にすると、FG の parametric 側が `LegalBinding` を満たす run に狭まる。成功した特殊化が `LegalBinding` を満たすこと（`specializeDesign_ok_legal`）は承認済みだが、FG の run からこれを受け取る経路は台帳で「見つからなかった」。**前件にして採用すれば範囲の縮小（禁止）にあたり得るので、仮説にせず registry に置いた**。(3) B.P-8 ⟹ B.P-1（`legalBinding_allPos`）なので、両方を仮説にすると重複する。reviewer に、前件にする形（義務として並べる）にしてよいか確認したい。
- **Q-F4（ブロックの粒度）。** 台帳の 1 ブロックは複数 binder を束ねる（§0）。型付けは **ブロック単位で全 binder が型付けできたときだけ**型付け区分にした（例: C.EN-6 は `hall` だけが閉じた Prop なので registry）。ブロックを binder 単位に割ると 110 が変わる。この計画は割らない。binder 単位の表が要るなら別表にする。B.P-4 の B1 は台帳に閉じた型があるが、B2-B4 は文章のみなので、ブロック全体を registry（コード B）にした。
- **Q-F5（carrier の扱い）。** `ReflectsAll` `Post` `GP` `CV` を全称 binder にすると、文は carrier ごとの条件付き schema になる（`fgCond_trivial`）。carrier を固定した値（`GP := genP env₀`、`Post := PostEntry`〈default route〉など）で書き直す案もあるが、`genP` は定義が見つからず、`PostEntry` は default route のみ、`ConstValue` は未記述で、どれも今は書けない。carrier が固定されたら、registry の K / R 行が「carrier に対する仮説」に変わる。この遷移を行う unit の freeze には、台帳 §5 の形で消える行・増える行を数える。

### 8.9 前提差分と 4 段

- この計画（と書く Lean の文）の前提差分: **解消 0 / 追加 0。** 文の 7 仮説・14 行は全て既存の台帳行で、この計画は新しい前提を足していない。T1 区分 16 行と T1 台帳の行との対応は参照であって、解消ではない。
- 進捗の 4 段（設計承認 / 条件付き部品 / 前提解消 / 最終受理）: この計画は **設計（段 1）** の記録。どの行も、条件付き部品、前提解消、最終受理に進めない。
- 次（承認後）: coder が §8.6 の G-ENV, G-FG を行い、§8.3 と §8.7 の 2 ファイルを書いて build し、clean build の証跡を付ける。registry 69 行の型付けは §8.4 の各 freeze の owner の仕事（それぞれの freeze に「台帳の前提がいくつ消え、いくつ増えるか」を必須とする）。台帳 §5 の 3 本の流れ（流れ 1: runReads→ClosingRun、T1 の流れ A・B）のうち、**この文に入る 7 仮説はどの流れの「消える予定の ID」でもない**。流れ 1 の C.RK-5（PA）・D.T-8（PA）・D.T-9（PA）・D.T-5（除かれた行）は文に仮説として現れない。流れ 1 の最初の単位の freeze は、この計画とは別。

## 9. 段 2 承認後の確認（agent `fgreg1`、branch `kjob/fgreg1`、base `kjob/fgstmt1` 13c7d5a3。文書のみ。Lean・build なし）

reviewer が段 2 承認時（seq 5716, 5755）に残した確認を行った記録。**この節は前提の供給ではない。この節による台帳の前提差分は 解消 0 / 追加 0。** 流れ 1 の解消（110 表の 3 行 + 除外済みの指し示し行 D.T-5 の注記、§9.1）は別の単位の成果で、reviewer 承認済みのものを反映しただけである。

### 9.1 前提解消の反映（FG 側）

| 台帳ID | 現在の状態 | 根拠 |
|---|---|---|
| C.RK-5 | **前提解消（e6d8e55b、reviewer 承認）** | U2 `readMachine_agrees_of_run`（`runReads_of_run` が R を置換）。kjob/flow1-b e6d8e55b |
| D.T-8 | **前提解消（e6d8e55b、reviewer 承認）** | U1 `callTie_of_run_{one_ex,group_kidW}`（run 側の前提が `hsh` を置換）。kjob/flow1-b 29701f80 |
| D.T-9 | **前提解消（e6d8e55b、reviewer 承認）** | 同上 U1 |
| D.T-5 | 指し示し行（110 表に含まれない。現在値に数えない） | 同上 U1 の解消対象 ID に挙がるが、§4 で ClosingRun の行へ統合され、110 の表（§8.2）には現れない行（下の注意） |

- 承認記録: `managerctl plan history sparkle-gen5-dg-closingrun` seq 5756（approved、前提差分 FG -4 / +0、T1 0、「台帳 FG 110→106」。これは承認時点の記録の引用で、現在値は 107（§2 の定義）。-4 のうち 110 表の行は 3）。clean build `f1v-e6d8e55b` exit 0、dirty=false、842 jobs、sorry 0、標準 axioms のみ。Check 集計は Tie: TYPE 2 / MUTANT 38 + NEGATIVE 3 / CONTROL 5 / REACH 2 / AXIOMS 2、Reads: TYPE 1 / MUTANT 23 + NEGATIVE 2 / CONTROL 4 / REACH 1 / AXIOMS 1（Issue の note による。この agent は再 build していない）。mutant は signature / defeq での棄却であって意味的反例ではない。
- **残る前提（承認 note の記録）**: `hord` / `hGen` / `hIH` / `hKI`、非空虚性、depth0 `stop`、`hk` / `hHead` / `h0s`、DG-ENV、served。**条件付き部品であり、ClosingRun や FG の完了ではない。**
- **現在値と版の履歴**: 現在値 **FG 107**（定義は §2）。段 1・段 2 の基準件数 **146 / 110** は書き換えていない（§2）。
- **数え方（確定）**: 流れ 1 の承認 note は「110 → 106」で 4 ID（C.RK-5、D.T-5、D.T-8、D.T-9）を引いたが、元の 110 行表に含まれる解消印の行は C.RK-5、D.T-8、D.T-9 の **3 行**で、D.T-5 は §4 で除かれた 36 行の 1 つ（ClosingRun の指し示し行）である。よって現在値は 110 − 3 = **107**（定義は §2）。106 を維持する根拠になる 110 表内の第 4 行は見つからなかった。§8.2 / §7 の行数（110 / 146）と Check のリテラルは変えていない。§7 と §8.2 の C.RK-5、D.T-8、D.T-9 の行には「前提解消」の印、D.T-5（§7 のみ）には指し示し行の注記を置いた。
- **T1 側（この台帳では数えない）**: T1L-20 / T1L-22 / T1L-24 は kjob/flowa-b 82cb67a6（U18、reviewer 承認 seq 5748、clean build `fav-82cb67a6` exit 0）で前提解消（T1 62 → 59、U18 後の履歴値）。その後 T1L-28 が U-B1 83820d32 で解消し、現行 T1 は 58。T1 台帳の話なので、FG 台帳の数には入れない。FG 台帳に関係するのは §9.3 の A.P-07 の行の注記だけ。

### 9.2 registry 69 行: 支払い予定の Issue（owner）と型の根拠

読み方:
- 「型の区分」は §8.4 のコード（C 閉包未固定 48、R 6、D 4、N 3、B 3、K 3、U 2。上の表の行を数えると一致した）。
- 「支払い予定の Issue」は**台帳（部分ファイル）と各 Issue の履歴に書いてある**もの。履歴上決まっていない行は **未割当**と書いた。「候補・条件付き」は、Issue 名がタイトルまたは設計文書にあるだけで、履歴本文に支払いの記録が見つからなかったもの。
- 「型の根拠」は、**Lean 名 + branch@SHA :path**（部分ファイルが `git show` の原文を貼っているもの）、**文書の型**（freeze / 設計文のみ）、**名前のみ**、**型が見つからなかった**に分けた。「見つからなかった」はこの調査で辿った範囲の話で、存在しえないという意味ではない。
- Issue 名は台帳の短縮名。`sparkle-gen5-<名>` として `managerctl show` で確認できたもの: dg-env / dg-acc / dg-sem / dg-dataof / dg-readertrace / dg-closingrun / dg-audit（todo）、dg-cover（approved）、dg-readkinds（doing）、dg-runreads（done）。**dg-wfcover、dg-pkgassign、dg-declconnect は同名では `show` できなかった**（dg-cover の題名に WFCOVER、dg-acc の題名に PKGASSIGN を含む。dg-declconnect に当たる題名は decl-bridge）。台帳の記載のまま書き、実在する Issue への読み替えは決めていない。
- この表の branch@SHA は部分ファイルが引くもので、本確認で `git cat-file -e` により path の存在を確かめた（kjob/g4fb-fb25、g5ac-r26、g5dc-r23、g5env-r22、g5cv-r13、g5rt-r10、g5sm-u23、g5ba-r16、g4par-r21/r23、g4gate-g3c、g5rk-r23、g5do-r6）。**行番号は部分ファイルの記載で、本確認では読み直していないものがある。**

| 台帳ID | 型の区分(§8.4) | 支払い予定の Issue(owner。台帳と履歴の記載) | 割当 | 型の根拠 | 根拠の種類 |
|---|---|---|---|---|---|
| A.P-05 | K | 未割当(GENERAL_SPEC §1.1 は M4 で固定と書く。Issue 割当なし。parametric route の Post 採用は未承認 seq 4318) | 未割当 | GEN2_DEFS.lean.txt:305-306,324-325,337-338 の式(par/gen2-spec)。Lean 定義は読んでいない | 文書の型 |
| A.P-18 | C | G3GEN_CALL_PLAN §4 は「M5」。Issue 名はタイトル上 gencall-proof / t2-tie / dgen の候補(履歴本文は未読) | 候補・条件付きの記載 | HPointAt: Tools/ShippingQuadHPoint.lean:14, ShippingQuadCalls.lean:223 @par/gen2-spec d0ddc50b。HPointG: Tools/ShippingGen2CallField.lean:75-87 @par/gen2-spec 3b702f15 | Lean(名と branch@SHA) |
| B.G-1 | R | 未割当 | 未割当 | EntryDefines: Tools/ShippingInlineSoundness.lean:48 @d0ddc50b。gate 版 binder: kjob/g4gate-g3c 59b68658 | Lean(名と branch@SHA) |
| B.G-3 | R | 未割当 | 未割当 | GateLeaf.old: Tools/ShippingGen4GateIface.lean @kjob/g4gate-g3c 59b68658 | Lean(名と branch@SHA) |
| B.G-4 | R | 未割当 | 未割当 | GateLeaf.peel: 同上 | Lean(名と branch@SHA) |
| B.G-5 | R | 未割当 | 未割当 | GateLeaf.he: 同上(`e.WF kb kv vw`) | Lean(名と branch@SHA) |
| B.G-6 | R | 未割当 | 未割当 | GateLeaf.hb/hv: 同上 | Lean(名と branch@SHA) |
| B.G-7 | C | 未割当(seq 3500「幅1は調査継続」) | 未割当 | hw1: Tools/ShippingGen4GateOutTy.lean @kjob/g4gate-g3c 59b68658 | Lean(名と branch@SHA) |
| B.G-9 | D | 未割当(assembler は sparkle-gen4-fg-assembly だがその履歴に記述なし) | 未割当 | Q/hQ の型: IfaceMap, Tools/ShippingGen4Iface.lean @kjob/g4gate-g3c 59b68658。供給側(route table assembler)は Lean なし | Lean(名と branch@SHA) |
| B.F-4 | C | 未割当(seq 5568: 台帳で割当時に再開) | 未割当 | hS: Tools/ShippingGen4FbFragRun.lean @kjob/g4fb-fb25 4519e2fb | Lean(名と branch@SHA) |
| B.F-8 | C | 未割当 | 未割当 | ChildRunN: Tools/ShippingGen4FbDzRun.lean:17,:75 @kjob/g4fb-fb25 4519e2fb(PostReady は Tools/ShippingEntrySoundness.lean:636) | Lean(名と branch@SHA) |
| B.P-1 | C | 未割当(seq 3648/5358: B1-B3/T/FG 未供給) | 未割当 | AllPos: Tools/ShippingGen4ParamLayerA.lean 約:44 @kjob/g4par-r21 0ebbddc0。legalBinding_allPos は kjob/g4par-r23 50d22e3b | Lean(名と branch@SHA) |
| B.P-2 | C | 未割当 | 未割当 | Bound/PosDim/NonNegDim/SliceOK: Tools/ShippingGen4ParamLayerA.lean @0ebbddc0 | Lean(名と branch@SHA) |
| B.P-3 | C | 未割当 | 未割当 | ExprOK/TyPos/TyBound: SpecExpr/SpecType(Tools/ShippingGen4ParamBridge*.lean)@0ebbddc0 | Lean(名と branch@SHA) |
| B.P-4 | B | 未割当(決定資料 §5「決定が無ければ B1-B3 は未供給」) | 未割当 | B1 は閉じた型が台帳にある。B2-B4 は文章のみ。requirePositive_eq は Tools/ShippingGen4ParamBridgeLegal.lean:44 @kjob/g4par-r23(B4 の一部、解消済みの差分) | 文書の型 |
| B.P-5 | U | 未割当(D3 のユーザー判断待ち) | 未割当 | SpecSuccessAllPositive: Tools/ShippingGen4ParamIface.lean:106 @kjob/g4par-r21 0ebbddc0 | Lean(名と branch@SHA) |
| B.P-7 | B | 未割当 | 未割当 | body_symbolic_keeps 等: Tools/ShippingGen4ParamKeeps.lean(旧 RefLaws 上)。Start→Out0 の補題は PARAMETRIC_FREEZE の F1 行に「見つからなかった」 | Lean(名と branch@SHA) |
| B.P-8 | C | 未割当 | 未割当 | LegalBinding: legal_facts 等 Tools/ShippingGen4ParamBridgeLegal.lean:52,:79,:84 @kjob/g4par-r23 50d22e3b。D か D.addModule b かは固定されていない | Lean(名と branch@SHA) |
| C.RR-2 | B | FG の仮説そのもの(支払い先なし。履歴・台帳に割当の記載なし) | 未割当 | RunsTo(synthesizeCombinationalCore X [] false) の文は部分ファイルにあるが、entry run → core run の橋の命題は見つからなかった | 型が見つからなかった |
| C.CR-2 | D | DG-COVER + DG-WFCOVER + genP_generated(C6) + DG-ENV(R6 freeze §2 / DGEN_FREEZE) | Issue 名あり | GeneratedAt: par/gen5-t2 c398021c scripts/gen5/DGEN_FREEZE.md(設計文のみ)。RunReadsAt: par/gen2-spec 88771739 RunReads.lean:42。GeneratedAtK: kjob/g5ac-r26 cff12a48 Tools/ShippingGen5AccGenP.lean:33 | 文書の型 |
| C.EN-1 | C | dg-env(履歴 5467/5476: 「L′/QuietStrength 未供給」) | Issue 名あり | QuietStrength: kjob/g5env-r22 b6b3206b Tools/ShippingGen5EnvQ.lean:38 | Lean(名と branch@SHA) |
| C.EN-2 | C | dg-env | Issue 名あり | AdmDown: Tools/ShippingGen5EnvQ.lean:42 @kjob/g5env-r22 b6b3206b | Lean(名と branch@SHA) |
| C.EN-3 | C | dg-env(5476: 実 start cache 未供給) | Issue 名あり | CacheInvN: Tools/ShippingGen5EnvCacheC.lean:25, RealChildN: EnvCache.lean:26 @kjob/g5env-r22 | Lean(名と branch@SHA) |
| C.EN-5 | C | dg-env(5476: ¬DRow 未供給) | Issue 名あり | DRow: Tools/ShippingGen5EnvFrame3.lean:35 @kjob/g5env-r22 | Lean(名と branch@SHA) |
| C.EN-6 | C | dg-env(C0 は履歴の全 note で未供給) | Issue 名あり | hall 等: Tools/ShippingGen5Env*.lean @kjob/g5env-r22(ブロック全体は閉包未固定) | Lean(名と branch@SHA) |
| C.EN-7 | C | 未割当(U9 freeze §0: G-REACH / DG-READKINDS が持つ行は名前のみ) | 未割当 | hentry の Lean 文は C_M5dg.md EN-7 に貼ってある。RealChildN: Tools/ShippingGen5EnvCache.lean:26 @kjob/g5env-r22 b42ce414(hentry 自身の定義行は読み直していない) | Lean(名と branch@SHA) |
| C.EN-8 | U | 未割当 | 未割当 | hn: mctx.canUnfold? = none(kjob/g5env-r22 RealChildN の field)。採否はユーザー判断 | Lean(名と branch@SHA) |
| C.RK-2 | C | 未割当 | 未割当 | EnvFrame: Tools/ShippingEnvSnapshot.lean:43(base)。coreHead X は Tools.ShippingEntryReadsLinked | Lean(名と branch@SHA) |
| C.RK-4 | C | dg-runreads / dg-closingrun(run existence。U13 freeze 表) | Issue 名あり | readMachine: Tools/ShippingMachineCommand.lean:440 の run。RunsTo は Tools.ShippingEntrySoundness | Lean(名と branch@SHA) |
| C.RK-7 | D | 未割当(RK-1/RK-2 と同じ) | 未割当 | U14 の hM/hC: kjob/g5rk-r23 221d590a の freeze 文。Lean は未実装 | 文書の型 |
| C.RK-8 | C | DATAOF freeze: C-QWIT は「供給元未発見」。割当なし | 未割当 | readN_quote: Tools/ShippingGen5ReadKinds.lean:401, readTot_of_quote_body: :702, RootFacts: :725 @kjob/g5rk-r23 221d590a | Lean(名と branch@SHA) |
| C.DO-2 | N | dg-cover / dg-readkinds(DG_DATAOF_FREEZE 本文) | Issue 名あり | Rdr / s = sp の Lean 命題は見つからなかった(DATAOF freeze §11.3 は定理なしと記す) | 型が見つからなかった |
| C.DO-3 | N | S-OK は dg-cover / dg-wfcover。他は記載なし | 候補・条件付きの記載 | row 6a, C-CMP, C-QWIT, S-OK, S-COV-FLOAT: DG_DATAOF_FREEZE.md(kjob/g5do-r6 063056d6)に名前のみ | 名前のみ |
| C.SM-1 | C | dg-dataof(5492 note)。dataOfAt_sound は別 branch で SEM から import 不可 | Issue 名あり | DataOfSound: Tools/ShippingGen5SemGenData.lean:18 @kjob/g5sm-u23 7af6c7cc(未 review) | Lean(名と branch@SHA) |
| C.SM-2 | C | dg-acc A12(ordCallees₀ + ordCallees₀_mem、5342 approved)。SEM 側への接続は別 branch | Issue 名あり | ordCallees: SemCall.lean:17。ordCallees₀_mem: Tools/ShippingGen5AccOrdCallees.lean:21 @kjob/g5ac-r26 cff12a48 | Lean(名と branch@SHA) |
| C.SM-3 | C | dg-acc(genS が hunf/hinv を満たす構成。5492) | Issue 名あり | factsOf_all_of_genDataInv 等 @kjob/g5sm-u23。genS_unfold: Tools/ShippingGen5Acc.lean:121 @kjob/g5ac-r26 は候補 | Lean(名と branch@SHA) |
| C.SM-4 | C | dg-acc(AC-8) | Issue 名あり | factsOf_all_of_acc_unfold @kjob/g5sm-u23。hacc_of_top_runs: Tools/ShippingGen5AccReads.lean:137 @kjob/g5ac-r26 | Lean(名と branch@SHA) |
| C.SM-6 | C | dg-cover(rowC_of_reader / rowA3_of_inv)/ dg-wfcover(5492: GenWF は DG-COVER) | Issue 名あり | GenWF/GenData: Tools/ShippingGen5SemGenData.lean:27, SemGen.lean:61 @kjob/g5sm-u23 | Lean(名と branch@SHA) |
| C.AC-2 | C | dg-sem(5456: 実 GenData/genSem/hev 未供給) | Issue 名あり | GDEvidence: Tools/ShippingGen5AccGenDataEv.lean:22 @kjob/g5ac-r26 cff12a48 | Lean(名と branch@SHA) |
| C.AC-3 | C | dg-sem(実 genSem から。接続は別 branch) | Issue 名あり | Tools/ShippingGen5AccMkKit.lean @kjob/g5ac-r26 cff12a48 | Lean(名と branch@SHA) |
| C.AC-4 | C | dg-cover / dg-dataof(A13: genData₀ が成功する条件) | Issue 名あり | ReachCover: Tools/ShippingGen5Acc.lean:206 @kjob/g5ac-r26 cff12a48 | Lean(名と branch@SHA) |
| C.AC-5 | C | 未割当 | 未割当 | GatesNoneAt: Tools/ShippingGen5AccRoute.lean:34 @kjob/g5ac-r26 cff12a48 | Lean(名と branch@SHA) |
| C.AC-7 | C | dg-env | Issue 名あり | ReadsSupplyAt / ChainReadsAt: Tools/ShippingGen5AccReads.lean @kjob/g5ac-r26 cff12a48 | Lean(名と branch@SHA) |
| C.AC-9 | C | dg-dataof(DataSound / dataOfAt_sound) | Issue 名あり | RunDataLink / DataOfShape: Tools/ShippingGen5AccServed.lean:64-70 @kjob/g5ac-r26 cff12a48 | Lean(名と branch@SHA) |
| C.CV-1 | C | 未割当(履歴 4246 は R-trace/R-in/R-nl/R-dom を dg-readertrace としたが、hq 自身の担当は見つからなかった) | 未割当 | LetQuoteEq: Tools/ShippingGen5Cover3.lean:693 @kjob/g5cv-r13 44d72eaf | Lean(名と branch@SHA) |
| C.CV-2 | C | dg-readertrace(4246 note) | Issue 名あり | LetsNoLoose: Tools/ShippingGen5Cover3.lean:699 @kjob/g5cv-r13 44d72eaf | Lean(名と branch@SHA) |
| C.CV-3 | C | dg-readertrace | Issue 名あり | FullInv: Tools/ShippingGen5Cover3.lean:316 @kjob/g5cv-r13 44d72eaf | Lean(名と branch@SHA) |
| C.CV-5 | C | dg-dataof(4246: row 6b / nDecl) | Issue 名あり | shapeAgree_of_* の binder: Tools/ShippingGen5Cover5.lean @kjob/g5cv-r13 44d72eaf | Lean(名と branch@SHA) |
| C.CV-6 | N | hcb は src-argw(4246 の B3)、R-in/R-dom/R-nl は dg-readertrace、SigTyPh は dg-env | Issue 名あり | hcb: rowB1_of_inv(Cover3)。R-in/R-dom は ShapeInputs 等の名前のみ(REV7) | 名前のみ |
| C.RT-1 | C | dg-readertrace(自身) | Issue 名あり | TraceGood: Tools/ShippingGen5ReaderTraceCtl.lean:94-99 @kjob/g5rt-r10 6e6c880f | Lean(名と branch@SHA) |
| C.RT-2 | C | dg-readertrace(REV7: ShapeInputs) | Issue 名あり | TracePre/PhPre: ReaderTraceCtl.lean:47-70 @kjob/g5rt-r10 6e6c880f | Lean(名と branch@SHA) |
| C.RT-3 | C | 未割当(5560 に hT/成功 run とあるのみ) | 未割当 | chainStep/convStep の hv: ReaderTraceChain/Arms.lean @kjob/g5rt-r10 6e6c880f | Lean(名と branch@SHA) |
| C.RT-4 | C | dg-readertrace(REV4 §0 が未供給 arm を列挙) | Issue 名あり | readF_traceGood_of_step: Tools/ShippingGen5ReaderTraceArms.lean:195 @kjob/g5rt-r10 6e6c880f | Lean(名と branch@SHA) |
| C.DG-1 | D | (i) dg-cover (ii) dg-wfcover (iii) dg-pkgassign(DGEN_FREEZE の inhabitation argument) | Issue 名あり | GeneratedAt: par/gen5-t2 c398021c DGEN_FREEZE.md(設計文のみ) | 文書の型 |
| D.D-1 | R | boundary-audit §4 の表は supplier を「M4/M5 G3」とし state OPEN。割当の Issue 名は履歴に無い | 未割当 | 型は Laws mref cref → Name → List (String × Nat) → Prop(Tools/ShippingGen5FG.lean:30 @kjob/g5dc-r23 0fcce4e7)。定義は見つからなかった | 型が見つからなかった |
| D.D-3 | K | package-coverage(todo、設計なし)/ dg-acc の genP_pkg(条件付き) | 候補・条件付きの記載 | 型 Environment → Pkgs ι dom(Tools/ShippingGen5FG.lean:42 @0fcce4e7)。genP の定義は見つからなかった | Lean(名と branch@SHA) |
| D.D-4 | K | decl-bridge(todo)。DC-FORM / DC-SUPPLY は t2cover seq 2721 の study unit | 候補・条件付きの記載 | ConstValueRel: Tools/ShippingGen5DeclConnect.lean:267 @kjob/g5dc-r23 0fcce4e7。ConstValue の定義は未記述 | Lean(名と branch@SHA) |
| D.D-5 | C | decl-bridge(設計のみ)/ dg-sem / dg-dataof / dg-acc | 候補・条件付きの記載 | declConnect_of_rows, dcGen_of_rows: Tools/ShippingGen5DeclConnect*.lean @kjob/g5dc-r23 0fcce4e7 | Lean(名と branch@SHA) |
| D.D-7 | C | dc-connect の U-CORENR(74343ad8、freeze 28f2627c は seq 5327 承認、実装は未 review) | Issue 名あり | NoRawBelow: Tools/ShippingGen5DCEntryR.lean:14 @kjob/g5dc-r23。実 core run との接続 noRawBelow_of_coreRun は 74343ad8(未 review) | Lean(名と branch@SHA) |
| D.E-1 | C | MemTagsNamed は U4(下の D.E-6 に帰着)。割当の Issue 名は boundary-audit | Issue 名あり | hmemSame_of_memTagsNamed: Tools/ShippingGen5NameKids2.lean:71 @kjob/g5ba-r16 96e862fe | Lean(名と branch@SHA) |
| D.E-2 | C | boundary-audit(E-6〜E-9 に帰着) | Issue 名あり | hself_of_rank: NameKids2.lean:80, hself_all_reached: NameKids3.lean:99 @kjob/g5ba-r16 96e862fe | Lean(名と branch@SHA) |
| D.E-3 | C | boundary-audit。文書は synthesis run の事実とし供給元は不明 | Issue 名あり | hn_kidNameAt: NameKids2.lean:58 @kjob/g5ba-r16。ordinary kid の y.1.name = ofDecl c(B7)は見つからなかった | Lean(名と branch@SHA) |
| D.E-4 | C | boundary-audit。B5 はユーザー判断の可能性あり | Issue 名あり | BOUNDARY_AUDIT_FREEZE.md §1.2 の B3/B4/B5。machineClosesAtA_of_memKids'(CallsMemPinned.lean:330)の binder | 文書の型 |
| D.E-5 | C | U4 / U5 / U6 が各 hmem/hg/hin(boundary-audit) | Issue 名あり | NameKids3.lean(GraphAgrees/ReachSpans/InClass)@kjob/g5ba-r16 96e862fe | Lean(名と branch@SHA) |
| D.E-6 | C | reader-bridge(machineDefines_of_readsAll、partial) | Issue 名あり | hmem_of_machineShapeF: NameKids4.lean:33 @kjob/g5ba-r16 96e862fe | Lean(名と branch@SHA) |
| D.E-7 | C | 未割当(production の ds/Reach/S が未供給) | 未割当 | graphAgrees_of_firstOcc: NameKids5.lean:20 @kjob/g5ba-r16 96e862fe | Lean(名と branch@SHA) |
| D.E-8 | C | 未割当 | 未割当 | inClass_graphOf: NameKids6.lean:18 @kjob/g5ba-r16 96e862fe | Lean(名と branch@SHA) |
| D.E-9 | C | U8(graphAgrees_of_mem)は freeze のみ承認。Lean なし | 候補・条件付きの記載 | reachClosed_ordPath: NameKids7.lean:20 @kjob/g5ba-r16 96e862fe | Lean(名と branch@SHA) |
| D.E-12 | C | 未割当 | 未割当 | writer_prints_endpoint_artifact: Tools/ShippingDesignWriterRun.lean:119(G7-a) | Lean(名と branch@SHA) |

**数えた値（上の表の列を数えたもの。推測なし）**

| 項目 | 行数 |
|---|---|
| 合計 | 69 |
| 割当: Issue 名あり / 候補・条件付き / **未割当** | 33 / 6 / **30** |
| 型の根拠: Lean（名と branch@SHA） / 文書の型 / 名前のみ / 型が見つからなかった | 58 / 6 / 2 / 3 |

- 未割当 30 行が、`ReflectsAll` の構成要素（B.G-*）、parametric（B.P-*）、fallback（B.F-*）、boundary-audit の一部（D.E-7, E-8, E-12）、DG-ENV の一部（C.EN-7, EN-8）などに及ぶ。**履歴上の割当を持たない Issue**（gen5-gencall-proof / package-coverage / reader-bridge / decl-bridge / boundary-audit / gen4-fg-assembly）の存在は §2 のとおり。
- **「型の根拠」が Lean でも、閉包（どの reach・run・carrier の上の全称か）が固定されていない行（C 48 行）は型付けできていない**（§8.4）。この表は owner と型の出どころを揃えただけで、型付けの前進ではない。
- 本確認で読み直したのは部分ファイルの記載と、branch 上の path の存在、`hacc_of_top_runs` など §9.4 の補題の署名のみ。上の branch の Lean を build し直してはいない。

### 9.3 T1 crosswalk（Q-F1 の 16 行）: 1 行ずつの確認。合算しない

比較元: T1 台帳 `scripts/gen3/PREMISE_LEDGER.md` @ **kjob/t1stmt2 51ebec20**（`git show` で全文を読んだ。T1 の数は 71 行 / リーフ 62 = TRUSTED 1 + 入力 2 + 証明義務 56 + 監査 3。型付き 27 / registry 29、§11.1。その後 T1L-20 / 22 / 24 が 82cb67a6 で前提解消して T1 59（履歴値）、さらに T1L-28 が U-B1 83820d32（sparkle-gen3-data-supply）で解消して現行 T1 58）。

確認の中身: (a) FG 行の別名・本文に書かれた名前（G-MEMCALLS、G-DATA-CALL、LiftShips、hrow / hord、MemParentDataOk、ExtInS、OneOutWidth など）が T1 台帳 §3 の表の該当行の「別名」「前提」欄・§4・§6 に書かれているか、(b) 役割（何を述べる前提か）が同じか。**「一致」は名前と役割が T1 台帳の記載で一致したという意味で、Lean の型の同値は確認していない。** T1 側の agent の確認は受けていない。

| FG の行（§8.2 の区分 T1） | FG 側の内容 | T1 台帳の ID（§3） | T1 側の状態（§11.1、51ebec20） | 対応の確認 |
|---|---|---|---|---|
| A.P-07（merged C.AC-6） | `MachineTaken` / `MachineClosesAtA`（G-CLOSES） | T1L-08（親）→ 20-25、21 | 21: 型付き `h_T1L_21`。23, 25: registry。**20, 22, 24: 前提解消（82cb67a6、T1 62→59）**。`MachineTaken` 自体は T1 §6 で「T1Hyp.defines / closes から導出」で行ではない | 親にのみ対応。FG の `MachineTaken` の読みは T1 §6 と整合。リーフ単位の一致は T1 台帳が示さない。**T1L-20 / 22 / 24 の解消は T1 台帳の話で、FG の数は動かさない** |
| A.P-08 | package の存在・生成事実（G3-GEN / G3-DECL）、`T1Hyp.pkg` | T1L-06 | 型付き `h_T1L_06`。支払い先は FG 台帳（T1 §8） | **一致**（T1L-06 の記載が `T1Hyp.pkg` / G3-GEN） |
| A.P-09 | `DataOkB` の行と callDec 系 `hok` / `hco` / `hslots` | T1L-32、39、40 | 32: registry（理由 L）。39, 40: 型付き | **一致**（T1L-39 = `callsOk`、T1L-40 = `ss.length = slots.length`、T1L-32 = `DataOkB p = true`）。FG ledger も「A.P-09 は特に読みが入る」と書いていた（§8.1）。`outTy` / `outHead` に対応する T1 行は見つけていない |
| A.P-10 | `MemParentDataOk` | T1L-12 | 型付き | **一致**（T1L-12 の記載が `MemParentDataOk q ∧ ExtInS q`）。T1 は T1L-13 を T1L-12 に統合（同じ文の別 binder） |
| A.P-11 | `LeafDataOk` | T1L-11 | 型付き | **一致**（`LeafDataOk q ∧ ExtInS q`） |
| A.P-12 | `ExtInS` | T1L-11、12（`ExtInS` の連言） | 型付き | **一致**（T1 側では独立の行ではなく T1L-11 / 12 の連言）。FG 側 A.P-10 / A.P-11 / A.P-12 は T1 では 2 行に束ねられる（多対一） |
| A.P-14 | case 前提（insts / instFields / slots / Nonempty ι / `StepCaseOK`） | T1L-15..18、T1L-03（親） | 15-18: registry（`sparkle-gen2-step` 型待ち）。T1L-41 は非 Prop 入力 | **部分一致**。T1L-15..18 は未被覆 case の `TopShips` で、`StepCaseOK` 側の case 前提は T1L-03 の範囲。case 前提の各項を T1 のどの行が持つかは T1 台帳が示さない |
| A.P-15 | `hrst`（rst が入力でない）、`hnoRst` / `hnoClk` | T1L-17（補集合） | registry（slotless one-output with `rst` an input、C5S） | **補集合として対応**。FG の `hrst` は T1L-17 の否定側（`StepStmtCases` の case 制限）で、同じ前提ではない。T1 側が数えるのは T1L-17（case S の `TopShips`）のみ |
| A.P-16（merged D.T-11） | `MemDec`（G-MEMCALLS）、`hG_MEMCALLS` | T1L-26 | 型付き `h_T1L_26` | **一致**（T1L-26 の記載が `MemDec` supply / G-MEMCALLS、「`hG_MEMCALLS` of `Tools/ShippingGen5T2Tie.lean` と同じ前提」と T1 §8 にもある） |
| A.P-19（merged D.T-10） | `callArgsOkAt` / arity（G-DATA-CALL） | T1L-27 | registry（理由 D、`PortTie` 未設計） | **一致**（T1L-27 = G-DATA-CALL の run-local assembly）。T1L-28（`hPW`）は別行 |
| A.P-22 | G-SERVED の trace（`ServedP (ShipsRes L P)`） | FG 台帳の読み: T1L-03（親、`hStep`）。T1 台帳の別の読み: §6 の `ServedShips0Stmt` → `hrow`（T1L-04） | T1L-03 はリーフなし。T1L-04 は型付き | **不一致の可能性**。FG 台帳は T1L-03 としたが、T1 §6 は served 系を `hrow` に置換したと書く。どちらが対応するかは未確定（reviewer / T1 側の確認事項） |
| A.P-23 | `LiftShips`（G-LIFT） | T1L-19 | 型付き `h_T1L_19`（`Tools/ShippingGen2StepLift.lean` の 1 ファイル） | **一致**（`LiftShips L P`）。`LiftShipsInstFree` は別の弱い文で、T1 側でも「instance-free restriction only」 |
| A.P-24（merged B.F-1, C.CR-3, C.AC-8） | `ChildKeepsInv`（G-KEEP-CHILD）、`hIH` / `hKI` の一部 | **対応する行なし** | T1 §6: `KeepChildStmt` は `keepChild_proved`（@9b79bf3a）で行でなくなった。`LimitStmt` も `limitStmt_proved` | **T1 側に行がない**。FG 台帳は「T1 側で解消済み」と読んで T1 区分に置いた。FG の `hIH` / `hKI`（C.CR-3 の `AccIHAt` / `AccChildKeeps`）がこの解消でカバーされるかは確認していない。**この 4 行（統合後は 1 行）を FG の数に残すかは reviewer の確認事項** |
| A.P-25（merged D.T-3） | `hW : OneOutWidth P p k`（G-ONEOUT-WID） | T1L-14 | 型付き `h_T1L_14` | **一致** |
| A.P-26 | `hnomem`（名前半分）と `hord`（起源半分） | T1L-04（`hrow`、`hord` に使う） | 型付き `h_T1L_04` | **一致（`hord` の部分）**。名前半分は O-copies で除去済み（FG 側の記載）。C.CR-1 と同じ T1L-04 に当たる（下） |
| C.CR-1 | `hrow` / `hord`（`closingRun0_of_run`） | T1L-04 | 型付き `h_T1L_04` | **一致**。**A.P-26 と C.CR-1 の 2 行が T1 の 1 行（T1L-04）に当たる**（多対一）。流れ 1（e6d8e55b）は `hord` を前提のまま残している（§9.1） |

**集計（上の表を数えた値）**: 16 行のうち、名前と役割が T1 台帳の記載で一致したもの **11**（A.P-08, 09, 10, 11, 12, 16, 19, 23, 25, 26, C.CR-1）、親行・補集合にのみ対応し、リーフ単位は未特定のもの **4**（A.P-07, 14, 15, 22。うち A.P-22 は別の読みが T1 §6 にある）、**T1 側に行がないもの 1**（A.P-24）。多対一は A.P-10 / A.P-11 / A.P-12 → T1L-11、12（3 行が 2 行）、A.P-26 / C.CR-1 → T1L-04（2 行が 1 行）。

- **合算していない。** FG の 107（現在値）と T1 の 58（現在値。62 → 59 は U18 後の履歴値、その後 U-B1 83820d32 で T1L-28 が解消して 58）は数え方が違う（FG はブロック、T1 はリーフ）。16 行を重複なしで足し引きするには、この表の多対一と A.P-24 の扱いを決める必要があり、その決定はこの agent は行わない。
- §8.1 の「T1 と同じとみなした 21 行」のうち、この 16 行の外の 5 行は A.P-01、A.P-02、A.P-04（文脈 / 前件）、A.P-28（監査）、C.CV-4（FG が型付けした `h_C_CV4`、T1L-43 と共有）。ここでは確認していない。C.CV-4 / T1L-43 の「どちらの文が持つか」は Q-F1 の未決事項のまま（推奨は FG が持つ）。
- T1 §8 は FG 側の前提（`hDG_GENP`、`hDG_CLOSINGRUN`、`hDG_SEM`、`hkidW`、`KD` / `OSH` / `ENV` / `TEL` など）が T1 に効くと書く。逆向きの対応（T1L-06 / 07 / 42 / 43 / 48 / 49 が FG のどの行か）はこの確認の範囲外。

### 9.4 次に前提を減らせる候補の流れ（FG 側。2 つ）

**これは候補であって実績ではない。2 候補とも、追加前提を含む純差分が確定するまで、着手可能な減算候補として扱わない。** 消える予定の ID は、補題が行の前提を満たすことを freeze で型として示せたときの候補で、消えたとは言えない。増える前提は**数えていない**（推測の数は書かない）。着手は reviewer / ユーザーの判断で、各 freeze に「消える / 増える」を数えて書くことを必須にする（§5 と同じ）。選定の根拠は、§9.2 の表で「Lean（名と branch@SHA）」があり、かつ実 run（`Start` と `RunsTo (synthesizeCombinationalCore …)`）または成功した reader から前件が作られる補題が branch 上にあること。以下の署名は本確認で `git show` により読んだ。

**候補 A: DG-ACC / DG-SEM の Acc → 因果性の鎖（C.SM-4、C.SM-2。C.SM-5 の残りを減らす）**
- 実 run から払える補題:
  - `hacc_of_top_runs`（kjob/g5ac-r26 cff12a48、`Tools/ShippingGen5AccReads.lean:137`）: top ごとに `Start L mctx cctx w ∧ RunsTo (synthesizeCombinationalCore t [] false) …` を与えると、`∀ c, ReachEdge K Top c → Acc (CallRel K) c`（C.SM-4 の `hacc ∀ Y s, G Y = some s → Acc R Y` の形に当たる）。内部で `acc_top_of_run`（:124、同ファイル）。
  - `srcCausal_of_acc_unfold`（kjob/g5sm-u23 7af6c7cc、`Tools/ShippingGen5SemAccStep.lean:14`）: `hunf` と `Acc R X` から `SrcCausal s`（C.SM-5 の `CalleesCausal` の材料）。
  - `ordCallees₀_mem`（kjob/g5ac-r26、`Tools/ShippingGen5AccOrdCallees.lean:21`）: C.SM-2 の `hmem`（ordC の membership）を `ordCallees₀` で具体化。
- 消える予定の ID: **C.SM-4**（`hacc`）、**C.SM-2**（`hmem`、`ordC := ordCallees₀` に限る）。C.SM-5 は既に PA で、C.SM-4 が消えれば残りは C.SM-3（`hinv` / `hunf`）だけになる。
- 増える前提の見込み（名前のみ。数は未計数）: `hacc_of_top_runs` が取る `hLim : LimitStmt L`、`AccServed0Stmt K L (ReachEdge K Top)`、`AccKeepChildStmt K L (ReachEdge K Top)`。`LimitStmt` は T1 側で `limitStmt_proved`（T1 §6）。`AccServed0Stmt` と C.AC-8 の `hS` の関係、および FG 台帳が C.AC-8 を A.P-24 に統合した扱いとの整合は未確認。kit `K` の carrier の固定（§8.4 の「DG-SEM と DG-ACC を 1 本の木に置く」）が先に要る。
- **純差分を確定するために数えるもの**: (a) 上の 3 件（`LimitStmt`、`AccServed0Stmt`、`AccKeepChildStmt`）が FG 側で新しい仮説になるか、既存の行（T1 側の `limitStmt_proved`、C.AC-8 / A.P-24 等）に帰着するかを行ごとに数える。型の根拠は各補題の署名（`Tools/ShippingGen5AccReads.lean:137` の `hacc_of_top_runs` の引数）。(b) `K` の carrier 固定で増える仮説（§8.4 の「DG-SEM と DG-ACC を 1 本の木に置く」）。(c) 局所統合で増える定義・仮説の有無。この調査では (a)–(c) の数は数えていない。消える C.SM-4 / C.SM-2 の 2 行と増える数の差を出すまでは「純減」と書かない。
- 前置きの作業: kjob/g5ac-r26 と kjob/g5sm-u23 の局所統合（§8.6 の試行では `lakefile.lean` のみ衝突。連続した merge の build は未確認）。g5sm-u23 の最新実装 7af6c7cc は未 review、g5ac-r26 の A13 は freeze 止まり（C.AC-4, C.AC-9 は残る）。

**候補 B: boundary-audit の名前の鎖を、型付き仮説 `h_C_CV4` に帰着させる（D.E-6、D.E-1）**
- 実 run から払える補題:
  - `hmem_of_machineShapeF`（kjob/g5ba-r16 96e862fe、`Tools/ShippingGen5NameKids4.lean:33`）: `hF : ∀ c, Reach c → ∀ sp, S c = some sp → ∃ n sm ps ci senv ai, machineShapeF n sm ps ci senv ai = some (some sp)` から `MemTagsNamed sp`。
  - `hmemSame_of_memTagsNamed`（`NameKids2.lean:71`、同 branch）: `MemTagsNamed shape` から D.E-1 の `hmemSame`。
  - `hself_of_rank`（`NameKids2.lean:80`）、`hn_kidNameAt`（`NameKids2.lean:58`）は D.E-2、D.E-3 の built 側。
- 消える予定の ID: **D.E-6**（`hF`）、**D.E-1**（`hmemSame`）、D.E-5 の `hmem` の部分（ブロック全体ではない）。
- 増える前提の見込み（名前のみ。数は未計数）: (1) `hF` を **文 §8.3 の `h_C_CV4`**（`machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)`）から作るには、`S c = some sp` と run の `machineShape? … = some sp` を結ぶ対応が要る（`S` の carrier は D.E の全行で未固定。reader-bridge の `machineDefines_of_readsAll` が候補だが partial）。(2) `hF` の量化する `sm ps ai` と `h_C_CV4` の固定値（`false [] true`）の一致は、本確認では Lean で確認していない。
- **注意**: この流れで消える D.E-6 / D.E-1 は C.CV-4（既に台帳にある、実 run から払う補題が無い境界 = DG-COVER D2(b)）に帰着させる案である。C.CV-4 から `hF` を作る供給経路は未証明のままなので、現時点では前提の純減ではなく**移し替え**であり、新しい支払い元もできない。
- **純差分を確定するために数えるもの**: (a) `S c = some sp` と run の `machineShape? … = some sp` を結ぶ対応（`machineDefines_of_readsAll` が候補。`Tools/ShippingGen5NameKids4.lean:33` の `hmem_of_machineShapeF` の `hF` の型が根拠）が新しい仮説になるか、既存行に帰着するかを数える。(b) `hF` の量化する `sm ps ai` と `h_C_CV4` の固定値（`false [] true`）の一致が、追加の仮説になるか。(c) `S` の carrier の固定で増える仮説。この調査では (a)–(c) の数は数えていない。消える D.E-6 / D.E-1（と D.E-5 の部分）と、増える数の差が確定するまで「純減」と書かない。実 run から払える根拠の強さは候補 A より弱い。

候補にしなかったもの: 段 1 の流れ 3（default route の post / entry。`synthesizeCombinational_postEntry` と `postEntry_lookup_ne`）は、D.D-8 が既に PA、D.D-2 が A.P-05 に統合されていて、引ける独立の ID が §8.2 に残っていないため。流れ 2（DataOf の健全性）は候補 A に含めた。

### 9.5 前提差分と 4 段（本版）

- この版の前提差分: **解消 0 / 追加 0**（文書の確認と反映のみ。流れ 1 の解消は kjob/flow1-b の closingrun 側で計上済み。110 表の 3 行）。
- 現在値: **FG 107 / T1 58**（FG の定義は §2。T1 は U18 82cb67a6 で 62 → 59、U-B1 83820d32（sparkle-gen3-data-supply、T1L-28）で 59 → 58）。基準件数 FG 146 / 110、T1 62 と U18 後の 59 は版の履歴。
- 4 段（設計承認 / 条件付き部品 / 前提解消 / 最終受理）: 本版は設計（段 1）の記録の更新。FG の最終受理はまだ何も満たしていない。

## 10. 候補 A / B の純差分の確定（agent `fgnext1`、branch `kjob/fgnext1`、base `kjob/fgreg2` 8fd85e5d。文書のみ。Lean・build なし）

**これは調査の記録であって前提の供給ではない。台帳の前提差分は 解消 0 / 追加 0。現在値は FG 107 / T1 58 のまま。** 署名は `git show <branch>:<path>` で読んだ原文で、この調査では build していない（各 branch の build・承認状態も確認していない）。「未供給」は「この調査で辿った候補経路では供給元・経路が見つからなかった」の意味で、存在しえないという意味ではない。

数え方: **純差分 = 消える台帳行数（§8.2 の 110 表の行）− 新しい前提数**。補題の仮説を 1 つずつ「既存の台帳行（ID）に当たる / 新しい前提」に判定した。既存行に当たるものは、その行が未解消のまま残るので新しい前提には数えない（ただしその行への依存は書く）。別の未供給境界に帰着させるだけのものは「移し替え」と書き、減算に数えない。

### 10.1 候補 A（DG-ACC / DG-SEM の Acc）

**調査で分かったこと（§9.4 の記述の訂正を含む）。** §9.4 は C.SM-4 の補題を `hacc_of_top_runs` としたが、C.SM-4 の型 `∀ Y s, G Y = some s → Acc R Y`（C_M5dg.md SM-4）は、`G := genS K`、`R := CallRel K` と置けば run を使わずに出る。`genS K X = some s` から `Acc (CallRel K) X` を返す補題が既にあるため（下の補題 A1）。`hacc_of_top_runs` が要るのは別の用途（`genS` が到達する全名に `some` を返すこと、`genS_isSome_of_cover` の前件 `∀ c, Reach c → Acc …`）で、C.SM-4 の消去には使わない。

**消える予定の台帳 ID（2 行）: C.SM-4、C.SM-2。**

| 行 | 補題（実名・完全な型・branch@SHA） | 状態 |
|---|---|---|
| C.SM-4 | A1 `Tools.ShippingGen5Acc.genS_some_inv`（`Tools/ShippingGen5Acc.lean`、kjob/g5ac-r26@cff12a48）: `{ι} {dom} {env₀} (K : AssignKit ι dom env₀) {X : Name} {s : SemPkg ι dom} (hs : genS K X = some s) : ∃ (E : ConstantInfo) (g : K.GD E), entry₀ env₀ X = some E ∧ K.genData₀ E = some g ∧ Acc (CallRel K) X ∧ (∀ k ∈ K.ordCallees (K.dOf g), ∃ sc, genS K ((K.dOf g).shape.insts[k]).1 = some sc) ∧ s = K.genSem (genS K) X g`。第 3 連言が `Acc`。`genS_of_not_acc` により `¬Acc` なら `genS K X = none` | 補題あり。C.SM-4 の型は A1 の `.2.2.2.1` で出る（組み立て 1 行の系。**この系の名前・型は未記述なので、freeze で書く型**: `hacc_genS (K) : ∀ (Y : Name) (s : SemPkg ι dom), genS K Y = some s → Acc (CallRel K) Y`） |
| C.SM-2 | A2 `Tools.ShippingGen5Acc.ordCallees₀_mem`（`Tools/ShippingGen5AccOrdCallees.lean:21`、kjob/g5ac-r26@cff12a48）: `(d : MachineData) (k : Fin d.shape.insts.length) : k ∈ ordCallees₀ d ↔ (d.shape.instOrigins.getD k .ord).child? = none`。A3 `mkKit_ordCallees₀_dataSound`（同ファイル:28 付近）: `(f) (GD) (dOf) (genData₀) (genSem) (hev : GDEvidence f GD dOf env₀) (hloc …) (hdecl …) (hd …) (hf : DataSoundAt f) : DataSound (mkKit f GD dOf genData₀ ordCallees₀ genSem ordCallees₀_mem hev hloc hdecl hd)` | 補題あり。ただし SEM 側 `hmem` の `ordC` は `SemCall.lean:17` の `ordCallees`（述語版 filter）で、A2 の `ordCallees₀`（`isNone` の Bool 版）と字面が違う。**両者を結ぶ補題は見つからなかった。freeze で書く型**: `ordCallees_eq_ordCallees₀ (d : MachineData) : ordCallees d = ordCallees₀ d`（定義の同値で、証明は `List.filter` の述語の一致。未確認） |

**これらの補題が要求する仮説の判定（1 つずつ）。**

| 補題 | 仮説 | 判定 | 型の根拠 |
|---|---|---|---|
| A1 | `K : AssignKit ι dom env₀` | carrier（binder）。仮説ではない（§8.3 の規則）。ただし A3 で組む場合は f / GD / dOf / genData₀ / genSem の **5 つの carrier** になる（`mkKit` の引数、A3 の署名）。§8.3 は carrier を前提に数えないので +0 としたが、reviewer が数えると決めるならこの欄が変わる | `Tools/ShippingGen5Acc.lean:32`（`AssignKit` の field） |
| A1 | `hs : genS K X = some s` | 補題の前件で、使う側（SEM の `hacc` の ∀ Y s, G Y = some s）が与える。仮説ではない | A1 の署名 |
| A2 | なし | — | — |
| A3 | `hev : GDEvidence f GD dOf env₀` | **既存行 C.AC-2** | `Tools/ShippingGen5AccGenDataEv.lean:22`（§9.2） |
| A3 | `hloc` / `hdecl` / `hd` | **既存行 C.AC-3** | A3 の署名、§9.2 |
| A3 | `hf : DataSoundAt f` | **既存行 C.SM-1（merged C.DO-1, C.AC-1）** | `DataSoundAt`（C_M5dg.md SM-1 の別名欄） |

新しい前提: **0**（この表の範囲）。ただし A3 で組むと、K を `mkKit … ordCallees₀ …` に固定する **文の選択**（`G := genS K`、`ordC := ordCallees₀`、`R := CallRel K`）が入る。これは前提の追加ではないが、§8.4 の「DG-SEM と DG-ACC を 1 本の木に置く（kit K の carrier を固定）」という既存の未決事項の決定であり、台帳前提の付け替えに当たる。

**前置きの作業（この調査では未確認）**: kjob/g5ac-r26 と kjob/g5sm-u23 の局所統合（§8.6 の試行では `lakefile.lean` のみ衝突。連続 merge の build は未確認）。SEM 側の `hacc`（`factsOf_all_of_acc_unfold`）の署名を g5sm-u23@7af6c7cc で読み直し、`G` と `R` を A1 の `genS K` と `CallRel K` で置換できる形か（binder の順・暗黙引数）を確認する必要がある。この調査では `hacc` を取る補題の原文は C_M5dg.md SM-4 の貼付だけを読んだ。

**C.AC-8（hI / hKI / hLim / hS）は減算に入れない。** 補題の面では `limitStmt_proved`（`Tools/ShippingGen2T1.lean:127`、base）と `accKeepChild_proved`（`Tools/ShippingGen5AccKeep.lean:337`、g5ac-r26）が前提なしで、`acc_of_run`（`AccInd.lean:146`）が `hS : AccServed0Stmt` から `hI` / `hKI` を作る。`hS` は `accServed0_of_cover_gates`（`Tools/ShippingGen5AccRoute.lean:70`）が `hcl`（`ReachEdge` の閉包で成立）と C.AC-4（`ReachCover`）・C.AC-9（`DataOfShape`）・C.AC-5（`GatesNoneAt`）・C.AC-6（`ClosesOfShape`、= A.P-07 に統合）・C.AC-7（`ReadsSupplyAt`）に帰着させる。すべて既存行で、新しい前提は見つからなかった。しかし C.AC-8 は §4 で A.P-24 の組に統合された行（110 表の行は A.P-24）で、A.P-24 を FG の数に残すかは §9.3 の reviewer 確認事項のまま。この調査は A.P-24 を減算に入れない。

**純差分（A）= 消える 2（C.SM-4、C.SM-2）− 新しい前提 0 = +2。** どちらの消去も、使う補題は証明済み（A1、A2）で、残る依存は既存の未解消行（C.AC-1/2/3 = A3 の仮説）だけ。移し替えではない（C.SM-4 は run にも別境界にも帰着せず、A1 で直接出る）。ただし上の 2 つの未確認（統合 build、SEM 側署名の一致）と `ordCallees_eq_ordCallees₀` の型が freeze で確定するまでは「見込み」であり、消えたとは言わない。

### 10.2 候補 B（boundary-audit の名前の鎖）

**消える予定の台帳 ID: D.E-6（`hF`）、D.E-1（`hmemSame`）。** D.E-5 は `hg` / `hsp` / `hin` が残るので、`hmem` の部分が消えてもブロックは消えない（減算に入れない）。

| 補題 | 完全な型・branch@SHA |
|---|---|
| B1 `hmem_of_machineShapeF`（`Tools/ShippingGen5NameKids4.lean:33`、kjob/g5ba-r16@96e862fe） | `{Reach : Name → Prop} {S : Name → Option MachineShape} (hF : ∀ c, Reach c → ∀ sp, S c = some sp → ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool), machineShapeF n sm ps ci senv ai = some (some sp)) : ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp` |
| B2 `hmemSame_of_memTagsNamed`（`Tools/ShippingGen5NameKids2.lean:71`、同 branch） | `(shape : MachineShape) (h : MemTagsNamed shape) : ∀ (k) (hk : k < shape.insts.length) (k') (hk' : k' < shape.insts.length), memKey (originAt shape k) ≠ none → memKey (originAt shape k) = memKey (originAt shape k') → (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1` |

`hF` は B1 の仮説で、`hF` を作る補題（`S c = some sp → ∃ …, machineShapeF … = some (some sp)`）は **この調査では見つからなかった**（B1 のファイル先頭コメントも「`hF` は production bridge ではない」と書く）。書く必要のある型と、それが要求する仮説:

`hF_of_defines`（freeze で書く型、未実装）: `S := fun c => (GP (envAt cref w) c).map (·.d.shape)`、`Reach := TgtRun (GP (envAt cref w)) declName`（§8.3 の Q-F2 の閉包）として、`hF` の結論を、(i) 文 §8.3 の `h_A_P06`（`MachineDefines … c q.d.shape`）、(ii) `h_C_CV4`（`machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)`）から作る。`MachineDefines`（`Tools/ShippingMachineEntry.lean:2345`、kjob/g5dc-r23@0fcce4e7）は `∀ w1 ci w2 w5 envR w6 w7 envR' w8, RunsTo (getConstInfo c) … → RunsTo getEnv … → RunsTo getEnv … → … ∧ machineShape? false [] (entryConst true false [] ci …) (structEnv envR') = some shape` の形なので、`machineShape? … = some sp` を取り出すには **3 つの run の存在**が要る。

| 仮説 | 判定 | 根拠 |
|---|---|---|
| `h_A_P06`（`MachineDefines`） | **既存行 A.P-06**（§8.3 の typed 7 の 1 つ） | 文 §8.3 |
| `h_C_CV4` | **既存行 C.CV-4**（typed 7 の 1 つ） | 文 §8.3、`Cover5.lean:97` |
| 2 本の `getEnv` の run の存在 | 前提ではない（`getEnv_runs_exists`、`ShippingEntryReadsLinked`/`ShippingGen5Acc` で使用。任意の world で存在。本調査では署名を `git grep` で確認しただけ） | g5ac-r26 `AccServed.lean` の使用箇所 |
| `AdmCtx L.O.quiet mctx' cctx'` の witness | 既存行 A.P-02 / A.P-04 の `Start`（`EntryWitness` の第 1 conjunct）から top については取れる。**子の名前 `c` では、`TgtRun` の全 `c` に対して取る補題は見つからなかった**（`RealChildA` は `AdmCtx` を含むが、`TgtRun` との接続は未記述） | `Tools/ShippingGen2Defs.lean:52`、`FG.lean:26` |
| `TgtRun` の全 `c` に対し、`getConstInfo c` が成功する run（ci と world）の存在 | **新しい前提 1**。台帳に当たる行が無い（C.RK-4 は `readMachine declName` の run で、`getConstInfo c` の run の存在ではない。C_M5dg.md RK-4 の型を比較した）。top は `EntryWitness` の run から `core_chain` で取れる可能性があるが、子は子の run（`RealChildA`）が要り、`hacc_of_top_runs` のコメントも「他の reached name の run は無い」と書く | `ShippingGen5AccReads.lean` の `hacc_of_top_runs` 付近、`RK-4` |
| S の carrier の固定（`S := (GP …).map (·.d.shape)`） | 前提ではなく文の選択。ただし D.E の全行（E-5/E-7/E-8/E-9）の `S`・`Reach` が「production の ds/Reach/S が未供給」と書く既存の未決事項の決定になる | §8.4、D_M5t2.md E-5/E-7 |

**純差分（B）= 消える 2（D.E-6、D.E-1）− 新しい前提 1（`TgtRun` の全 `c` の `getConstInfo` run の存在 + `AdmCtx` witness）= 形式上 +1。ただしこれは移し替えである。** D.E-6 の内容（`S` の shape が `machineShape?` の出力であること）を、既存の A.P-06 / C.CV-4 と、**新しい未供給の境界（子ごとの実 run の存在）** に帰着させるだけで、供給の道（子の run を `TgtRun` に結ぶ補題）は B 側に無い。§9.4 の注意（C.CV-4 への移し替え）が、この調査で 1 つの新しい境界に変わっただけである。よって **B は減算に数えず、着手可能としない。** 形式上の +1 を採るかは reviewer / coder の判断。なお D.E-1 は D.E-6 の `S` の shape から `MemTagsNamed` を作る経路（B1）を共有するので、D.E-6 を数えないなら D.E-1 だけを単独で減算にはできない（`memTagsNamed_of_tagsAgree`（`NameKids2.lean:62`）の `TagsAgree shape` を別に供給する経路は、この調査では辿っていない）。

### 10.3 結論

- **着手可能: 候補 A（純差分 +2、C.SM-4 と C.SM-2）。** 条件: freeze が承認されること（台帳前提の付け替え・carrier の固定を含むので、共通ルール 14 の分担により reviewer の承認が要る freeze）。
- **着手不可: 候補 B（移し替え。形式 +1 を採るなら reviewer の判断）。**
- 最初の単位（A）の freeze に書くこと（短く）:
  1. 目標: C.SM-4 と C.SM-2 の 2 行の消去。**消える ID と新しい前提を ID で列挙し、純差分 +2 / 追加 0 を台帳の前提差分欄に書く。**
  2. 書く型 3 つ: `hacc_genS`（A1 の系。上の型）、`ordCallees_eq_ordCallees₀`（上の型）、およびそれらを SEM の `hacc` / `hmem` の binder に渡す 1 つの組み立て（`G := genS K`、`R := CallRel K`、`ordC := ordCallees₀`）の完全な型。
  3. 使う仮説の判定表: C.AC-2 / C.AC-3 / C.SM-1 は既存行のまま、新しい前提 0。carrier（f / GD / dOf / genData₀ / genSem の 5 つ）の扱い（§8.3 の規則で前提に数えない、とするかの reviewer 確認）。
  4. 前置き: g5ac-r26@cff12a48 と g5sm-u23@7af6c7cc の統合木の build、SEM 側 `hacc` / `hmem` の署名の一致の確認。
  5. 明記: `hacc_of_top_runs` は使わない（C.SM-4 の消去に run は不要）。C.AC-8 / A.P-24 は減算に入れない。mutant は signature / defeq での棄却であって意味的反例ではない（Check を書く場合）。供給・共同充足性・FG 証明は主張しない。

### 10.4 前提差分と 4 段（本版）

- この版の前提差分: **解消 0 / 追加 0**（調査の記録のみ）。現在値は **FG 107 / T1 58**。純差分 +2（A）は見込みで、freeze 承認・実装・clean build の後に初めて台帳に反映する。
- 4 段（設計承認 / 条件付き部品 / 前提解消 / 最終受理）: 設計（段 1）の前の調査記録。どの行も進めない。

## 11. A / SM3 受理後の次候補（agent `fgnext2`、branch `kjob/fgnext2`、base `kjob/fgnext1` b54e343d。文書のみ。Lean・build なし）

**これは調査の記録であって前提の供給ではない。この版の台帳の前提差分は 解消 0 / 追加 0。現在値は FG 107 / T1 58 のまま。** 候補 A（C.SM-2 / C.SM-4、`kjob/canda-pa2` 628bc5d3、Issue sparkle-gen5-dg-sem）と SM3（C.SM-3、`kjob/sm3-pa2` 4cade1d0、Issue sparkle-gen5-dg-acc）は dry-run 合格・本番 proof-accept 待ちで、**まだ減算していない**（本番合格後に FG -3 で 104 の予定）。以下の「A / SM3 受理後」は、その 2 つが受理された場合の見込みを前提にした条件付きの話である。候補 B（D.E-6 / D.E-1）は §10.2 のとおり移し替えで、ここでも減算に数えない。

方法: A / SM3 の root 型（`kjob/canda1` の `scripts/gen5/CANDA_FREEZE.md`、`kjob/smb1` の `scripts/gen5/SM3_FREEZE.md`）と、candidate 628bc5d3 / 4cade1d0 の Lean 原文を `git show` で読んだ。補題の署名は原文で、**この調査では build も elaborate もしていない**（Lean を書かない指示のため）。したがって下の「書く型」のうち証明の形は案であり、elaborate の確認は freeze 承認後の実装の最初の作業になる。「未供給」は「この調査で辿った候補経路では供給元・経路が見つからなかった」の意味で、存在しえないという意味ではない。mutant は signature / defeq での棄却であって意味的反例ではない（Check を書く場合）。

### 11.1 出発点: A / SM3 受理後の assembly に残る仮説

`factsOf_genS_assembled'`（`Tools/ShippingGen5AccHinv.lean`、kjob/sm3-pa2 4cade1d0。HYP = `hs hev hloc hdecl hd`）の仮説の台帳上の行（CANDA_FREEZE §3、SM3_FREEZE §3 の判定表のとおり）:

| 仮説 | 台帳行 | 状態 |
|---|---|---|
| `hs : DataOfSound dataOf initsOf` | C.SM-1（merged C.DO-1, C.AC-1） | 残る |
| `hev : GDEvidence …` | C.AC-2 | 残る（CANDA_FREEZE §3: 「`genData_evidence` で埋まる形だが、この freeze は C.AC-2 を消さない」） |
| `hloc` / `hdecl` / `hd` | C.AC-3 | 残る |
| `genData₀` | carrier（成功は C.AC-4 / C.SM-6 側） | 関数引数 |

CANDA_FREEZE §3 は `hev` を「`GD := GenData` の `genData_evidence` で埋まる形」と書き、AccHinv の判定表も `hev`、`hloc`/`hdecl`/`hd` を「変更なし（残る）」とした。**この調査はその 4 つが、固定 carrier（`GD := GenData`、`dOf := (·.d)`、`genSem := GenData.genSem hs`、`ordCallees := ordCallees₀`）では既存の定理で出るかを 1 つずつ辿った。**

### 11.2 候補 C（C.AC-2 / C.AC-3: GenData-kit の証拠・局所性・宣言名・データ一致）

**消える予定の台帳 ID（2 行）: C.AC-2、C.AC-3。** 行の内容（`C_M5dg.md` AC-2 / AC-3 の原文）は、一般の `GD` / `dOf` / `genSem` についての `hev` と `hloc` / `hdecl` / `hd` で、A の carrier 固定（`GD := fun E => GenData dataOf E (structEnv env₀)`）の後は、`mkKit` に渡すこの 4 引数が `GenData` の定理になる。

| 仮説 | 供給する既存補題（実名・完全な型・branch@SHA） | 辿った結果 |
|---|---|---|
| `hev` | `Tools.ShippingGen5Sem.genData_evidence`（`Tools/ShippingGen5SemGenData.lean:57`、kjob/canda-pa2@628bc5d3、g5sm-u23 系）: `{dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} (senv : StructEnv) (E : ConstantInfo) (g : GenData dataOf E senv) : machineShape? false [] E senv = some g.d.shape ∧ dataOf E senv g.d.shape = some g.d` | `GDEvidence dataOf GD dOf env₀`（`Tools/ShippingGen5AccGenDataEv.lean:22`）は `∀ E g, machineShape? false [] E (structEnv env₀) = some (dOf g).shape ∧ dataOf E (structEnv env₀) (dOf g).shape = some (dOf g)`。`GD := GenData …`、`dOf := (·.d)` で、`genData_evidence (structEnv env₀) E g` と字面が一致する（`GenData` の field `hshape` / `hdata` がそのまま）。新しい仮説なし |
| `hdecl` | `Tools.ShippingGen5Sem.genSemI_decl`（`Tools/ShippingGen5SemCall.lean:112`）: `(Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : (genSemI Q X g).decl = X` | `GenData.genSem hs Q X g = genSemI Q X (g.toIn hs)`（`SemGenData.lean`、定義の展開）なので `genSemI_decl Q X (g.toIn hs)` で出る。新しい仮説なし |
| `hd` | `Tools.ShippingGen5Sem.genSemI_d`（`SemCall.lean:115`）: `(Q) (X) (g : GenIn) : (genSemI Q X g).d = g.d` と `genData_toIn_d`（`SemGenData.lean:46` 付近、`rfl`）: `(g.toIn hs).d = g.d` | 目標 `(GenData.genSem hs Q X g).d = g.d` は 2 つの合成。新しい仮説なし |
| `hloc` | `Tools.ShippingGen5Sem.genSemI_local`（`SemCall.lean:182`）: `(Q Q' : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : ∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) : genSemI Q X g = genSemI Q' X g`、および `Tools.ShippingGen5Acc.ordCallees_eq_ordCallees₀`（`Tools/ShippingGen5AccSemJoin.lean:27`、kjob/canda-pa2@628bc5d3）: `(d : MachineData) : ordCallees d = ordCallees₀ d` | `hloc` の前件は `ordCallees₀ g.d` 上、`genSemI_local` の前件は `ordCallees (g.toIn hs).d` 上（`(g.toIn hs).d = g.d` は `rfl`）。両者を A が置く `ordCallees_eq_ordCallees₀` で結ぶ（CANDA_FREEZE §2.2 が「`hloc` を `genSemI_local` につなぐ実装段階で使う」と書いた橋）。新しい仮説なし |

**書く型（freeze に書く。全て新規ファイル `Tools/ShippingGen5AccGenDataKit.lean`（案）、namespace `Tools.ShippingGen5Acc`、`import Tools.ShippingGen5AccHinv`（A と SM3 の candidate を積む）。共通の `variable {ι} {dom} {env₀}` と open は CANDA_FREEZE §2 のとおり。証明は上の列の補題を並べる形の案で、elaborate は未確認）:**

```lean
theorem genData_gdEvidence
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData) :
    GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀
-- 案: fun E g => genData_evidence (structEnv env₀) E g

theorem genData_genSem_decl
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X
-- 案: fun Q X E g => genSemI_decl Q X (g.toIn hs)

theorem genData_genSem_d
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d
-- 案: fun Q X E g => genSemI_d Q X (g.toIn hs)

theorem genData_genSem_local
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g
-- 案: genSemI_local Q Q' X (g.toIn hs) に、ordCallees_eq_ordCallees₀ g.d で前件を書き換えて渡す

theorem factsOf_genS_assembled''
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀))) :
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
        (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)) X = some s →
      FactsOf s
-- 案: factsOf_genS_assembled' hs genData₀ (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)
```

`factsOf_genS_assembled''` の仮説は `hs`（C.SM-1）と carrier `genData₀` だけになる。`factsOf_genS_assembled'` との差は、`hev hloc hdecl hd` の 4 つの binder が定理 4 つの適用に置き換わることだけ。

**仮説の判定（1 つずつ）。** 4 補題の仮説は `hs : DataOfSound dataOf initsOf`（既存行 C.SM-1。上の `genData_gdEvidence` だけは `hs` も取らない）以外にない。`genData₀` は carrier（§8.3 の規則）。**新しい前提: 0。** `genSemI_local` / `genSemI_decl` / `genSemI_d` / `genData_evidence` / `ordCallees_eq_ordCallees₀` はすべて仮説なしの定理（または `hs` だけ）で、原文で確認した。

**純差分（C）= 消える 2（C.AC-2、C.AC-3）− 新しい前提 0 = +2。** 移し替えではない（別の未供給境界に帰着せず、既存の定理で直接出る）。

**注意（reviewer 確認事項）:**
1. C.AC-2 / C.AC-3 の行の本文は一般の `GD`（kit の field）についての仮説で、「kit `K` の carrier が固定されていない」と §8.2 は書く。**これが消えるのは、A の carrier 固定（`GD := GenData`）を最終 assembly が採る場合に限る。** A13 の `GDf` / `genDataF`（`GenData` と別型、DG_ACC freeze 承認済み・Lean 未実装）を最終 assembly の kit に採る場合は、C.AC-2 / C.AC-3 は別の `GD` について再び要る。A 自体がこの carrier を前提にしている（CANDA_FREEZE §3 reviewer 確認事項 1、2）ので新しい決定ではないが、「A を承認 = GenData-kit を採る」を C の前提として明記する。
2. 前置き: **A の本番 proof-accept（628bc5d3）が通っていること**（`ordCallees_eq_ordCallees₀` と `factsOf_genS_assembled'` を使う）。SM3 の受理は C の型には要らない（`factsOf_genS_assembled'` は SM3 の candidate 4cade1d0 の AccHinv にあるので、C を SM3 の上に積むなら SM3 も要る。A だけに積むなら `factsOf_genS_assembled`（`hinv` を取る版）に対する `hinv` が残るので、SM3 の上に積む形を推奨）。
3. 5 つの carrier（`dataOf`、`GD`、`dOf`、`genData₀`、`genSem`）を前提に数えない扱いは A / SM3 と同じ。
4. C.AC-4（`ReachCover`、`genData₀` の成功）、C.AC-5 / C.AC-7 / C.AC-9、C.SM-6（`GenWF`）、A.P-24（C.AC-8 統合）は減算に入れない（11.4）。

### 11.3 候補 D（C.SM-1: `DataOfSound` を `dataOfAt lvl` で供給する）

**消える予定の台帳 ID: C.SM-1（条件付き）。** 補題:

- `Tools.ShippingGen5DataOf.dataOfAt_sound`（`Tools/ShippingGen5DataOf.lean:211`、kjob/g5do-r6@063056d6）: `(lvl : Lean.Expr → Nat) {E : ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData} (h : dataOfAt lvl E senv s = some d) : d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j)) (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧ d.initOk (initsOf d) = true`。ここで `initsOf` は `Tools.ShippingGen5DataOfPure.initsOf (d : MachineData) : HList (tys d.ss)`（`ShippingGen5DataOfPure.lean:354`）。
- 並べると `DataOfSound (dataOfAt lvl) Tools.ShippingGen5DataOfPure.initsOf`（`Tools/ShippingGen5SemGenData.lean:18` の定義、4 連言が一致）は `fun E senv s d h => dataOfAt_sound lvl h` で出る形。**書く型（案）:** `theorem dataOfSound_dataOfAt (lvl : Lean.Expr → Nat) : DataOfSound (Tools.ShippingGen5DataOf.dataOfAt lvl) Tools.ShippingGen5DataOfPure.initsOf`。

判定:
- 新しい仮説は見つからなかった（`dataOfAt_sound` の `h` は `DataOfSound` の `∀ … d, dataOf E senv s = some d →` の内側で束縛される）。`lvl` は carrier（`exprSize` は DG-READKINDS の側で、`g5do-r6` の木に無い。`C.DO-3` の「`dataOf at exprSize`」の行が既にある）。
- **消えるかの条件。** C.SM-1 は C.DO-1 と C.AC-1 を統合した行で（§4、別名 `DataOfSound` / `DataSoundAt`）、§8.2 は「`DataOfSound` と coverage `dataOfAt = some d`」と書く。上の補題が供給するのは `DataOfSound` の半分で、`dataOfAt = some d` の被覆（`genData₀` の成功、DO-1 の本来の内容。`dataOfAt` を `some` にする定理は `g5do-r6` に無い、DATAOF freeze §11.2）は供給しない。被覆の半分を既存行（C.DG-1 (i)、C.AC-4）が持つと reviewer が判断すれば C.SM-1 は消え**+1**。そう判断しないなら、行は残り、この候補は 0（行の分割は 110 を変えるので、この調査では行わない）。
- **前置きの作業（未確認）:** kjob/g5do-r6 は A / SM3 の木と祖先関係が無く（merge-base 9d26005c）、`git merge-tree` では `lakefile.lean` だけが衝突する（lean_lib の和集合で足りる見込み）。import の連鎖（`ShippingReaderApp`、`ShippingMachineCommand` 等）が A / SM3 の木と同時に build できるかは確認していない。さらに `dataOf := dataOfAt lvl` に固定すると、production の reader との一致（C.DO-2）、`lvl` の選択（C.DO-3）が `dataOf` carrier を通して assembly に結び付く。この 2 行は既存行のまま。
- 並行して C.AC-9 の `hDS : DataOfShape K` の半分は、`K.dataOf = dataOf` と C.SM-1 の第 1 連言（`d.shape = s`）から `dataOfShape_of_sound` で出る見込みだが、C.AC-9 は `RunDataLink`（run 依存）も持つので行は残る（減算に入れない）。

**純差分（D）= 消える 1（C.SM-1、reviewer が被覆の半分を既存行と判定した場合）− 新しい前提 0 = +1。判定されない場合は 0。** 被覆と lineage の確認が先なので、C の次の順位とする。

### 11.4 辿ったが減算候補にしなかったもの

- **候補 B**（D.E-6 / D.E-1）: §10.2 のとおり移し替え。変更なし。
- **C.AC-4**（`ReachCover K Reach`、`hcl`）: `genS_isSome_of_cover` が前件に取る被覆で、`genData₀ E = some g` の成功を述べる。`genData₀` の成功を run から作る補題は、この調査で辿った経路（`hacc_of_top_runs`、`accServed0_of_cover_gates`、`dataOfAt_sound`）には見つからなかった（`dataOfAt` の被覆は DATAOF freeze §11.2 で未供給）。
- **C.AC-5 / C.AC-7 / C.AC-9 の `RunDataLink`**: `accServed0_of_cover_gates` が前件に取る行で、`GateRunsAt` / `ReaderRunsAt`（AC-5 の別名）、`QuietStrengthA`（AC-7 → C.EN-1）、run の `MachineDefinesR`（AC-9）に帰着する。いずれも既存行（C.EN-1 / C.EN-6 / A.P-06 等）への帰着で、消える行より増える行の方が多いか同数で、純差分が正になる経路は見つからなかった。
- **C.AC-8 / A.P-24**: §10.1 のとおり減算に入れない。
- **C.SM-6**（`GenWF`）: `rowC_of_reader` 等が `hq` / `hnl` / `FullInv`（C.CV-1/2/3）を前件に取る。これらは run-local の reader state で、供給元は見つからなかった。

### 11.5 結論（優先順）

1. **第 1: 候補 C（C.AC-2 + C.AC-3、純差分 +2）。** 条件: A の本番受理（628bc5d3）、SM3 の本番受理（積む場合）。最初の単位の freeze に書く内容（短く）:
   - 目標: C.AC-2（`hev`）と C.AC-3（`hloc` / `hdecl` / `hd`）の 2 行を、固定 carrier（`GD := GenData`、`ordCallees₀`）で消す。**消える ID と新しい前提を ID で列挙し、純差分 +2 / 追加 0 を台帳の前提差分欄に書く。**
   - 書く型: 11.2 の 5 つ（`genData_gdEvidence`、`genData_genSem_decl`、`genData_genSem_d`、`genData_genSem_local`、`factsOf_genS_assembled''`）。
   - 判定表: 使う仮説は `hs`（C.SM-1、残る）だけ。`genData₀` は carrier。
   - 明記: 「A の carrier 固定（GenData-kit）を最終 assembly が採ることが前提」「A13 の `GDf` を採る場合は C.AC-2 / C.AC-3 が再び要る」「C.AC-4 / SM-6 / AC-5 / AC-7 / AC-9 / A.P-24 は減算に入れない」。供給・共同充足性・FG 証明は主張しない。elaborate は実装の最初の作業。
   - 台帳の分担（共通ルール 14）: 行の除去を含むので reviewer の承認が要る freeze（1 回）。
2. **第 2: 候補 D（C.SM-1、条件付き +1）。** 先に reviewer が「C.SM-1 の被覆の半分を既存行が持つ」と判定し、`g5do-r6` と A / SM3 の木の統合 build の見込みを確認する。判定されなければ 0 なので、第 1 の後に起こす。

その後に残る FG 側の assembly 仮説は C.SM-1 と `genData₀` の成功（C.AC-4 / C.SM-6 / C.DG-1）で、後者は run から払う補題がこの調査では見つからなかった。**実 run から払える根拠のある行を挙げるなら**（正の純差分の候補が尽きた後の参考）: 流れ 2 の C.RK-4（`readMachine declName` の run 存在）は §9.2 で dg-runreads / dg-closingrun の予定、未計数のため候補に数えない。

### 11.6 前提差分と 4 段（本版）

- この版の前提差分: **解消 0 / 追加 0**（調査の記録のみ）。現在値は **FG 107 / T1 58**。A / SM3 の本番受理後は FG 104（-3）の予定、C を受理すれば 102（-2）、D が成立すればさらに 101 の見込み（いずれも見込みで、受理・台帳反映前は書かない）。
- 4 段（設計承認 / 条件付き部品 / 前提解消 / 最終受理）: 設計（段 1）の前の調査記録。どの行も進めない。

## 12. 現在値の更新（2026-11-01、coder。文書のみ。Lean・build なし）

§11 の時点（FG 107 / T1 58）以降に、本番 proof-accept と reviewer の承認で受理された減算を記録する。§2 の現在値の定義（§8.2 の 110 行表のうち未解消の行数）はそのまま使う。110 / 146 の基準件数と表の行は書き換えない。

| 単位 | 消えた FG 行 | 根拠（候補 SHA、verdict） | 条件 |
|---|---|---|---|
| A（Issue sparkle-gen5-dg-sem） | C.SM-2、C.SM-4 | candidate 628bc5d3、`~/git/.kjob-state/proof-accept/sparkle-gen5-dg-sem-628bc5d3dc2c-20261031T235825Z-8e4757`（pass、imports 564 unchanged） | 固定 carrier（GenData-kit）を最終 assembly が採ること |
| SM3（sparkle-gen5-dg-acc） | C.SM-3 | candidate 4cade1d0、`…/sparkle-gen5-dg-acc-4cade1d0dccf-20261101T000326Z-291a21`（pass、565） | 同上 |
| CKIT（sparkle-gen5-dg-kit） | C.AC-2、C.AC-3 | candidate 4bc671dd、`…/sparkle-gen5-dg-kit-4bc671dd447a-20261101T000840Z-1a1fd4`（pass、566） | §11.2 の注意 1: A13 の `GDf` を採る場合は再び要る |

- **現在値: FG 102**（107 − 5）。T1 側の現在値は T1 台帳 §12 のとおり **T1 54**。
- 候補 D（C.SM-1）は reviewer 裁定で 0（`dataOfAt_sound` は被覆を作らない）。§11.5 の第 2 は起こさない。
- その後の調査 `scripts/gen5/GENDATA_COVER_SURVEY.md`（b68e83bd、reviewer 承認）: C.AC-4 / C.SM-6 / C.DG-1 は、この調査で辿った候補経路では未供給。正の純差分の候補なし。
- 合算していない（§9.3 のとおり、FG と T1 は数え方が違う）。
