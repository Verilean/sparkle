# 台帳の出口の比較資料: M4 経路を続けるか、IP 限定に切り替えるか、別の行を直接消すか

Issue: `sparkle-ledger-shorten`（agent rt181、文書のみ。Lean は書いていない。build していない）。
base: b2efa8c0（par/memo-legacyk5、M4 の現状）。台帳の根拠: FG `par/fg-ledger-sync` 8f2c1ded（scripts/gen2/PREMISE_LEDGER.md §12.10）、T1 `par/t1-ledger-sync`（scripts/gen3/PREMISE_LEDGER.md）。

**台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。** この資料に出る −n / +n は見込みで、受入済みの台帳は変えない。

書き方の約束:
* 「確認した」= この Pod で grep / ls / wc を実行した、または文書を読んだ。「読んだ」= コードや文書の読みで、Lean では確かめていない。「測定済み」= 過去の測定の記録が文書にある（再測定していない）。
* 「見つからなかった」は「この調査では供給元・経路が見つからなかった」の意味で、不可能・導出不能とは言っていない。
* mutant は出てこない。出てくる場合は signature / defeq での棄却で、意味的反例ではない。
* 費用の行数・時間は推定で、測った値ではない。

## 0. 結論（先に）

1. **今の M4 の経路は、最後まで行っても FG の純減は −1（91 → 90）**。途中で 92 まで 1 増える。純減が出るのは「parametric の残り全部」が揃った後だけで、そこまでの距離は大きい（§1.3）。
2. **M4 の (b)（K walk 全体の受入）は、今のままでは閉じない**。`MsgMvK`（Elab.lean 6605 の `msgToString`）に、この調査では供給元・経路が見つからなかった。閉じるには家族に新しい文を足す（TRUSTED 境界の文、reviewer）か、別の経路が要る。LegacyImplK の H11 は 4 回 OOM / 時間切れで、まだ build が通っていない。
3. **既存 IP の到達分析**（§2）: 記録上、legacy だけの宣言は 0 / 391、memo hit は 0（399 入口）、parametric の入口は IP と Examples のファイルに 0 件（grep）。ただしこれらは「測定の記録」と「grep」で、unreachable の**定理**ではない。IP 限定の定理にしても、FG の scope（成功したコンパイル全部）を狭める仮定になるので、**一般台帳の減算には数えない**（読み。reviewer / ユーザー確認が要る）。
4. **別の直接減算**（§3）で、M4 より早く確かに消せそうな行は 2 つ見つかった: `A.P-26 + C.CR-1`（run 局所の `closingRun0_of_run`、見込み −2）と `A.P-24`（`ih_allPF` の差し込み、見込み −1）。どちらも**非リーフ**の行なので、合計の 91 は減るが、リーフ（証明対象）62 は減らない。さらに base にはそれらの材料のファイルが入っていない（§3.1）。
5. **推奨**（§4）: M4 の実装は (b) の手前で止めて土台を保つ（新しい freeze を積まない）。§3 の 2 候補を先に進める。IP 限定への切り替えは、台帳の効果が 0 なので、単独の目標にしない。測定 3 件（§2.6）を coder が回す。ユーザー判断が要るのは §4.4。

## 1. 今の M4 MemoFamily 経路の減算表（FG 91 → (b) 92 → (c) 90）

### 1.1 91 の内訳（確認の仕方）

FG 台帳 §12〜§12.10 の増減を、`LEDGER_SHORTEN_PLAN2.md`（par/ledger-replan）の 93 行の内訳に当てて足し引きした（台帳本文に 91 行の表示は無い。私が計算した）:
リーフ 63 に、+5（N1-a `DeclValuePh`、N2-b `PackTupleInputsBridge`、N3-b `RawNodePh`、`NormNodePh`、`RecRulePhU`）、−3（C.RT-2、C.CV-2、C.CV-3）、−2（D.E-7、D.E-8）、−1（B.F-4）で **リーフ 62**。非リーフ 30 から A.P-22 を引いて **29**。62 + 29 = **91**。台帳の記録と合う。

M4 に関わる残りの行: `B.P-1, B.P-2, B.P-3, B.P-4, B.P-7, B.P-8, A.P-05`（B-PARAM）、`B.P-5`（TRUST）、`B.F-8`（legacy / memo）、`D.E-12`（hno / htop は 1 行に束ねてある）。

### 1.2 減算表

「束ねた行は束ごとに数える」に従う。root theorem の名前は、base の `scripts/gen4/KWALK_PLAN.md` と `MEMO_FAMILY_FREEZE.md` から写した。まだ無いものは「未命名」。

| 段 | 受け入れるもの | 消える ID | 増える ID | FG | 消える条件 | まだ残る条件 | root theorem |
|---|---|---|---|---|---|---|---|
| 今 | — | — | — | 91 | — | — | — |
| (a) | MemoFamily freeze rev3（13〜14 文）の承認 | なし | なし（文の承認だけでは数えない） | 91 | なし | Diag と窓の文は未実装 | なし |
| (b) | K walk 全体: `LegacyImplK`（H11）と `MsgMvK` を閉じ、`topEntry_K` の仮説を `MemoFamily` だけにする | なし | **M4.MEMO-01**（`MemoFamily` を R-1 で 1 行） | **92** | なし（家族の行が増えるだけ） | `MemoFamily` が TRUSTED として残る | `topEntry_K_of_family`（Induct2 版は `topEntry_K_of_family2`）。今の閉包の仮説は `LegacyImplK` だけ |
| (c) | parametric の残り全部: F-kids の残り、F-θ、F-top、F-post、shape、assembly | **B.P-8**（`LegalBinding D θ`）、**B.P-1**（`AllPos θ`） | なし | **90** | `LegalBinding` が実 run から出る → `legalBinding_allPos` / `legalBinding_covers`（F3、50d22e3b、承認済み）で `AllPos θ` が出る | `B.P-2/3`（`Bound`、`ExprOK`）、`B.P-4`（production との橋）、`B.P-5`（TRUST）、`B.P-7`（`RefLaws` I3c）、`A.P-05`、`M4.MEMO-01`、`D.E-12` の非 machine 分、`B.F-8` | 未命名（assembly の定理。freeze が先） |
| quiet C（ユーザー 2026-11-04） | 1c を実装しない | なし | なし | ±0 | — | `hno` は未供給のまま。`D.E-12` は hno / htop の束なので、hno だけ供給しても 0 | — |

注意:
* (c) の「−2」は、PARAM_INV_ESTIMATE §6 と M4_CONSULT §2.1 にある reviewer の指示による。**全部が揃った場合だけ**で、F-kids 単独は 0。どれか 1 つでも欠けると (b) の 92 のまま。
* B.P-8 の coverage 項目が B.P-2 の `Bound θ d` に当たるかは、台帳（B_M4 P-8）では 1 対 1 が確認されていない。
* (c) が終わっても、M4 が受け持つ他の行（`B.F-8`、`D.E-12` の非 machine 分）は動かない（2c、1c の保留）。M4 全体の完了にはならない。

### 1.3 残りの仕事、費用、確かさ、純減までの距離

| 仕事 | 状況（確認） | 費用の見込み（推定） | 確かさ | 備考 |
|---|---|---|---|---|
| LegacyImplK の H11（`Rec.translateExprToWireImpl` の本体） | `Tools/ShippingGen4KWalkLegacyH11.lean` は 94 行。lakefile 未登録で、build が通っていない。KWALK_PLAN に、H10 は 9 分で、H11 は 11 分 40 秒で終わらず止めたと記録。最後の commit（b2efa8c0）は rt179 の Pod が OOMKilled で止まったあとの WIP。担当指示に「H11 は 4 回 OOM」とある | 不明。腕ごとに分ける案（Elab 6930-7985）か、`kjob run` の長い上限（coder）。どちらも見積りの根拠が無い | 低〜中 | Tac2（規則を当てる補助、433 行）で全体を歩く設計の限界が出ている可能性。原因は未特定（KWALK_PLAN は「原因は未特定」と書く） |
| `MsgMvK`（Elab 6605、`handleDefinitionUnfold` の失敗側の `ex.toMessageData.toString`） | MEMO_FAMILY_FREEZE rev3 §R2.6 が、供給元・経路が見つからなかったと記録。`OkMsg` の `withContext c` は throw 時の環境を使い、現在の world の環境ではない。memo 版の `OkMsg` と `excOk` の memo 版が要る | 家族に文を 1 つ足すなら小。だが TRUSTED 境界の文の追加で、reviewer の承認とユーザー判断が要る | 中（文の追加なら）。経路が無ければ止まる | (b) の前提。ここで止まると (b) の +1 も起きない |
| `Induct2` の組み立てと Check | Induct2 は BUILT（33 秒）。`hImpl`（= LegacyImplK）を仮説に取る形。組み立て・Check は H11 待ち | 小〜中 | 中 | H11 の後 |
| F-kids（`StatePF` / `WorldPF` の翻訳器全体の walk） | 未着手。PARAM_INV_ESTIMATE §3.4 が **3500〜5000 行**と推定（約 100 個の定義に保存補題）。K walk の土台（`kwalk`、`FramedNM` の補題、結合子）は再利用できる見込み（読み） | K walk の実績: `Tools/ShippingGen4KWalk*.lean` は **43 ファイル、6262 行、74 commit、commit の日付は 2026-11-03〜11-04**（確認）。それでも (b) は閉じていない。F-kids が K walk より小さい根拠は無い | 低 | 規模の推定は PARAM_INV_ESTIMATE の推測のまま。測った値ではない |
| F-θ | 未着手。小（`dupParams`、`core_symbolic_prologue` が既にある。読み） | 小 | 中 | |
| F-top | 未着手。`ModuleNameCheck.check` の Lean の文が新しく要る | 小 | 中 | |
| F-post | 未着手。`parameters` / name の保存補題 4 本（読み）。F-kids の `ParamFree` 補題を共有 | 小 | 中 | |
| shape（`D` か `D.addModule b` か、`SrcAt`） | 未着手 | 不明 | 低 | |
| assembly | 未着手。F-θ / F-top / F-kids / F-post / shape の後 | 小（`legalBinding_covers` への接着） | 中 | |

**純減が出るまでの距離**: (b) の閉鎖（H11 と `MsgMvK`）の後に、F-kids（K walk と同程度かそれ以上の規模の推定）と、5 つの小〜不明の証明が全部揃う必要がある。(b) から (c) までの間は台帳が今より 1 多い（92）。純減 −1 に届く時期は、この調査では見積もれない。**確かさは低い**。

M4 の経路が副次的に効く可能性（確認していない）: K walk が示す「memo の key ⊆ child cache の key」は、T1 の `T1L-25`（G-MEMO、`CacheShips` が memo を覆わない）の材料になるかもしれない。この調査では読んでいない。確かめれば T1 −1 の見込みが立つかもしれないが、今は数えない。

## 2. 既存 IP の到達分析

### 2.1 「実 IP の全入口」の出どころ（確認）

* **corpus の一覧の出どころ**: `scripts/shipping-coverage/run.sh` の先頭の grep。`Tests`、`IP`、`Examples` の下の `.lean` で、`^#synthesizeVerilog` / `^#writeDesign` / `^#writeVerilogDesign` / `^#synthesizeVerilogDesign` / `^#synthesize ` の行、または `synthesizeCombinational` / `synthesizeHierarchical` を含むファイルを集める。
* この Pod で同じ grep を実行した件数（base b2efa8c0）: **IP 43、Tests 435、Examples 4 ファイル**。`#synthesizeVerilog` は 119 ファイル 301 箇所、`#writeDesign` は 15 ファイル 16 箇所、`#synthesizeVerilogDesign` は 3 ファイル 4 箇所、`#synthesizeParameterizedVerilog` は 1 ファイル 4 箇所。IP の .lean ファイルは全体で 398 個、`hardware_module` の出現は 94 箇所。
* **コンパイラ側の入口**（Elab.lean、確認）: コマンド `#synthesize`（8969）、`#synthesizeVerilog`（8999）、`#synthesizeParameterizedVerilog`（9040）、`#synthesizeDesign`（9136）、`#synthesizeVerilogDesign`（9145）、`#writeDesign`（9324、9332）、`#sim`（9369）。ライブラリ側の呼び出し: `#simChecked`（`SimChecked.lean` 77）、`CoSim.lean` 90、`CostCmd.lean` 59 / 88、`Display/Synthesise.lean` 68 / 83（いずれも `synthesizeCombinational` か `synthesizeHierarchical`）。`#writeVerilogDesign` は Elab.lean の説明コメントにだけ出て、`elab` の定義は見つからなかった。
* **この一覧の限界**: ユーザーが書く任意のプログラムは入口になりうる。「全入口」はリポジトリ内のファイルに限った一覧で、これ以上のものではない。corpus の測定は 1 ファイル 300 秒の timeout で、終わらないファイルと elaborate できないファイル（過去の記録で 23 ファイル）は数えない（`status.txt`）。

### 2.2 測定の意味（確認）

`report.py` は profile log の各行 `synthesizeCombinational <decl> <what>` を宣言名ごとに数える。`certified front end` / `mixed` / `machine` / `MEMO HIT` / `starting`（= legacy）。**子の入れ子の呼び出しも同じ log に出る**ので、「宣言 391 個」には入れ子の宣言も入る。1 つの宣言が certified 系と legacy の両方で走ると certified と数える（`report.py` の分岐）。「legacy only」は legacy の行だけの宣言。この定義は、呼び出し 1 回ごとの経路を数えたものではない。

### 2.3 case ごとの表（測定済み / コードから読める / 未測定）

| case | 測定済み（記録） | コードから読める | 未測定 | 到達するか |
|---|---|---|---|---|
| fallback / legacy 腕（top） | legacy だけの real 宣言 **0 / 391**（gold53、2026-10-08、TrustBase §、Milestones S7）。machine 経路 364 宣言 | 4 経路（certified / mixed / machine / legacy）の分岐は `synthesizeFromConst`（5290-5400）。legacy は他が拒否したときの落ち先 | **現在の tree（b2efa8c0）での再測定**（gold53 は古い SHA。その後コンパイラは変わった） | 記録上は到達しない。再測定が要る |
| legacy 腕（子として） | 上の 0 / 391 に子の宣言も入る（§2.2）。ただし「certified と legacy の両方で走る宣言」は certified に数える | TrustBase に「certified の compile から legacy の handler に届くことがある」と明記（Legacy handlers reached from a certified compile） | 呼び出し 1 回ごとの経路別の件数 | **未決**。0 / 391 は coverage の証明ではないと GeneralTheorem-Audit §4 も書く |
| memo hit（depth 0） | **399 入口で 0 hit**（FinalGoal の記録。どの corpus の測定かは文書に書かれていない） | 各 top の入口で memo を空にする（5540）。depth 0 では hit できない（`outer_miss`、ただし `RefLawsM` が前提） | — | 到達しない（読み） |
| memo hit（入れ子） | 同上の 0 hit | hit は「子の child cache に無く、memo にはある」ときだけ。by-name の循環が要る（docs/parallel/B-memo.md）。K 不変量（memo の key ⊆ child cache の key）がこれを閉じる | 現在の tree での再測定 | **K walk が示そうとしているのが、この unreachable そのもの** |
| parametric | — | 入口は `synthesizeCombinationalWithParameters`（8940）と `#synthesizeParameterizedVerilog`（9040）で、別の関数。翻訳器の中から呼ばれるのは symbolic top の 1 箇所（PARAM_INV_ESTIMATE §2.3）と読んだ | — | grep: `synthesizeParameterizedVerilog` / `WithParameters` を使う .lean は `Tests/SymbolicParameterEmit.lean`、`Tests/VerilogTests.lean`、`Tests/TestCppSim.lean`、`Tests/Gen4/*`、`Tools/ShippingGen4ParamIface.lean`、`Sparkle/Compiler/Elab.lean`。**IP と Examples には 0 件**（確認） |
| 再入 `hno` / `htop` | — | 循環すると depth 上限 1024 で throw（Elab 5465）。ただし `tryInlineUnfold` の catch / retry が入れ子の throw を飲めるので、上限だけでは閉じない（FB_HNO_STUDY §2.3）。直接の自己再帰 1 例は実際に失敗した（観測） | corpus の宣言ごとの `hno` の直接観測（§2.6 の測定 2） | 不明。直接測れる（`hno` は hierarchical が `addModule` の分岐に入ることと同値、FB_HNO_STUDY §2.2） |
| `msgToString` の経路（`MsgMvK`） | — | `handleDefinitionUnfold` の catch の中、`throwError` の直前（6595-6610、確認）。**失敗側の文字列作り**。ただし外側の catch が飲めば、その run は成功しうる | 成功した run でここを通った例があるか | 不明 |

### 2.4 unreachable を示すために何が要るか

| 方式 | 要るもの | 持っているか |
|---|---|---|
| 入口ごとの証明 | IP の入口を有限個の `declName` の一覧にして、各宣言について経路を kernel で確かめる | **machine 経路だけは持っている**: 宣言ごとに生成される `f.machine_sound` 系の endpoint（gold64 で終わったファイルの 367 / 367、TrustBase）。これは宣言ごとの前提 `MachineDefines` で legacy 経路を外す。legacy 経路には、この生成の仕組みが無い |
| 一般の route 判定の定理 | 「入口が X ならこの経路を通らない」という Elab のコード上の定理 | 無い。`Environment` と `IO.Ref` は論理の中で不透明なので、コードの参照グラフを使う定理は書けない（FB_HNO_STUDY §2.3）。K walk は、この判定を walk で示す試み |
| 測定だけ | profile log | 定理にならない |

### 2.5 IP 限定の定理は FG に接続できるか

* FG の scope は「成功したコンパイルの出力は正しい」で、入口の集合に制限が無い（M4_DECISION §1、GENERAL_SPEC §1）。「入口は IP の一覧の中」は、その scope を狭める仮定になる。**承認済みの scope に許された仮定とは読めない**ので、IP 限定の成功定理は FG の一般台帳に**数えない**（読み。接続できるかの最終判断は reviewer / ユーザー）。
* 数えない場合でも、IP 限定の定理には「このリポジトリの設計については legacy / memo / parametric を気にしなくてよい」という使い道がある。ただし、既に宣言ごとの machine endpoint がその役を担っている（§2.4）ので、**新しい価値は小さい**（読み）。

### 2.6 coder が `kjob run` で測る（2 時間で終わらないので、やっていない）

先に `lake build Tests.AllTests` が完了していること、他の `lake build` と並行しないこと（run.sh の注意）。ログはソースツリーの外に置く。

1. **現在の tree で route を呼び出し 1 回ごとに再測定**: `PASSES=1 scripts/shipping-coverage/run.sh WORKDIR`（`SPARKLE_PROFILE=1`）。`profile.log` から宣言ごとに `certified` / `mixed` / `machine` / `MEMO HIT` / `starting` を**呼び出しごと**に数え、「certified と legacy の両方」の宣言の件数を別に出す（`report.py` は混ぜて数える）。見る値: legacy 呼び出しの件数、MEMO HIT の件数、入れ子の legacy の件数。
2. **`hno` の直接測定**: corpus の各 `#synthesizeVerilog` の宣言に対し、scratch の tail（`scripts/shipping-coverage/*_tail.lean.in` と同じ形）で `synthesizeCombinational declName` を走らせ、`design.modules.any (·.name == module.name)` が `false` かを数える（`hno_iff_not_any`）。
3. **parametric の使用**: `grep -rlE "synthesizeParameterizedVerilog|WithParameters" IP Examples` と、`Tests` の使用ファイルが IP の設計を入口にしていないことの確認（確認済みの grep は上のとおり）。

## 3. 別の直接減算の候補

調べた範囲: FG の残り 91 行（束ごと）と T1 の残り 57 行を、`LEDGER_SHORTEN_PLAN2.md` と各台帳の行表で読んだ。**根拠のある候補は 2 つ**。残りの 3 つは「調べる価値がある」止まりで、減算の見込みは不明。

### 3.1 候補 1: A.P-26 + C.CR-1（run 局所の `closingRun0_of_run`、`hord` を取らない版）

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | A.P-26（`hnomem` の名前半分と `hord` の起源半分）、C.CR-1（`hrow`、`closingRun0_of_run` では `hord`）。T1 側は 1 行（T1L-04、除去済み）への多対一 |
| 消える条件 | `hord : ∀ q, DataOk q → q.d.shape.instFields = [] → ∀ k, … child? = none` を仮説に取らない版。run の `RunReadsAt.shapeEq` に `machineShape?_noMemRow`（877c1498）を当てて、その run の `p` だけの `hord` を作る |
| まだ残る条件 | `ClosingRun` の他の前提（C.CR-2 `hGen`、非空虚性、depth0 stop）。コンパイラのゲート（par/hrow-gate の系統）が効く tree での build |
| root theorem | 未命名。`closingRun0_of_run` から `hord` を除いた版（`hT : T1HypND …` と `hrun` から `ClosingRun0`）。型は「全パッケージ上 → この run の `p` だけ」に変わる（意味の変更。reviewer の規則に当たる） |
| 費用（推定） | 小〜中（材料は `closingShared_of_run` の中に揃っている、と LEDGER_NONLEAF_CHECK §1.1 が読んでいる。新しい定理の本体は数十〜数百行の見込みだが、測った値ではない）。**ただし base には材料のファイルが無い**（確認: `ls Tools` に `ShippingGen5ClosingRun2` も `ShippingGen3HrowGate*` も `ShippingGen2T1` も無い）。par/aud-ua4-hrowfree 系を取り込む統合が先に要る |
| 確かさ | 中。型の上の筋は文書で読めているが、Lean で通っていない |
| 新しい TRUSTED / freeze | TRUSTED は不要。freeze は要る（型の変更）。reviewer の承認は要る（run 局所化は意味の変更、非リーフの数え方） |
| 台帳への効果 | 合計 **FG 91 → 89**（非リーフ 29 → 27）。**リーフ 62 は変わらない**。証明の進捗ではなく、重ねて数えていた行の除去（R0 と同種）である点を、報告で必ず書く |

### 3.2 候補 2: A.P-24（`ChildKeepsInv`、`hIH` / `hKI`）

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | A.P-24（B.F-1、C.CR-3、C.AC-8 を統合済みの行） |
| 消える条件 | `ih_allPF`（`Tools/ShippingGen2T1.lean:197`）が `IHAt D ∧ ChildKeepsInv D` を `keepChild_proved`、`keepBody`、`limitStmt_proved` と T1 の行から出す。FG の `hIH` / `hKI`（`closingRun0_of_run`）に差し込む |
| まだ残る条件 | (a) `ih_allPF` は `T1Hyp`（`dec` を含む）を取るが、FG の `closingRun0_of_run` は `dec` の無い `T1HypND` を取る。(b) 差し込む定理が書かれていない。(c) 循環がないことの確認（LEDGER_NONLEAF_CHECK §1.4） |
| root theorem | 未命名（差し込みの定理）。入力は `ih_allPF` |
| 費用（推定） | 中。材料は読めているが、(a) の `dec` の扱いで型の選択がある。base に材料のファイルが無いのは候補 1 と同じ |
| 確かさ | 低〜中（(a) が未決） |
| 新しい TRUSTED / freeze | TRUSTED は不要のはず（`dec` を FG に持ち込む選択をすると、T1L-09 の `dec` の数え方が FG に入る → 台帳の数え方の変更で reviewer）。freeze は要る |
| 台帳への効果 | 合計 −1（非リーフ）。リーフは変わらない |

### 3.3 調べる価値があるが、見込みは不明なもの（減算を約束しない）

| 候補 | 内容 | 見込み | 確かさ | 備考 |
|---|---|---|---|---|
| X3: T1L-25（G-MEMO）を K walk の結果で払えるか | K 不変量が memo miss を与えるなら、T1 の `CacheShips` が覆わない memo の義務に使える可能性 | T1 −1 か 0。**確認していない** | 低 | M4 の (b) が閉じた後の副次効果。単独では起こせない。`T1L-25` は割当なし |
| X4: B.G-9 の `hQ` を P1 以外の道で | B.G-9 は `U-GC1` と P1 接続が通れば −1 の候補。P1 は共有定義を変える `sparkle-gate-p123` と同種で、ユーザーが 2026-11-02 に見送った | −1 か 0 | 低 | P1 を P123 以外で通せるかは「調べていない」（PLAN2 §2.5）。調査は文書のみ |
| X5: C.AC-5（`GatesNoneAt env₀ Reach`） | 割当なし。B-KIT の 3 行のうち 1 行。台帳 §11.4 は、AC-5 / AC-7 / AC-9 の純差分が正になる経路を見つけていない | 0 以下 | 低 | 調べても 0 の可能性が高い |

## 4. 比較と推奨

### 4.1 比較表

| 道 | 台帳への実際の効果 | 費用（推定） | 出口までの距離 | リスク |
|---|---|---|---|---|
| A. M4 を続ける（(b) → (c)） | 途中で +1（92）、全部揃って最終 −1（90）。リーフ・非リーフの区別なく合計 | 大。H11 が 4 回 OOM、`MsgMvK` に経路なし、F-kids は K walk 以上の規模の推定、他に 5 つの未着手 | 長く、時期の見積りなし | `MsgMvK` で TRUSTED の文が増える（reviewer）。途中の +1 が長く残る。H11 の build が原因不明のまま |
| B. IP 限定に切り替える | **一般台帳は 0**（scope を狭める仮定なので数えない、読み）。IP 限定の定理として価値は小さい（machine endpoint が既にその役） | 測定 3 件 + 入口の一覧の定理化。小〜中 | 台帳の出口には届かない | 「IP の一覧」の保守。一覧に無い入口には保証が無い |
| C. 別の行を直接消す（§3.1、§3.2） | 合計 −2（候補 1）、−1（候補 2）。**リーフは減らない** | 小〜中（ただし材料の統合が先） | 近い（M4 より桁で近いと読むが、見積りの根拠は上の推定） | 数え方（非リーフの除去は表示の変更）が reviewer に通らない場合は 0。run 局所化は意味の変更 |

### 4.2 推奨

1. **C を先に進める**: 候補 1（A.P-26 + C.CR-1）を第 1、候補 2（A.P-24）を第 2。freeze は「型の変更（run 局所化）」の 1 本で reviewer に出す（§5）。
2. **M4 は (b) の手前で止める**（`sparkle-gen4-parametric-supply` は todo、解除の条件を書く）。K walk の土台（43 ファイル、6262 行）はそのまま保つ。新しい freeze や条件付き承認を積み増さない。再開の条件: (i) `MsgMvK` の経路が見つかる、または家族の文の追加が承認される、かつ (ii) H11 の build が原因を特定して通る。
3. **B は単独の目標にしない**。測定 3 件（§2.6）の結果は、M4 の再開判断と、IP 向けの説明資料に使う。
4. 注意: 推奨 1 の効果は「重ねて数えていた非リーフの行を外す」ことで、リーフ（証明対象）の 62 は動かない。**「FG が 2 減った」と報告するときは、リーフが動かないことを必ず併記する**。

### 4.3 「現時点では一般定理から支払い不可」の branch

| branch | 理由（この調査で分かったこと） | 代わりの価値 / 別の道 |
|---|---|---|
| M4 (b) 単独 | 純減なし（+1）。`MsgMvK` に経路が見つからなかった。H11 が未 build | K walk の土台は他の M4 部品に残る。止めても失われない |
| `D.E-12` の非 machine 分（`hno` / `htop`） | `hno` は 1c を保留（ユーザー 2026-11-04）で未供給。depth 上限だけでは閉じない。`htop` の legacy 分は circuit state を追う walk（約 1874 行の見積り、FB_HNO_STUDY）。束ねた行なので hno だけでは 0 | IP 限定: §2.6 の測定 2 で `hno` を corpus 上で観測できる（定理ではない） |
| `B.F-8`（legacy の cache shim） | 2c で保留。`ReachesInline` は現行コンパイラでは cacheable な呼び出しで証明できないと契約が書く | 狭い IP 定理: legacy を通らない宣言なら不要（§2.3 の再測定が前提） |
| `D.E-4` | B4 を文のまま残す（ユーザー 3、2026-11-03）。B5 の判断が出ても行は消えない | 範囲の明記（FG 台帳 §12.5）で足りている |
| `B.G-9`、`B.G-1,3-7` | P1 接続は見送り。残りは供給元が見つからなかった | §3.3 の X4（調査のみ） |
| B-ENV（C.EN-1,2,3,5,6,7、C.RK-2,4） | 調査 U-A〜U-F がすべて 0 または見送り | 再開条件: L′ の構成の供給元が見つかる |
| `B.P-5`（`SpecSuccessAllPositive`）、`C.EN-8` | TRUST の行で、範囲の縮小になる扱い（禁止）。ユーザー判断 D3 の回答は記録で見つからなかった | 証明では消えない行 |
| `A.P-27` / `A.P-28`（非空虚性の監査） | 非空虚な `Laws` の値、具体 run の供給元が見つからなかった | 宣言単位の witness が作れれば IP 限定の価値はあるが、一般の行は消えない |
| IP 限定の unreachable 定理（memo / parametric / legacy） | FG の scope を狭める仮定になる（読み） | 一般台帳に数えず、IP 向けの説明に使う |

### 4.4 ユーザー判断が要る点（判断資料）

この資料自体が判断資料。判断は 1 つ:「M4 の実装を (b) の手前で止め、§3 の 2 候補へ移るか」。

| 項目 | 内容 |
|---|---|
| 前提知識なしの説明 | 一般定理の前提の数 91 を減らす道が 3 つある。M4 を最後まで続けると最終的に 1 つ減るが、途中で 1 つ増え、終わりが遠い。別の道は、重ねて数えていた行を外すことで、近い。ただし後者はリーフを減らさない |
| 影響（止まる後続） | 止める場合: `sparkle-gen4-parametric-supply`、`sparkle-gen4-fallback-supply`（どちらも todo）。M3 と M5 は止まらない |
| 選択肢と影響・費用 | A（M4 を続ける）: 費用大、台帳 +1 → −1。B（IP 限定）: 台帳 0、費用小〜中。C（別の行）: 台帳 −2 / −1（非リーフ）、費用小〜中。推奨は C を先、M4 は止める |
| 推奨と理由 | C。近く、新しい TRUSTED を要しない。M4 は `MsgMvK` と H11 の 2 つの詰まりがあり、終わりに見積りが無い |
| 後から変えられるか | 変えられる。M4 の土台と部品は残り、再開の条件は §4.2 に書いた |
| 判断しない場合 | 現状のまま。`sparkle-gen4-*` が停止、C は reviewer の承認を待つ。台帳 91 / 57 のまま |

## 5. reviewer に回すもの（TRUSTED・freeze 境界・scope の変更だけ）

1. **`MsgMvK` の扱い**: 家族に文を足す（memo 版の `OkMsg` と `excOk`）か、仮説のまま M4 を止めるか。TRUSTED 境界の文。M4 を再開するときの判断。
2. **候補 1 の型の変更**: `closingRun0_of_run` を「全パッケージ上の `hord`」から「この run の `p` だけ」にする。意味の変更。freeze は reviewer の番。
3. **候補 1 / 2 の数え方**: 非リーフの行を、材料が揃った時点で除くこと（A.P-22 の §12.7 と同じ種類）。リーフは動かない。
4. **候補 2 の `T1Hyp` と `T1HypND`**: `dec` を FG に持ち込むか。持ち込むなら T1L-09 の数え方が FG に入る。
5. **IP 限定の定理の位置づけ**: FG の scope を狭める仮定として、一般台帳には数えない、という読み（§2.5）の確認。ユーザー方針 1 の確認でもある。
6. **MemoFamily freeze rev3 の保留**: Diag と窓の文（13〜14 文）。M4 を止めるなら、この承認も保留でよいか。台帳は動かない。

## 6. この資料のためにしたこと（確認）

* 読んだ: PREMISE_LEDGER（FG §12 まで、T1 の行表）、LEDGER_SHORTEN_PLAN2.md、M4_DECISION.md、M4_CONSULT_2026-11-04.md、KWALK_PLAN.md、PARAM_INV_ESTIMATE.md、PARAMETRIC_SPECSUCCESS_DECISION.md、FB_RESUME_STUDY.md、FB_HNO_STUDY.md、LEDGER_NONLEAF_CHECK.md（par/ledger-nonleaf）、MEMO_FAMILY_FREEZE.md の該当部、docs の TrustBase / Coverage / GeneralTheorem-Audit / FinalGoal / parallel/B-memo.md、scripts/shipping-coverage/run.sh、report.py、endpoints.sh。
* 実行した: `grep`、`ls`、`wc`、`git log`（Pod 内、読み取りのみ）。Lean の build と corpus の測定は**していない**。
* 読めなかった / 読んでいない: 指示にある `scripts/gen4/FB_*_STUDY.md` は base（b2efa8c0）に存在しなかった（`ls` で確認）。`FB_RESUME_STUDY.md` と `FB_HNO_STUDY.md` は branch（kjob/rt150、kjob/rt156）から `git show` で読んだ。`MEMO_FAMILY_FREEZE.md` と `KWALK_PLAN.md` は全文ではなく該当部だけ。`scripts/gen5` は base に無かった（この資料で新規）。

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）
