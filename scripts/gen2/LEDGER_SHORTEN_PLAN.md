# 台帳の短縮計画（2026-11-02、coder。文書のみ）

出発点: FG 103 / T1 56（受入済み）。U1（C.RT-1/3/4）は設計承認済みで、Check の受理待ち（受理すると FG 100）。
数えた元:
- FG 台帳 `scripts/gen2/PREMISE_LEDGER.md` @par/fg-ledger-sync 44889946: §8.2 の 110 行表、§9.1・§12・§12.1 の解消記録。
- T1 台帳 `scripts/gen3/PREMISE_LEDGER.md` @par/t1-ledger-sync 33b4edb0: §3 の 71 行、§7、§12・§12.1・§12.2。
- 行の分類は、台帳自身の区分（§8.1 の CTX / ANT / TY / UN / T1 / PA / AU / XC）と、台帳本文に書かれた「止まっている理由」の文言から機械的にまとめた。

この文書は計画である。ここに書いた −n はすべて見込みで、受理されるまで台帳の数は変えない。

## 1. 行の数は証明の数ではない（FG 103 の内訳）

FG の現在値は、§8.2 の 110 行表のうち未解消の行数として定義されている（§2）。
この 110 行には、FG 側で証明する必要のない行が 31 行含まれている。

| 区分 | 行数 | 台帳 ID | 証明が要るか |
|---|---|---|---|
| T1 と同じ前提（T1 区分） | 16 | A.P-07, 08, 09, 10, 11, 12, 14, 15, 16, 19, 22, 23, 24, 25, 26, C.CR-1 | FG 側では要らない。T1 台帳の行が解ければ一緒に消える。§8.1 自身が「文に入れない（二重に数えない）」としている。A.P-24 は T1 側で解決済み（keepChild_proved）なのに FG の現在値には残っている |
| 派生行（PA。リーフから組み立てる行） | 7 | A.P-13, A.P-17, C.CR-4, C.SM-5, C.SM-7, D.T-2, D.D-8 | 個別の証明は要らない。リーフが消えれば組み立てで出る。C.SM-5 の材料（C.SM-3 / C.SM-4）は解消済みなので、今すぐ消せる候補 |
| 監査項目（AU） | 2 | A.P-27, A.P-28 | 前提ではない（非空虚性の Check 項目） |
| 文から除いた行（XC） | 3 | A.P-21（廃止）, B.G-10, D.E-13（保証の外の printer） | 前提ではない |
| 文の文脈・前件（CTX / ANT） | 3 | A.P-01 Laws, A.P-02 Start, A.P-04 run | 定理の入力。消す対象ではない（Laws は TRUSTED 境界、T1L-01/02 と共有） |
| **FG 側で証明が要るリーフ** | **72** | §2 | TY 7 + UN 69 − 解消 6（C.SM-2/3/4, C.AC-2/3, C.CV-1）+ 追加 2（SigTyClosed, InstSFieldsDet） |

**数え方の提案（R0）。** 現在値を「FG リーフ 72」と「T1 共有・派生・監査・除外・入力 31」に分けて表示する。
- これは表示の重複除去であって、証明の進捗ではない。T1 共有の 16 行は T1 台帳の行として残り、そちらで数える。
- 数え方の変更なので reviewer の承認が要る。月ごとの進捗の比較は、新旧両方の数で出す。
- 承認されれば、表示上 FG 103 → 72（U1 受理後 69）。証明で減った数としては数えない。

## 2. FG リーフ 72 行の束（同じ証明・同じ型の固定でまとめて動く単位）

| 束 | 行数 | 台帳 ID | まとめられる根拠（台帳本文の文言） | 動かす単位と実作業 Issue | 証明後に消える数（見込み） | 増える前提（見込み） | 依存 |
|---|---|---|---|---|---|---|---|
| **B-RT** reader 状態・被覆 | 15 | C.RT-1〜4, C.CV-2, CV-3, CV-5, CV-6, C.RK-8, C.DO-2, DO-3, C.DG-1, C.SM-1, C.SM-6, C.AC-4 | 「reader state st is run-local」「reader-internal induction data」。同じ readF の trace 不変量と同じ machineShapeF の run から出る | U1（RT-1/3/4、sparkle-rt-u1）→ U2（RT-2, CV-2, CV-3、sparkle-rt-u2-compose。葉: rt-kdof, rt-samest, rt-inline-compose）→ CV-5 / CV-6 / RK-8（reader 完全性）→ 被覆（DG-1, SM-6, AC-4, SM-1） | U1 −3、U2 −3、その後 −9 | U2 +4（N1-a, N2-b, N3-b ×2）、inline 枝で RecRulePh +1、S2 は fuel 化（ユーザー判断 A）なので +0 | U1 受理、inline 合成、S2（rt40） |
| **B-ENV** 2 本目の Laws と共有環境 C0 | 8 | C.EN-1, 2, 3, 5, 6, 7, C.RK-2, C.RK-4 | 6 行に同じ文言「second Laws `L'` / `env₀` / per-run variables not fixed」。1 本の freeze で `L'` と `env₀` の閉包を固定すれば、6 行の型が同時に決まる | sparkle-gen5-dg-env（todo）。まず carrier 固定の freeze（新規探索 Issue、§4） | 型の固定だけでは 0。その後の証明で最大 −8 | 未確定（固定の freeze で決まる） | なし（並行可） |
| **B-KIT** GenData-kit の carrier | 3 | C.AC-5, AC-7, AC-9 | 「kit K / Reach carrier not fixed」。C.AC-2/3 は同じ kit で解消済み（CKIT 4bc671dd） | sparkle-gen5-dg-kit の続き | −3 | 0 見込み | C.AC-4（B-RT 被覆）と同じ carrier |
| **B-AUD** 境界監査の call-graph carrier | 10 | D.E-1〜9, D.E-12 | 9 行に同じ文言「call-graph carriers g, ds, S not fixed」。1 本の carrier 固定で 9 行の型が決まる | sparkle-gen5-dg-audit（todo）。まず carrier 固定の freeze（新規探索 Issue、§4） | 型の固定だけでは 0。その後最大 −10 | D.E-4 の B5 はユーザー判断の可能性 | なし（並行可） |
| **B-GATE** gate 経路の ReflectsAll | 8 | B.G-1, 3, 4, 5, 6, 7, 9, D.D-1 | 「component of ReflectsAll (gate route)」。同じ carrier の成分 | sparkle-gen4-gate-supply（todo、台帳待ちで停止中） | −8 | 未確定 | なし |
| **B-PARAM** parametric 経路 | 7 | B.P-1, 2, 3, 4, 7, 8, A.P-05 | 「closure needs the route guard and θ := parameters」 | sparkle-gen4-parametric-supply（todo、停止中） | −7 | B.P-4 は production↔model の橋（B1〜B4）で、仮定が増える可能性 | B.P-5 のユーザー判断（D3） |
| **B-GEN** generator / call / closing の残り | 13 | A.P-06, A.P-18, C.CR-2, C.RR-2, B.F-4, B.F-8, C.RK-7, D.T-1, D.T-4, D.D-3, D.D-4, D.D-5, D.D-7 | 共通の carrier はない。行ごとに別の証明 | 行ごと（dg-closingrun, dg-declconnect, dg-pkgassign ほか） | 個別に −1 ずつ | 個別 | 個別 |
| **TRUST** 信頼境界・ユーザー判断 | 8 | C.EN-4 CellPrem, C.RK-1 ReadKeeps, C.RK-6 ReflExprAgree, C.CV-4 ShapeFuelBridge（= T1L-43）, C.EN-8, B.P-5, SigTyClosed, InstSFieldsDet | 型付きの閉じた命題（TY-O）か、ユーザー判断（UN-U）、または C0 の名前付き条件 | 証明では消えない。TRUSTED として置くか、ユーザー判断 | 0（TRUSTED への移動は、N3 の裁定どおり行を残す） | 0 | ユーザー判断 |

合計 15 + 8 + 3 + 10 + 8 + 7 + 13 + 8 = 72。

**読み:**
- まとめて型が決まる束は 3 つある。B-ENV（6 行が 1 本の固定）、B-AUD（9 行が 1 本の固定）、B-KIT（3 行が既存の kit）。
- この 3 束（21 行）は、型の固定が先で、証明は行ごとの小さな単位に分けられる見込み。
- 個別に証明が要るのは B-GEN の 13 行。
- 証明では消えないのは TRUST の 8 行。

## 3. T1 56 の束

| 束 | 行数 | 台帳 ID | 扱い |
|---|---|---|---|
| 入力・TRUSTED・監査 | 6 | T1L-01 Laws, 02 Start, 41 i₀, 69, 70, 71（監査） | 消す対象ではない（監査 3 は前提ではない） |
| C++ / core の振る舞い仮定 | 10 | T1L-50 LiftAgrees, 51 Inst1Agrees, 53 EnvTypesFVarFree, 55 LiftAgrees0, 56 LowerAgreesEq, 57 BetaRange, 72 EqvAtom, 73 ReplaceAgrees, 74 HeadBetaAgrees0, 43 OSH（= C.CV-4） | 方針どおり小さな明示的仮定として残す。消えるのは、モデルの全域化で置き換えられたときだけ |
| step の場合分け | 6 | T1L-14〜19 | sparkle-gen2-step。G0 / G1 / C5S / case X は同じ StepStmtCases の 4 腕 |
| 行（rows） | 3 | T1L-04, 11, 12（13 は 12 と同一） | DataOk の束。ユーザーは今回「DataOk 強化」を選ばなかった |
| REACH / cache | 3 | T1L-21, 23, 25 | 20 / 22 / 24 は U18 で解消済み。同じ harness の残り |
| mem / call | 2 | T1L-26, 27 | G-MEMCALLS / G-DATA-CALL |
| DS（データ形状） | 10 | T1L-29, 30（31 は統合）, 32〜39 | sparkle-gen3-data-supply の続き（40 は K1 で解消済み） |
| kinding / env | 7 | T1L-42, 44, 45, 46, 48, 49, 06 | 06 / 42 / 48 / 49 は FG 側が払う |
| U-R9 | 9 | T1L-60〜68 | reader 側（B-RT と同じ readF の run）。U2 の後に再読する |

注: 合計 6 + 10 + 6 + 3 + 3 + 2 + 10 + 7 + 9 = 56。T1 の束ごとの数は、§7 の数え方（親 7 行と統合 2 件を除く）と、§12 以降の解消を当てたもの。T1L-03 / 05 / 07 / 08 / 09 / 10 / 47 は親行なので数えない。

## 4. 並行して着手する探索 Issue（受入とは分ける）

状態は doing のまま、note に「段階: 条件付き」と必須行を書く（manager-conditional-progress の仕様）。sorry を含むもの、仮定付きのものは、受入・台帳の減算に数えない。

| 新規 Issue | worker | 内容 | 出力（次の検証可能な成果） | 重複しない理由 |
|---|---|---|---|---|
| sparkle-ledger-r0 | rt49（-c 2） | R0（§1 の数え方）の freeze。31 行の行ごとの根拠、C.SM-5 の即時除去の根拠 | freeze md（reviewer 承認待ち）。承認されれば表示が 72 / 69 | 文書だけで、他の Issue と触るファイルが別 |
| sparkle-env-carrier | rt50（-c 2） | B-ENV の carrier 固定の freeze。`L'`・`env₀`・per-run 変数の閉包を 1 つ決め、C.EN-1/2/3/5/6/7 の完全型を書く | freeze md + scratch の elaborate（6 行の型） | DG-ENV（todo）を探索として開くだけで、reader 系とはファイルが別 |
| sparkle-audit-carrier | rt51（-c 2） | B-AUD の carrier 固定の freeze。g / ds / S を 1 つ決め、D.E-1〜9 の完全型を書く | freeze md + scratch の elaborate（9 行の型） | dg-audit（todo）を探索として開くだけ |

すでに動いているもの（重複起動しない）:
- rt40: S2 の全域化（sparkle-rt-pass-total）。
- rt43: U1 Check の修正。
- rt44: inline 合成。
- rt45: U2 の freeze と skeleton。
- rt46: kDOf の補題。
- rt47: samest の補題。
- rt48: RecRulePh の freeze。

## 5. クリティカルパスの 3 束と「純減 0 なら止める」規則の例外

選んだ 3 束: **B-RT**（進行中、最大 −15、U1 だけで −3）、**B-ENV**（6 行が 1 本の固定に依存）、**B-AUD**（9 行が 1 本の固定に依存）。
B-ENV と B-AUD の最初の単位（carrier 固定の freeze）は、単体では純減 0 になる。

**例外の条件の提案（E0）。** 純減 0 の単位は、次の 4 つをすべて満たすときだけ続けてよい。
1. その単位の出力（型・carrier・定理名）を、後続の単位がそのまま使う。後続の単位を Issue として先に登録し、依存を張る。
2. 後続で消える行の ID と、見込みの純差分を、単位の note に書く（「解除:」行と「条件付き台帳:」行）。
3. 後続の最初の 1 単位の freeze を、この単位の受理から 1 往復以内に出す。出せなければ止めて、理由を記録する。
4. 新しい前提が増えるなら、その数を後続の減算見込みと並べて書く。後続の減算見込みが増分以下なら、例外にしない。

## 6. 並列数の実測と担当

- **測定（2026-11-02 23:3x UTC、`kjob -N sparkle-dev ls`）:** agent 7（rt40, 43〜48、各 -c 6）と build 1（-c 8）が同時に ACTIVE、QUEUED 0。予約は約 50 / 60 core（12 + 32 + 16）。
- **これまでの実測:** cold build は 14〜59 分（キャッシュの鍵が変わると、797 jobs をすべてビルドする）。cached target build は数分。corpus 測定は 28 分（並列 3）。
- **決め方:**
  - 文書と freeze だけの worker は -c 2 -m 8Gi で 3 つ足す（rt49〜51、合計約 56 / 60）。
  - Lean を書く worker は、今の 7 を上限にする。どれかが終わったら次を足す。
  - clean build は coder が 1 本ずつ投げる。worktree と .lake は worker ごとに分ける。

## 7. 束ごとの次の検証可能な成果と、未解決のリスク

| 束 | 次の検証可能な成果 | 未解決のリスク |
|---|---|---|
| B-RT | U1 Check（WATCH を完全修飾名で照合）の受理で FG −3。U2 の freeze 承認 | inline 枝が S2（fuel の上限値を IP で実測）と RecRulePh に依存する。U2 は +4 を伴う |
| B-ENV | carrier 固定の freeze と、6 行の型の elaborate | 2 本目の Laws `L'` が実際の run で取れるか、この調査では未確認 |
| B-AUD | carrier 固定の freeze と、9 行の型の elaborate | D.E-4 の B5 がユーザー判断になる可能性 |
| B-KIT | C.AC-5/7/9 の freeze（既存 kit の上で） | C.AC-4（被覆）と carrier を共有するので、B-RT の被覆の後になる |
| B-GATE / B-PARAM | 停止中。再開は、上の 3 束のどれかの受理後 | B.P-4 の橋（production↔model）で仮定が増える可能性 |
| B-GEN | 行ごと。今は着手しない | 行ごとに別の証明が要る |
| TRUST | 消さない。表示を分ける（R0） | — |
| R0 | reviewer の承認で、表示上 FG 72（U1 後 69） | 数え方の変更なので、月次の比較は新旧両方で出す |

## 8. 月単位で見るための記録

各 Issue の note に、次の行を必ず書く。
- `台帳: FG n / T1 m（今回 …）`（受入済みの数）
- `条件付き台帳: …`（条件付きの成果が受理されたときの見込み）
- 束の名前（B-RT など）

manager の「前提台帳の残り」は受入済みの数だけから読まれ、条件付きは別の系列になる（manager-conditional-progress）。
