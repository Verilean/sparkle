# 判断資料: 前提台帳の「実 run で払えない」行をどう扱うか

- Issue: `sparkle-premise-nopay`（親 `sparkle-fg-final`）。agent `nopay2`（初版）、`nopay3`（本改訂: §0.1 平易な比較、§4.4 N3 範囲監査、§4.3・§8 の書き換え）。branch `kjob/nopay3`（base `kjob/nopay2` 9c036525、元は `par/gen2-spec` d0ddc50b）。文書のみ。Lean・build・共有定義・compiler の編集はしていない。
- 状態: **ユーザー判断待ち**。この資料は新しい TRUSTED・保証変更・FG の縮小を**推奨として書くだけ**で、実施していない。
- 読んだ材料（`git show <branch>:<path>` で読んだ。checkout / merge していない）:
  - T1 前提台帳: `kjob/t1-ledger-int` が指す承認済み版のうち、依頼文が指定した 51ebec20 の `scripts/gen3/PREMISE_LEDGER.md`（行 41 は非 Prop の入力に再分類済み）。
  - FG 前提台帳: 8fd85e5d + §10（b54e343d）の `scripts/gen2/PREMISE_LEDGER.md` と `premise_ledger/A_M2.md, B_M4.md, C_M5dg.md, D_M5t2.md`。
  - 周辺: `scripts/gen2/GEN2_DEFS.lean.txt`、`scripts/gen2/GENERAL_SPEC.md` §1.2 / §5、`Tools/ShippingChildInvA.lean:255-334`（`RefLawsAOps` / `RefLawsATele`）、`kjob/g2tc-ptop21` の `TOP_CTRL_FREEZE.md` §19、`kjob/g3aw-a24` の `Tools/ShippingLetsExternSpec.lean` と `SRC_ARGW_B3_R9_FREEZE.md`、`kjob/g5ba-r11` の `scripts/gen5/BOUNDARY_AUDIT_FREEZE.md`。
- 台帳の現在値: **FG 104 / T1 57**（Issue の note と依頼文の 2026-11-01 時点の値。今回この値は数え直していない）。初版の本文にある「FG 107 / T1 58」は初版時点の値。この資料は台帳の行を増減させない（今回 FG -0 +0 / T1 -0 +0）。台帳 ID の版: 依頼文の版（T1 51ebec20、FG b54e343d）を正として読んだ。`kjob/t1-ledger-int` 先端 907d1c1d とは §7 の 1 行と §11 の文言に差があった（`diff` で見た範囲。§7 の件数表は同じ）。`kjob/fg-ledger-int` 先端 f2e4b379 とは差分（284 行）があり、全文は読み比べていない。先端の版を使うかは reviewer の確認事項。
- 書き方の規則: 「見つからなかった」は「この調査で辿った候補経路では未供給」の意味で、不可能・導出不能の主張ではない。mutant（棄却）は signature / defeq での棄却で、意味的反例ではない。数えていない数は書かない。見積もりは**工数の数値を書かない**（根拠になる数えた量だけを書く）。

## 0. 先に結論（一覧）

判断が要る行は 4 本に整理できる（台帳 11 行 + FG 側の対応 + FG の TRUSTED 候補）。

| 項目 | まとめた台帳 ID | 推奨 | 新 TRUSTED / 保証変更を伴うか |
|---|---|---|---|
| **N1 `Laws`（実行時の法則 G5）** | T1L-01 = A.P-01（B.F-3, D.E-10 を統合済み） | (2) TRUSTED。ただし 14 フィールドを名前付きで列挙し、非空虚性（N2）の監査を別単位で続けることが条件 | 伴う（ユーザー未承認の新しい TRUSTED 境界） |
| **N2 非空虚な `Laws`（監査項目）** | T1L-69 = FG 監査 N1（FG §8.5）。関連: T1L-70, T1L-71, A.P-28 | TRUSTED にしない。仮説にも入れない。監査項目として残し、持ち主を決める（(1) の経路: 非空虚な `Laws` の構成） | 伴わない（現状維持） |
| **N3 C++ extern / `partial` との一致 9 行** | T1L-50, 51, 52, 54, 55, 56, 57, 58, 59（FG 側に対応する行はこの調査では見つからなかった） | (2) TRUSTED。件数は 9 のまま、文面を呼び出し範囲・証明が実際に使う形に絞った原文（§4.4）を、`lean-toolchain` の版に紐づけて名前付きで列挙。並行して差分テストを運用上の緩和策にする。絞る作業は新しい Lean の単位（reviewer の freeze が先）。長期は (1)（reader の置き換え）を別途検討 | 伴う（新 TRUSTED） |
| **N4 G7-c 印字（printer）** | D.E-13（FG のみ。T1 に対応行なし） | (2) 既存の位置づけを維持（GENERAL_SPEC §5 M5 が「G7 is TRUSTED and stated」と既に書く）。保証が「`checkedOptimize b` の `runModuleTG` まで」であることを最終保証の文面に明記 | 新規なし（既存の宣言の確認のみ） |

判断しないと止まるもの（台帳が名前を挙げている Issue。網羅ではない）: `sparkle-gen3-src-argw`（N3: U-R9 以降の供給）、`sparkle-gen2-top-contract`（N2: 一時停止中）、`sparkle-gen5-boundary-audit`（N1 / N4）、`sparkle-gen3-t1-assembly` / `sparkle-fg-final`（最終定理の文面。N1 / N3 の置き場所が決まらないと前提リストを閉じられない）。

## 0.1 平易な比較（reviewer と相談した結論）

**ひとことで**: N1・N2・N4 は reviewer も上の推奨どおりで良いと同意した。N3 は「9 件まとめて TRUSTED」ではなく、9 件を 1 件ずつ監査した結果（§4.4）に従い、件数は 9 のまま、呼び出し範囲・証明が実際に使う形に絞った原文を TRUSTED 候補にする（絞る作業は新しい Lean の単位で、reviewer の freeze が先）。

注意: この調査で辿った候補経路では、9 件が届く先は `ReadTyped` の 4 要素のうち `MemSrcKinds` だけで、残り 3 要素と `argWidthAt_of_closingRun` までの組み立ては未確認。9 件を TRUSTED にしても T1 が閉じるとは限らない（§4.4 末尾）。

読み方: 「信頼」は、証明せずに「正しい」と置く前提。偽だと、その上の定理は「偽の仮定の下の定理」になり、保証の根拠がなくなる（それだけで出力回路が必ず誤るわけではないが、正しさの根拠は無い）。「証明」は信頼が減るが手間がかかる。「文面変更」は前提の数を減らさず、利用者に見える書き方を変える。

| 項目 | 選ぶと | 得るもの | 失うもの・新たに信頼するもの | 誤った回路の可能性 | 後から変えられるか |
|---|---|---|---|---|---|
| **N1 `Laws`**（Lean 本体の実行の約束事 14 個） | 証明する | 信頼が減る。FG / T1 の `L` 前提が消える | 14 法則を成り立たせる非空虚な `Laws` と、Lean 本体の IO 等のモデルの構成が要る。供給経路はこの調査で辿った範囲では未供給。後続の Issue が長く止まる。モデルが実際の Lean とずれれば別物の保証になる | 証明できれば根拠は強い。モデルの妥当性が新たな信頼対象 | 証明が済めば TRUSTED は不要になる。途中で止めて TRUSTED に切り替えることもできる（signature は変わらない） |
| | TRUSTED にする（推奨・条件付き） | 早く進む。`GENERAL_SPEC` §5 M5 が許す形 | Lean 本体（`lean-toolchain` の固定版）の挙動が 14 法則どおりだと信頼する。過去に旧 `RefLaws.frame` が反証された前例がある | 偽なら定理の根拠が無くなる。回路が必ず誤るとは言えない。Lean の版更新時に再確認が要る | 後でモデルが得られれば TRUSTED を外せる（保証が強くなる方向）。signature は変わらない |
| | 文面だけ変える | すぐできる。条件が利用者に明確 | 前提の数は減らない（14 個を並べる、または `∃ w, quiet w` を足すだけ） | 変わらない | 容易 |
| **N2 非空虚な `Laws`**（「法則を満たす値が実在する」という確認） | 非空虚な `Laws` を構成する | 定理が空（前件が一度も成り立たない）でないと分かる | N1 の証明と同じモデルが要る。N1 を TRUSTED にすると、この経路は別の単位として残る | 空虚性そのものは誤った回路を出さない（定理が何も言わないだけ）。「証明済み」と読み違える運用リスク | 構成できた時点で文面の注記を消せる |
| | 存在を TRUSTED にする（非推奨） | 形の上では前提が閉じる | 「存在する」と信じるだけで偽でも検出できず、監査の目的を自分で無効にする | 検出手段が無い | 容易だが意味が無い |
| | 「非空虚性は未確認」と明記し、持ち主を決める（推奨） | すぐ透明になる | 保証の強さは上がらない。持ち主（`sparkle-gen2-top-contract` の再開か後継）を決める手間 | 変わらない | 容易（文面の追記）。構成できたら外す |
| **N3 Lean 本体の関数との一致 9 件** | 証明する、または reader を仕様モデルに置き換える | 信頼が減る。置き換えれば 9 件のうち該当分が前提から消える候補 | コンパイラ（reader）の変更が要る（現在は禁止、別途承認）。置換後は、モデルと本体が食い違う入力で出力回路が変わりうる。差分テストが要る。個々の extern を Lean 内で展開する経路は、この調査で辿った範囲では未供給 | 置き換えた場合は、食い違う入力で別の回路が出うる（回帰リスク） | 置き換えた reader を元に戻すには再び変更が要る |
| | TRUSTED にする（推奨・絞った原文） | 進む。署名（signature）は変わらない | Lean 本体の `liftLooseBVars` 等がモデル / 仕様どおりだと信頼する。誤りなら、引数幅の保証の根拠が無くなる。Lean の版固定が要る | 偽でも回路が必ず誤るとは言えない。実際に誤る場合の分析はしていない。差分テストが緩和策（証明ではない） | 後で置き換えが済んだ行は外せる。signature は変わらない |
| | 前提として見える化する、または保証を縮める | 利用者に透明 | 前提は消えない。保証を縮めると対象回路が狭まる（FG の縮小で、ユーザー承認が要る。推奨しない） | 縮めると保証対象の回路が減る | 見える化は容易、縮小は戻しにくい |
| **N4 印字器（printer）** | 印字の意味保存を証明する | 出力の Verilog 文字列まで保証が及ぶ | 大きな単位（経路はこの調査では未確認） | 証明できれば減る | 後から TRUSTED を外せる |
| | 既存の TRUSTED を維持（推奨） | 新規の信頼なし（`GENERAL_SPEC` §5 M5 が既に宣言） | 印字器を信頼する。印字器のバグがあれば Lean 内で証明した設計と出力文字列が食い違いうる | Verilog との不一致は保証の対象外。parse-back は検査（証明ではない） | 証明が得られれば外せる |
| | 保証範囲を明記する（推奨・併用） | 「`checkedOptimize b` の `runModuleTG` まで」と読めるので誤読を防ぐ | 保証の範囲は広がらない | 変わらない | 容易 |

## 1. 用語（前提知識なしで読むための説明）

- **FG / T1**: FG は最終目標の定理（Lean で書かれた回路記述をコンパイラが回路へ変換する、その成功した実行ごとに「出てくる回路が仕様どおり」と言う保証）。T1 はその中間定理（階層を持つ設計についての定理）。どちらも「前提」を持つ。
- **前提台帳**: FG / T1 の定理が仮定として取っている項目（binder や、未証明のまま残している命題）を 1 行ずつ数えた表。「実 run で払える」は、「コンパイラを実際に走らせた成功実行の事実から、承認済みの補題でその前提を導ける」の意味。「いいえ」は「走らせても得られない種類の前提」（この調査では、実行の事実ではなく Lean 本体の実装についての主張）。**「いいえ」は不可能という意味ではない。** 別の手段（Lean での証明、信頼の宣言）で成立させる余地がある。
- **TRUSTED**: Lean で証明せず、「これは成り立つものとして信頼する」と明示的に宣言した命題。保証の利用者が信頼しなければならないものが増える。増やすのはユーザーの判断事項。
- **`Laws mref cref`**: `structure Laws`（`GEN2_DEFS` §2、`Tools/ShippingGen2Defs.lean:46`）。`O : RefLawsAOps MkRefd mref cref`（`quiet`, `diag`, `frameT`, `excOk`, `frameQ`, `cacheSetQ`, `depthSetQ`, `frame`, `cacheSet`, `depthSet` の 10 フィールド）と `T : RefLawsATele O.quiet mref cref`（`telescope`, `lamTelescope`, `localDecl`, `letDecl` の 4 フィールド）の計 14 フィールド（D.E-10）。内容は、Lean 本体の Meta / Core モナドが使う 2 つの状態参照 `mref` / `cref` を、コンパイラの内部で使う小さなプログラム（診断、例外、`forallTelescopeReducing` など 4 つのテレスコープ関数）が実行したとき、コンパイラの状態（キャッシュ cv・深さ sv・dv など）をどう保つか、という「Lean 本体の実行の約束事」。どの宣言でも同じ（一様）。

## 2. 項目 N1: `Laws`（T1L-01 = A.P-01、統合: B.F-3, D.E-10）

### 2.1 説明
FG も T1 も `∀ L : Laws mref cref` を取る（A.P-01 の「FG/T1 のどの binder に効くか」: F1）。`Laws` は 14 個の命題の束で、Lean 本体が実際にそう動く、という主張を含む。実際の 1 回の実行からは得られない理由: 実行 1 回の結果は「その 1 回で何が起きたか」であって、すべてのプログラム `p` について `endW … p w` の状態がどうなるか、という全称的な法則は、1 回の実行の事実から出てこない（T1 台帳 §3: "a law is not a run fact"）。

履歴上の事実（台帳 A.P-01 / TOP §19.1）: `Laws` の値を 1 つ構成する経路は確認済みだが、それは `quiet := fun _ => False` の `lawsQuietFalse` だけで（各フィールドは `False.elim`）、その `L` では `PbhRunEx L` は偽（`not_pbhRunEx_lawsQuietFalse`）。`quiet` が空でない `Laws` の値、および Lean の IO プリミティブ（`IO.FS.Handle.mk` / `putStrLn` / `flush`。`Diag` の列挙）の `Void IO.RealWorld` 上のモデルは、この調査で辿った候補経路では未供給。旧 `RefLaws.frame` は REFUTED（Gaps §1 G5 行）で、現在の境界の runtime fit と joint satisfiability は OPEN（Gaps row 127）。つまり**法則が過去に誤りだった前例がある**。`GENERAL_SPEC` §5 M5 は G5 を「`Laws` のモデル、または明示的な TRUSTED」と要求している。

### 2.2 選択肢
**(1) 一般定理として証明する**
- 必要なもの: 14 フィールドが成り立つ `Laws` の値（`quiet` が空でないもの）を、Lean 本体の Meta / Core モナドの実行モデルの上で構成すること。`O` の 10 フィールドは `Diag` / `Throws` / `FramedA` を満たす任意の `MetaM` プログラムについての状態保存則、`T` の 4 フィールドは `forallTelescopeReducing` / `lambdaTelescope` / `withLocalDeclD` / `withLetDecl` についての `Keeps` 継続則。`IO.RealWorld` 上のプリミティブのモデルも要る。
- 今ある経路: `RefLawsAOps.quietFalse` / `RefLawsATele.quietFalse`（空虚）だけ。非空虚な値への経路はこの調査で辿った範囲では未供給。フィールドごとの使用トレースも未実施（D.E-10）。
- 見積もりの根拠: 工数は見積もらない。数えた量は、証明対象 14 フィールド、供給経路 0（空虚な 1 例を除く）、モデルが必要なプリミティブの列挙が `Tools/ShippingChildInv.lean:264` の `Diag` にあること、の 3 点。
- 利用者に見える影響: 成功すれば FG / T1 の `L` 前提が消え、信頼するものが減る。
- 誤った回路 / データ損失の可能性: 証明すればなし。ただし**モデルが実際の Lean 本体と違えば**、証明は別物についての保証になる（モデルの妥当性が新たに信頼対象になる）。
- 運用リスク: 大きな単位になり、他の前提（FG の閉じた証明項）を待たせる。コスト: 高い（未見積もり）。

**(2) TRUSTED にする**
- 境界: `Laws mref cref` の 14 フィールドの Prop をそのまま（`Tools/ShippingChildInvA.lean:255-334` の原文）、名前付きで TrustBase に列挙する。「Lean 本体（`lean-toolchain` の固定版）の Meta / Core 実行は、`AdmCtx` で許される文脈の下でこの 14 の法則を満たす」と信頼する。範囲は「全宣言で一様」。
- 信頼すること: 上記が実際の Lean 本体について真であること。旧 `RefLaws.frame` が REFUTED だった前例があるので、**偽である可能性は、過去に実際に起きたこととして**ある。
- 利用者に見える影響: 保証の文面に「Lean 本体の実行法則 14 個を信頼する」が加わる。FG / T1 の signature は変わらない（`L` はすでに binder）。
- 誤った回路を出す可能性: `Laws` が実際の Lean について偽なら、FG の結論は「偽の仮定の下の定理」になり、出力回路が正しいという主張の根拠がなくなる。**偽だと回路が必ず誤る**とは言えない（保証の根拠が無くなるだけ）。条件: Lean の版が変わる、または法則が実際の挙動と合っていない場合。緩和策: `lean-toolchain` の版を TRUSTED の宣言に含める（版が変われば再確認）。非空虚性（N2）の監査を続ける。
- 運用リスク: Lean 更新のたびに再確認が要る。コスト: 小〜中（TrustBase の記述と、14 Prop の Check）。

**(3) 最終目標の書き方を変える**
- `L : Laws` はすでに FG / T1 の明示 binder なので、「全称 `∀ L` の保証」のまま、文書で「`Laws` を満たす `L` についての保証」と書く形が現状。変える案は 2 つ: (a) `Laws` を 14 個に分け、フィールド単位で FG の仮説として並べる（見た目の透明性は上がるが、論理の内容は同じ）、(b) 保証を `∃ w, L.O.quiet w` つき（非空虚）の `L` に限る（binder が 1 つ増える）。いずれも前提の数を減らさない。
- 利用者に見える影響: (a) は signature が長くなる、(b) は N2 を仮説に押し出す。誤った回路の可能性は (2) と同じ（`Laws` が偽なら根拠が無い）。コスト: 小〜中（T1 / FG の文面の書き換えが伴う。共有定義には触れない）。

### 2.3 推奨と理由
**(2) TRUSTED。条件: (i) 14 フィールドの Prop を TrustBase に原文で名前付き列挙、(ii) Lean 版と結び付ける、(iii) N2 の監査を別単位で続けて「この `Laws` は空虚ではない」を示すまで、保証の文面に「非空虚性は未確認」と書く。** 理由: `GENERAL_SPEC` §5 M5 が明示的な TRUSTED を許す形で要求している。(1) は供給経路がこの調査では未供給で大きく、(3) は前提を減らさない。ただし**旧 `RefLaws.frame` の REFUTED の前例**があるため、無条件の TRUSTED は勧めない。
- 後から変えられるか: 変えられる。後で (1) のモデルが得られれば TRUSTED の項目を消す（保証が強くなる方向の変更）。逆に TRUSTED を後から増やす・外す場合、定理の signature は変わらないので既存の証明は影響を受けない。
- 判断しない場合: `Laws` は台帳に「TRUSTED 候補」のまま残る。FG / T1 は「`Laws` を仮定した条件付き定理」のまま完了できず、最終保証の文面を閉じられない（`sparkle-gen5-boundary-audit`, `sparkle-fg-final`, `sparkle-gen3-t1-assembly`）。
- 根拠: `scripts/gen2/GEN2_DEFS.lean.txt` §2、`Tools/ShippingChildInvA.lean:255-334`、T1 台帳 T1L-01（51ebec20）、FG 台帳 A.P-01 / D.E-10（b54e343d）、`kjob/g2tc-ptop21` `TOP_CTRL_FREEZE.md` §19.1、`kjob/g5ba-r11` `BOUNDARY_AUDIT_FREEZE.md`（14 フィールドは CONTRACT 分類で、TRUSTED とは明示されていない。これを TRUSTED とするのが今回のユーザー判断）。

## 3. 項目 N2: 非空虚な `Laws`（T1L-69 = FG 監査 N1）

### 3.1 説明
T1 の段 2 の reviewer 指摘（`managerctl plan history sparkle-gen3-t1-assembly`）で、T1L-69 / 70 / 71 は証明仮説ではなく**非空虚性の監査項目 3 つ**にする方針。T1L-69 は「`∃ w, L.O.quiet w` を持つ `Laws` の値がある」。FG 側は FG §8.5 の N1 が同じ監査で、二重に数えない扱い。必要な理由: `Laws` が `quiet := False` しか許さないなら、FG / T1 の前件が成り立つ run が 1 つも無く、定理は中身が空になる。実 run から払えない理由: これは「ある `L` が存在する」という存在の主張で、1 回の run の事実ではない（T1 台帳: "a law value is not a run fact"）。

関連: T1L-70（`PbhRunEx L` が成り立つ具体 run と前提の同時充足）と T1L-71（`T1Hyp` の住人）、FG の A.P-28（具体 run の存在）。この 3 つは台帳の「実 run で払える」が「不明」で、今回の 11 行には入らない。扱いは §7（振り分け手順）。

### 3.2 選択肢
**(1) 一般定理として証明（非空虚な `Laws` の構成）**: N1 (1) と同じモデルが要る。今ある経路は `lawsQuietFalse`（空虚）のみで、`not_pbhRunEx_lawsQuietFalse` は「その `L` には run が無い」を示すだけ（TOP §19.4: 他の `L` については何も言わない）。N1 (1) が成功すれば同時に N2 が示せる。コスト: N1 (1) に含まれる。
**(2) TRUSTED**: 「非空虚な `Laws` が存在する」を信頼する案。これは新しい**存在の信頼**で、偽でも検出する手段が無く、空虚性の監査という目的を自分で無効にする。**勧めない。**
**(3) 書き方を変える**: 非空虚性を仮説として追加する（`∃ w, L.O.quiet w`）か、保証の文面に「非空虚性は未確認」と書く。前者は binder を足すだけで N2 を解決しない。後者は利用者に正直だが、保証の価値は変わらない。
- 各案の利用者に見える影響: (1) 保証が空でないと分かる。(3) の文面案は「定理は条件が満たされるときだけ意味を持つ」と明示される。誤った回路の可能性: 空虚性自体は誤った回路を出さない（定理が何も言わないだけ）。ただし利用者が「証明済み」と読み違える運用リスクがある。

### 3.3 推奨
**(3) の文面案を今すぐ採り（保証の文書に「非空虚性は未確認」と記す）、監査項目は (1) の経路で `sparkle-gen2-top-contract`（一時停止中）または後継に持ち主を決める。TRUSTED にはしない。** 理由: 存在を信頼しても監査にならない。N1 の (1) が進まない限り (1) も進まないので、持ち主の決定が実質の判断。
- 後から変えられるか: 変えられる（文面の追記だけ）。
- 判断しない場合: 持ち主が決まらない（現状、payer 欄は「paused」「unassigned」）。`sparkle-gen2-top-contract`（P-TOP）は止まったまま。
- 根拠: T1 台帳 §11.8、T1L-69 / 70 / 71、FG §8.5 N1、`kjob/g2tc-ptop21` `TOP_CTRL_FREEZE.md` §19.1 / §19.4（U7 の結果。非空虚な `Laws` の値は未供給）。

## 4. 項目 N3: C++ extern / `partial` 定義との一致 9 行（T1L-50, 51, 52, 54, 55, 56, 57, 58, 59）

### 4.1 説明
SRC-ARGW の U-R9（`Tools/ShippingGen3ArgSupply15.lean` @ kjob/g3aw-a24 8fff703c）の `siteLetOk_structEnv'` が取る binder のうち 9 つ。コンパイラの reader が `let` を含む式を読むとき、Lean 本体の関数（`Expr.liftLooseBVars`, `Expr.instantiate1`, `Expr.lowerLooseBVars`, `Expr.beta`、`rootFloat` など。C++ extern または `partial def`）を呼ぶ。そのため reader が各 `let` 位置で正しい型を持つ（`SiteLetOk`）ことを示すには、これらの関数が Lean 内の仕様モデル（`liftSpec`, `inst1Spec`, `rootFloatS` など）と一致する、という命題が要る。実 run から得られない理由: これは「Lean 本体の 1 つの関数が、全入力についてモデルと一致する」という主張で、run が 1 回通ったという事実は、その run が踏んだ入力でしか確かめていない。Lean の中ではこれらの関数を展開できない（Tools/ShippingLetsExternSpec.lean の LC6 の注記: "Direct unfolding of the externs / `partial def` is unavailable; the correspondence is still UNPROVED (PREMISE)"）。

| 台帳 ID | 命題（`kjob/g3aw-a24` 8fff703c の原文） | 備考 |
|---|---|---|
| T1L-50 | `LiftAgrees := ∀ e, LetOk 0 e = true → e.liftLooseBVars 0 1 = liftSpec e 0 1 ∧ e.liftLooseBVars 1 1 = liftSpec e 1 1` | `(0,1)` と `(1,1)` のみ。LC6 で reader の呼び出し箇所に狭めてある |
| T1L-51 | `Inst1Agrees := ∀ b a, b.instantiate1 a = inst1Spec b a 0` | LC5 から不変 |
| T1L-52 | `RootFloatAgrees := ∀ e, LetOk 0 e = true → rootFloat e = rootFloatS e` | `rootFloatS` は全域モデルで停止は証明済み。残るのは転記の忠実性 |
| T1L-54 | `ZeroLitAgrees`（`Tools/Prototype/PreprocLetOk.lean:143`） | 本体の続きは今回写していない（ledger §5 の注記と同じ。:143 が正本） |
| T1L-55 | `LiftLooseRange := ∀ e s d, LetOk 0 e = true → LetOk 0 (e.liftLooseBVars s d) = true` | 任意の `(s,d)`。T1L-50 は 2 つの組しか固定しない |
| T1L-56 | `LowerLooseRange := ∀ e s d, LetOk 0 e = true → LetOk 0 (e.lowerLooseBVars s d) = true` | 同上 |
| T1L-57 | `BetaRange := ∀ f a, LetOk 0 f = true → LetOk 0 a = true → LetOk 0 (f.beta #[a]) = true` | |
| T1L-58 | `LiftScalarCorr senv := ∀ dom vars e w r, machLiftScalarN senv dom vars e = some (w, r) → ∃ fuel, liftN senv dom vars fuel e = some (w, r)` | 実装と燃料つきモデルの一致 |
| T1L-59 | `BoolMapCorr senv := ∀ dom a wa body r, machBoolMap senv dom a wa body = some r → boolMapModel (machLiftScalarN senv dom [(wa, a)]) dom body = some r` | 同上 |

注意: 個々が C++ extern か `partial def` かは、初版では未確認だった。§4.4 で Lean v4.32.1 のソースと `Sparkle/Compiler` の定義を見て行ごとに確認した（C++ extern: 50, 51, 55, 56。Lean 側の `partial def` に依存: 57。コンパイラ自身の `partial def`: 52, 58, 59。C++ extern を呼ぶコンパイラの `def`: 54）。FG 台帳（A-D）にこの 9 行に対応する行は、この調査では見つからなかった（FG 側には `C.CV-2` の注記に「`Expr.hasLooseBVars` / `liftLooseBVars` は extern で補題が無い」がある程度で、独立の行は無い）。T1L-53（`EnvTypesFVarFree env₀`）は台帳が「不明（kernel fact）」としており、この 9 行には入らない。

R9 freeze が記録している状態: `LiftLooseRange`（任意 `(s,d)`）を `LiftAgrees` から導く補題は無い（`(0,1)`/`(1,1)` だけ固定のため）。`LowerLooseRange`, `BetaRange`, `LiftScalarCorr`, `BoolMapCorr`, `ZeroLitAgrees` の 5 つは「命題そのもの以外に出現が無い」（この調査で辿った候補経路では未供給）。

### 4.2 選択肢
**(1) 一般定理として証明する**
- 範囲: 2 通りの経路。(a) reader が呼ぶ Lean 本体の関数を、証明可能な Lean 内の仕様モデル（`liftSpec`, `inst1Spec`, `rootFloatS` 等）に**置き換える**。置き換えれば一致の前提そのものが不要になり、9 行のうち少なくとも `liftSpec` / `inst1Spec` / `rootFloatS` に紐づく 50, 51, 52 が消える候補になる（残りの行が同じ形で消えるかは未確認）。ただしこれは**生成側（reader / コンパイラ本体）の変更**で、現在の禁止事項（コンパイラ・本番編集）に当たる。(b) 本体の関数そのものの等式を Lean 内で証明する。Lean 本体の extern は展開できないため、この調査で辿った範囲では経路が無い。
- 今ある経路: モデルと「モデルは `LetOk` を保つ」補題（`liftSpec_ok`, `inst1Spec_ok`, `rootFloatS_ok`）は証明済み。欠けているのはモデルと本体の一致のみ。
- 見積もり: 工数は見積もらない。数えた量は、対象 9 行、うち経路が一部ある行 3（50, 51, 52。モデルがある）、命題以外に出現が無い行 5（54, 56, 57, 58, 59）、(s,d) 一般化が要る行 1（55）、の分類（R9 freeze §の表から）。
- 利用者に見える影響: (a) が成功すると 9 行（のうち置換で消える分）が保証の前提から消え、信頼対象が減る。出力回路は、モデルと本体が一致する入力では変わらない。
- 誤った回路の可能性: (a) は reader の実装を変えるので、**モデルが本体とある入力で食い違っていれば、その入力で出力回路が変わりうる**（今動いている設計が、変更後は別の回路を出す）。条件: モデルと本体の不一致。緩和策: 変更前後の差分テスト（検査であって証明ではない）。
- コスト: 高い（reader の変更、再 review、既存の T1 / FG の証明の再接続）。後続の単位に及ぶ。

**(2) TRUSTED にする**
- 境界: 上の表の 9 個の命題を**そのまま**（原文で）、名前付きで列挙する。意味は「`lean-toolchain` の固定版の Lean 本体の C++ / `partial` 実装が、Lean 内の仕様モデルと一致する」。範囲は reader が呼ぶ箇所に狭められた命題（50, 52 は `LetOk 0` 入力、50 は `(0,1)`/`(1,1)` のみ）まで。
- 信頼すること: Lean 本体の `liftLooseBVars` / `instantiate1` / `lowerLooseBVars` / `beta` / `rootFloat` などと、reader の機械関数 `machLiftScalarN` / `machBoolMap` が、書かれたモデルと一致していること。
- 利用者に見える影響: 保証の文面に「Lean 本体の Expr 操作が仕様どおり」が 9 項目加わる。FG / T1 の signature は変わらないか、(3) と合わせれば 1 つの名前つき仮説になる。
- 誤った回路 / データ損失: 一致が偽だと、reader が各 `let` 位置で正しい型を持つ、という根拠が無くなり、**T1 の引数幅の保証が実際の run に対して根拠を失う**。そのとき実際に誤った回路が出るかどうかは、この調査では分析していない。条件: Lean 版更新による挙動変更、またはモデルの転記ミス。緩和策: 版の固定、コーパスでの差分テスト（検査であって証明ではない）。
- 運用リスク: Lean 更新のたびに 9 項目の再確認。コスト: 小〜中。

**(3) 最終目標の書き方を変える**
- 9 行を 1 つの名前付き仮説（例: 「Expr 操作が仕様どおり」）にまとめて、FG / T1 の signature に明示する。論理的には (2) と同じ内容だが、定理の利用者が仮説として見る。または reader の型付けに頼る範囲（引数幅の主張）を狭める案（FG の縮小になるので、ユーザー承認の対象であり、**推奨しない**）。
- 利用者に見える影響: 前者は signature に 1 つ増える（利用者が自力で供給できる種類の前提ではない）。誤った回路の可能性: (2) と同じ。コスト: 中（T1 / FG の文面の書き換え）。

### 4.3 推奨（§4.4 の範囲監査を受けて書き直し）
**(2) TRUSTED。ただし「9 件をそのまま」ではなく、§4.4 末尾の表の 9 件の原文（件数は 9。うち元のまま 2 件、元より弱い・狭い形に差し替える 7 件）を、名前付き・Lean 版つきで列挙する。並行して運用上の緩和として差分テスト。長期の別案として (1)(a)（reader の置き換え。§4.4 の「別の経路」）を別単位で検討する。** 理由: (1)(b) の経路はこの調査で辿った範囲では未供給。(1)(a) は現時点で禁止されているコンパイラ変更を要する。(3) は (2) と論理が同じで、利用者が供給できない仮説を signature に見せるだけ。9 件を元の文面のまま TRUSTED にしない理由: 55・56 は呼び出し範囲より広く、51・52・54・58・59 は証明が使うのが「`LetOk` を保つ」という弱い形だけなので、信頼する内容を減らせる（§4.4）。
- 条件: (i) 絞った文面は新しい Lean の単位で `siteLetOk_structEnv'` などの binder を差し替え、reviewer の freeze を通す（この資料は Lean を書いていない）、(ii) 9 件の原文の確定は、その freeze の後。(iii) 9 件を TRUSTED にしても、`ReadTyped` の残り 3 要素と `argWidthAt_of_closingRun` までの組み立て（この調査で辿った候補経路では未確認）が別に要る。
- 5 行（54, 56, 57, 58, 59）の「命題以外に出現なし」は、いずれも `siteLetOk_structEnv'` の binder として最終的に使われる（54 は `zeroLit_ok`、56・57 は `rawNode_ok`、58・59 は `normNodeRange_structEnv` 経由）ことを §4.4 で辿った。「命題が意図した内容か」の確認は、#4–#9 の原文案が呼び出し箇所と合うことを reviewer が見る作業に置き換わる。
- 後から変えられるか: 変えられる。(1)(a) が実現した行は TRUSTED から外せる。signature は変わらない（(2) の場合）。
- 判断しない場合: 9 行は T1 / FG の前提のまま残る。`sparkle-gen3-src-argw`（U-R9 以降の LK1 / ReadTyped の供給）は「条件付き部品」止まりで、T1 の `argWidthAt_of_closingRun` 経路を完了にできない。
- 根拠: T1 台帳 T1L-50..59 / §5 の 50-60（51ebec20）、`kjob/g3aw-a24` 8fff703c `Tools/ShippingLetsExternSpec.lean` ヘッダ（LC6）、`SRC_ARGW_B3_R9_FREEZE.md`、§4.4 の監査。

### 4.4 範囲監査（reviewer の N3 変更要求への回答。9 命題を 1 件ずつ）

調べ方（読んだもの。ビルドしていない）: 命題と証明は `kjob/g3aw-a24` 8fff703c（`Tools/ShippingLetsExternSpec.lean`、`Tools/ShippingGen3ArgSupply15.lean`、`Tools/Prototype/RawNodeRangeLetOk.lean`、`LiftScalarModelLetOk.lean`、`BoolMapModelLetOk.lean`、`PreprocLetOk.lean`）。コンパイラ側の呼び出しは本ブランチ 9c036525 の `Sparkle/Compiler/MachRawSurface.lean` と `Elab.lean`（`git diff 8fff703c 9c036525 -- Sparkle/Compiler` は空なので、行番号は両方で同じ）。Lean 本体は `lean-toolchain` v4.32.1 の `Lean/Expr.lean` と `Lean/Util/ReplaceExpr.lean`。命題の経路の説明に出す「使う補題」は、すべて 8fff703c の名前。

**経路（目標定理まで）**: `argWidthAt_of_closingRun`（`SRC_ARGW_SUPPLY_FREEZE.md` §1.2）は前提 `TY`（`ReadTypedAt HK SK …`）を取る。`ReadTyped = ConvKind ∧ LetSrcKinds ∧ CallSrcKinds ∧ MemSrcKinds`（同 §3.3 の直前、`ReadTyped` の定義）。`MemSrcKinds` は `memSrcKinds_of_allSites`（`ArgSupply12:67`）が `SiteLetOk`（`hLO`）と `LiftAgrees`（`hA`）から作る。`SiteLetOk` は `siteLetOk_structEnv'`（`ArgSupply15:30`）が 9 命題（+ `EnvTypesFVarFree`）から作る。

| 台帳 ID | (a) コンパイラの呼び出し箇所（関数・file:line、引数） | (b) 命題は呼び出し範囲より広いか | (c) 目標定理の経路で使うか（使う補題 @ kjob/g3aw-a24 8fff703c） | (d) 本体の種別 | 判定 |
|---|---|---|---|---|---|
| T1L-50 `LiftAgrees` | `machConv` Elab.lean:3993、`machChain` Elab.lean:4158（`ty.liftLooseBVars 0 1`、`b.liftLooseBVars 1 1`）。`rootFloat` MachRawSurface.lean:201（(0,1)、(1,1))、205（(0,1)） | 広くない。`LetOk 0` 入力で (0,1)・(1,1) のみ（LC6 で絞り済み）。`MachTupleIn.lean:87`（`packTupleInputs`、(1,1)・(0,1)）の入力が `LetOk 0` かは辿っていない | 使う。`liftRange_of_agrees`→`pureFacts_structEnv`（ArgSupply14:19）→`siteLetOk_structEnv'`。さらに等式のまま `memSrcKinds_of_allSites` の `hA`（ArgSupply12:68）、`allMemSites_float`（ArgSupply11:390）、`skbv_lift_of_liftAgrees`（ArgSupply10:35）が使う | `Expr.liftLooseBVars`: C++ extern（`lean_expr_lift_loose_bvars`、Expr.lean:1362） | 残す（原文のまま） |
| T1L-51 `Inst1Agrees` | `machInstanceS` の `inst` Elab.lean:4095（forall の本体に引数 `a` を代入）、`machNorm` Elab.lean:4989（`Nat` の `let`）・4992（閉じた `BitVec` の `let`）、`zetaAll` MachRawSurface.lean:220。`instantiate1` を `fvar` で呼ぶ Elab.lean:6206 など（elaboration 側）は辿っていない | 命題は `∀ b a` の等式で、`LetOk` の制限がない。証明が使うのは `inst1Range_of_agrees`（ExternSpec:128）の `Inst1Range`（`LetOk n b → LetOk n a → LetOk n (b.instantiate1 a)`、ShippingLetsReaderInvMain.lean:62）だけ（`Inst1Agrees` の出現は ArgSupply14/15 と ExternSpec のみ） | 使う。`pureFacts_structEnv`、`letOk_norm_structEnv`（ArgSupply14:25） | `Expr.instantiate1`: C++ extern（`lean_expr_instantiate1`、Expr.lean:1446） | 狭める（`Inst1Range` に差し替え） |
| T1L-52 `RootFloatAgrees` | `machConv` Elab.lean:3990、`machChain` Elab.lean:4155（`rootFloat v`、`v` は `let` の値）。`machineShape?` Elab.lean:5088（`rootFloat (zeroLit … (inlFoldNat (machNorm senv e)))`、全体） | 広くない（`LetOk 0` 入力）。ただし証明が使うのは `rootFloatRange_of_agrees`（ExternSpec:239）の `RootFloatRange`（`LetOk 0 v → LetOk 0 (rootFloat v)`、Main:53）だけ | 使う。`pureFacts_structEnv` | `rootFloat`: コンパイラ自身の `partial def`（MachRawSurface.lean:198）。中で C++ extern の `liftLooseBVars` を呼ぶ。Lean 本体の関数ではない | 狭める（`RootFloatRange` に差し替え） |
| T1L-54 `ZeroLitAgrees` | `machineShape?` Elab.lean:5088（`zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat (machNorm senv e))`） | 命題は全 `e` について `zeroLit … e = e.replaceNoCache …`（PreprocLetOk.lean:143、`LetOk` の制限なし）。証明が使うのは `zeroLit_ok`（同:151）が示す「`LetOk n e → LetOk n (zeroLit … e)`」だけ | 使う。`zeroLit_ok`→`readSub_letOk`→`siteLetOk_of`（ArgSupply13:69） | `zeroLit` はコンパイラの `def`（MachRawSurface.lean:211）で、`Expr.replace`＝C++ extern（`lean_replace_expr`、ReplaceExpr.lean:16-19）を呼ぶ | 狭める（範囲の形に差し替え。原文案は下） |
| T1L-55 `LiftLooseRange` | `rawNode` MachRawSurface.lean:100・102・104（`forM` の分岐）、120・122・124、148（pair の分岐）。`rawNode` の呼び出しは `machNorm` Elab.lean:4982。引数は (s,d) = (0,n)、(0,i)、(0,j)（n・i・j は `forM` の長さ / 添字 / `let` の個数） | **広い**。命題は任意の `(s,d)`。呼び出しは全て `s = 0`（`d` は任意） | 使う。`rawNode_ok`（RawNodeRangeLetOk:428）→`rawNodeRange_of`（:557）→`rawNodeRange_structEnv`（ArgSupply15:20）。`LiftAgrees` から導く補題はない（(0,1)・(1,1) のみ） | `Expr.liftLooseBVars`: C++ extern | 狭める（`s = 0` に） |
| T1L-56 `LowerLooseRange` | `rawNode` MachRawSurface.lean:142（`t.lowerLooseBVars i i`、pair の分岐） | **広い**。命題は任意の `(s,d)`。呼び出しは `s = d = i` | 使う。`rawNode_ok`（:553 の `hlo t i i ht`）→`rawNodeRange_structEnv` | `Expr.lowerLooseBVars`: C++ extern（`lean_expr_lower_loose_bvars`、Expr.lean:1357） | 狭める（`s = d`） |
| T1L-57 `BetaRange` | `rawNode` MachRawSurface.lean:100（引数 `PUnit.unit`）、102・120（引数 `a.liftLooseBVars 0 i`、関数 `f.liftLooseBVars 0 i`）。引数はすべて 1 個。`MachRecUnfold.lean:57・161` の `beta` は引数の個数が可変で、この命題の範囲外（この経路では辿っていない） | 広くない（1 引数、`LetOk 0` の関数と引数） | 使う。`rawNode_ok`（:496・508・539）→`rawNodeRange_structEnv` | `Expr.beta`: Lean の `def`（Expr.lean:1624）で `partial def betaRev`（Expr.lean:1593）に依存する。C++ extern ではない（Lean 側の `partial`） | 残す（原文のまま） |
| T1L-58 `LiftScalarCorr` | `machNormApLift` Elab.lean:4806・4815（引数 `vars` は `args` から作る任意長）、`machLiftScalar` 4768（`vars = [(wa, a)]`）、`machLiftScalarN` 自身の再帰（4664 ほか） | 命題は `machLiftScalarN` の成功 → モデル `liftN` の成功の対応で、`LetOk` の制限なし。証明が使うのは `liftScalarRange_of`（LiftScalarModelLetOk:355）の `LiftScalarRange`（NormNodeRangeLetOk:146）だけ | 使う。`normNodeRange_structEnv`（ArgSupply15:25）→`normRange_of`→`letOk_norm_structEnv` | `machLiftScalarN`: コンパイラの `partial def`（Elab.lean:4652）。Lean 本体の関数ではない | 狭める（`LiftScalarRange` に差し替え） |
| T1L-59 `BoolMapCorr` | `machNormMap` Elab.lean:4911（`machBoolMap senv dom a wa body`）、自身の再帰（4835） | 同上（`LetOk` の制限なしの対応。証明が使うのは `boolMapRange_of`（BoolMapModelLetOk:106）の `BoolMapRange`、NormNodeRangeLetOk:152） | 使う。`normNodeRange_structEnv`→`letOk_norm_structEnv` | `machBoolMap`: コンパイラの `partial def`（Elab.lean:4831） | 狭める（`BoolMapRange` に差し替え） |

「差し替え」の意味: 差し替え後の命題は元の命題から証明済みの補題で導ける（`inst1Range_of_agrees`、`rootFloatRange_of_agrees`、`zeroLit_ok`、`liftScalarRange_of`、`boolMapRange_of`）ので、**元より弱い**（信頼する内容が少ない）。ただし `siteLetOk_structEnv'` などの binder を差し替える新しい Lean の単位が要り、reviewer の freeze が先。この調査では、差し替えた形の Lean を書いても elaborate してもいない。

**必要最小限の TRUSTED 候補（原文。9 件。数えた件数）**

この調査で辿った候補経路（`siteLetOk_structEnv'` → `MemSrcKinds`）では、9 件のどれも「経路に現れない」とは言えなかった。外せる行は無く、狭める行が 7 件、残す行が 2 件。

| # | 台帳 ID | 原文（`LetOk` は `Tools.ShippingLetsAliasInv.LetOk`） | 元の命題との関係 |
|---|---|---|---|
| 1 | T1L-50 | `∀ e, LetOk 0 e = true → e.liftLooseBVars 0 1 = liftSpec e 0 1 ∧ e.liftLooseBVars 1 1 = liftSpec e 1 1` | 元のまま |
| 2 | T1L-51 | `∀ n b a, LetOk n b = true → LetOk n a = true → LetOk n (b.instantiate1 a) = true`（= `Inst1Range`） | `Inst1Agrees` より弱い |
| 3 | T1L-52 | `∀ v, LetOk 0 v = true → LetOk 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = true`（= `RootFloatRange`） | `RootFloatAgrees` より弱い |
| 4 | T1L-54 | `∀ n e, LetOk n e = true → LetOk n (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? e) = true`（原文案。未 elaborate。`n` を 0 に絞れるかは未確認） | `ZeroLitAgrees` より弱い |
| 5 | T1L-55 | `∀ (e : Lean.Expr) (d : Nat), LetOk 0 e = true → LetOk 0 (e.liftLooseBVars 0 d) = true`（原文案。未 elaborate） | `LiftLooseRange` を `s = 0` に絞る |
| 6 | T1L-56 | `∀ (e : Lean.Expr) (i : Nat), LetOk 0 e = true → LetOk 0 (e.lowerLooseBVars i i) = true`（原文案。未 elaborate） | `LowerLooseRange` を `s = d` に絞る |
| 7 | T1L-57 | `∀ (f a : Lean.Expr), LetOk 0 f = true → LetOk 0 a = true → LetOk 0 (f.beta #[a]) = true` | 元のまま |
| 8 | T1L-58 | `∀ (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) (w : Nat) (r : Lean.Expr), LetOk 0 dom = true → (∀ p ∈ vars, LetOk 0 p.2 = true) → LetOk 0 e = true → machLiftScalarN senv dom vars e = some (w, r) → LetOk 0 r = true`（= `LiftScalarRange senv`） | `LiftScalarCorr` より弱い |
| 9 | T1L-59 | `∀ (dom a : Lean.Expr) (wa : Nat) (body r : Lean.Expr), LetOk 0 dom = true → LetOk 0 a = true → LetOk 0 body = true → machBoolMap senv dom a wa body = some r → LetOk 0 r = true`（= `BoolMapRange senv`） | `BoolMapCorr` より弱い |

もう 1 つの内容の違い: #3 #8 #9 の本体は Lean 本体ではなくコンパイラ自身の `partial def` で、#1 #2 #5 #6 は C++ extern、#4 は C++ extern を呼ぶコンパイラの `def`、#7 は Lean 側の `partial def`。コンパイラ自身の `partial def`（#3 #8 #9）は、将来コンパイラを変えて停止性つきの定義にすれば TRUSTED から外せる候補だが、いまはコンパイラ編集が禁止なので、この資料は推奨しない。

**別の経路（TRUSTED を減らす候補）**: `kjob/g3aw-a24` 8fff703c の `Tools/Prototype/ExtReaderFinal.lean` に、reader の呼び出し箇所を仕様モデル（`liftM`、`lowerM`、`inst1M`、`betaM`、`rootFloatS`、`zeroLitM` など）に置き換えた「モデル reader」`machineShapeXM` についての `machineShapeXM_typed_all` があり、同ファイルの記載では上の対応の前提（`LiftLooseRange` など）は要らない。ただし (i) 出荷中の `machineShape?` についての定理ではない（出荷への切り替えは別の判断で、コンパイラ変更）、(ii) `rawNodeX shippedOps = rawNode` は証明されていない、(iii) この定理が T1 の `argWidthAt_of_closingRun` 経路につながっているかは、この調査で辿った候補経路では未確認。§4.2 (1)(a) の具体例だが、今回は推奨しない。

**辿れなかった点（この調査で辿った候補経路では未確認）**:
- `ReadTyped` の残り 3 要素（`ConvKind`、`LetSrcKinds`、`CallSrcKinds`）と `TY` から `argWidthAt_of_closingRun` までの組み立て。8fff703c の木には `memSrcKinds_of_allSites` を使う定理が `siteLetOk_structEnv'` まで以外に見つからなかった。
- `MachTupleIn.lean:87` と `MachRecUnfold.lean:57,161`、elaboration 側の `instantiate1`（Elab.lean:6206 ほか）が、T1 / FG の他の定理の前提として出てくるか。
- `Inst1Range` の `n`、`ZeroLit` の `n` が、呼び出しでどの値まで要るか（`n = 0` で足りるか）。

## 5. 項目 N4: G7-c 印字（D.E-13。FG のみ）

### 5.1 説明
コンパイラの出力 `Design` を Verilog / SystemVerilog 文字列に変換する印字器（`emitModule`）。FG の保証は `checkedOptimize b` の `runModuleTG` までで、印字器の正しさは保証の外（boundary-audit §3: 「TRUSTED by design（printer）。parse-back は validation のみ」、Gaps row 129）。T1 には対応する行が無い。実 run から払えない理由: 印字結果の正しさは run の事実でなく、印字器の実装の性質。台帳は「対象外」とした。

### 5.2 選択肢
**(1) 証明**: 印字器 → 文字列の意味保存。この調査では経路を辿っていない。G7-b（`runModuleTG` ⇒ `DesignSV`）の定理も `TopShips` については見つからなかった。コスト: 大（範囲が大きい。未見積もり）。
**(2) TRUSTED**: すでに `GENERAL_SPEC` §5 M5 が「G7 is TRUSTED and stated」と書く。新しい宣言は不要で、保証の文面に「印字器を信頼する」を明記するのみ。利用者の影響: 文面に明示される。誤った回路: 印字器にバグがあれば、**Lean 内で証明された `Design` と、出力された Verilog 文字列が食い違い**うる（データ損失ではなく出力の誤り）。条件: 印字器の不具合。緩和: parse-back による validation（検査であって証明ではない）。
**(3) 書き方を変える**: 保証が `checkedOptimize b` の `runModuleTG` で終わることを、最終保証の文面に書く。FG の縮小ではなく、現状の保証範囲の明記。

### 5.3 推奨
**(2) の既存の位置づけを維持し、(3) の明記を最終保証の文面に入れる。** 新 TRUSTED ではない（既に宣言済みの確認）。後から変えられる: (1) が得られれば外せる。判断しない場合: 現状どおり（台帳に「TRUSTED 候補」として残る）で、`sparkle-gen5-boundary-audit` の最終監査の記載が閉じない。根拠: FG 台帳 D.E-13（b54e343d）、`kjob/g5ba-r11` `BOUNDARY_AUDIT_FREEZE.md` §3、`GENERAL_SPEC.md` §5 M5。

## 6. この資料が数えた事実（数えたものだけ）

- T1 台帳 §7 の表の行数 71、「実 run で払える」欄の内訳は、この資料の作成時に `^| T1L-` の行を欄ごとに数え直して、`unknown` で始まるもの 56（35 + 13 + 7 + 1）、`no` で始まるもの 11（8 + 2 + 1）、`yes` 1、`n/a` 2、`see FG ledger` 1、で §7 の 1 / 11 / 56 / 2 / 1 と一致した。
- `Laws` のフィールド数 14（D.E-10 の列挙: `O` 10 + `T` 4）。
- 9 行の命題の原文は `kjob/g3aw-a24` 8fff703c から写した（ZeroLitAgrees を除く）。
- FG 側で「不明」の行の件数は**数えていない**（FG の「実 run から払えそうか」欄は部分ファイルごとの自由記述で、書式が揃っておらず、FG 台帳 §2 も分類別の合算を行っていない）。

## 7. 「不明」の行を はい / いいえ に振り分ける手順（今回は振り分けない）

対象: T1 台帳の「実 run で払える: 不明」56 行、FG 台帳の「不明」とした行（件数は未計数。上記）。着手時に次の手順で振り分け、台帳に反映する。**この資料の作業では、どの行も振り分けていない。**

1. **基準の固定**。T1 台帳 §2 の規則を使う: 「はい」は、承認済みの補題が、その行の前提を実 run の事実から導くと型として示せている場合だけ。補題名と `branch@SHA` を行に書く。条件つきなら条件を書く（「条件付きではい」）。
2. **行ごとに調べる**（1 行 1 項目）: (a) 前提を結論とする補題が `Tools/` にあるか（`git grep` で名前と型）、(b) その補題の前提が run 由来のものだけか（他の「いいえ」の前提を含まないか）、(c) 履歴の freeze / note に支払い予定があるか。
3. **振り分け**: 「はい」＝(a)(b) を満たす補題名を書ける。「いいえ」＝前提の中身が run の事実でなく、Lean 本体 / 一様な法則 / 外部関数の性質（この資料の N1–N4 のような種類）である。それ以外は「不明のまま」とし、**調べた経路と「この調査で辿った候補経路では未供給」を行に書く**（「不可能」とは書かない）。
4. **「いいえ」になった行は、この資料と同じ形式（説明・3 択・推奨・可逆性）で判断資料に追加する**。ユーザーの判断なしに TRUSTED / 保証の変更をしない。
5. **台帳の更新**: 欄と根拠の更新のみで、行の解消扱いにはしない。件数（現在値は FG 104 / T1 57。初版時点は FG 107 / T1 58）は、振り分けだけでは変わらない。振り分けの前後で「はい / いいえ / 不明」の数を数えて、更新の note に書く（数えた分だけ）。
6. **確認**: reviewer が「はい」の行の補題名を抜き取りで確認する。台帳の更新は文書のみの単位として、Lean は触らない。

## 8. 判断してほしいこと（まとめ）

1. N1 `Laws` を、条件つきで TRUSTED にしてよいか（推奨: 14 フィールドの原文を列挙し、Lean 版と結び付け、N2 の監査を継続）。
2. N2 非空虚な `Laws` の持ち主（`sparkle-gen2-top-contract` の再開か後継）と、保証の文面に「非空虚性は未確認」と書くこと（推奨: はい。TRUSTED にはしない）。
3. N3 C++ extern / `partial` との一致を、条件つきで TRUSTED にしてよいか。範囲監査（§4.4）の結果、対象は 9 件のまま、うち 2 件は元の原文、7 件は呼び出し範囲・証明が実際に使う形に絞った原文（原文案は §4.4 末尾の表）。推奨: はい。条件は、原文列挙 + Lean 版 + 差分テスト + 絞った文面を使う新しい Lean の単位を reviewer の freeze 経由で通すこと。絞る作業を待たずに初版の 9 件の原文を TRUSTED にする選択肢もあるが、信頼する内容が多くなるので推奨しない。reader の置き換え（§4.4 の別の経路）は別単位の検討で、今回は求めない。
4. N4 印字器の既存 TRUSTED の位置づけと、保証範囲の明記（推奨: はい。新規ではない）。

どれも決めない場合: 台帳の該当行は現在値（FG 104 / T1 57）のまま残り、上記の Issue が条件付き部品止まりで止まる。回答があれば、決まった範囲で、TRUSTED の記述・Check・最終保証の文面の単位を別 Issue として起こす（この資料はそれを実施していない）。
