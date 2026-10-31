# 判断資料: 前提台帳の「実 run で払えない」行をどう扱うか

- Issue: `sparkle-premise-nopay`（親 `sparkle-fg-final`）。agent `nopay2`、branch `kjob/nopay2`、base `par/gen2-spec` d0ddc50b。文書のみ。Lean・build・共有定義・compiler の編集はしていない。
- 状態: **ユーザー判断待ち**。この資料は新しい TRUSTED・保証変更・FG の縮小を**推奨として書くだけ**で、実施していない。
- 読んだ材料（`git show <branch>:<path>` で読んだ。checkout / merge していない）:
  - T1 前提台帳: `kjob/t1-ledger-int` が指す承認済み版のうち、依頼文が指定した 51ebec20 の `scripts/gen3/PREMISE_LEDGER.md`（行 41 は非 Prop の入力に再分類済み）。
  - FG 前提台帳: 8fd85e5d + §10（b54e343d）の `scripts/gen2/PREMISE_LEDGER.md` と `premise_ledger/A_M2.md, B_M4.md, C_M5dg.md, D_M5t2.md`。
  - 周辺: `scripts/gen2/GEN2_DEFS.lean.txt`、`scripts/gen2/GENERAL_SPEC.md` §1.2 / §5、`Tools/ShippingChildInvA.lean:255-334`（`RefLawsAOps` / `RefLawsATele`）、`kjob/g2tc-ptop21` の `TOP_CTRL_FREEZE.md` §19、`kjob/g3aw-a24` の `Tools/ShippingLetsExternSpec.lean` と `SRC_ARGW_B3_R9_FREEZE.md`、`kjob/g5ba-r11` の `scripts/gen5/BOUNDARY_AUDIT_FREEZE.md`。
- 台帳の現在値: **FG 107 / T1 58**。この資料は台帳の行を増減させない（今回 FG -0 +0 / T1 -0 +0）。台帳 ID の版: 依頼文の版（T1 51ebec20、FG b54e343d）を正として読んだ。`kjob/t1-ledger-int` 先端 907d1c1d とは §7 の 1 行と §11 の文言に差があった（`diff` で見た範囲。§7 の件数表は同じ）。`kjob/fg-ledger-int` 先端 f2e4b379 とは差分（284 行）があり、全文は読み比べていない。先端の版を使うかは reviewer の確認事項。
- 書き方の規則: 「見つからなかった」は「この調査で辿った候補経路では未供給」の意味で、不可能・導出不能の主張ではない。mutant（棄却）は signature / defeq での棄却で、意味的反例ではない。数えていない数は書かない。見積もりは**工数の数値を書かない**（根拠になる数えた量だけを書く）。

## 0. 先に結論（一覧）

判断が要る行は 4 本に整理できる（台帳 11 行 + FG 側の対応 + FG の TRUSTED 候補）。

| 項目 | まとめた台帳 ID | 推奨 | 新 TRUSTED / 保証変更を伴うか |
|---|---|---|---|
| **N1 `Laws`（実行時の法則 G5）** | T1L-01 = A.P-01（B.F-3, D.E-10 を統合済み） | (2) TRUSTED。ただし 14 フィールドを名前付きで列挙し、非空虚性（N2）の監査を別単位で続けることが条件 | 伴う（ユーザー未承認の新しい TRUSTED 境界） |
| **N2 非空虚な `Laws`（監査項目）** | T1L-69 = FG 監査 N1（FG §8.5）。関連: T1L-70, T1L-71, A.P-28 | TRUSTED にしない。仮説にも入れない。監査項目として残し、持ち主を決める（(1) の経路: 非空虚な `Laws` の構成） | 伴わない（現状維持） |
| **N3 C++ extern / `partial` との一致 9 行** | T1L-50, 51, 52, 54, 55, 56, 57, 58, 59（FG 側に対応する行はこの調査では見つからなかった） | (2) TRUSTED。9 個の Prop をそのまま名前付きで、`lean-toolchain` の版に紐づけて列挙。並行して差分テストを運用上の緩和策にする。長期は (1)（reader を Lean の仕様モデルに置き換える）を別途検討 | 伴う（新 TRUSTED） |
| **N4 G7-c 印字（printer）** | D.E-13（FG のみ。T1 に対応行なし） | (2) 既存の位置づけを維持（GENERAL_SPEC §5 M5 が「G7 is TRUSTED and stated」と既に書く）。保証が「`checkedOptimize b` の `runModuleTG` まで」であることを最終保証の文面に明記 | 新規なし（既存の宣言の確認のみ） |

判断しないと止まるもの（台帳が名前を挙げている Issue。網羅ではない）: `sparkle-gen3-src-argw`（N3: U-R9 以降の供給）、`sparkle-gen2-top-contract`（N2: 一時停止中）、`sparkle-gen5-boundary-audit`（N1 / N4）、`sparkle-gen3-t1-assembly` / `sparkle-fg-final`（最終定理の文面。N1 / N3 の置き場所が決まらないと前提リストを閉じられない）。

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

注意: 9 行のうち、個々が C++ extern か `partial def` かは、行ごとには確認していない（台帳の記載と R9 freeze の「each state one extern/`partial` call」に従う）。FG 台帳（A-D）にこの 9 行に対応する行は、この調査では見つからなかった（FG 側には `C.CV-2` の注記に「`Expr.hasLooseBVars` / `liftLooseBVars` は extern で補題が無い」がある程度で、独立の行は無い）。T1L-53（`EnvTypesFVarFree env₀`）は台帳が「不明（kernel fact）」としており、この 9 行には入らない。

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

### 4.3 推奨
**(2) TRUSTED（9 個の原文を名前付き・Lean 版つきで列挙）+ 運用上の緩和として差分テスト。長期の別案として (1)(a)（置き換え）を別単位で設計検討する。** 理由: (1)(b) の経路はこの調査で辿った範囲では未供給で、(1)(a) は現時点で禁止されているコンパイラ変更を要する。(3) は (2) と論理が同じで、利用者にとって供給不能な仮説を signature に見せるだけ。ただし 54, 56, 57, 58, 59 の 5 行は命題以外に出現が無く（55 は 50 から導く補題が無い）、TRUSTED にする前に**命題が意図した内容か（弱すぎ・強すぎないか）を reviewer が確認**すること。
- 後から変えられるか: 変えられる。(1)(a) が実現した行は TRUSTED から外せる。signature は変わらない（(2) の場合）。
- 判断しない場合: 9 行は T1 / FG の前提のまま残る。`sparkle-gen3-src-argw`（U-R9 以降の LK1 / ReadTyped の供給）は「条件付き部品」止まりで、T1 の `argWidthAt_of_closingRun` 経路を完了にできない。
- 根拠: T1 台帳 T1L-50..59 / §5 の 50-60（51ebec20）、`kjob/g3aw-a24` 8fff703c `Tools/ShippingLetsExternSpec.lean` ヘッダ（LC6）、`SRC_ARGW_B3_R9_FREEZE.md`。

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
5. **台帳の更新**: 欄と根拠の更新のみで、行の解消扱いにはしない。件数（FG 107 / T1 58）は、振り分けだけでは変わらない。振り分けの前後で「はい / いいえ / 不明」の数を数えて、更新の note に書く（数えた分だけ）。
6. **確認**: reviewer が「はい」の行の補題名を抜き取りで確認する。台帳の更新は文書のみの単位として、Lean は触らない。

## 8. 判断してほしいこと（まとめ）

1. N1 `Laws` を、条件つきで TRUSTED にしてよいか（推奨: 14 フィールドの原文を列挙し、Lean 版と結び付け、N2 の監査を継続）。
2. N2 非空虚な `Laws` の持ち主（`sparkle-gen2-top-contract` の再開か後継）と、保証の文面に「非空虚性は未確認」と書くこと（推奨: はい。TRUSTED にはしない）。
3. N3 C++ extern / `partial` との一致 9 行を、条件つきで TRUSTED にしてよいか（推奨: はい。原文列挙 + Lean 版 + 差分テスト。reader の置き換えは別単位の検討）。
4. N4 印字器の既存 TRUSTED の位置づけと、保証範囲の明記（推奨: はい。新規ではない）。

どれも決めない場合: 台帳の該当行は現在値（FG 107 / T1 58）のまま残り、上記の Issue が条件付き部品止まりで止まる。回答があれば、決まった範囲で、TRUSTED の記述・Check・最終保証の文面の単位を別 Issue として起こす（この資料はそれを実施していない）。
