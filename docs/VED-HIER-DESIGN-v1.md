# VED 階層（複数 module）U1 の設計相談 v1（sparkle-ved-hier）

前提: main 6c29b9b8。U1 は返却 IR に対する strict（reset=0、order-free）。基準文書 §2（階層を分母から除かない）、§3、§5、§7。

## 1. いまの事実
- `synthesizeCombinational decl` は `(m, d)` を返す。`m` が top、`d : Design` は子 module の列。
  - 子は `@[hardware_module]` 呼び出しから `Stmt.inst modName instName conns` で参照される。
  - 実装: Sparkle/Compiler/Elab.lean:4062。
- main の IR 意味論は **open-module** である（Sparkle/IR/Semantics.lean:185-198, 227）。
  - instance の出力は、親の自由入力として扱う。
  - 子の振る舞いはすべて量化される。
  - 閉じた階層意味論は「future work」と明記されている。
- U1 の `ShapeStmt` は v1 範囲として instance を持つ module を拒否する（Tools/VedU1Contract.lean:280-284（main 6c29b9b8。PR #152 b5da6b86 では 311-315））。
- 測定（a18ab/cdc41 の u1_deep）: prep で「single-module designs only」が 36 行。
  - ファイルは IPv4/ARP/ICMP/HTTP/TCPHeader、AESHW、Keccak、SHA256/512、ECDSA/Policy/P256/Fido2、PCIe、MultiInstanceTest、MultiOutputSubModuleHangRepro など。
  - u1 経路では、それより前の段（table/proof/checker）で止まる行が多い。

## 2. 決めてほしいこと
1. **階層の意味（statement が何を保証するか）**
2. **証明の構成（何を信頼し、何を kernel が検査するか）**
3. **最初の代表と範囲**

## 3. 選択肢

### A. 閉じた設計意味論を定義し、子ごとの U1 を合成する（推奨）
`DesignStep d top` を新しく定義する。
- 親の 1 cycle を評価するとき、各 `.inst modName instName conns` の出力に、`d` 内の `modName` の module を conns の入力で評価した値を入れる。
- 組合せの子は同じ cycle の関数になる。
- 順序の子は、状態を親の状態の積に加える。

statement は `U1HStmt c d m stmt` とする。中身は U1Stmt と同じ形で、OutputsStmt を閉じた意味で読む。

証明は次の 3 つから組み立てる。
1. 子ごとの U1 定理（子の宣言 = 子 module、既存の生成器を流用）
2. 親の中間契約（裁定2）。既存 U1Stmt は inst を拒否し、任意の子出力について元の親宣言と等しいとは言えないので、open-module U1 をそのまま流用はしない。子の入力/出力関係を仮定として持つ親の中間契約を立てる。
3. 合成補題：実際の子定理でその関係を供給し、元の親宣言に戻る結論を得る。中間仮説は最終 strict 定理ですべて供給し、ChildFn や接続の意味保存を未供給 binder に残さない。補題の本数・規模は未検証の見積り（「1本で済む」とは言わない）。
   - これは module に依存しない定理として 1 回だけ証明する。

| 項目 | 内容 |
|---|---|
| 仕様（新しい axiom・TRUSTED ではない） | `DesignStep` の定義は保証内容を定める仕様で、返却 Module/Design だけから定義し reviewer が仕様として承認する（§7 裁定1）。生成器と証明は信頼しない（kernel） |
| 利用者に見える影響 | なし（compiler 出力は不変、検査の追加だけ） |
| 費用 | 意味論の定義と合成補題 1 本（組合せの子：中、順序の子：大）、生成器の結線 |
| 後から変えられるか | 変えられる。DesignStep を変えると statement が変わるので、版を上げて再測定する |

### B. 平坦化した 1 module に対して既存の U1 を使う
`flatten (m, d)` を Tools に新しく作り、平坦 module に対して U1 を証明する。

| 項目 | 内容 |
|---|---|
| 新しい信頼 | flatten の正しさ（証明するなら、結局 A と同じ設計意味論が要る）。証明しないなら、保証は「返却 IR」ではなく「flatten した IR」についてになり、§4 の段が 1 つ増える |
| 利点 | 生成器をそのまま使える。規模が大きいと proof/checker の費用が親子の積で増える（測定上、checker の heartbeat がすでに 56 行） |
| 推奨しない理由 | 返却 artifact は階層のままである。保証と出力の対応が間接になる |

### C. 未対応として数え続ける（現状）
- 分母から除かずに「未対応（instance）」と報告する。
- 費用 0。階層を含む行は現状のままでは未対応。

## 4. 推奨する最初の範囲（A を選んだ場合）
- **H1:** 組合せの子だけ（子に register/memory なし）、子は単一出力、親は既存の生成器の範囲。
  - 子の重複呼び出し（同じ子の instance が複数）を含む。
  - 合成補題と DesignStep をここで固める。
- **H2:** 順序の子（register 1 個の遅延など、既存スクリプトの範囲）。状態の積。
- **H3:** 複数出力の子（2b の port 命名の結果を使う）。
- 代表:
  - inventory の MultiInstanceTest（PE は register 2 個・structure 出力なので H2+H3）。
  - H1 では、まず inventory 外の小さな対照（組合せの子 1 個、2 回呼び出し）で縦断し、inventory 行は 36 行の中から register-free の子を持つものを探して報告する。件数は約束しない。
- **拒否の対照:**
  - 子 module の名前の入れ替え
  - conns の入れ替え
  - 子の本体の改変
  - design から子が欠落
  - 同じ名前の子が 2 つ
  - いずれも拒否され、定理は残らない。

## 5. 判断しないとどうなるか
- 階層の Issue（5 番目）は着手できない。
- 36 行と、それより前の段で止まっている階層行は未対応のまま残る。
- 他の Issue（front end、2b、性能、gate）は止まらない。

## 6. 根拠
- 測定: ~/git/workspaces/ved-u1-results/full-231d5ee7/final-cdc41/results.tsv（u1_deep の prep_error に "single-module"）
- コード: Sparkle/IR/Semantics.lean:185-198, 227、Tools/VedU1Contract.lean:280-284（main 6c29b9b8。PR #152 b5da6b86 では 311-315）、Sparkle/Compiler/Elab.lean:4062

## 7. reviewer 裁定（2026-11-10、対象 406bd83b）と反映
方向の許可であり、U1HStmt の凍結、階層 strict の達成、Issue の完了、release の承認ではない。

1. **A を採用**（B の平坦化は今は追加しない）。
   - DesignStep は新しい axiom や TRUSTED ではない。保証内容を定める仕様である。
   - 元宣言を参照せず、返却 Module/Design だけで定義する。
   - 葉（instance なし）では既存意味論に一致することを補題にする。
2. **親の中間契約**（子の入出力関係を仮定）、**実際の子定理による供給**、**元の親宣言に戻る結論**を明記する。中間仮説はすべて最終定理で供給する。
3. **階層用の Order/Shape を新設する。** 既存の WO・runModule_perm・ReorderInvariance は inst の read/write を無視するので、そのまま適用しない。
   - inst の入力 read と出力 write は、子 module の port 方向から定める。
   - assign/inst を横断する依存順序について、存在と、全許容順序での一致を証明する。
   - 次はすべて拒否する：循環、undriven、入力への書込み、多重 driver（assign/reg/inst 間も）、幅不整合。
   - 燃料切れや lookup 失敗を 0 値で補わず、失敗にする。
   - 入力範囲内の全 stream について、実行が存在することも結論に含める（空虚さの防止）。
4. **同じ合成 run の (m, d) 全体を保持・引用し、次を検査する。**
   - top の対応、子 module 名の一意性、全 inst の解決
   - 各入出力 port の接続：過不足、重複、方向、幅
   - H1 の出力接続は ref のみなど、狭い明示範囲でよい。
   - 子定理は d から解決したその module そのものに結ぶ（別 run や同名 module の証明は代用不可）。
   - 未使用の inst や子 module を証明のために除去しない。unsupported な残存 module の扱いを明記し、黙って検査対象から落とさない。
5. **H1 の範囲：** 深さ 1、組合せの leaf 子、単一出力、memory/primitive/parameter なし。同じ子を 2 回呼ぶ小例を含める。
   - 親はまず組合せとし、通った後に既存対応範囲の親 register へ進む。
   - 子間接続の依存、異なる入力、非対称な関数と値を使い、接続の取り違えを観測できる対照にする。
   - H2（状態は instance path ごとに独立。同時更新・初期値・reset=0/clock 範囲を別途定義）と H3（multi-output と連携）は今回実装しない。
6. **次の提出物：**
   - H1 の型付き契約
   - 葉の縮約補題と合成補題
   - 同じ返却 artifact に対する、自動生成の最小 strict 1 例
   - 対照（すべて拒否）：子 2 回、conns の交換・欠落・余分・幅違い、子 body の改変、子の欠落・重複名、循環、undriven、別 Design・別証明。意味が変わらない一貫した rename は拒否必須にしない。
   - 監査：std3、完全型、同一 artifact、変数なし
   - 合成時間、証明時間、peak memory の記録
   - 先に 36 拒否行から H1 候補を 1 行調査して指定する。見つからなければ、理由と最初の阻害を報告する。小例は 327 に加算しない。
   - frontend/comb 等を中断する全面変更はしない。

## 8. H1 の実装（ved/hier-h1、型は未凍結）

方向の許可（§7）に沿った最小縦断。ファイル:
- `Tools/VedU1HierSem.lean`: 閉じた階層意味論 `stepH`/`runH`（返却 Module/Design だけで定義）、`instEval`、`runAt`（燃料）、
  葉補題 `evalAssignsI_leaf`、階層順序 `WOH` と全許容順序での一致 `evalAssignsI_perm`。
- `Tools/VedU1HierComp.lean`: 子の定理から供給する関係（合成補題）`child_rel`/`child_rel_out`、`instEval_leaf`、`instEval_laws`。
- `Tools/VedU1Hier.lean`: 文 `U1HStmt`、artifact 検査 `HierShape`/`OrderOkH`、`outputsH_of_step`、`stepH_of_b0`、`exists_arr`、`stepH_leaf`。
- `Tools/VedU1HierEntry.lean`: `#ved_u1_hier decl`（合成 1 回、(m, d) を保持、子ごとに `checkU1E`、親の証明を生成）。
- `Tests/Ved/U1HierCheck.lean`: 肯定例と対照（327 には加算しない）。

意味論の要点: 失敗は `none`（子の欠落・primitive・入力の未接続・存在しない port への接続・出力接続が `ref` でない・子の register/memory・
燃料切れ）。配列の選択は `arr : Module → List Stmt`（全ての許容配列で結論が成り立つ）。中間契約は、親の証明が使う子の関係
（`hrel`: 宣言 `g` の値 = `leafOut`（子の閉じた評価）と `hI`: instance の書込み）で、最終定理では子の実定理（`child_rel_out`）と
`d` から解決した module への束縛（`decide`）で全て供給する（未供給の binder なし）。

H1 の範囲外（明示的に拒否）: 親・子の register/memory（H2）、複数出力の子（H3）、`ref` 以外の接続、primitive・parameter 付きの子、
深さ 2 以上（`assignOnly` でない子）、`d` に未使用の module。
