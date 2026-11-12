# VED 階層 H2b: register を持つ親（register を持つ葉の子、深さ 1、子の入力は親入力への ref）

基準: ved/hier2-h2a 22d2efa7（H2a、PR #162）。設計: docs/VED-HIER-H2-DESIGN.md（§1.2 同時更新、§11 裁定、§12）。
本文書は実装記録であり、文の凍結、327 行への加算、hierarchical strict の inventory 主張、release を主張しない。
小例（`oneInstance` 等）は 327 に加算しない。

## 1. 範囲

- 深さ 1、単一出力の葉の子（assign と register、H2a と同じ）、親が register を持つ。
- instance の入力 port は親の **入力** への `ref` のみ（H2a と同じ。内部 wire・導出式・別 instance の出力は `[conns]` で拒否）。
- 同じ返却 `(m, d)` に対する同じ完全な型の文、`synthesizeCombinational` は 1 回、axioms は標準 3 つのみ。
- 広げていないもの: 内部 wire の instance 入力、多出力の子、深さ 2 以上。

## 2. ファイル

| ファイル | 内容 |
|---|---|
| `Tools/VedU2HierReg.lean`（新） | `U2HRStmt`、`outputsOnHS_of_stepR`（親 register の合成定理）、`runHSTrace_next` / `restrictTo_perm` / `nextKeys_eq_regOuts` / `applyH_root_cons` |
| `Tools/VedU2HierRegEntry.lean`（新） | `#ved_u2_hier`（H2a / H2b の分岐）、`checkU2HR`、`vedU2HierEntryR`、証明スクリプトの生成 `scriptTextR`、`ved_fin_norm` |
| `Tests/Ved/U2HierRegCheck.lean`（新） | H2b の正例・拒否対照・正の対照 |
| `Tools/VedU2HierEntry.lean` | **変更は 2 点だけ**: (a) `elab "#ved_u2_hier"` を `VedU2HierRegEntry` に移した（`checkU2H` / `vedU2HierEntry` は不変で、H2a の checks はこれらを直接呼ぶ）、(b) `genOpen` に既定値付きの引数 `openSuf := "ved_open"`（H2a の名前は不変） |

H2a の文 `U2HStmt`、`Tools/VedU2HierStmt.lean`、`Tools/VedU2HierSem.lean`、`Tools/VedU2HierProj.lean`、`Tools/VedU2HierKid.lean`、`Tools/VedU2HierOrder.lean`、
`Tests/Ved/U2HierCheck.lean` / `U2HierPin.lean` / `U2HierSemCheck.lean` は変更していない（すべて通る: §8）。

## 3. 文

```
def U2HRStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeS d m = true ∧
  WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f
```

`U2HStmt` から連言肢 `regsOf m.body = []` だけを除いた別定義（`Tests/Ved/U2HierRegCheck.lean` に
`U2HStmt ↔ U2HRStmt ∧ regsOf m.body = []` の `example` がある）。`OutputsStmtHS` / `OutputsOnHS` / `runHS` / `st0H` は H2a と同じ定義で、
`runHS` は元から親 path `[]` の register を同時更新する（`stepHS`: 親と全子の next を更新前状態から作り、`applyH` を 1 回）。
`U2HRStmt` に未供給の binder はない（`ExprsSupp`、`ChildSucc`、`htie`、`hwr`、`InputsOk`、親 register の init / next はすべて証明の中で供給）。
最終定理は `decl.ved_u1 : U2HRStmt decl.ved_contract decl.ved_mod decl.ved_design decl`（register のない親は従来どおり `U2HStmt`）。

親 register の init は `ShapeCore` の `inits`（`contractOf` が `m` から読む）には現れても、宣言の init との一致は文では述べず、
**生成した証明が deep の事実 `_deep_inits` と `st0Of m` を kernel で比べる**ことで担保する（init を変えると `[proof]` で拒否: §6）。

## 4. 合成定理 `outputsOnHS_of_stepR` の構造

`Ow ins y t` は instance 出力 wire `y` の oracle（H2a と同じ）。親 register の状態は `R ins t p`（`p` は根の slice `st []`）で、次を仮定する（生成する）:

- `hkid`: 成功した閉じた run の各 cycle で、instance 出力 wire は oracle の値（`kid_inst`、子の実定理から。子は親 **入力** だけを読むので、親 register の状態に依存しない）。
- `h0`: `R ins 0 (st0Of m)`。
- `hstep`: `R ins t p` なら、検査済みの arrangement `b0` の **open 評価**（instance 出力 = oracle、`oracleIE`）が成功し、親 register の next `nx` が計算でき、
  出力は宣言の値で、`R ins (t+1) (applyNexts p nx)`。

証明は H2a と同じ形で閉じた fold = open fold（`fold_oracle`）を使い、さらに:
`runHSTrace_next`（trace の cycle `t` の root slice `S' []` は `applyNexts (S []) nx`）、`restrictTo_perm`（seed の register 名は arrangement によらない）、
`regNexts_perm` + `applyNexts_perm`（`regNexts` の順序の違いは鍵の一意性で吸収、`nextKeys_eq_regOuts`）により、任意の admissible な arrangement に運ぶ。
`R` に対する cycle 帰納（`chain`）は trace の `sts[t]` で行う。

## 5. 入口（`checkU2HR`、`CommandElabM`）

1. phase1（`TermElabM`、`checkU2H` と同じ段階: `table` / `multi-output` / `artifact` / `hier-shape` / `clkrst` / `order` / `scope`（instance なし）/ `child` / `conns` / `open`）。
   `scope` の「親が register を持つ」拒否は H2b には無い。open 親は `genOpen`（H2a と同じ生成、`kabstract` は構成の道具、等式 `decl xs = open xs calls` は kernel の `rfl`）。
2. `#verify_elab_deep` を **生成した open 親** に対して `elabCommand` で走らせる（`[deep]` 段階。DeepElab は既存で変更していない）。
3. phase2: deep の事実（`_deep` / `_nm` / `_inp` / `_deep_trace` / `_deep_next` / `_deep_inits` / `_deep_out`、`#ved_u1_deep` が使うものと同じ）から不変量と補助定義
   （`ved_inpU`、`ved_irS`）を作り、`U2HRStmt` の証明を elaborate、`addDecl`、格納型の比較、`strictAudit`（std3）。
4. 失敗は保存した `Command.State`（定数とメッセージ）の restore。deep が根 namespace に置く定数も含め、拒否後に何も残らない（Check が環境全体を比べる）。

不変量: open 回路の register slot `i` ↔ 親の `(regsOf m.body)[i]`（body 順、生成スクリプトの中で kernel が検査。対応が違えば証明が通らない）。
`R ins t p := ∧ᵢ p (親 register i) = irS ins t ⟨i, _⟩`、`irS ins t := Cdo.irState deep nm (inpU ins) t`、`inpU` の入力 slot は
親のデータ入力の signal と、各 child 呼出し（oracle）の signal。`hstep` は `oracleIE` + `regNexts` の `simp` による 1 cycle の評価と、
deep の `_deep_trace` / `_deep_next` の比較（`#ved_u1_deep` の step 証明と同じ形）。

## 6. 対照（`Tests/Ved/U2HierRegCheck.lean`）

正例（各々、完全な型 `U2HRStmt c m d decl`、`std3Only`（機械判定）、`ved_open_eq` の axiom 無し）: `oneInstance`、`threeInstances`（Issue #107 の複製、後述）、
`twoRegsFed`（親 register 2 個を instance 出力で駆動、片方はフィードバック）、`parentMixFlat`、`regCtl`。閉じた run（親 register を含む）を宣言の値と比較: 255, 0, 249, 223（clk を変えても同じ）。

拒否対照（`checkU2HR` を実 synthesis の `(m, d)` を 1 箇所だけ変えて実行。段階と原因の語を検査し、環境全体が元と同じことを検査）。観測した出力:

| 対照 | 段階 | 原因 |
|---|---|---|
| 親 register の init を変える（2 通り） | `[proof]` | unsolved goals |
| 親 register の next を変える（`u - p` → `u + p`、2 register の入力の交換、定数） | `[proof]` | omega could not prove the goal |
| 1 cycle の時間ずれ（出力が register の次の値を読む、2 通り） | `[proof]` | omega could not prove the goal |
| instance の出力 wire の交換、instance 入力の取違え | `[proof]` | omega could not prove the goal |
| 親 register の出力が instance 出力 wire と衝突 | `[order]` | drives a register output |
| register の二重書込み（追加、出力名の重複） | `[order]` | twice |
| 親 register の clock が data 入力 / reset が data 入力 / 両方 / 存在しない入力 / clock と reset の入れ替え | `[hier-shape]` | clock/reset |
| 契約を data 入力の対に強制 | `[table]` | CorrStmt |
| undriven な register 入力 | `[order]` | undriven net |
| 親の組合せループ（register の入力 net を読む wire） | `[order]` | combinational cycle |
| instance の自己ループ（出力が自分の入力） | `[order]` | combinational cycle |
| 入力への書込み、register 出力への assign、register 出力が入力 | `[order]` | write to a top input / drives a register output / register output is a top input |
| instance 入力が register の出力 | `[conns]` | not connected to a parent input |
| 多出力、instance なし、導出式の instance 入力（register あり） | `[multi-output]` / `[scope]` / `[conns]` | H3 / no child instance / not connected to a parent input |

（register を経由するループ `p' = u - p` は組合せループではなく、正例に含まれる。）

「親 register が子の register 名と状態を共有する」: 状態は `(path, 名前)` が鍵なので、親 register の出力名を子の register 名に **付け替えても**
親の slice `[]` と instance の slice `[inst]` は別で、**受理される**（正の対照 `regSh`。名前単位の平坦な状態なら通らない）。閉じた run も付け替え前と同じ。
拒否になるのは、同じ名前が親の **wire の駆動** と衝突する形（instance 出力 wire・assign との衝突、`[order]`、上の表）。
正の対照: 親 register の一貫した改名（`regRn`）、instance の入替え（`regSw`）。

## 7. 実測で見つかったこと

- **入れ子の stateful な inline 呼出し（解消済み）**: `NestedCacheCheck.parentMix`（親の register `p`、`@[hardware_module]` の instance `accMod`、
  **inline の stateful 関数 `accInl`**）の open 親は、以前は `_deep_trace` が `closers exhausted` で失敗した。原因は DeepElab の loop node 発見で、
  入れ子の `runCircuitH` の slot 署名（幅・init）が top と同じだと「top 自身の echo」として捨てられ（`nestedNodes` の署名フィルタ）、
  入れ子 loop が IR の register block に結ばれなかったこと。修正は echo を署名ではなく構文で判定する（top の適用そのもの、特殊化 wrapper の head だけを除く）。
  これで同じ署名の入れ子 node が候補 block 試行（誤った block は step の証明で落ちる）に載る。`parentMix` は `#ved_u2_hier` で strict 受理
  （`Tests/Ved/U2HierRegCheck.lean`）、最小例・2 段の入れ子・拒否対照は `Tests/Ved/U2HierNestedInlineCheck.lean`。
  `parentMixFlat` は従来どおり受理される。
- Issue #107 の `toggle`（`Signal.loop` で `Bool` 出力）は `#verify_elab_deep` が拒否（`could not locate the top-level runCircuitH`）し、
  deep 経路の子は bit-vector 出力のみ（`BitVec 1` は synthesizer が出力 port を `bit` にするので `ShapeCore` が拒否）。
  `oneInstance` / `threeInstances` は構造（1 / 3 個の let 束縛 instance が親 register を駆動）を保って `toggle` を 8 bit の enable 付きカウンタにした **複製**（Check に注記）。
- deep の簡約の限界: 入力が 4 個以上になると open 回路の入力 slot の lookup が `Fin.mk (↑4 - 2) _` / `[…][↑4 - 2]`（依存型のため `simp` が書き換えられない）になる。
  `ved_fin_norm`（`Fin.val` の数値と、閉じた引数の `Fin.mk` を defeq で数値に直す tactic、`Meta.transform`）を `simp` の合間に挟んだ。`-Fin.reduceSucc` を外した。
  これで 3 register + 6 入力 + 3 instance（親の証明 ~8 秒）、4 register + 3 入力 + 2 instance（~20 秒）が通る。#160 の注記にある「register と入力が多いと heartbeat 超過」は未解消の一般的な限界。
- `#verify_elab_deep` は定数の一部を **根 namespace に ident の最後の成分で** 宣言する（`ved_open_deep_body` 等）。同じファイルで 2 つの親を検査すると衝突したので、open 親の名前の最後の成分を宣言ごとに一意にした
  （`ved_open_<宣言名>`、`genOpen` の引数）。残りの deep の定数は `decl` の namespace に置く。
- 証明の case 分割は検査済み arrangement `b0` の instance の順（`m.body` の順ではない: register が `b0` では先に来る）で行う。

## 8. 実際の宣言への適用（lake 外の probe）

`$KJOB_REPORT_PATH` と同じ場所の `h2b-real-rows/`（各 `.lean` は元のテストファイルの宣言を、その `open` と共に写したもの。`#ved_u2_hier` だけを加えている。IP は `kjob lake build IP.Net.ARP IP.Net.HFTStrategy IP.Net.HTTP IP.Bus.PCIeHFT` で構築済み）。
個数は主張しない（coder が harness で 14 行すべてを測る）。

| 行 | 宣言 | 最初の拒否 |
|---|---|---|
| R210 | `synth_arpResponderByte`（Tests/IP/Net/ARPTest.lean） | `[conns]`: instance `Sparkle.IP.Net.ARP.arpPacketByte` の入力 port が親の入力でない（導出式 / 内部 wire） |
| R220 | `synth_hftOutByte`（Tests/IP/Net/HFTStrategyTest.lean） | `[conns]`: instance `Sparkle.IP.Net.HTTP.httpGetByte` の入力 port が親の入力でない |
| R92 | `synth_hftPcieOutByte`（Tests/IP/Bus/PCIeHFTTest.lean） | `[conns]`: instance `Sparkle.IP.Net.HTTP.httpGetByte` の入力 port が親の入力でない |

3 行とも `[scope]`（親が register を持つ）は通過し、次の阻害は H2b の範囲外の「instance の入力が内部 wire」（F2 の一般化）。

### 8.1 追記（2026-11-11、上の 3 行の probe とは別の測定）: 固定 14 行の harness 測定

上の表は実装時の lake 外 probe（3 行）。その後 coder が harness で固定 14 行すべてを u2_hier で測った（a8f3b7d2、run 2da6812270291120、
ran=14、harness_error 0、各 8〜13 s、peak 約 1.7 GiB）。14 行すべての最初の拒否が `[conns]`（子 instance の入力が親の入力でない）で、strict は 0。

| 行 | 子（`[conns]` を起こした instance） |
|---|---|
| R92, R220, R223 | `Sparkle.IP.Net.HTTP.httpGetByte` |
| R193, R194 | `Sparkle.IP.Crypto.SHA512HW.kMux` |
| R210, R211 | `Sparkle.IP.Net.ARP.arpPacketByte` |
| R224 | `Sparkle.IP.Net.HTTP.httpRespByte` |
| R227, R228 | `Sparkle.IP.Net.ICMP.icmpHeaderByte` |
| R230, R231, R232 | `Sparkle.IP.Net.IPv4.ipv4HeaderChecksumSig` |
| R246 | `Sparkle.IP.Net.UsbWebServer.respByteMux` |

測定の制限: harness（scripts/ved）は H2b の branch に無いので未追跡で写し、u2_hier の import を `Tools.VedU2HierRegEntry` に 1 箇所変えた。
strict の probe は旧 `U2HStmt`（register なし）用のままなので、受理された行は strict に数えられない（過少にしかならない）。今回は全行が
`[conns]` で probe に届かないため阻害の記録としてのみ使う。成功を数える前に `U2HRStmt` 用の独立 probe が要る。後段（deep・proof）で通るかは未確認。

## 9. 未了と質問

- **質問 1（parentMix）**: 解消（上、§7）。(b) の橋で通った。
- **質問 2（状態の共有名）**: 「親 register が子の register 名と状態を共有する」拒否は、状態の鍵が `(path, 名前)` なので該当せず、受理（正の対照）とした。拒否にしたい意図が別にあれば指示を求める。
- 親 register を持つ実在 14 行は、14 行すべてで `[conns]`（内部 wire の instance 入力）が次の阻害（§8.1）。F2 の一般化（H2c）が要る。
- レビュー回答（2026-11-11）: 質問 1 は (b) DeepElab の入れ子 runCircuitH→slot の橋を第一候補に別単位で調べる。質問 2 は受理（(path, 名前) で別状態）。
- 子の `#verify_elab_deep` を入口が自動で走らせることはしない（H2a と同じ。親の open 親に対しては入口が走らせる）。
- 閉じた run の数値は小例のみ。親 register の init が 0 でない例は `regCtl`（q の init 1）。

## 10. ビルド

```
kjob lake build Tests.Ved.U2HierRegCheck Tests.Ved.U2HierCheck Tests.Ved.U2HierPin Tests.Ved.U2HierSemCheck Tests.Ved.U1MultiRegCheck
```

結果は報告（`$KJOB_REPORT_PATH`）に記録。`ved.yml` の H2 の step に `Tests.Ved.U2HierRegCheck` を `U2HierCheck` の隣に追加し、`lakefile.lean` に
`Tools.VedU2HierReg` / `Tools.VedU2HierRegEntry` / `Tests.Ved.U2HierRegCheck` を登録した。
