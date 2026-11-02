# U-A7b 調査: D.E-12 の calls 枝 `hsep` の供給元、machine 以外の経路、ClosingRun のデータ前提

- Issue: sparkle-aud-ua7b（親 sparkle-ledger-shorten）。base: par/aud-ua7 7a4b70a8（AUD_UA7_STUDY.md）。文書のみ（Lean のソースは編集していない）。
- 種別: 調査（freeze ではない）。台帳の現在値は変えない: FG 94 / T1 54（今回 0 / 0）。
- 用語: `AuditE12`（scripts/gen5/AUDIT_CARRIER_FREEZE.md:112-117）は
  `∀ w2 raw D, RunsTo (synthesizeCombinationalCore declName [] false) … w (raw, D) w2 → (∀ x ∈ D.modules, x.name ≠ raw.name) ∧ D.topModule = raw.name`。
  `hsep'` は UA7 で出た「calls 枝の子と子の design の module に、名前が `ofDecl declName` のものがない」。

## 0. 結論（先に）

1. **`hsep'` は 2 つの半分に分かれる**（§1）。(a) 子自身の module 名（`ChildIfaceP.name = ofDecl callee`）と `callee ≠ declName`、(b) 子の design の module 名が `ofDecl declName` でないこと。
   - (a) の `callee ≠ declName` は、既存の `hself_all_reached`（Tools/ShippingGen5NameKids3.lean:99）が `InClass`（D.E-8 の `hnd`/`hr`）+ `GraphAgrees` + `ReachSpans` から出す。台帳の既存の行（D.E-6〜E-9）の範囲で、**この調査では新しい前提は見つからなかった**。
   - (b) は、この調査では供給元・経路が見つからなかった（§1-(b)）。具体的な宣言には `decide` で入れる実例（generated code）があるが、一般の補題は見つかっていない。
2. 子が持つ interface 事実（`ChildIfaceP`）と (a)(b) から `hsep'` の形を出す補題を scratch で elaborate した（`hsep_of_ifaces`、§4）。(b) は仮定 `ofDecl declName ∉ nms` のまま。
3. **ClosingRun のデータ前提は接続できた**（§3）。`Pkg.ok` / `Pkg.body_eq`（Tools/ShippingGen2Pkg.lean:88, :94、定理で field ではない）から `transition_closed` の前提 `positive, e, he, hb, hv, hbody` が作れ、ClosingRun の `shared` ブロックの `MReturns (synthesizeMixedCertified … p.d.shape.binders p.d.shape.body)` にそのまま当たる（scratch `e12_data`、`e12_closingRun`、§4）。
4. **machine 以外の経路**: `AuditE12` の型は全経路の run を量化するが、既存の補題で `hno`/`htop` を出すものは machine 経路（と、gate 葉の `hno`）にしか見つからなかった（§2 の表）。選択肢は §5（ユーザー判断の材料）。
5. **E-12 は未解消**。`hsep'` の (b) と machine 以外の経路が残るため、E-12 の −1 は見込みに入れない（§6）。`hsep'` を新しい前提として足した扱いにもしていない。

## 1. `hsep'` の分解と供給元

calls 枝で `hno` が要る形（UA7 §4 `e12_calls` の `hsep`）:

```lean
∀ c ∈ children, ∀ g ∈ c.1 :: c.2.modules, g.name ≠ ofDecl declName
```

`children` の各 `c` は ClosingRun の `ChildrenShipsI`（Tools/ShippingGen2ServedRun.lean:342）で、呼び出し `k` ごとに、(M) メモリ子（`(instOrigins.getD k .ord).child? = some y`、`y = memModule cb aw dw`）か、(R) `RealChildA O (shape.insts[k]).1 y`（＋ reached なら `ShipsRes`）のどちらか。

- (M) メモリ子: `memModule` の名前は `ofMem …`、design は `[memModule …]` で、`ofDecl_ne_ofMem`（Tools/ShippingModuleName）と `memModule_design_modules`（Tools/ShippingSrm12Corr.lean:139）から出る。**在る**（scratch `hsep_of_ifaces` で使用）。
- (R) 実子 `y`: 次の 2 つに分けて探した。
  - **(a) `y.1` 自身**: `y.1.name = ofDecl callee`（`ChildIfaceP.name`、Tools/ShippingMemClosesKids.lean:169）かつ `callee ≠ declName`。
  - **(b) `y.2.modules`**: 子の design の module 名が `ofDecl declName` でない。`ChildIfaceP` では「`own ∉ nms`」（`sep_of_iface` の `hown`、Tools/ShippingSrm3Callee.lean:130）。

### (i) D.E-8 / D.E-9（graphOf、OrdPath、非巡回）

| 項目 | 定理 | file:line | 結果 |
|---|---|---|---|
| 呼び出しグラフを宣言リストから読む | `graphOf`、`callees_graphOf`（`FirstOcc`） | Tools/ShippingSrm15Graph.lean:32, :39 | 在る |
| 順位の計算と辺での減少 | `declRank`、`rkOf_edge`、`rkOf_decl`、`inClass_rank` | Tools/ShippingSrm7Rank.lean:212 ほか | 在る |
| `InClass` を `hnd`/`hr` から | `inClass_graphOf` | Tools/ShippingGen5NameKids6.lean:18 | 在る（`hnd` `hr` は D.E-8 の行で未供給） |
| `ReachClosed` を `OrdPath` で | `reachClosed_ordPath` | Tools/ShippingGen5NameKids7.lean:20 | 在る（`GraphAgrees` が条件） |
| **(a) `callee ≠ declName`** | `hself_of_rank` → `hself_all_reached` | Tools/ShippingGen5NameKids2.lean:80; NameKids3.lean:99 | **在る**（`memKey (originAt sp k) = none → insts[k].1 ≠ c`）。条件: `InClass`、`GraphAgrees`、`ReachSpans`（D.E-6〜E-9 の行） |
| (a) の形の接続 | `hself_all_reached` の結論は `memKey … = none`、`hsep_of_ifaces` の仮定は `child? = none`。同じ内容を `memKey_none_of_child`（Tools/ShippingGen5AuditUA1.lean:71, private）が結ぶ | | 在る（private なので scratch では使わず、`hne` を仮定にした） |
| **(b) 子の design に `ofDecl declName` が無い** | 同じ rank で言うには「design の各 module が `y.1` から辿れる」が要る。`InstClosed`（Tools/ShippingGen2Defs.lean:129）は「各 module をどれかが instantiate する」だけで、`y.1` から到達できるとは言わない（2 つの design module が互いに instantiate する閉路でも成り立つ） | | **この調査では供給元・経路が見つからなかった** |

(b) について: `ModCorr`/`DesignCorr`（Tools/ShippingSrm12Corr.lean:56, :62）と `ran_designCorr`（:210）、`inst_rank`（:333）は、design の各 module の instance 文と呼び出しグラフの辺の対応、および rank が定義されている module について辺で rank が下がることを与える。しかし、design の module の rank が定義されていること、`y.1` から到達できることは与えない。**到達性（design の module がすべて `y.1` から辿れる）か、provenance（下の (iii) 参照）が要る**。これが新しい前提になるのか、既存の行で払えるのかは、この調査では決まっていない。

### (ii) RealChildA が持つ名前の事実（U-A4 の行と関係）

- `RealChildA`（Tools/ShippingChildCacheA.lean:105）は「`synthesizeCombinational c` の run の結果」というだけで、名前の field を持たない。名前は **経路ごと**に出る:
  - machine 葉: `seqChild_of_realA`（Tools/ShippingSeqChildIfaceA.lean）の `hI.name`、design が空（`hI.design`）。`hsep_of_leaf_kids`（Tools/ShippingSeqChildDeepConsumerA.lean:41）が `hsep` をここから出す（`callee ≠ c` は呼び出し側が渡す）。
  - machine の深い子: `deepChild_ifaceP`（Tools/ShippingSrm3Iface）/ `memCallee_ifaceP`（Tools/ShippingSrm3Callee.lean:138）。`hsep` は `sep_of_iface`（:130）で `hC.parent`・`hC.parentD`（`MemCalleeData` の field、:64, :66）から作る。**`parentD : ofDecl C ∉ namesK k` は `MemCalleeData` の field（データ）**。
  - gate 葉: `first_child_name`（Tools/ShippingGateDesignWalk.lean:1184）、`ChildFull.name` / `ChildFull.design = []`（Tools/ShippingGateChildComb.lean:165-170）、`childFull_of_realA`（Tools/ShippingCallsGateA.lean:48）。
  - 一般の `RealChildA` から名前が出る路は、この調査では見つからなかった（route を知る必要がある）。
- U-A4 の行との関係: 名前の事実 `y.1.name = ofDecl (insts[k]).1` は `ran_designCorr` の `hname`（Tools/ShippingSrm12Corr.lean:225）、`hname_of_iface`（Tools/ShippingSrm15Graph.lean:58）の形で既に仮定になっている。**U-A4 の行がこれを払うかは、この調査では確認していない**（U-A4 の文書は読んでいない）。

### (iii) designWith / mem_visited の性質

- `designWith_modules`、`mem_visited`（Tools/ShippingDesignWithG.lean:57, :68）は、calls 枝の `D` の module が「子自身か子の design の module」に限られることを与える（UA7 §2 (f) 前半）。(a)(b) の対象を `children` に限る役割で、名前については何も言わない。
- 近くに provenance の系がある: `Prov`/`Fresh`/`fresh_post`（Tools/ShippingCacheCoherentRun.lean:96, :102, :219）は、**cache の中身の性質**として「各 entry の module は `ofDecl key`、その design の module は memory module か cache の entry の module」を言い、`fresh_post` は key が cache に無い（`m.get? c = none`）ことから `hno` を出す。`entryOk_machine`（Tools/ShippingCacheCoherentCert.lean）は machine 経路でこれを出すが、旧 `RefLaws` の枠で、「`¬ K c`（親が自分の callee の鍵集合に入っていない）」が要る。これは (b) と同じ内容（非巡回）で、**新しい供給元ではなく別の言い方**。現行の `Laws`/`InvAt` の枠に載るかは、この調査では確認していない。

### (iv) 既に `hsep` を仮定にしている定理の呼び出し側の実例

- `ShippingSeqChildDeepFactsA.lean:62`（`deepChild_ranA` ほか :103, :142, :203）、`ShippingSrm4Core6.lean:177` の `hsep` は、呼び出し側で次のように供給される:
  - `ShippingSeqParentGenD2M.lean:120-133`（`_C_hsep`）、`ShippingQuadLeafGeneric.lean:150-157`（`leafCallee_hsep`）、`ShippingSeqParentGenD2.lean:167`: `hsep_of_leaf_kids` に **具体的な宣言の名前の比較**（`by decide` / `decide +kernel`、`hC.GneC`）を渡す。つまり**生成された具体的な宣言ごとのデータ**で、一般の補題ではない。
  - 深い子: `memCallee_ifaceP` の `hC.parent`・`hC.parentD`（`MemCalleeData`）。これも宣言ごとのデータ（`Tools/ShippingGen5NameKids.lean:13` のヘッダも "B3 `hparentD`, B4 `hdisjD`, B5 `hfresh`, B7 `hn` stay OPEN" と書く）。
- 結論: **実例は具体的な宣言への `decide` で、`AuditE12` のように全 run を量化する文を払う一般の補題は見つからなかった**。

## 2. machine 以外の経路で `hno` / `htop` を出す既存の補題（経路ごと）

経路は scripts/gen2/ROUTE_CENSUS.md §1 の番号。`raw`/`D` は core run の結果（`synthesizeFromConst` の戻り: Sparkle/Compiler/Elab.lean:5288-5412）。

| 経路 | core の戻り | `hno` | `htop` | 既存の補題 / 備考 |
|---|---|---|---|---|
| 3 machine 葉 | `(closeMachine …, d₀)` | **在る** | **在る** | UA7 `e12_leaf`（scratch、§4 `e12_closingRun` の葉枝） |
| 3 machine calls | `CloseCalls …` | `hsep'` が要る | **在る** | UA7 `e12_calls`、本調査 `e12_closingRun` |
| 2 mixed gate（葉。`mixedGatePeel` が quote 形） | `synthesizeMixedCertified …` の戻りそのもの | **在る**（full entry の design が空: `ChildFull.design`、Tools/ShippingGateChildComb.lean:170 → core の design も空。§4 `hno_of_full_empty`） | この調査では見つからなかった（`ChildFull` に `topModule` が無い。`transition_closed` は内部で `st.design = (CircuitM.init (ofDecl declName)).design` を得るが export していない: Tools/ShippingTransitionClosed.lean:56。同じ形で scratch `e12_data` が `d₀ = Design.empty (ofDecl declName)` を出すので、前提 `d.ok`・`hbody` 相当が gate 側にあれば出せる見込み） | gate 葉は `gate_child_fullG` / `childFull_of_realA`（premise: `EntryDefines`、quote 形、`he`/`hb`/`hv`） |
| 2 mixed gate（instance root。`unifiedInstanceRoot`） | design に子の design が入る | この調査では見つからなかった | 同左 | `gate_parent_run`（Tools/ShippingGateParentRun.lean:191）は `(∀ x ∈ D.modules, x.name ≠ M.name) → design.modules = D.modules` を**結論の一部（含意）**として持ち、前件は出していない |
| 1 first gate | `synthesizeCertified …` | 葉は `first_child_name`（:1184）で name、design の形は `ChildFull` 相当（`first_child_fullFacts`）で空 | この調査では見つからなかった | gate 葉と同じ。親（instance 付き）は上の行 |
| 5 memo | `sparkleSubModuleCache` の過去の結果 | この調査では見つからなかった（過去の結果が E-12 を満たすという cache 不変条件が要る） | 同左 | `MemoInv`/`KeepsMemo`（G-MEMO open、ROUTE_CENSUS.md §2） |
| 6 legacy | 他の `defnInfo` | この調査では見つからなかった | 同左 | `legacy_translate_contract`（LegacySemContract:264, :327）は契約のみ。測定は `writer_prints_endpoint_artifact` の注記 37/37（測定であって証明ではない） |
| 7 parametric | `synthesizeCombinationalWithParameters`、top は 6 | この調査では見つからなかった | 同左 | ROUTE_CENSUS.md: none found。`AuditE12` の `[] false` の core には parametric は入らない（`parameters = []`、`symbolicMode = false`）ので、**7 は `AuditE12` の量化の外**と読める（要 reviewer 確認） |

補足（新規に scratch で通した小補題）: `full_modules_length`（full entry の design の module 数 = core の design の module 数。post pass が `modules.map` のため）と `hno_of_full_empty`（full entry の design が空なら core の design も空 → `hno`）。§4。

## 3. ClosingRun のデータ前提（`d.ok` / `hbody`）と `transition_closed` の前提の接続

- `transition_closed`（Tools/ShippingTransitionClosed.lean:35）の前提: `positive : PositiveBinders bs`、`e`、`he : e.WF kb kv vw`、`hb`、`hv`、`hbody`。
- `seqChild_ifaceA`（Tools/ShippingSeqChildIfaceA.lean:63-100）は、これらを `d.ok = true`（unfold）と `hbody` から作っている。
- ClosingRun 側: `p : Pkg ι dom` が引数で、`shared` の `MReturns (synthesizeMixedCertified … p.d.shape.binders p.d.shape.body) (t, d₀)` が `p.d.shape` を使う。`Pkg.ok p : p.d.ok = true` と `Pkg.body_eq p : p.d.shape.body = quote …`（Tools/ShippingGen2Pkg.lean:88, :94）は**定理**（場合分けで証明済み、field ではない）。よって **接続は新しい前提なしで通る**（scratch `e12_data`、`e12_closingRun`）。
- `d.callsOk` / `hslots` / `hdomB`（`DataRows`、Tools/ShippingGen2PostFacts.lean:56-60）は、本調査の補題では**使わなかった**（`transition_closed` には要らない）。

## 4. scratch での elaborate（`set_option autoImplicit false`、`kjob lake env lean`）

ソースツリーには入れていない（scratchpad）。結果は §6 の末尾に追記する。

SCRATCH_RESULT_PLACEHOLDER

## 5. 選択肢（ユーザー判断の材料）

`AuditE12` は経路の guard を持たず、全 run を量化する。既存の補題で `hno`/`htop` が出るのは machine 経路（と gate 葉の `hno`）に限られる（§2）。

| | 内容 | 影響 | コスト | 可逆性 |
|---|---|---|---|---|
| A. 型に guard を足す | `AuditE12` の前件に `Reach declName`、`P declName = some q`、`MachineTaken L mctx cctx n declName q.d.shape raw D`（Tools/ShippingGen2Defs.lean:136）などを足す。`PostFactsStmt` は既に `MachineTaken` を前提に持ち（Tools/ShippingGen2PostFacts.lean:39 以降）、T1 の scope は route 3（`T1Hyp.closes`）なので、消費側（`ihAt_stepPF` → `writer_prints_endpoint_artifact`）の使い方と合う見込み | 台帳の文の変更（freeze に reviewer の承認が要る）。消費側が guard を渡せるかの確認が要る（この調査では `ihAt_stepPF` 側の引数までは確認していない）。FG は縮めない（T1 は FG ではない、ROUTE_CENSUS.md §2） | 小（型の変更と UA7 の補題を ClosingRun に載せる、scratch 済み） | 型は後から変更可。変更する場合は freeze のやり直し |
| B. 経路ごとの補題を作る | gate 葉、gate instance root、memo、legacy で `hno`/`htop` を個別に出す | 型は変わらない。ただし memo（G-MEMO）と legacy（契約のみ）は既存の枠に載っていない。機械的に出せるのは gate 葉（`hno` は scratch 済み、`htop` は `e12_data` と同じ形で見込み）まで | 大（memo は cache 不変条件、legacy は契約を超える証明が要る可能性。見積りは未） | 補題の追加は後から可能 |

推奨: **A**（理由: 消費側が既に `MachineTaken` を持つ形で、T1 の範囲と同じ。B の memo / legacy は M4 の risk 条項に属する）。ただし (b)（`hsep'` の design 半分）はどちらの選択肢でも残る。判断しない場合: E-12 は未解消のまま、`hno`/`htop` の台帳行は動かない。

## 6. 台帳の見込み

- 受入済みの台帳: FG 94 / T1 54（今回 0 / 0）。
- 条件付き台帳: E-12 の −1 を**主張しない**。−1 になる条件:
  1. `hsep'` の (b)（子の design の module 名）に供給元ができる。**既存の行で払えるなら 0、新しい前提なら +1**（差し引き 0。相殺しない）。(a) は既存の D.E-6〜E-9 の範囲で、この調査では 0。
  2. `AuditE12` の経路の扱い（§5）が決まる。
  3. ClosingRun のデータ前提（§3）は新しい前提 0 で接続できた。
- 新しい前提: 今回の調査が増やした数 0。上の (b) が +1 になりうる（未決）。

## 7. 次

- reviewer: §1 の分解（特に (b) の読み）、§2 の表（特に 7 parametric が量化の外かどうか）、§5 の選択肢の整理を確認。
- ユーザー判断: §5（A / B）。決まれば freeze（台帳の文の変更を含むので reviewer 承認が要る）。
- 続く調査の候補: (b) の供給元（design の module が `y.1` から到達できる、または provenance `Prov` の現行枠での形）。mutant は扱っていない。
