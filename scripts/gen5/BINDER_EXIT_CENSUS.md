# FG 残り 88 行の束縛変数の出口の調査（文書のみ）

Issue: `sparkle-ledger-binder-census`（親 `sparkle-ledger-shorten`、agent rt182）。Lean は書いていない。build していない。
base: 392dc221（par/hord-run）。台帳の根拠: FG `par/fg-ledger-sync` §8.2 の行表と §12.11（FG 88 = リーフ 62 / 非リーフ 26）、T1 `par/t1-ledger-sync`（57）。比較資料 `origin/par/ledger-exit-compare:scripts/gen5/LEDGER_EXIT_COMPARE.md`（§3、§4.3）。手本 `scripts/gen5/HORD_RUN_FREEZE.md`。
**台帳: FG 88 / T1 57（今回 FG -0 +0 / T1 -0 +0）。** この資料の −n は見込みで、受入済みの台帳は変えない。
詳細（各行の根拠の全文）: `scripts/gen5/BINDER_EXIT_CENSUS_DETAIL.md`。

書き方の約束:
* 「確認」= ファイルを開いて署名・本体を読んだ（Lean は走らせていない）。「読み」= 文書とコードの読みで決めた。この資料の分類はほぼ全て「読み」である。
* 「見つからなかった」は「この調査では供給元・経路が見つからなかった」の意味で、不可能・導出不能とは言っていない。
* mutant は出てこない。出てくる場合は signature / defeq での棄却で、意味的反例ではない。
* 費用の行数は推定で、測った値ではない。
* 裁定（2026-11-05）: 非リーフの行を外せるのは、FG の定理の束縛変数が実際に消えるか、既存の行に Lean で置き換わったときだけ。名前・役割の一致だけでは外さない。この資料の P / R はその条件を満たす道があるかを見たもの。

## 0. 結論（先に）

1. 88 行の分類（読み）: **P 16 / R 5 / D 14 / U 25 / X 28**（合計 88）。R は run から出せそうなもので、うち 3 つは条件付き（B.P-1、B.P-8、C.EN-3）。
2. **run だけから束縛変数を消せる行は、この調査では本質的に見つからなかった。** gate 系（B.G-*）は per-declaration の生成定数の kernel 事実で、run が「どの枝を通ったか」の証拠を持たない。env 系（C.EN-*）は第 2 の Laws L′ と全 world の `ReadsAt` が要り、run は特定の world 列しか与えない。reader の `partial def` に当たる行（C.RK-6、C.DO-2、C.CV-4、N2-b など）は、証明から展開できない。
3. **既存の証明済み定理で置き換わりそうな行（P）が実質の候補**。ただし多くは「定理は別 branch にある」「統合 tree が無い」がつく（§2 の各候補に書く）。
4. 上位候補（§2）: ① C.RK-1（C.EN-4 の conjunct から、リーフ −1 の見込み。projection・elaboration と Check が通るまで台帳は減らさない）、② C.RR-2（base の `entryWitness_left_postEntry`。**default route 限定**で、一般 FG の減算は parametric の橋が揃うまで 0）、③ A.P-13（`stepStmtCases_of_rows`、統合待ち）、④ carrier を `dataOfAt` に固定する一括単位（C.AC-9 / C.CV-5 / C.SM-1 の半分）、⑤ C.CV-6（`hcb` の新補題）。
5. 文書だけで外せそうに見える行（A.P-07、D.T-2、C.SM-7、D.D-8）は、A.P-22 型の「FG 側に独立した束縛変数が無い」読みだが、上の裁定では**単独では外せない**（既存の行に Lean で置き換わる定理が要る）。候補としては挙げるが、数えない（§2.6）。
6. 台帳の数・行の文は変えていない。新しい TRUSTED / law、FG の縮小、GenWF の強化は提案していない。

## 1. 88 行の表

分類: R = run や既に取っている仮説から出せそう / P = 既存の証明済み定理で既存の行に置換 / D = パッケージのデータの性質（データ供給側）/ U = この調査では経路が見つからなかった / X = 現時点では一般定理から支払い不可。
「定理」= その束縛変数を取る（または carrier として出す）FG 側の定理。base = 392dc221。`rad` = DG 系の統合 branch、`rtF` = par/rt-final@378f8e31、`g2st-r6` = kjob/g2st-r6@2be39bc4。**FG の root（`Tools/ShippingGen5FG.lean` の `FG_CONNECT`、`Tools/ShippingGenFGLedgerPremises.lean` の `FGLedgerPremisesStmt`）の束縛変数として直接現れる行は少ない**（`FGLedgerPremisesStmt` は 14 行しか型を持たない、FG 台帳 §8.1）。残りは供給側の定理（括弧内）の束縛変数。

### 1.1 A 群（A.P-*、23 行）

| ID | 束縛変数 | 定理 | 分類 | 要点（読み/確認） |
|---|---|---|---|---|
| A.P-01 | `L : Laws` | 全定理 | X | TRUSTED 候補。法則は run の事実でない。確認（定義） |
| A.P-02 | `Start`（EntryWitness 前件） | `FG_CONNECT` FG.lean:54 | X | 保証の前件。供給する対象でない |
| A.P-04 | `RunsTo (synthesize…)` ∨ | 同上 | X | 前件そのもの。default route の分解は証明済み（`synthesizeCombinational_postEntry` DCEntryD.lean:28）だが前件は消えない |
| A.P-05 | carrier `Post` | `o1_default` DCEntry.lean:46 | U | default は証明済み。parametric の後処理は未承認 |
| A.P-06 | `T1Hyp.defines` closure | `closingRun0_of_runR` ClosingRun3.lean:44 | U | `MachineDefines` は全 world の文。候補 `machineDefines_of_readsAll` Env.lean:69 は C.EN 側が閉じないと経路にならない |
| A.P-07 | `ran : MachineTaken` | `memParent_ships` 他 / `stepStmtCases_of_rows`（g2st-r6） | P | T1.lean:242-244 が `hT.closes` から出す。FG 側に独立束縛変数が無い（裁定上は §2.6） |
| A.P-08 | `T1Hyp.pkg`（`GenFacts` 等） | `callDec_of_hPointG_at` CallField.lean:131 | D | `GP`/生成器の健全性は一般には無い |
| A.P-09 | DataOkB の行（ok/callsOk/ss.length/outTy/outHead） | `callDec_of_callTie` T2Tie.lean:298 | P（部品別） | `ok`=`Pkg.ok`、`ss.length`=`Pkg.ss_length`（k1-pa）、`outTy`=`outTy_of_core`（R）。`callsOk`=T1L-39、`outHead` は経路なし。行は残る |
| A.P-10 | `MemParentDataOk`（5 行） | `memParent_ships` 他 | D | 5 行のうち ok / ss.length / outTy は出る。`callsOk` と `.domain` が残る |
| A.P-11 | `LeafDataOk`（4 行） | `leaf_ships` Leaf.lean:274 | D | 同上。`callsOk` が残る |
| A.P-12 | `ExtInS p` | `leaf_ships` 他 | D | `.comb` は定義から出る見込み。`.gen/.loop` は供給元なし |
| A.P-13 | `hmo : MemOrigin p` | `memParent_ships` | P | `stepStmtCases_of_rows`（g2st-r6）が `memOrigin_of_memDec`（base MemFacts.lean:51）で内部生成。確認。統合待ち |
| A.P-14 | case 前提（O1/L/M/X/S/C） | `StepStmtCases`（g2st-r6） | U | O1 の `hord` と case X は `runShape_noMemRow`/`caseX_run_absurd`（t1l18-conn）で出る。群親 G0/G1 と case S は `TopShips` を結論とする定理なし |
| A.P-15 | `hrst : "rst" ∉ inputs` | `oneOutSl_topShipsNC` SlotlessTop.lean:447 | U | 宣言の入力の性質。run から出す補題なし |
| A.P-16 | `MemDec`（T1L-26） | `memParent_ships`、`stepDec_of_ties` | D | 結論とする定理なし。宣言ごとの kernel チェック |
| A.P-17 | `T1Hyp.dec` | `StepStmt`、`stepDec_of_ties` T2Tie.lean:312 | P（候補） | 葉は A.P-16/18/19, D.T-1/4。`dec` を置換すると ClosingRun→IH→`dec` の循環の有無が未確認 |
| A.P-18 | `HPointAt`/`CallFactF` | `callTie_of_dgen` T2Tie.lean:259 | D | D.T-1/D.T-2 に分解。生成器 family の LetTie が未固定 |
| A.P-19 | `DataCallAt`（arity/args） | `callDec_of_hPointG_at` | R（arity）+ U（args） | arity は `callArity_noIota_of_trace`（flowb-b）で trace から。args は `ArgWidthAt` そのもの、経路なし |
| A.P-21 | （retired）`hseq` | `group_childShips` | P | 署名に `hseq` なし。確認 |
| A.P-23 | `LiftShips` | `servedP_lift_of_liftShips`（g2st-r6） | U | 結論とする定理なし |
| A.P-25 | `OneOutWidth`（T1L-14） | `oneOut_topShipsO` OneOutTopO.lean:336 | D | `oneOutWidth_of_strictP` は Bool 行 `callWidthsStrict` に置き換えるだけ。ゲート追加は共有定義/コンパイラの変更（X 寄り） |
| A.P-27 | `TopShips` の実行前件（非空虚性） | `TopShips` Defs:288 | U | 結論側の前件。監査 |
| A.P-28 | `PbhRunEx L` | `ptop_pbh_ofEx`（g2tc-ptop19） | U | 非空虚な `Laws` の値は見つからず（`lawsQuietFalse` では偽）。監査 |

### 1.2 B 群（B.*、C.RR-2。17 行）

B.G-* は FG の束縛変数ではなく carrier `ReflectsAll`（D.D-1）の構成要素。束縛変数が出るのは供給側の定理（`fg-assembly` に Lean なし）。

| ID | 束縛変数 | 定理 | 分類 | 要点 |
|---|---|---|---|---|
| B.G-1 | `entry : EntryDefines`（B.G-8/F-6/F-7 統合） | `gate_combChildRunN` GateLeaf.lean:221 @gen4-gate | X | package の値と環境を結ぶ反射。A.P-06 と同種 |
| B.G-3 | `old`（certifiedShape?=none） | `gate_core_facts` ShippingGateChild.lean:55 | D | 生成器が `rfl` で作る per-declaration の事実（GateChildCommand.lean:89-92）。route 証拠（mixed 枝を通った）が run に無い（`synthesizeFromConst_mixed_run` は仮説に取る） |
| B.G-4 | `peel`（mixedGatePeel=some …） | 同上 | D | 生成器が `rfl`。Expr→Term の復号が見つからない |
| B.G-5 | `he : e.WF …` | 同上 | D | 生成器が `decide`（GateChildCommand.lean:93-96） |
| B.G-6 | `hb`/`hv` | 同上 | D | binder 位置の `decide` |
| B.G-7 | `hw1 : g.srt.width ≠ 1` | `gate_full_outputs` GateKid.lean:90 | U | 出力型が `d.type` 依存。候補: `GateRec` に出力型を持たせる（共有定義の変更） |
| B.G-9 | `Q`/`hQ` | `gateLeaf_shipsResI` @gate-p123 | X | 表 `GT` への置換は共有定義の変更。2026-11-02 に見送り |
| B.G-10 | U-G7a `InstCore` 他 | `instParent_combChildRunN` @g4gate-g5 | U | 未 review。FG との対応が台帳に無い |
| B.F-8 | 非 fragment の `ChildRunN` | `childRunN_dz_instFree` @fb-resume | X | legacy の意味論そのもの。first-gate fragment 分は既存 FB-22 で P |
| B.P-1 | `AllPos θ` | `legalBinding_allPos` BridgeLegal:79 | R（条件付き） | 結論を `ParamTopShips`（`∀ θ, LegalBinding … →`）形にすれば前件から出る。FG の結論型の差し替えは reviewer/ユーザー判断。FG 側にまだ束縛変数なし |
| B.P-2 | `Bound/PosDim/NonNegDim/SliceOK` | `specTypeM_ok` SpecType:44 | X | translator が `.sub/.div/.mod` を出し `PosDim` が排除する。run から出ない |
| B.P-3 | `ExprOK/TyPos/TyBound` | `specExprM_ok` SpecExpr:159 | X | B.P-2 に同じ |
| B.P-4 | B1–B4 production↔model | PARAMETRIC_BRIDGE_FREEZE | X | `evaluate` 等が `partial`（opaque）。total 化か新 law でユーザー判断 |
| B.P-5 | `SpecSuccessAllPositive` | ParamIface | X | ユーザー判断 D3。範囲の縮小に当たる |
| B.P-7 | I3c 旧 `RefLaws` 上 | `core_symbolic_keeps` ParamKeeps:103 | U | `Laws` からの変換なし。候補: A-family への移植 |
| B.P-8 | `LegalBinding D θ` | `specializeDesign_ok_legal` | R（条件付き） | B.P-1 と同じ |
| C.RR-2 | entry run → core run `hr` | `entryWitness_left_postEntry` DCEntryW.lean:34 @base | P | base の `entryWitness_left_postEntry`＋`synthesizeCombinational_postEntry` が橋。確認。台帳の「橋の命題は見つからなかった」は古い |

### 1.3 C 群のうち env / reader / closing 系（18 行）

| ID | 束縛変数 | 定理 | 分類 | 要点 |
|---|---|---|---|---|
| C.CR-2 | `hGen`（`Gen` 述語） | `closingRun0_of_runR` ClosingRun3 | U | `genP_generated`（g5ac-r27）経路は `GenSFacts` 等を足す（移動で置換でない） |
| C.CR-4 | `hT : T1HypND` | 同上 | X | 束縛変数は残る。数え方の判断だけ（LEDGER_CROSSCOUNT_DECISION と同種） |
| C.EN-1 | `QuietStrength L L' env₀` | `quiet_down` EnvQ.lean:46- | X | `L′` の構成（`RefLawsAOps` 9+`RefLawsATele` 4 field）の経路なし。env₀ は `envAt cref w` で取れる |
| C.EN-2 | `AdmDown L L'`、`hA'` | `realChildA_down` 他 | X | `AdmCtx` の `canUnfold?` は任意関数。run は context を持たない |
| C.EN-3 | `hC/hE/hN`（start cache） | `start_up_of_parts` EnvStart.lean:22 | R（条件付き） | `head_jqc_start`（EnvQ Q10）は取らない。depth0 の根で不要にできる見込みだが EN-1/EN-2 が未供給なので実質の前進は reviewer 判断 |
| C.EN-4 | `CellPrem MkRefd mref cref` | `h_C_EN4` FGLedgerPremises.lean:41 | X | 不透明な `ST.Ref.get/set` の命題。run は「return した」しか言わない |
| C.EN-5 | `¬ DRow p`（13 constructor） | `frameQ_plus` EnvFrame3 | X | `whnf`/`inferType` 等は opaque。translator body が実際に呼ぶ |
| C.EN-6 | C0 `hall` 他 | `machineDefines_of_readsAll` Env.lean:69 | X | `hall` は全 world。depth0 では `readsAt_self`+RK-1+RK-2 で出るが `T1HypND.defines` を変える共有定義の変更 |
| C.EN-7 | `hentry` | `synthesizeChild_realN` EnvCacheE:30 | U | 旧 `hentryT_of_bodyP` 経路は T1 側。N 版の供給元なし |
| C.EN-8 | `canUnfold? = none` | `start_up_empty` | X | FG の `Start` より狭い（範囲の縮小）。ユーザー判断 |
| C.RK-1 | `ReadKeeps cref` | `h_C_RK1` FGLedgerPremises.lean:42 | P | `CellPrem` の 9 番目 conjunct `ReadWorld cref` に `ReadWorld.readKeeps`（base StRefCorrespondence.lean:50、確認）。§2.1 |
| C.RK-2 | `EnvFrame (coreHead X)` | U13/U12b @g5rk-r23 | U | `coreHead` は IO.getEnv・ログ・ref を含む。`DRow`/`Diag` の経路なし |
| C.RK-4 | `hrun`(readMachine)・`hX` | U13 | U | `hX` は `rfl` で消える。`hrun` は補助コマンドの run で供給元なし |
| C.RK-6 | `ReflExprAgree` | `h_C_RK6` FGLedgerPremises.lean:43 | X | `reflExpr` が `partial def`（ShippingEntrySoundness.lean:1737）。全域化はコンパイラ変更 |
| C.RK-7 | U14 `hM`/`hC` | U14c（設計のみ） | U | RK-1→EN-4 / RK-2 に帰着。新 payer なし |
| C.RK-8 | `Complete cfg` 他（per d） | `readN_quote` @g5rk-r23 | D | endpoint 構成では `kindsCfg_complete'`。生成データの性質 |
| C.DO-2 | `Rdr`、`s = sp` | DG_DATAOF_FREEZE §11.3 | X | Lean 命題なし。`partial def` が不透明 |
| C.DO-3 | row 6a/C-CMP/C-QWIT/S-OK/S-COV-FLOAT | 同 §4,§11.2 | U | 名前のみ。束縛変数として扱えない |

### 1.4 C 群のうち SM / AC / CV / DG と D.D-*（17 行）

| ID | 束縛変数 | 定理 | 分類 | 要点 |
|---|---|---|---|---|
| C.SM-1 | `DataOfSound` ＋被覆 `dataOfAt = some d` | `GenData.toIn` SemGenData:34 @rad | P（hs 半分）＋ U（被覆半分） | `dataOfAt_sound` で `hs` は消える。被覆は C.AC-4 と同じ義務 |
| C.SM-6 | `GenWF d = true` | `genWF_of_rows` Cover:104 | U | 7 連言のうち 6 は reader から出る。b23 の letSort 4 等式（B3）が残る |
| C.SM-7 | `hord`（originOf.child?=none） | `genExtAtCall_of_genSem` SemExtPkg:17 | P | `originOf` は定義上 `instOrigins.getD k .ord`。`h_D_T1` の前件に同じ guard がある（読み） |
| C.AC-4 | `ReachCover`・`hcl` | `genS_isSome_of_cover` Acc:210 | U | `hcl` は P。被覆の (S) は R 候補だが carrier 未固定 |
| C.AC-5 | `GatesNoneAt env₀ Reach` | `machineRouteAt_of_cover` AccRoute:49 | U | `RunReadsAt.gates` が実 run の gate 情報を持つ（R 候補）。Reach 全体への拡張が要る |
| C.AC-7 | `ReadsSupplyAt e L Reach` | `readsSupply_of_quiet` AccReads:99 | P（条件付き） | `QuietStrengthA`（C.EN-1）と `GetEnvFrame`（C.RK-1）に置換。ルートを L′ 上で述べる必要 |
| C.AC-9 | `RunDataLink`・`hDS : DataOfShape K` | `accServed0_of_cover` AccServed:445 | P | `dataOfShape_of_sound`（AccDataSound:30）、`mkKit_dataSound` |
| C.CV-4 | `ShapeFuelBridge` | `shapeAgree_of_production` Cover5:97 | X | `machineShape?` が `partial`。全域化はコンパイラ変更 |
| C.CV-5 | `hsp/hss/hls/hn`（reader state `st`） | `shapeAgree_of_sides` Cover5:76 | P | `st` は `readerTrace_final` の結論の ∃ 変数で束縛変数でない。4 節は `dims_of_dataOfAt` と `StateSideWitness` から出る。台帳の「run-local」の注記は当たらない |
| C.CV-6 | `hcb`（R-in/R-dom は名前のみ） | `rowB1_of_inv` Cover3:798 | R | `machineShape?_callBinder`（base ShippingMachineShapeTail.lean:61）＋`dataOfFrom_nIn` で `hcb`。台帳の「hcb は B3」は取り違えの可能性。R-in/R-dom は `readerTrace_final` 経由 |
| C.DG-1 | `dataOf` 成功・`GenWF`・`P = genP env₀` | DGEN_FREEZE / `genP_generated` | P（条件付き） | C.AC-4、D.D-3 に帰着 |
| D.D-1 | carrier `ReflectsAll` | `FG_CONNECT` FG.lean:54 | X | 簿記用の carrier。定義を与えること自体が各 route の行の供給 |
| D.D-3 | carrier `GP` | `FG_CONNECT` | P（条件付き・要ユーザー判断） | `GP := genP (K env) (hF env)` に固定。FG の結論を DGEN 経路に特化する選択 |
| D.D-4 | carrier `CV : ConstValueRel` | `FG_CONNECT` | U | `ConstValue` の定義が全 branch で見つからない |
| D.D-5 | `hAcc/hclosed/hstep` と順序 `R` | `declConnect_of_rows` DeclConnect:300 | U | `hclosed` は R、`hAcc` は P（C.AC-8）、`hstep` は未供給 |
| D.D-7 | `NoRawBelow`（hno） | `noRawBelow_of_closeInsts` DCEntryS:27 | U | 候補 `noRawBelow_of_coreRun`（g5dc-r23、未レビュー）。leaf と (a3) が残る |
| D.D-8 | `hlk`（moduleByName 保存） | `postEntry_lookup_ne` DCEntryN:84 | P | default route は証明済み（確認）。parametric は `Post` 未供給で対象外 |

### 1.5 D 群 T/E と後から加えた 7 行（13 行）

| ID | 束縛変数 | 定理 | 分類 | 要点 |
|---|---|---|---|---|
| D.T-1 | `GenExtAtCall` | `FGLedgerPremisesStmt` :55-58 | D | `ext` の選び方の性質。run は縛らない。`genExtAtCall_of_genSem`（candA）は `GP` を `genP K hF` に固定し `hF` が要る（§2 では扱わない、要ユーザー判断） |
| D.T-2 | `CallOutRange`（PA） | `callOutRange_of_widths` T2Range:162 | P | FG の root（ND 側 `callTie_of_served_*_t1ND`）は取らない。確認。非リーフの派生（裁定上 §2.6） |
| D.T-4 | `hkidW` | `FGLedgerPremisesStmt` :59-64 | D | RealChildA は子側の出力のみ。親の binder 幅との突合は `callWidthsOk` の行。コンパイラ側にゲートなし（`git grep` 0 件） |
| D.E-4 | 束 B3/B4/B5 | `machineClosesAtA_of_memKids'` ShippingCallsMemPinned:330 | U（束・行は残る） | B3: `auditE3B3_of_t1hyp_run` で名前部分は供給済み（P）。B4: ユーザー判断で残す（X）。B5: 未判断（U） |
| D.E-12 | `hno`/`htop`（束） | `writer_prints_endpoint_artifact` DesignWriterRun:119 | U（束・部分供給） | machine の htop・leaf の hno は UA7b の scratch のみ。calls 枝の子 design 名と非 machine の hno は経路なし。§3 |
| D.E-13 | （束縛変数なし）G7-c 印字 | — | X | TRUSTED by design。保証の外 |
| SigTyClosed | `SigTyClosed (structEnv env)` | `readerTrace_final` @rtF | X | 環境の事実。`Lean.Environment` は未モデル化 |
| InstSFieldsDet | `InstSFieldsDet` | 同上 | X | `partial def machOuts?` の型付けの事実 |
| N1-a DeclValuePh | `DeclValuePh env` | 同上 | X | 環境の事実 |
| N2-b PackTupleInputsBridge | `packTupleInputs` = `packTupleInputsF …` | 同上 | X | コンパイラ内部の `partial def` の等式。除く道はコンパイラの全域化 |
| N3-b RawNodePh | `RawNodePh` | 同上 | X | `partial def betaRev` 等の範囲保存 |
| N3-b NormNodePh | `NormNodePh` | 同上 | U | 候補 N3-c（`par/ptot-m4` 統合後）。費用大、確かさ低 |
| RecRulePhU | `RecRulePhU env` | `shapeInputs_of_inline'` @rtF | X | 環境の事実 |

（後から加えた 7 行の Lean は base に無く、par/rt-final@378f8e31 にある。）

### 1.6 件数

| 群 | P | R | D | U | X | 計 |
|---|---|---|---|---|---|---|
| A（23） | 5 | 1 | 7 | 7 | 3 | 23 |
| B + C.RR-2（17） | 1 | 2 | 4 | 3 | 7 | 17 |
| C env/reader/closing（18） | 1 | 1 | 1 | 6 | 9 | 18 |
| C SM/AC/CV/DG + D.D（17） | 8 | 1 | 0 | 6 | 2 | 17 |
| D.T/D.E + 追加 7（13） | 1 | 0 | 2 | 3 | 7 | 13 |
| **合計** | **16** | **5** | **14** | **25** | **28** | **88** |

リーフ 62 / 非リーフ 26 の内訳では、非リーフ 26（A.P-01/02/04、T1 区分 12、PA 6、XC 3、AU 2）の多くが A 群と D 群の X/P に当たり、リーフ 62 の大半は U と X。

## 2. 上位候補の減算表

候補は「束縛変数が実際に消える、または既存の行に Lean で置き換わる」道があるもの。いずれも本調査では Lean を走らせていないので、確かさは「読み」の確かさ。

### 2.1 候補 ①: C.RK-1 を C.EN-4 から出す（P）

| 項目 | 内容 |
|---|---|
| 消える ID | C.RK-1（`h_C_RK1`、リーフ） |
| 消える条件 | `FGLedgerPremisesStmt` の `h_C_RK1 : ReadKeeps cref` を、`h_C_EN4 : CellPrem …` の 9 番目の conjunct `ReadWorld cref` と `ReadWorld.readKeeps`（base `Tools/ShippingStRefCorrespondence.lean:50`）から証明の中で出す |
| 残る条件 | C.EN-4（`CellPrem`）。置換先が TRUSTED かの A/B/C 判断（DG_ENV_FREEZE §4、記録なし）は動かない |
| root theorem（型案） | `theorem readKeeps_of_cellPrem {MkRefd} (h : CellPrem MkRefd mref cref) : ReadKeeps cref := ReadWorld.readKeeps h.2.2.2.2.2.2.2.2.1`（添字は `EnvFrame3.lean:58-63` の並びによる。読み） |
| 費用 | 補題は数行。`FGLedgerPremisesStmt` から `h_C_RK1` を除く statement 変更と Check の期待値更新を含めて約 150 行（推定） |
| 確かさ | 高（`readKeeps` は証明済み、確認）。conjunct の位置（projection）は未確認。**projection の elaboration と Check が通るまで台帳は減らさない**（reviewer 2026-11-05） |
| freeze / TRUSTED | freeze 要（行の除去は reviewer 承認の対象）。新しい TRUSTED/law は不要 |
| 新しく増える行 | なし。純差分 FG **−1（リーフ）** |

### 2.2 候補 ②: C.RR-2 を base の既存定理で置換（P）

| 項目 | 内容 |
|---|---|
| 消える ID | C.RR-2（entry run → core run の橋、UN-B） |
| 消える条件 | `entryWitness_left_postEntry`（base `Tools/ShippingGen5DCEntryW.lean:34`）と `synthesizeCombinational_postEntry`（`ShippingGen5DCEntryD.lean:28`）が、`EntryWitness` の run から core run `hr` を出す（default route）。parametric 枝は別（B.P-6 / D.D-2 の `Post` が未承認） |
| 残る条件 | parametric route の core run への橋。A.P-04 の前件 |
| root theorem（型案） | 新規なし。既存定理を `closingRun*_of_run*` の `hrun` へ配線する小定理（default route 限定）。型案は DETAIL の out_2 の C.RR-2 行 |
| 費用 | 20〜40 行の配線（推定） |
| 確かさ | 高（定理は base にあり build 済み、確認）。ただし C.RR-2 が FG のどの束縛変数に当たるかの対応（台帳に「橋の命題が無い」とある行）を reviewer が読み替える必要。default route 限定の範囲になる |
| freeze / TRUSTED | freeze 要。TRUSTED 不要 |
| 新しく増える行 | なし |
| 台帳への効果（reviewer 2026-11-05 の修正） | **一般 FG: 0**。`EntryWitness` は parameterized route も含むが、`entryWitness_left_postEntry` / `synthesizeCombinational_postEntry` は既定の `synthesizeCombinational` route だけを扱う。parametric の橋（B.P-6 / D.D-2）が揃うまで一般 FG からは −1 と数えない。**default route 限定の見込み**: −1（一般台帳の減算ではない。IP 限定の結果と同じく別欄） |

### 2.3 候補 ③: A.P-13（MemOrigin）を `stepStmtCases_of_rows` で置換（P）

| 項目 | 内容 |
|---|---|
| 消える ID | A.P-13（PA、非リーフ） |
| 消える条件 | `stepStmtCases_of_rows`（kjob/g2st-r6@2be39bc4 `StepDispatch.lean:63`）は `hmo` を束縛変数に取らず `memOrigin_of_memDec`（base）で出す。この定理が FG の組み立てに入ること（g2st-r6 の統合） |
| 残る条件 | A.P-16（MemDec、T1L-26）、T1L-41（`Nonempty ι`）。base に `stepStmtCases_of_rows` が無い |
| root theorem | 新規なし |
| 費用 | 0（統合は coder / ユーザーの merge） |
| 確かさ | 中〜高（本体を読んだ。Lean は走らせていない） |
| freeze / TRUSTED | 不要（数え方の確認のみ）。新しい行なし。FG **−1（非リーフ）** |

### 2.4 候補 ④: carrier を `dataOfAt lvl` に固定する一括単位（C.AC-9、C.CV-5、C.SM-1 の半分）

| 項目 | 内容 |
|---|---|
| 消える ID | C.AC-9、C.CV-5。C.SM-1 は `hs` 半分のみ（被覆半分は C.AC-4 と同じ義務で残る） |
| 消える条件 | `dataOfShape_of_sound`（AccDataSound:30）で `hDS`、`dims_of_dataOfAt`・`StateSideWitness` で `hsp/hss/hls/hn` を証明の中で出す。`st` は readerTrace_final の結論の ∃ 変数 |
| 残る条件 | C.SM-1 の被覆、C.AC-4、C.CV-4、C.SM-6 |
| root theorem | 未命名。carrier `dataOf` を `dataOfAt lvl` に固定した組み立て定理 |
| 費用 | 40〜80 行（推定）。ただし DG 系（Sem/Acc/Cover/DataOf/ReaderTrace）、ClosingRun3、DeclConnect を同時に含む branch が無く、統合 tree を作る費用が別にかかる |
| 確かさ | 中 |
| freeze / TRUSTED | freeze 要（carrier の固定は statement の変更）。TRUSTED 不要。新しい行なし。FG **−2（リーフ。C.SM-1 は行として残るので 0）** |

### 2.5 候補 ⑤: C.CV-6（`hcb` の補題）（R）

| 項目 | 内容 |
|---|---|
| 消える ID | C.CV-6 |
| 消える条件 | `hcb` を `machineShape?_callBinder`（base `ShippingMachineShapeTail.lean:61`）と `dataOfFrom_nIn` から出す新補題。R-in / R-dom は `readerTrace_final` 経由で、RT_ADMIT_DECISION (A) が前提 |
| 残る条件 | C.SM-6 の b23（B3）。台帳の「hcb は B3」は取り違えの可能性 |
| root theorem（型案） | `theorem hcb_of_machineShape (hms : machineShape? … = some sp) … : ∀ k (hk : k < sp.insts.length), (sp.binders[kDOf d + k]?).map (·.2) = some (sp.insts[k]'hk).2.2` |
| 費用 | 約 25〜40 行（推定） |
| 確かさ | 中 |
| freeze / TRUSTED | freeze 要。新しい行なし。FG −1（リーフ） |

### 2.6 候補には挙げるが数えないもの（裁定上は単独で外せない）

A.P-07、D.T-2、C.SM-7、D.D-8 は、「FG 側に独立した束縛変数が無い」または「定理が default route だけ」という読みで、A.P-22 型の表示除去に見えるが、2026-11-05 の裁定（束縛変数が実際に消えるか、既存の行に Lean で置き換わる）からは、置き換える定理の特定が足りない。この資料では数えない。D.D-8 は `postEntry_lookup_ne`（default route）で、parametric を含めて外すには `Post` が要る。

## 3. 束ねた行の数え方（R0）

* D.E-12 = `hno`/`htop`: R0 では 1 行。**部分供給**は machine 側の `htop` と leaf の `hno` が UA7b の scratch のみ（tree に無い）。calls 枝の子 design 名と非 machine の `hno` は経路が見つからなかった。行は消えない。
* D.E-4 = B3/B4/B5: B3 は `auditE3B3_of_t1hyp_run` で供給済み（`ChildIfaceP` の他の field と B4 は含まない）。B4 はユーザー判断 (3) で残す。B5 は未判断。行は消えない（FG 台帳 §12.6 のとおり 0）。
* IP 限定の結果は一般台帳に数えない（legacy 0/391、memo hit 0、parametric 入口 0 は測定の記録と grep で、定理ではない）。

## 4. 推奨する次の単位

1. **C.RK-1（候補 ①）を次の単位にする**（C.RR-2（候補 ②）の配線は同じ単位に入れてよいが、default route 限定の結果で、一般 FG の減算には数えない）。どちらも base に必要な定理があり（`ReadWorld.readKeeps`、`entryWitness_left_postEntry`）、Lean の新規部分は配線だけで、統合 tree を作らない。新しい TRUSTED/law/行は増えない。freeze は reviewer の番（FG の statement から行を除くため）。**一般 FG の候補は ① の −1 だけ**（① と ② を −2 と合算しない）。② は default route 限定の見込み（−1）で、一般 FG の減算は parametric の橋が揃うまで 0。C.RK-1 の置換先 C.EN-4 は残る。① は projection・elaboration と Check が通るまで台帳を減らさない（reviewer 2026-11-05）。
2. **候補 ④（`dataOfAt` 固定の一括単位）の統合 tree の調査**を先にやる。DG 系を同時に含む branch が無いため、費用は定理の長さではなく統合にかかる。この単位は FG −2（リーフ）の見込みで、価値は大きいが、先に「どの branch をどの順で局所統合するか」の文書が要る。

run だけから消える行がほとんど無いことは §0 のとおりで、リーフ 62 の大半は U / X。X の多くは `partial def` の不透明性（C.RK-6、C.DO-2、C.CV-4、N2-b）か環境の事実（7 行）で、一般定理から払うにはコンパイラ変更か新しい仮定が要り、ユーザー判断の領域。

## 5. この資料でしたこと

* FG 台帳 §8.2 の 110 行表と §12 の減算記録から、残り 88 行（81 + 後から加えた 7 行）を機械的に特定した（リーフ 62 / 非リーフ 26 と一致することを確認した）。
* 5 つの読み取り専用の調査（A / B / C env / C SM-AC-CV-DG+D.D / D.T-D.E+追加 7 行）を並列に行い、結果を DETAIL に載せた。Lean は走らせていない。ソースツリーに Lean・ログ・測定データは置いていない。
* 台帳ファイルの数・Elab.lean・共有定義は変更していない。新しい law/TRUSTED、FG の縮小は提案していない。
