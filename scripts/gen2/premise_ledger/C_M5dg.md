# 前提台帳 C_M5dg（DG-* 11 Issue）

調査は読み取りのみ。Lean/ファイルの書き込み無し。FG = scripts/gen2/GENERAL_SPEC.md §1.1（`FG : ∀ L declName parameters mctx cctx w b D w', Start L mctx cctx w → (RunsTo … ∨ RunsTo …) → ReflectsAll L declName parameters → ∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D`）、`Start L mctx cctx w := AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`（§1.2）。
表記: branch@SHA。`par/gen2-spec`・`par/gen5-t2` は履歴の note に書かれた名前。ファイル行番号は当該 SHA のもの。
「mutant 棄却」は signature/defeq 棄却であり意味的反例ではない。「未供給」「経路が見つからなかった」は、履歴・freeze 文書が書いている範囲、およびこの調査で読んだ範囲の記述であり、不可能・導出不能の主張ではない。
TRUSTED 境界として明示された前提: 本グループの履歴・freeze 文書には「新 TRUSTED/新 law なし」と書かれており、TRUSTED として明示された前提はこの調査では見つからなかった（下の分類欄はすべて「未供給の義務」か「入力条件」）。

## 0. Issue 別の最新状態（履歴 $S/h/*.json から）

| Issue | 最新 approved（seq）| 対象SHA / branch | 検証（要点）| 残り（要点）| 後続 note |
|---|---|---|---|---|---|
| sparkle-gen5-dgen | approved 2831 / done 2833 | par/gen5-t2 c398021c（DGEN_FREEZE.md, T2COVER_FREEZE.md、設計のみ）| 文書照合、diff --check clean、Lean elaboration/build なし | ConstValue/adapterOf、dataOf_sound、genSem 各arm、genS_unfold/因果性、全成功runのGeneratedAt供給、共有ClosingRun、DG-ENV/ACC/COVER/DeclConnect は未証明 | 無し（done）|
| sparkle-gen5-dg-audit | 無し（created 2846, dependencies 3083 のみ）| この調査では見つからなかった | — | — | note 無し |
| sparkle-gen5-dg-runreads | approved 2994 / done 2995（scoped）| par/gen2-spec 88771739 (+comment-only 144c3f1e) | g5rr3-88771739 exit 0, 745 jobs; struct 正負, TYPE 3, MUTANT 4, controls 6, REACH 3, AXIOMS 3 | ClosingRun, GeneratedAt, InvAt at w5, env 同一性, fallback 被覆は別単位 | 無し |
| sparkle-gen5-dg-closingrun | approved 3790（scoped）| kjob/g5cr-r6 f3a29dbb | cr6v-f3a29dbb exit 0, 757 jobs; TYPE 12, MUTANT 38行, AXIOMS 11, REACH 8, CONTROL 12 | hrow/hrows, StepStmt, T1Hyp.dec, GeneratedAt(hGen), 非空虚性, depth0 stop は未供給 | 無し |
| sparkle-gen5-dg-env | approved 5476（U9 freeze 設計のみ）; Lean の最新 approved 5466（U8）| kjob/g5env-r21 4fa23d2e（freeze）; U8 = kjob/g5env-r20 bb49da59 | env20v-bb49da59 exit 0, TYPE 1 / MUT 8 / AX 1 | 実 hN, hentry, 非空例, L′/QuietStrength, CellPrem, ¬DRow, C0/FG は未供給 | 5539 doing: kjob/g5env-r22 b6b3206b（U9 `synthesizeChild_realN` 実装、clean build は coder、未review）|
| sparkle-gen5-dg-sem | approved 5495（U9 freeze 設計のみ）; Lean の最新 approved 5484（P8 U8）| kjob/g5sm-u22 7f72f5c3（freeze）; P8 U8 = kjob/g5sm-u21 d0a8cf66 | smu21v exit 0 | 実 dataOf/DataOfSound, 実 kit hmem/hinv, GenWF, run/FG は未供給 | 5573 doing: kjob/g5sm-u23 7af6c7cc（`dataOfSound_of_parts/_parts`、Pod 増分 build exit 0、clean build は coder、未review）|
| sparkle-gen5-dg-acc | approved 5505（A13 freeze 設計のみ）; Lean の最新 approved 5342（A12）| kjob/g5ac-r26 cff12a48（freeze）; A12 = kjob/g5ac-r25 86c45108 | ac25v exit 0, 730 jobs, TYPE 3 / BODY 1 / MUT 5 / AX 3, closure 6664 | 実 GD/genData₀/genSem/laws/hev/hf、成功 coverage、run/M5/FG | 5507 doing: A13 実装を agent g5ac-r27 で開始（kjob/g5ac-r27 は cff12a48 と同一コミット）|
| sparkle-gen5-dg-cover | approved 4240 / 4246 | kjob/g5cv-r13 44d72eaf（rev7.1 + U-E3a Cover6）| cv13v-44d72eaf exit 0, 709 jobs; TYPE 8+INDUCTIVE 1, MUTANT 8, AXIOMS 7, closure 2062 | readF→FReachC, R-in/R-nl/R-dom, row 6b/hbr/実reader coverage は未供給。sorry 警告 3 件は隔離負例 | 無し |
| sparkle-gen5-dg-readertrace | approved 5577 | kjob/g5rt-r10 6e6c880f（親 04b00b00）| rt10v-04b00b00 exit 0, 726 jobs; TYPE 2, MUTANT 6, AXIOMS 3, closure 4655 | hT/成功run、他arm、全体 TraceGood、FG | 無し |
| sparkle-gen5-dg-readkinds | approved 5578（U14 freeze 設計のみ）; Lean の最新 approved 5561（U13）| kjob/g5rk-r23 221d590a（freeze）; U13 = kjob/g5rk-r22 25540b18 | rk22v-25540b18 exit 0, 827 jobs; TYPE 3 comparison, 命題 mutant 6, AXIOMS 標準 | h0s/hk/hHead/run/C0/coverage/FG 未供給 | 無し |
| sparkle-gen5-dg-dataof | approved 4040（scoped）| kjob/g5do-r5 945fbe9a | do5v-945fbe9a exit 0, 762 jobs; TYPE 33 / MUTANT 23 / AXIOMS 30 / REACH 32 / CONTROL 8 | coverage/実reader一致は未供給 | 4078 doing: kjob/g5do-r6 063056d6（row 6b 射影 `dataOfAt_dims` 等、agent build のみ、clean build は coder、未review）|

後続 doing/changes_requested の一行: dgen は 2702 changes_requested（R6-R8）後に 2831 approved。他は上表の「後続 note」。

---

## 1. DG-RUNREADS（par/gen2-spec 88771739, Tools/ShippingGen5RunReads.lean）
主要定理: `runReads_of_run`（RunReads.lean:181）、`fromConst_machine_linkA`（:139）、`coreHead_jqcA`（:69）。承認済み。
`runReads_of_run` の署名: `(O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx) {X} {shape : MachineShape} {D₀ : Nat} {w w'} {raw} {D} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w') (entry : MachineDefines mctx mref cctx cref X shape) (closes : MachineClosesAtA O mctx cctx X shape) : ∃ b ci envR envR' w5 w6, RunReadsAt … ∧ JQC O (D₀ + 1) w5`

### RR-1 `hA` / `hw` / `hc`
- Lean名（binder名）: `hA`, `hw`, `hc`
- 完全な型: `hA : AdmCtx O.quiet mctx cctx`; `hw : JQ O.quiet D₀ w`; `hc : D₀ = 0 ∨ CacheInvA O (cv w)`
- 定義元: `AdmCtx`/`JQ`/`JQC`/`CacheInvA` は T1/M3 由来（`Tools/ShippingChildInvA`, `ShippingChildCacheA`）→ T1 台帳を参照
- 仮定している定理: `runReads_of_run` par/gen2-spec@88771739 RunReads.lean:181
- FG/T1のどこに効くか: FG の `Start L mctx cctx w`（§1.2: `AdmCtx ∧ JQC L.O 0 w`）。内側ランでは IHAt 側の InvAt（T1 台帳を参照）
- 同じ前提の別名: `ClosingRun2` の `hw : JQC L.O (dv w) w`, `hc : dv w = 0 ∨ CacheShips L P Reach (cv w)`（`invAt_w5_of_runReadsAt_JQC`, ClosingRun2.lean:54）
- 支払い予定のIssue: 履歴に割当の記載なし（外側ランは `Start`＝FG の仮説、内側ランは T1 の IH）→ 未割当
- 実runから払えそうか: depth 0 の外側ランでは `Start` が `AdmCtx` と `JQC 0 w` を与える（GENERAL_SPEC §1.2）。depth>0 の `hc` は `CacheShips` が要る（`invAt_w5_of_runReadsAt_JQC`）。その供給は T1 台帳側。
- 分類: 入力条件

### RR-2 `hr`
- Lean名: `hr`
- 完全な型: `RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'`
- 定義元: `RunsTo` は Tools.ShippingEntrySoundness（T1/M3 側）
- 仮定している定理: `runReads_of_run`（同上）
- FG/T1: FG の `RunsTo (synthesizeCombinational …) … w (b, D) w'` を core 実行へ落とした形（`Start` の次の仮説）。対応の明示的な記述はこの調査では見つからなかった（不明）
- 別名: ClosingRun の `hrun`, ReadKinds の `hrun`（readMachine 側は別の run）
- 支払い予定: FG の仮説そのもの
- 実runから払えそうか: はい（FG の `RunsTo` 仮説が定義上これ）。ただし FG の `RunsTo (synthesizeCombinational declName)` から `synthesizeCombinationalCore X [] false` の run を取り出す橋は、この調査で読んだ文書では確認できなかった（不明）
- 分類: 入力条件

### RR-3 `entry` / `closes`
- Lean名: `entry`, `closes`
- 完全な型: `entry : MachineDefines mctx mref cctx cref X shape`; `closes : MachineClosesAtA O mctx cctx X shape`
- 仮定している定理: `runReads_of_run`
- FG/T1: `T1Hyp.defines` / `T1Hyp.closes`（GENERAL_SPEC §1.3, T1HypND の field、`Tools/ShippingGen5T1ND.lean:35-50`）→ T1 台帳を参照
- 別名: `T1HypND.defines`, `T1HypND.closes`; DG-ENV では `MachineDefinesR`（EnvR.lean:24）に置換する候補
- 支払い予定: T1 側（G3-SHAPE / G-CLOSES）。DG-ENV は all-world `defines` を `MachineDefinesR env₀` に弱める候補を持つ（EN-6）
- 実runから払えそうか: 不明（RR は T1 の field をそのまま取る）
- 分類: 入力条件（T1 台帳の field）

---

## 2. DG-CLOSINGRUN（kjob/g5cr-r6 f3a29dbb, Tools/ShippingGen5ClosingRun2.lean / ClosingRun.lean）
主要定理: `closingRun0_of_run`（ClosingRun2.lean:127）、`closingShared_of_run`（:70）、`closingRun_of_run`（ClosingRun.lean:285）、`closingRun_of_run_ga`（ClosingRun2.lean:147）、`closingRun_nonempty_of_premises`（:184）。

### CR-1 `hrow`（`closingRun0_of_run` では `hord`）
- Lean名: `hrow`（`closingRun_of_run`, `closingRun_of_run_ga`, `ClosingPremises.hrow`）/ `hord`（`closingShared_of_run`, `closingRun0_of_run`）
- 完全な型: `hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true`; `hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] → ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none`
- 定義元: `OneOutNoMemRow` = `def OneOutNoMemRow (p : Tools.ShippingGen2.Pkg ι dom) : Bool := !p.d.shape.instFields.isEmpty || p.d.shape.instTagged.all (fun x => x.2.child?.isNone)`（`Tools/ShippingGen2DataBridge.lean:37`, kjob/g5cr-r6@f3a29dbb）
- 仮定している定理: `closingRun_of_run` / `closingRun_of_run_ga` / `closingRun_nonempty_of_premises`（hrow）、`closingRun0_of_run` / `closingShared_of_run`（hord）— kjob/g5cr-r6@f3a29dbb
- FG/T1: `DataOk`（GENERAL_SPEC §1.3 の placeholder Prop）に課す行条件。`hord` は `hrow` から `hord_of_row` で出る（R6 freeze §2）
- 別名: `servedShips0_proved` / `postFacts_proved` / `t1_of_step_rows` の `hrow`（T1 台帳側と同一）
- 支払い予定のIssue: 割当の記載なし → 未割当（R6 freeze §2: 「`DataOk` は抽象 Prop パラメータ、`hrow` 自体は未供給／経路未発見」）
- 実runから払えそうか: 不明。履歴・freeze に支払う補題の記載なし
- 分類: 未供給の義務（`DataOk` の具体化＝M2 U0 に依存）

### CR-2 `hGen`
- Lean名: `hGen`（`Gen` はパラメータ）
- 完全な型: `Gen : ConstantInfo → Environment → Environment → Prop`; `hGen : ∀ b ci envR envR' w5 w6, RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'`
- 定義元: `RunReadsAt` = par/gen2-spec@88771739 RunReads.lean:42。`GeneratedAt` は R6 freeze §2 によれば `par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` の設計文のみで、この tree には無い。`GeneratedAtK` は kjob/g5ac-r26@cff12a48 `Tools/ShippingGen5AccGenP.lean:33`（本文は未引用、下記 AC 節）
- 仮定している定理: `closingRun0_of_run`, `closingShared_of_run`, `closingRun_of_run`, `closingRun_of_run_ga`（`hGA` 形）— kjob/g5cr-r6@f3a29dbb
- FG/T1: DGEN の `GeneratedAt`（= G3-GEN の供給、DGEN_FREEZE: 「GENERAL_SPEC.md:491-493 の G3-GEN」）。FG の `ReflectsAll`／`Pk declName = some p` の `Pk` 側
- 別名: `GA`（`closingRun_of_run_ga` の `hGA`）、`GeneratedAtK`（DG-ACC）、`GeneratedAt`（DGEN）
- 支払い予定のIssue: R6 freeze §2: DG-COVER + DG-WFCOVER + `genP_generated`(C6) + DG-ENV（DGEN_FREEZE §604 による）。DG-WFCOVER は本グループ外
- 実runから払えそうか: 不明（R6 freeze: `Gen := GeneratedAt …` の供給は「経路未発見」。`gen_of_closingShared` は逆向き）
- 分類: 未供給の義務

### CR-3 `hIH` / `hKI`（`hst` / `h1`）
- Lean名: `hIH`, `hKI`（`closingRun_of_run` では `hst : InvAt L P Reach (dv w) w`, `h1 : 1 ≤ dv w` も）
- 完全な型: `hIH : IHAt L P Reach (dv w + 1)`; `hKI : ChildKeepsInv L P Reach (dv w + 1)`（`closingRun0_of_run` は `IHAt L P Reach 1` / `ChildKeepsInv L P Reach 1`）
- 定義元: `IHAt` = `Tools/ShippingGen2Defs.lean:165`、`ChildKeepsInv` = `:182`（T1/M3 側）→ T1 台帳を参照
- 仮定している定理: `closingRun0_of_run`, `closingShared_of_run`, `closingRun_of_run`, `closingRun_of_run_ga`
- FG/T1: T1 の IH（GENERAL_SPEC §1.3 `IHAt`, `ChildKeepsInv`）→ T1 台帳を参照
- 別名: `AccIHAt`/`AccChildKeeps`（DG-ACC の Acc 版）
- 支払い予定: R6 freeze §2: 名前付き producer の形は `Tools.ShippingGen2.ih_allPF …1 le_rfl`（ShippingGen2T1.lean:198）。その前提 `StepStmt`（Defs.lean:310）、`hrow`、`hrows : DataRows`、`T1Hyp.dec` は未供給。割当 Issue は記載なし → 未割当
- 実runから払えそうか: 不明（R6 freeze: 「供給元・経路が見つからなかった」）
- 分類: 未供給の義務（T1 台帳側の IH）

### CR-4 `hT`
- Lean名: `hT`
- 完全な型: `hT : T1HypND L P Reach DataOk`; 定義全文は `Tools/ShippingGen5T1ND.lean:35-50`（kjob/g5cr-r6@f3a29dbb）: `structure T1HypND … : Prop where pkg : ∀ c, Reach c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q`, `defines : ∀ c, Reach c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx → MachineDefines mctx mref cctx cref c q.d.shape`, `closes : … → MachineClosesAtA L.O mctx cctx c q.d.shape`, `closed : ∀ c, Reach c → ∀ q, P c = some q → ∀ k (hk : k < q.d.shape.insts.length), (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1`
- 仮定している定理: 上記 4 定理
- FG/T1: T1 台帳を参照（`T1Hyp` から `dec` を除いたもの）
- 別名: `T1Hyp`（`T1Hyp.toND`, T1ND.lean:53）
- 支払い予定: T1 側
- 実runから払えそうか: T1 台帳を参照
- 分類: 入力条件（T1 台帳）

### CR-5 `hs` / `hd0` / `hA` / `hR` / `hP` / `hrun`
- Lean名: `hs : Start L mctx cctx w`, `hd0 : dv w = 0`, `hA : AdmCtx L.O.quiet mctx cctx`, `hR : Reach X`, `hP : P X = some p`, `hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'`
- 完全な型: 上記のとおり
- 仮定している定理: `closingRun0_of_run`（hs, hd0, hR, hP, hrun）、`closingRun_of_run`（hA, hR, hP, hrun）
- FG/T1: `hs` = FG の `Start`; `hrun` = FG の `RunsTo`; `hR`/`hP` は Reach/Pk（T1 台帳）
- 支払い予定: FG の仮説／T1 台帳
- 実runから払えそうか: `hs`, `hrun` は FG の仮説として与えられる。`hd0`, `hR`, `hP`（Reach に X が属する・パッケージ割当）の支払いは記載なし（不明）
- 分類: 入力条件

注記（premise ではなく未供給の行。R6 freeze §2）: 非空虚性（`ClosingRun`/`ClosingRun0`/`ClosingShared`/`T1HypND` の具体例）は tree に無く、depth-0 `stop`（`InvAt 0 w'`）も `stop_of_run`（ClosingRun.lean:271, `1 ≤ dv w` を要する）の外で未供給。`closingRun_nonempty_of_premises` は `ClosingPremises` の包装であり witness ではない（R6 freeze 記述）。

---

## 3. DG-ENV（kjob/g5env-r22 b6b3206b を最新、承認済み Lean は kjob/g5env-r20 bb49da59、freeze は kjob/g5env-r21 4fa23d2e）
ファイル: Tools/ShippingGen5Env.lean, EnvR.lean, EnvQ.lean（Q1-Q10 = unit (d), HEAD 609b8094/3db43dcb）, EnvStart.lean, EnvFrame{,2,3}.lean, EnvCache{,B,C,D,E}.lean。

### EN-1 `QuietStrength L L' env₀`（`hq`）
- Lean名: `hq`
- 完全な型: `QuietStrength (L L' : Laws mref cref) (env₀ : Environment) : Prop := ∀ w, L'.O.quiet w ↔ (L.O.quiet w ∧ ReadsAt env₀ cref w)`（定義元 kjob/g5env-r22@b6b3206b `Tools/ShippingGen5EnvQ.lean:38`; 同文の `QuietStrengthA` = kjob/g5ac-r26@cff12a48 `AccReads.lean:31`）
- 仮定している定理: `quiet_down`, `readsAt_of_quiet`, `jq_down`, `realChildA_down`, `cacheInvA_down`, `jqc_down`, `closesA_up`, `t1HypND_up`, `jq_start`, `head_jqc_start`（EnvQ.lean:46-104）、`start_up_of_parts`, `start_up_empty`（EnvStart.lean:22,33）、`cacheInvA_up_of_N`, `start_up_of_N`, `realChildA_up_of_N`（EnvCache.lean）、`realChildN_up/_down`、`frameQ_plus` 他 `*_plus`（EnvFrame3.lean）— いずれも par/gen2-spec 系列の kjob/g5env-* branch
- FG/T1: FG の `∀ (L : Laws mref cref)` と `Start L mctx cctx w` を、実行中に使う L′ へ橋渡しする前提（`jq_start : QuietStrength L L' (envAt cref w₀) → Start L mctx cctx w₀ → JQ L'.O.quiet 0 w₀`）。`T1HypND`／`IHAt` の L を L′ へ持ち上げる（`t1HypND_up`）
- 別名: `QuietStrengthA`（DG-ACC, `AccReads.lean:31`）、DG_ENV_FREEZE の「TQ」
- 支払い予定: DG-ENV（履歴 5467/5476 の残り: 「L′/QuietStrength 未供給」）。具体的な L′ の構成を行う単位は記載なし
- 実runから払えそうか: いいえ、とは書けない。履歴 3071/5476 に「QuietStrength/AdmDown/hA′ と L′ の構成は未供給」、DG_ENV_T2_FREEZE_R3 §0 に「T2 では QuietStrength (L′) は得られない（FramedA 40 constructor のうち 13 が law-free 補題で閉じ、8 は IO lift 確認待ち、6 は unfolding 確認待ち、13 は経路未発見）」とある。→ 不明
- 分類: 未供給の義務

### EN-2 `AdmDown L L'`（`hd`）と `hA′`
- Lean名: `hd`, `hA'`
- 完全な型: `AdmDown (L L' : Laws mref cref) : Prop := ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L'.O.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx`（EnvQ.lean:42）; `hA' : AdmCtx L'.O.quiet mctx cctx`（`head_jqc_start`, `start_up_of_parts`）
- 仮定している定理: `realChildA_down`, `cacheInvA_down`, `jqc_down`, `closesA_up`, `t1HypND_up`（hd）; `head_jqc_start`, `start_up_of_parts`, `start_up_empty`（hA′/hA）
- FG/T1: `Start L′`／`AdmCtx` の持ち上げ（T1Hyp.defines/closes の `∀ mctx cctx, AdmCtx …` 量化を new→old で受ける）
- 別名: `AdmDownA`（AccReads.lean:35）、C-ADM（EnvQ.lean の注釈）
- 支払い予定: DG-ENV（未供給）
- 実runから払えそうか: R3 freeze §1: 「`AdmCtx`/`InertUnfold` は canUnfold? が任意関数であり T2 で `AdmDown`/`hA′` の経路未発見」。→ 不明
- 分類: 未供給の義務

### EN-3 開始 cache: `hC` / `hE` / `hN`
- Lean名: `hC`（`start_up_of_parts`）、`hE`（`start_up_empty`）、`hw`＝`hN`（`synthesizeChild_realN`, `cacheInvN_insert_runs`, `realChildN_of_run`）
- 完全な型: `hC : CacheInvA L'.O (cv w₀)`; `hE : cv w₀ = {}`; `hw : CacheInvN L env₀ (cv w)` ただし `def CacheInvN (L : Laws mref cref) (env₀ : Environment) (m : Std.HashMap Name Res) : Prop := ∀ c r, m.get? c = some r → RealChildN L env₀ c r`（EnvCacheC.lean:25）、`RealChildN` は EnvCache.lean:26 の inductive（`run … (hn : mctx.canUnfold? = none) (rd : ReadsAt env₀ cref w) (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildN L env₀ c' r') (synth : sv w = some synthesizeChild) (quiet : L.O.quiet w) (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChildN L env₀ c r`）
- 仮定している定理: `start_up_of_parts`（EnvStart.lean:22）、`start_up_empty`（:33）、`synthesizeChild_realN`（EnvCacheE.lean:30, kjob/g5env-r22@b6b3206b、未review）、`cacheInvN_insert_runs`（EnvCacheD.lean:24, kjob/g5env-r20@bb49da59、approved）
- FG/T1: `Start L′`（`JQC L′.O 0 w` の cache 側）／T1 の `CacheShips` 起点
- 別名: `CacheInvA`（旧）、`CacheInvN`（制限版）; `cacheInvA_of_empty`（EnvStart.lean:28）で空 cache なら `hE` から `hC`
- 支払い予定: DG-ENV（5476: 「実 start cache hN、非空例 未供給」）
- 実runから払えそうか: `hE` 形（開始時 `cv w₀ = {}`）は `hE` として仮説。実 run で `cv w₀ = {}` が成り立つかの根拠は履歴・freeze に見つからなかった（不明）
- 分類: 未供給の義務

### EN-4 `CellPrem`（セルの ReadWorld/SetFrame 前提）
- Lean名: `hcell`（`envFrameEnd_framedA`, `frameQ_plus` 他）、`hrw`（`synthesizeChild_realN`）、個別に `hr : ReadWorld r`, `hne : r.ref ≠ cref.ref`, `hf : SetFrame r cref`, `hs : SetGet cref`
- 完全な型（kjob/g5env-r22@b6b3206b）: `CellOK (cref) (r : IO.Ref σ) : Prop := ReadWorld r ∧ r.ref ≠ cref.ref ∧ SetFrame r cref`（EnvFrame3.lean:54）; `CellPrem Fresh mref cref : Prop := CellOK cref sparkleChildCache ∧ CellOK cref sparkleChildSynth ∧ CellOK cref sparkleSynthDepth ∧ (∀ {σ : Type} (r : IO.Ref σ), SideRef r → CellOK cref r) ∧ (∀ (σ : Type) (r : IO.Ref σ), Fresh σ r → CellOK cref r) ∧ ReadWorld mref ∧ SetFrame mref cref ∧ mref.ref ≠ cref.ref ∧ ReadWorld cref ∧ SetGet cref`（:58-63）; 基礎定義: `ReadWorld r := ∀ w, getW r w = w`（`Tools/ShippingStRefCorrespondence.lean:41`）, `SetGet r := ∀ v w, readOf r (setW r v w) = v`（:44）, `SetFrame r r' := r.ref ≠ r'.ref → ∀ v w, readOf r' (setW r v w) = readOf r' w`（:47）, `ReadKeeps r := ∀ w, readOf r (getW r w) = readOf r w`（:38）
- 仮定している定理: `envFrameEnd_get/_set/_modify/_modifyGet/_getEnv`（EnvFrame.lean）、`envFrameEnd_metaGet/_throwError/_getIO/_setIO/_modifyIO/_modifyGetIO/_metaModify/_coreModifyTrace/_freshFVar/_fvarThrowUnknown/_constInfo`（EnvFrame2.lean）、`envFrameEnd_framedA`、`envFrameEnd_throws`、`frameQ_plus` 他（EnvFrame3.lean）、`synthesizeChild_realN`（hrw : `ReadWorld sparkleChildCache`）
- FG/T1: `Laws` の `RefLawsAOps`/`RefLawsATele` 各 field（G5）を L′ で成立させるための環境不変条件。FG の `∀ L : Laws` の L′ 構成側
- 別名: ShippingStRefCorrespondence.lean 内のコメントで各セル前提は「PREMISE for the real runtime」と表記。DG_ENV_T2_FREEZE_R3 §0.2: 「law/TRUSTED を足さないのは仮説のままのとき」
- 支払い予定: DG-ENV（R3 freeze: 「セル前提は runtime で未供給（fit は open）」）
- 実runから払えそうか: 不明（R3 freeze §1.1: B 13 は cell premise からの law-free 補題、供給は未）
- 分類: 未供給の義務（これらを TRUSTED とするかの決定は DG_ENV_FREEZE §4 の A/B/C の判断としてユーザへ送る、と履歴 3040 にある。決定の記録はこの調査では見つからなかった）

### EN-5 `¬ DRow p`
- Lean名: 匿名 binder（`frameQ_plus` の `p` に対する `¬ DRow p`）
- 完全な型: `frameQ_plus … (hcell : CellPrem MkRefd mref cref) : ∀ {mctx cctx α}, AdmCtx L'.O.quiet mctx cctx → ∀ (p : MetaM α), FramedA MkRefd p → ¬ DRow p → ∀ w, L'.O.quiet w → L'.O.quiet (endW mctx mref cctx cref p w)`（EnvFrame3.lean）; `DRow` は EnvFrame3.lean:35 の inductive（`ioEnv`, `monoMs`, `mkExprCache`, `localMk`, `whnf`, `inferType`, `isClass?`, `whnfUntil`, `instantiateForall`, `mkLambdaFVars`, … の 13 constructor、全文は当該ファイル）
- 仮定している定理: `frameQ_plus`（kjob/g5env-r22@b6b3206b）
- FG/T1: `RefLawsAOps.frameQ` を L′ で成立させる際の「D 類」の除外
- 支払い予定: DG-ENV（履歴 5476: 「¬DRow 未供給」）
- 実runから払えそうか: 不明（R3 freeze §1.1: D 13 は「経路未発見」、HeapProvenance 自身の表でも OPEN）
- 分類: 未供給の義務

### EN-6 `hall`（C0: 全 world の `ReadsAt`）とゲート／shape 事実
- Lean名: `hall`, `hc`, `hg1`, `hg2`, `hsh`
- 完全な型: `hall : ∀ u, ReadsAt env₀ cref u`; `hc : env₀.find? c = some ci₀`; `hg1 : certifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀) (structEnv env₀)) = none`; `hg2 : mixedCertifiedShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀) (structEnv env₀)) (instancePredicate env₀) = none`; `hsh : machineShape? false [] (entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀) (structEnv env₀)) (structEnv env₀) = some shape`。`ReadsAt (env₀ : Environment) (cref) (w) : Prop := (∀ X ci, (envAt cref w).find? X = some ci → env₀.find? X = some ci) ∧ instancePredicate (envAt cref w) = instancePredicate env₀ ∧ userInliner (envAt cref w) = userInliner env₀ ∧ structEnv (envAt cref w) = structEnv env₀`（Env.lean:29）
- 仮定している定理: `machineDefines_of_readsAll`（Env.lean:69, sufficient-only）、`machineDefinesR_of_env`（EnvR.lean:46、`hall` 無し版・`MachineDefinesR`）、`machineDefinesR_of_defines`（EnvR.lean:40）
- FG/T1: `T1Hyp.defines`（all-world `MachineDefines`）の供給元。C0＝「一つの環境が全 run を通る」
- 別名: C0（履歴 2839 の title「one environment across runs (C0 incl. inst/instS SigEq at every world)」）、`MachineDefinesR`（relative 版）
- 支払い予定: DG-ENV（C0 は履歴の全 note で「未供給」）
- 実runから払えそうか: `hall`（全 world）は不明。run 側の `ReadsAt` は `readsAt_self`（Env.lean:36）で開始 world について得られる。world 間の tie（`h0s`）は RK-3 に記載
- 分類: 未供給の義務

### EN-7 `hentry`（入れ子 core run 終端の保存）
- Lean名: `hentry`
- 完全な型: `hentry : ∀ (w1 w2 : Void IO.RealWorld) (r1 : Res), L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) → RunsTo (synthesizeCombinational n) mctx mref cctx cref w1 r1 w2 → L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)`
- 仮定している定理: `synthesizeChild_realN`（EnvCacheE.lean:30, kjob/g5env-r22@b6b3206b、freeze は kjob/g5env-r21@4fa23d2e で approved、Lean は未 review）
- FG/T1: 子の synthesize 呼び出しに沿う `CacheShips`／`ChildKeepsInv` の保存（T1 側 KeepChild と同型）
- 別名: 旧 `synthesizeChild_realA` の `hentry`（`Tools.ShippingChildCacheA`）の制限版
- 支払い予定: 割当の記載なし（U9 freeze §0: 「rows owned by G-REACH / DG-READKINDS are named only」）→ 未割当
- 実runから払えそうか: 不明（U9 freeze: 「候補経路では未供給」）
- 分類: 未供給の義務

### EN-8 `hn`
- Lean名: `hn`
- 完全な型: `hn : mctx.canUnfold? = none`
- 仮定している定理: `start_up_empty`, `synthesizeChild_realN`, `cacheInvN_insert_runs`, `realChildN_of_run`
- FG/T1: `Start` の `AdmCtx` に関わる文脈条件（`admCtx_none`）
- 支払い予定: 記載なし → 未割当
- 実runから払えそうか: 不明
- 分類: 入力条件（Meta.Context の条件）

---

## 4. DG-READKINDS（kjob/g5rk-r23 221d590a、U13 = kjob/g5rk-r22 25540b18）
承認済み最上位定理: `readMachine_agrees_runReads_of_head_self`（`Tools/ShippingGen5ReadKindsU13.lean:22`）。台帳は DG_READKINDS_U13_FREEZE.md §1。

### RK-1 `hk`
- Lean名: `hk`
- 完全な型: `Tools.ShippingStRefCorrespondence.ReadKeeps cref`（`ReadKeeps r := ∀ w, readOf r (getW r w) = readOf r w`）
- 仮定している定理: `readMachine_agrees_runReads_of_head_self`（U13）、`..._of_head`（U12b, ReadKindsU12.lean:43）、`..._of_readKeeps`（U11）、`..._framed`（U10, `hg : GetEnvFrame`）— kjob/g5rk-r23@221d590a
- FG/T1: 不明（reader と run の整合 `r.entry = entryConst … ∧ r.shape = shape`; DG-COVER の reader 被覆へつなぐ）
- 別名: `hg : GetEnvFrame mctx mref cctx cref`（U10 まで。`getEnvFrame_of_readKeeps` で `hk` から）、DG-ENV の `ReadWorld cref`（`ReadWorld.readKeeps`）
- 支払い予定: 未割当（U13 freeze §1）
- 実runから払えそうか: いいえ、とは言えない。U13 freeze §2: 「`ST.Ref.get` の opaque な文。`RunReadsAt` もmachine run も cell について何も言わない。`runsTo_det` は決定性のみ」→ 不明
- 分類: 未供給の義務

### RK-2 `hHead`
- Lean名: `hHead`
- 完全な型: `Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref`; `EnvFrame x mctx mref cctx cref := ∀ (w) (a) (w'), RunsTo x mctx mref cctx cref w a w' → envAt cref w' = envAt cref w`（`Tools/ShippingEnvSnapshot.lean:43`）
- 仮定している定理: U13/U12b（上記）
- FG/T1: 不明
- 別名: DG-ENV の IO 段（`ioEnv`）と同名だが割当は未確認（U13 freeze §1 「the assignment is not confirmed」）
- 支払い予定: 未割当
- 実runから払えそうか: 不明（U13 freeze §2: 「run が return したと言うだけ。per-run 弱化も run の存在からは得られない」）
- 分類: 未供給の義務

### RK-3 `h0s`
- Lean名: `h0s`
- 完全な型: `Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws`（U13。U12 では `{env₀} … ReadsAt env₀ cref ws`）
- 仮定している定理: `readMachine_agrees_runReads_of_head_self`（U13）。U12b/U11/U10 では `h0 : ReadsAt env₀ cref w` も（U13 で `readsAt_self` により除去）
- FG/T1: 不明。2 つの run（readMachine の開始 world `w` と core run の開始 world `ws`）の環境の tie
- 別名: DG-ENV の C0（EN-6）、U14 freeze の「環境等式」
- 支払い予定: sparkle-gen5-dg-env（U13 freeze 表）
- 実runから払えそうか: いいえ、とは言えない。U13 freeze §2: 「`ReadsAt.of_envEq` は `envAt cref ws = envAt cref w` を要し、それが tie 自体」→ 未供給
- 分類: 未供給の義務

### RK-4 `hrun`（readMachine）と `hX`
- Lean名: `hrun`, `hX`
- 完全な型: `hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'`; `hX : declName = X`
- 仮定している定理: U13/U12b/U11/U10
- FG/T1: `readMachine`（`Tools/ShippingMachineCommand.lean:440`、補助 MetaM コマンド）の run。FG の仮説には無い
- 支払い予定: 履歴・U13 freeze 表: `sparkle-gen5-dg-runreads` / `-closingrun`（run existence）
- 実runから払えそうか: 不明（`hX` は命名の等式で U13 freeze は gap に数えない）
- 分類: `hrun` 未供給の義務、`hX` 入力条件（trivial）

### RK-5 `R : RunReadsAt …`
- Lean名: `R`
- 完全な型: `Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6`（定義全文は 1 節の RunReads.lean:42、par/gen2-spec@88771739）
- 仮定している定理: U13/U12b
- FG/T1: 実 run（core）の読み。`runReads_of_run`（RR-1..3）から構成
- 別名: ClosingRun の `ClosingRun.shared` 内 `RunReadsAt`
- 支払い予定: sparkle-gen5-dg-runreads（RR3 が `O, hA, JQ/cache, MachineDefines, MachineClosesAtA` から構築、U13 freeze §1）
- 実runから払えそうか: はい（`runReads_of_run`、ただし RR-1/RR-3 の前提つき）
- 分類: 入力条件（RR-1..RR-3 に帰着）

### RK-6 `hag : ReflExprAgree`
- Lean名: `hag`
- 完全な型: `Tools.Prototype.DGenStored2.ReflExprAgree`、`def ReflExprAgree : Prop := ∀ e, reflExpr e = reflExprS e`（`Tools/Prototype/DGenStored2.lean:646`、kjob/g5rk-r23@221d590a）
- 仮定している定理: `storedFromRead_of_dataE_run`（`ReadKindsU9.lean:96`）、`body_readback`（DGenStored2.lean:649）
- FG/T1: 不明（`dataE` 経路で reader の出力が stored shape を表すこと）
- 支払い予定: 未割当（記載なし）
- 実runから払えそうか: 不明（記載なし）
- 分類: 未供給の義務

### RK-7 U14 の置換前提 `hM` / `hC`（freeze 承認、Lean は未実装）
- Lean名: `hM`, `hC`（U14c `readMachine_agrees_runReads_of_ties` の前提）
- 完全な型: `hM = ∀ (e : Lean.Environment) (v1 : Void IO.RealWorld), RunsTo (Lean.getEnv : MetaM Lean.Environment) mctx mref cctx cref w e v1 → envAt cref v1 = envAt cref w`（U14a の結論）; `hC = ∀ s w1 w2 w3 ci e, RunsTo (coreHead X) … ws s w1 → RunsTo (Lean.getConstInfo X) … w1 ci w2 → RunsTo (Lean.getEnv : MetaM Lean.Environment) … w2 e w3 → envAt cref w1 = envAt cref ws ∧ envAt cref w2 = envAt cref w1 ∧ envAt cref w3 = envAt cref w2`（U14b の結論）。全文は `scripts/gen5/DG_READKINDS_U14_FREEZE.md` §2（kjob/g5rk-r23@221d590a）
- 仮定している定理: U14c（未実装）。`hk, hHead ⇒ hM, hC`（U14a/b）
- FG/T1: RK-1/RK-2 と同じ。履歴 5578: 「前提差分: 2 除去（hk, hHead）/ 2 追加（hM, hC）。純減 0 で供給なし」
- 支払い予定: RK-1/RK-2 と同じ未割当
- 実runから払えそうか: 不明
- 分類: 未供給の義務

### RK-8 reader 完全性の前提（`readN_quote` 系、U1-U4 の成果）
- Lean名: `hc`, `hq`, `hb`, `hv`, `hw`, `hwf`, `hdom`
- 完全な型: `readN_quote {cfg} (hc : Complete cfg) : ∀ {s} (t : Term s) (k : Nat), liftDepth t ≤ k → t.WF cfg.kb cfg.kv cfg.vw → readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩`; `readTot_of_quote_body (d) (isDom) (hdom : isDom d.dom = true) (hq : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j)) (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hwf : d.packed.WF d.kb d.kv d.vw) : readTot (kindsCfg d.dom isDom (kindsOf d)) d.shape.body = some ⟨_, d.packed⟩`（`Tools/ShippingGen5ReadKinds.lean`、kjob/g5rk-r23@221d590a）
- 仮定している定理: `readN_quote`, `readTot_of_quote_body`, `machine_wf_of_readN`, `packed_wf_cfg`
- FG/T1: DG-DATAOF の C-QWIT／DG-COVER の被覆へ接続（DATAOF freeze §11.2 行 4）
- 支払い予定: DATAOF freeze: C-QWIT は「供給元未発見」
- 実runから払えそうか: 不明
- 分類: 未供給の義務
- 注記: `RootFacts`（ReadKinds.lean:725）と `rootFactsAt_of_runReads`（U5）は `mixedGatePeel (packTupleInputs entryV) = some (bsIn, entryBody₀)` と `entryBody = rootFloat entryBody₀` を保持する構造。U13 freeze はこれを DG-READKINDS U5 側の行として名前だけ挙げている。支払い元の詳細はこの調査では見つからなかった。

---

## 5. DG-DATAOF（kjob/g5do-r5 945fbe9a 承認、kjob/g5do-r6 063056d6 未review）
主要定理（Tools/ShippingGen5DataOf.lean）: `dataOfAt_sound`（:211）, `dataOfFrom_sound`（:197）, `dataOfCore_sound`（:170）、`initOk_of_ok`（DataOfPure）、g5do-r6 の `dataOfAt_dims`, `dataOfAt_sound_dims`（`ShippingGen5DataOfDims.lean:138`）。

### DO-1 `h : dataOfAt lvl E senv s = some d`（coverage の行）
- Lean名: `h`
- 完全な型: `dataOfAt_sound (lvl : Lean.Expr → Nat) {E : ConstantInfo} {senv : StructEnv} {s : MachineShape} {d : MachineData} (h : dataOfAt lvl E senv s = some d) : d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j)) (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧ d.initOk (initsOf d) = true`。`dataOfAt` の定義: `def dataOfAt (lvl) (E) (senv) (shape) : Option MachineData := match E.value? with | none => none | some entryV => dataOfFrom lvl E senv shape (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) Sparkle.Compiler.MachRawSurface.rootFloat`（:134）
- 仮定している定理: `dataOfAt_sound`, `dataOfFrom_sound`, `dataOfAt_sound_dims`（kjob/g5do-r6@063056d6）
- FG/T1: DG-DATAOF が DGEN の `GeneratedAt` の `GenData.hdata` と `dataOf_sound` を供給（DGEN_FREEZE: 「`ok/body_eq/init` of every arm from `dataOf_sound g.hdata`」）
- 別名: `DataOfSound dataOf initsOf`（DG-SEM, SM-1）、`DataSoundAt f`（DG-ACC, AC-1: 先頭 3 連言のみ）、`K.dataOf`（AC kit）
- 支払い予定: DG-COVER（行 8 の `S-OK`、DATAOF freeze §11.2）。他の行は記載なし
- 実runから払えそうか: いいえ、とは言えない。§11.2 の行 1,2,3,4,5,6,8 が未供給、行 7 は 4,5 に依存（「`dataOfAt` を `some` にする既存定理は無い」）
- 分類: 未供給の義務（成功 run 全部での `dataOfAt = some` という被覆）

### DO-2 実 reader との一致（Rdr）と `s = sp`
- Lean名: 定理化されていない（§11.3）。`ShapeAgree d st`（DG-COVER）の `hsp`／`s = sp` 同一視
- 完全な型: 該当する Lean 命題はこの調査では見つからなかった。DATAOF freeze §11.3: (a) `readMachine`（`Tools/ShippingMachineCommand.lean:440`）との出力関係、(b) compiler の reader との関係、(c) `tin`, `fl`（`packTupleInputs entryV`, `rootFloat`、ともに partial）と `machineShape?` の使う値との関係、のいずれも定理無し
- 仮定している定理: 該当無し（未形式化）
- FG/T1: DGEN の `GeneratedAt` が「run の reads の E」「machineShape? の shape」「`d` が (E, senv, shape) の全関数」を結ぶ点
- 支払い予定: DG-COVER / DG-READKINDS（freeze 本文）
- 実runから払えそうか: 不明
- 分類: 未供給の義務

### DO-3 row 6a, C-CMP, C-QWIT, S-OK, S-COV-FLOAT, `dataOf at exprSize`
- 完全な型: `scripts/gen5/DG_DATAOF_FREEZE.md`（kjob/g5do-r6@063056d6）§4, §11.2 に名前のみ。Lean 定義は tree に無い（この調査では見つからなかった）
- 支払い予定: S-OK は DG-COVER／DG-WFCOVER。他は記載なし
- 分類: 未供給の義務

---

## 6. DG-SEM（kjob/g5sm-u21 d0a8cf66 承認、kjob/g5sm-u23 7af6c7cc 未review）
ファイル: Tools/ShippingGen5Sem*.lean。

### SM-1 `hs : DataOfSound dataOf initsOf`
- Lean名: `hs`
- 完全な型: `DataOfSound (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData) (initsOf : (d : MachineData) → HList (tys d.ss)) : Prop := ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData), dataOf E senv s = some d → d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j)) (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧ d.initOk (initsOf d) = true`（`Tools/ShippingGen5SemGenData.lean:18`、kjob/g5sm-u21@d0a8cf66）
- 仮定している定理: `GenData.toIn`, `GenData.genSem`, `genData_toIn_d`, `genData_genSem_eq_via`, `hunf_of_genData`（:62）, `factsOf_all_of_genDataInv`（:77）— d0a8cf66。`dataOfSound_of_parts`／`dataOfSound_parts`（SemDataOfParts.lean:15,28）は同値の分解 — kjob/g5sm-u23@7af6c7cc
- FG/T1: DGEN の `genFacts`／G3-GEN 側の `GenIn.ok/bodyEq/init` の供給
- 別名: `DataSoundAt f`（DG-ACC, 3 連言のみで `initOk` なし）、`DataSound K`（AccDataSound.lean:23）
- 支払い予定: DG-DATAOF（5492 note: 「実 dataOf/DataOfSound(DG-DATAOF)」）。`dataOfAt_sound` は別 branch で SEM から import 不可（5492: 「別ブランチで import 不可」）
- 実runから払えそうか: いいえ、とは言えない。`dataOfAt_sound`（DO-1）が 4 連言として同型を与えるが、`dataOfAt = some` の被覆が未供給
- 分類: 未供給の義務

### SM-2 `hmem`（ordC の membership）
- Lean名: `hmem`
- 完全な型: `∀ (d : MachineData) (k : Fin d.shape.insts.length), k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none`（`hunf_of_genData`, `factsOf_all_of_genDataInv`, `hunf_of_kitInv`, `factsOf_all_of_kitInv`、SemGenData.lean:62-77 / SemKitInv.lean）
- 定義元: `ordCallees (d) := (List.finRange d.shape.insts.length).filter fun k => (d.shape.instOrigins.getD k .ord).child? = none`（SemCall.lean:17）
- FG/T1: DGEN 経路の ordinary callee の順序（Acc 帰納）
- 別名: `AssignKit.mem_ordCallees`（Acc.lean:39）、`ordCallees₀_mem`（AccOrdCallees.lean:21、kjob/g5ac-r26@cff12a48: 具体 `ordCallees₀` で証明済み）
- 支払い予定: DG-ACC A12 で `ordCallees₀`＋`ordCallees₀_mem` として具体化（5342 approved）。SEM 側 `hmem` の `ordC := ordCallees₀` への接続は別ブランチ
- 実runから払えそうか: はい（`ordCallees₀_mem` は kjob/g5ac-r26 で証明済み）。ただし SEM branch からは import 不可（5495 の根拠）
- 分類: 未供給の義務（SEM 側への接続）

### SM-3 `hinv`（kit の invariant）／`hunf`
- Lean名: `hinv`, `hunf`
- 完全な型: `hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s → ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧ (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd`（`factsOf_all_of_genDataInv`）; `hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s → ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y`（`srcCausal_of_acc_unfold`, `factsOf_of_acc_unfold`, `factsOf_all_of_acc_unfold`, SemAccStep.lean）
- FG/T1: `genFacts`（G3-GEN の facts）を全 `G` に配る帰納
- 別名: `AssignKit` の field（`genSem_local`, `genSem_decl` 等, Acc.lean:32-46）
- 支払い予定: DG-ACC（`genS` が `hunf`／`hinv` を満たす構成）。5492: 「実 kit hmem/hinv(DG-ACC)」
- 実runから払えそうか: 不明（DG-ACC の `genS_unfold`（Acc.lean）が候補。SEM 側への型の一致の記述はこの調査では見つからなかった）
- 分類: 未供給の義務

### SM-4 `hacc`
- Lean名: `hacc`
- 完全な型: `∀ (Y : Name) (s : SemPkg ι dom), G Y = some s → Acc R Y`（`factsOf_all_of_acc_unfold`）
- FG/T1: 再帰の well-founded 性（DGEN の `CallRel` 上の `Acc`）
- 別名: DG-ACC `Acc (CallRel K) X`, `acc_top_of_run`, `hacc_of_top_runs`
- 支払い予定: DG-ACC（AC-8）
- 実runから払えそうか: AC-8 に記載
- 分類: 未供給の義務

### SM-5 `hQ : CalleesCausal Q g.d`
- Lean名: `hQ`
- 完全な型: `CalleesCausal (Q : Name → Option (SemPkg ι dom)) (d : MachineData) : Prop := ∀ k ∈ ordCallees d, ∀ s, Q (d.shape.insts[k]).1 = some s → SrcCausal s`（SemCausal.lean:26）
- 仮定している定理: `genFacts`（SemFacts.lean:54）, `genFacts_gen`, `calleeOut_causal`, `callOut_causal`, `ExtStage_causal`, `extCausal_of_genSem`, `extJoint_of_genSem`, `genSemI_srcCausal`（SemSrcCausal.lean）
- FG/T1: DGEN の callee 限定因果性（R8）。T1Hyp の `GenFacts.causal`
- 支払い予定: SM-3/SM-4 の Acc 帰納（`srcCausal_of_acc_unfold`）が与える形
- 実runから払えそうか: はい（`srcCausal_of_acc_unfold`、`hunf` と `Acc R X` から）。`hunf`・`Acc` が前提
- 分類: 未供給の義務（SM-3/SM-4 に帰着）

### SM-6 `GenWF d = true`（`GenData.wf`／`GenIn.wf`）
- Lean名: `wf`（structure field）
- 完全な型: `structure GenData … where d : MachineData; wf : GenWF d = true; hshape : machineShape? false [] E senv = some d.shape; hdata : dataOf E senv d.shape = some d`（SemGenData.lean:27）; `GenIn` は `wf : GenWF d = true`, `ok : d.ok = true`, `bodyEq`, `init : d.initOk inits = true`（SemGen.lean:61）; `GenWF d := RowA d && RowB d && RowC d`（SemGen.lean:58）
- FG/T1: DGEN の (ii) `GenWF d = true`（DG-WFCOVER）
- 支払い予定: DG-COVER（`rowC_of_reader`, `rowA3_of_inv` 等、CV 節）／DG-WFCOVER（本グループ外）。5492: 「GenWF(DG-COVER)」
- 実runから払えそうか: CV 節参照（hq, hnl, FullInv が未供給）
- 分類: 未供給の義務

### SM-7 `hord`（`genExtAtCall_of_genSem`）
- Lean名: `hord`, `hp`, `hq`
- 完全な型: `genExtAtCall_of_genSem {ι} {dom} (P : Pkgs ι dom) (X : Name) (g : GenIn) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) (hp : p.toSem = genSemI (semOf P) X g) (hq : P (p.d.shape.insts[k]'hk).1 = some q) (hord : (originOf p.d k).child? = none) : GenExtAtCall p q k hk`（SemExtPkg.lean:17）
- FG/T1: T1 の `GenExtAtCall`（T1 台帳を参照）
- 支払い予定: 記載なし → 未割当
- 実runから払えそうか: 不明
- 分類: 入力条件（k が ordinary 呼び出しであること）

---

## 7. DG-ACC（kjob/g5ac-r26 cff12a48、A12 = kjob/g5ac-r25 86c45108）
Tools/ShippingGen5Acc*.lean。構造: `AssignKit ι dom env₀`（Acc.lean:32、fields: dataOf, GD, dOf, genData₀, ordCallees, genSem, mem_ordCallees, genData₀_dataOf, genSem_local, genSem_decl, …）。

### AC-1 `hf : DataSoundAt f`
- 完全な型: `DataSoundAt (f : ConstantInfo → StructEnv → MachineShape → Option MachineData) : Prop := ∀ (E) (se) (s) (d), f E se s = some d → d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j)) (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed`（AccDataAgree.lean:23）
- 仮定している定理: `dataSound_of_agree`（:35）, `mkKit_dataSound`（AccMkKit.lean:74）, `mkKit_ordCallees₀_dataSound`（AccOrdCallees.lean:25）
- FG/T1: DG-ACC kit の `DataSound K`（`DataOfShape K`＝RunDataLink の入力）
- 別名: `DataOfSound`（DG-SEM, `initOk` 付き）; `dataOfAt_sound` の先頭 3 連言（5124 note で型一致を確認）
- 支払い予定: DG-DATAOF（`dataOfAt_sound` が候補、5124 note）。kjob/g5do-r6 は kjob/g5ac-r26 の祖先でなく import 不可（5456 note）
- 実runから払えそうか: いいえ、とは言えない（DO-1 の被覆が未供給）
- 分類: 未供給の義務

### AC-2 `hev : GDEvidence f GD dOf env₀`
- 完全な型: `GDEvidence (dataOf) (GD : ConstantInfo → Type) (dOf : {E : ConstantInfo} → GD E → MachineData) (env₀ : Environment) : Prop := ∀ (E : ConstantInfo) (g : GD E), machineShape? false [] E (structEnv env₀) = some (dOf g).shape ∧ dataOf E (structEnv env₀) (dOf g).shape = some (dOf g)`（AccGenDataEv.lean:22）
- 仮定している定理: `mkKit`, `mkKit_dataOf`, `mkKit_agrees`, `mkKit_dataSound`, `genData₀_dataOf_of_evidence`
- FG/T1: DGEN の `GenData.hshape/hdata`（A13 freeze: 「f 由来 GD は DG-SEM の GenData とは別型で genSem を含まない」）
- 支払い予定: DG-SEM の実 `GenData`（5456: 「実 GenData/genSem/laws/hev/hf 未供給」）
- 実runから払えそうか: 不明。A13（`GDf`, `genDataF`; freeze approved 5505、Lean 未実装）は `hf`・shape witness・f 成功を前提にした条件付き結果
- 分類: 未供給の義務

### AC-3 `hloc` / `hdecl` / `hd`
- 完全な型: `hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E} (g : GD E), (∀ k ∈ ordCallees (dOf g), Q ((dOf g).shape.insts[k]).1 = Q' ((dOf g).shape.insts[k]).1) → genSem Q X g = genSem Q' X g`; `hdecl : ∀ Q X {E} (g : GD E), (genSem Q X g).decl = X`; `hd : ∀ Q X {E} (g : GD E), (genSem Q X g).d = dOf g`（AccMkKit.lean:21-39）
- FG/T1: `genSem` の局所性・宣言名・データ一致（DGEN R8 locality）
- 別名: SEM 側の `genSemI_local`（SemCall）、`genSemI_decl`、`genSemI_d` が実 genSem について証明済み（SemCall.lean）
- 支払い予定: DG-SEM（実 `genSem` から）。接続は別ブランチ
- 実runから払えそうか: 不明（SEM 側に該当補題名があるが、ACC branch から import 不可の旨）
- 分類: 未供給の義務

### AC-4 `ReachCover K Reach` と `hcl`
- 完全な型: `ReachCover (Reach : Name → Prop) : Prop := ∀ c, Reach c → ∃ (E : ConstantInfo) (g : K.GD E), entry₀ env₀ c = some E ∧ K.genData₀ E = some g`（Acc.lean:206）; `hcl : ∀ X c, Reach X → CallEdge K X c → Reach c`
- 仮定している定理: `genS_isSome_of_cover`, `machineRouteAt_of_cover`, `accServed0_of_cover_gates`, `accServed0_of_cover`, `closesOfShape_of_data`
- FG/T1: `T1Hyp.pkg`（G3-GEN: 全 reached に package）／`T1Hyp.closed`
- 支払い予定: DG-COVER／DG-DATAOF（A13: 「genData₀ が成功する条件」）
- 実runから払えそうか: 不明（5505: 「実データ成功 coverage は未供給」）
- 分類: 未供給の義務

### AC-5 `GatesNoneAt env₀ Reach`
- 完全な型: `∀ c ci, Reach c → env₀.find? c = some ci → certifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀)) = none ∧ mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀)) (instancePredicate env₀) = none`（AccRoute.lean:34）
- 仮定している定理: `machineRouteAt_of_cover`, `accServed0_of_cover_gates`（AccRoute.lean:49,70）
- FG/T1: ルート 3（machine）に落ちること（GENERAL_SPEC §2 行 1,2 の gate が none）
- 別名: `GateRunsAt`（AccGates.lean）, `ReaderRunsAt`（AccReader.lean）から `gatesNoneAt_of_gateRunsAt`/`gatesNoneAt_of_readerRuns` で導出（条件付き）
- 支払い予定: 記載なし → 未割当
- 実runから払えそうか: 不明
- 分類: 未供給の義務

### AC-6 `ClosesOfShape env₀ L Reach`（= `ClosesData` ∧ `ClosesCalls`）
- 完全な型: `ClosesOfShape … := ∀ c ci shape, Reach c → env₀.find? c = some ci → machineShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀)) (structEnv env₀) = some shape → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx → MachineClosesAtA L.O mctx cctx c shape`（AccRoute.lean:42）; `ClosesData K Reach := ∀ c d, Reach c → dataOf₀ K c = some d → d.ok = true ∧ d.shape.body = quote … d.packed ∧ d.letsAliasOk = true`（AccCloses.lean:29）; `ClosesCalls K L Reach := ∀ c d, Reach c → dataOf₀ K c = some d → d.shape.insts ≠ [] → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx → CallsClose mctx mref cctx cref c d.shape`（:37）
- 仮定している定理: `closesOfShape_of_data`（:42）, `machineRouteAt_of_cover`, `accServed0_of_cover_gates`
- FG/T1: `T1Hyp.closes`（G-CLOSES）
- 別名: `T1HypND.closes`、`MachineRouteAt`（AccServed.lean:60）
- 支払い予定: 記載なし → 未割当
- 実runから払えそうか: 不明。`closesData_of_sound` は `hL : ∀ c d, Reach c → dataOf₀ K c = some d → d.letsAliasOk = true` を別前提に取る（AccDataSound.lean:33）
- 分類: 未供給の義務

### AC-7 `ReadsSupplyAt e L Reach`
- 完全な型: `ReadsSupplyAt (e : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop := ∀ X, Reach X → ∀ (mctx) (cctx) (w), AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → ChainReadsAt e mctx mref cctx cref X w`、`ChainReadsAt e mctx mref cctx cref X w := ∀ s w1 w2 w3 w5 ci envR envR', RunsTo (coreHead X) … w s w1 → RunsTo (getConstInfo X) … w1 ci w2 → RunsTo (Lean.getEnv : MetaM Environment) … w2 envR w3 → RunsTo (Lean.getEnv : MetaM Environment) … w3 envR' w5 → ReadsAt e cref w1 ∧ ReadsAt e cref w2 ∧ ReadsAt e cref w3`（AccReads.lean:39-51）
- 仮定している定理: `accServed0_of_route`, `accServed0_of_cover`, `accServed0_of_cover_gates`, `tripleAcc_clear`, `readsSupply_of_quiet`（`QuietStrengthA` から）
- FG/T1: DG-ENV の C0（`ReadsAt env₀` の world 間 tie）
- 別名: `QuietStrengthA`（EN-1）経由で `readsSupply_of_quiet`
- 支払い予定: DG-ENV
- 実runから払えそうか: 不明（EN-1/EN-6 に帰着）
- 分類: 未供給の義務

### AC-8 `hI : AccIHAt K L Reach 1`, `hKI : AccChildKeeps K L Reach 1`, `hLim : LimitStmt L`, `hS : AccServed0Stmt`
- 完全な型: `AccIHAt L Reach D := ∀ c, Reach c → ∀ mctx cctx u u' r, AdmCtx L.O.quiet mctx cctx → AccInvAt K L Reach D u → RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' → Acc (CallRel K) c`; `AccChildKeeps L Reach D := ChildSynthA L.O (AccInvAt K L Reach D)`（AccInd.lean:44,56）; `AccServed0Stmt`（:66）は X の run から `∀ c, CallEdge K X c → Acc (CallRel K) c` を与える主張で、前提に `AccIHAt … (dv w + 1)` と `AccChildKeeps … (dv w + 1)` を含む
- 仮定している定理: `acc_top_of_run`（AccReads.lean、`hS`, `hI`, `hKI`, `hSt : Start L mctx cctx w`, `hr`）、`hacc_of_top_runs`（`hLim : LimitStmt L`, `hS`, `hKC : AccKeepChildStmt K L (ReachEdge K Top)`, `hrun : ∀ t, Top t → ∃ mctx cctx w w' r, Start L mctx cctx w ∧ RunsTo (synthesizeCombinationalCore t [] false) …`）
- FG/T1: T1 の IH（`IHAt`）の Acc 版。FG の `Start` と `RunsTo` を使う
- 別名: `IHAt`, `ChildKeepsInv`（CR-3）
- 支払い予定: `acc_of_run`（AccInd.lean、`AccOfRunStmt`）が `LimitStmt L`, `AccServed0Stmt`, `AccKeepChildStmt` から導出する形。`LimitStmt` は T1 側（`limitStmt_proved`, ShippingGen2T1.lean）
- 実runから払えそうか: 部分的（`accKeepBody`/`accKeepChild_proved` は証明済み、AccInd/AccKeep）。`AccServed0Stmt` は AC-4..AC-7 に帰着
- 分類: 未供給の義務

### AC-9 `RunDataLink` / `hDS : DataOfShape K`
- 完全な型: `RunDataLink L Reach := ∀ c, Reach c → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx → ∀ shape, MachineDefinesR env₀ mctx mref cctx cref c shape → ∃ d, dataOf₀ K c = some d ∧ d.shape = shape`; `DataOfShape : Prop := ∀ (E) (se) (s) (d), K.dataOf E se s = some d → d.shape = s`（AccServed.lean:64-70）
- 仮定している定理: `accServed0_of_route`（RunDataLink）, `accServed0_of_cover`/`_gates`（`DataOfShape`）, `closesOfShape_of_data`
- 別名: `DataSound K` から `dataOfShape_of_sound`（AccDataSound.lean:30）
- 支払い予定: DG-DATAOF（`DataSound`／`dataOfAt_sound`）
- 実runから払えそうか: AC-1 に記載
- 分類: 未供給の義務

---

## 8. DG-COVER（kjob/g5cv-r13 44d72eaf、Tools/ShippingGen5Cover*.lean）
主要定理: `rowA2_of_inv`, `rowA3_of_inv`, `rowA4B23_mem_of_inv`, `rowB1_of_inv`, `rowC_of_reader`（Cover3）、`rowC_of_reader_ok`（Cover4）、`shapeAgree_of_sides`, `shapeAgree_of_fuel_run`, `shapeAgree_of_production`（Cover5）、`fullInv_reachC`, `fullInv_ctrl`, `fullInv_empty`（Cover6）。割当表は DG_COVER_FREEZE_REV7.md §6（4240 note もこの割当を再掲）。

### CV-1 `hq : LetQuoteEq d st`
- 完全な型: `LetQuoteEq (d : MachineData) (st : MachRead) : Prop := ∀ (j : Nat) (hj : j < d.ls.length) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → quote d.dom (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.bpos i)) (fun i => inputExpr (kDOf d + st.insts.size + st.kinds.size + st.lets.size) (d.vpos i)) (d.ls[j]'hj).2 = machClose st.insts.size st.kinds.size st.lets.size 0 v`（Cover3.lean:693）
- 仮定している定理: `rowC_of_reader`（Cover3）、`rowC_of_reader_ok`（Cover4.lean:54）
- FG/T1: `GenWF` の `RowC`（SM-6）
- 別名: DATAOF／READKINDS の quote 等式（`hq` in `readTot_of_quote_body` は別の命題）
- 支払い予定: 履歴 4246: 「担当: R-trace/R-in/R-nl/R-dom/readF⇒FReachC/U-E3b = dg-readertrace」。`hq` 自身の担当の記載はこの調査では見つからなかった
- 実runから払えそうか: 不明（REV7: 「`LetQuoteEq`, `FullInv` for a real run, `d.ok` for a run は unchanged（未供給）」）
- 分類: 未供給の義務

### CV-2 `hnl : LetsNoLoose st`（R-nl）
- 完全な型: `LetsNoLoose (st : MachRead) : Prop := ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ b, ¬ LooseOcc 0 v b`（Cover3.lean:699）
- 仮定している定理: `rowC_of_reader`, `rowC_of_reader_ok`
- 支払い予定: dg-readertrace（4246 note）。REV7 §6 は当初「new Issue」、後に readertrace が受けた
- 実runから払えそうか: 不明（REV7 S5: `machClose_bvar` は root bvar のみ、`Expr.hasLooseBVars`/`liftLooseBVars` は extern で補題無し）
- 分類: 未供給の義務

### CV-3 `hi : FullInv nDecl st`／`FReachC`（readF の trace）
- 完全な型: `FullInv (nDecl : Nat) (st : MachRead) : Prop := CallOrderInv st ∧ RangeInv nDecl st ∧ OrigAligned st ∧ EntryKinds st`（Cover3.lean:316）; `fullInv_reachC {nDecl} {st0 st} (h : FullInv nDecl st0) (hr : FReachC nDecl st0 st) : FullInv nDecl st`（Cover6）
- 仮定している定理: `rowA3_of_inv`, `rowA4B23_mem_of_inv`, `rowB1_of_inv`, `rowC_of_reader(_ok)`, `fullInv_reachC`
- FG/T1: `GenWF` の RowA/RowB/RowC（SM-6）
- 支払い予定: dg-readertrace（RT 節）
- 実runから払えそうか: 不明。REV7 §0 行 1: 「R-trace for `readF` calls は 未供給／経路未発見。U-E3a は step relation の拡張と `machReserve` step のみ」
- 分類: 未供給の義務

### CV-4 `hbr : ShapeFuelBridge`
- 完全な型: `hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape), machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)`（`shapeAgree_of_production`, Cover5.lean:97）
- FG/T1: production の `machineShape?` と fuel 版 `machineShapeF` の同一視（reader coverage）
- 支払い予定: `sparkle-gen5-reader-bridge`（REV7 §6 の割当表）。本グループ外
- 実runから払えそうか: 不明（REV7: reader-bridge の goal に「fuel 版の正しさだけで production との同一性を主張しない」と書かれている）
- 分類: 未供給の義務

### CV-5 shape 側の同一視 `hsp` / `hss` / `hls` / `hn`
- 完全な型: `hsp : d.shape = sp`; `hss : d.ss.length = sp.layout.slots.length`; `hls : d.ls.length = sp.layout.lets`; `hn : sp.insts.length ≤ d.nIn`（`shapeAgree_of_sides`, `shapeAgree_of_fuel_run`, `shapeAgree_of_production`）; `hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧ sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size`
- 仮定している定理: 上記 3 定理（Cover5）
- FG/T1: `ShapeAgree d st`（Cover3）を介して `RowA` 等へ
- 別名: DO の row 6b。`dataOfFrom_dims`/`dataOfAt_dims`（kjob/g5do-r6@063056d6）が `d.shape = s`, `d.ss.length`, `d.ls.length`, `s.insts.length ≤ d.nIn` を供給（agent build のみ、未review）。ただし DATAOF freeze §10: `s = sp` の同一視は消費側の仮定
- 支払い予定: dg-dataof（4246: 「row 6b/nDecl = dg-dataof」）
- 実runから払えそうか: `hsp`/`hss`/`hls`/`hn` の d 側は `dataOfAt_dims` が与える（`dataOfAt = some` を前提に）。`s = sp` は未供給
- 分類: 未供給の義務

### CV-6 `hcb`（`rowB1_of_inv`）, R-in, R-dom
- 完全な型: `hcb : ∀ k (hk : k < d.shape.insts.length), (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2`（Cover3, `rowB1_of_inv`）。R-in／R-dom は Lean 命題として固定されていない（REV7: `ShapeInputs`, `RootFloatPh, LiftPh, Inst1Ph, BundleIotaPh, SigTyPh` は名前のみ）
- 支払い予定: `hcb` は 4246 note の「B3 = src-argw」、R-in／R-dom／R-nl は dg-readertrace、`SigTyPh` は dg-env
- 実runから払えそうか: 不明（未供給と REV7 に記載）
- 分類: 未供給の義務

---

## 9. DG-READERTRACE（kjob/g5rt-r10 6e6c880f、Tools/ShippingGen5ReaderTrace{,Arms,Chain,Ctl}.lean）
主要定理（承認済み）: `chain_basic_trace`（Chain.lean:30）、`conv_basic_trace`（Arms.lean:106）、`readF_traceGood_of_step`（Arms.lean:195）、`bindLet_reach`, `convBvar_trace`（ReaderTrace.lean）。

### RT-1 `hT : TraceGood senv nDecl (readF senv n)`（帰納仮定）
- 完全な型: `def TraceGood (senv : StructEnv) (nDecl : Nat) (h : Hs) : Prop := ∀ c, TracePre senv nDecl c → ∀ v, h c = some (some v) → TracePost senv nDecl c v`; `TracePre := Pre c ∧ PhPre senv nDecl c`; `TracePost senv nDecl c v := Post c v ∧ FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v`（ReaderTraceCtl.lean:94-99）
- 仮定している定理: `chain_basic_trace`（`ChainBasic e`＝letE 以外）、`conv_basic_trace`（`ConvBasic e`）
- FG/T1: DG-COVER の `FullInv`／`FReachC` 供給（CV-3）
- 支払い予定: 本 Issue 自身（全 arm の `hstep` が揃えば `readF_traceGood_of_step` が全 n の `TraceGood` を与える）
- 実runから払えそうか: いいえ、とは言えない。5560/5577: 「hT/成功run、他arm、全体 TraceGood は未供給」
- 分類: 未供給の義務

### RT-2 `hpre : TracePre senv nDecl (Call.…)`
- 完全な型: `TracePre senv nDecl c := Pre c ∧ PhPre senv nDecl c`、`PhPre` は call 種別ごと（conv/nested/inst/instS/chain/loopBody/loopRoot）に `TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (… + nDecl) e = true` 等を課す（ReaderTraceCtl.lean:47-70）
- 仮定している定理: `chain_basic_trace`, `conv_basic_trace`
- FG/T1: DG-COVER R-in
- 支払い予定: REV7: `ShapeInputs`（R-in）は dg-readertrace の担当
- 実runから払えそうか: 不明
- 分類: 未供給の義務

### RT-3 `hv`（成功 run）
- 完全な型: `hv : (chainStep senv env e st).run (readF senv n) = some (some v)`（Chain）／`hv : (convStep senv env d e st).run (readF senv n) = some (some v)`（Arms）
- FG/T1: FG の成功 run の被覆
- 支払い予定: 記載なし（5560: 「hT/成功run」）
- 実runから払えそうか: 不明
- 分類: 入力条件（成功 run の仮定）

### RT-4 `hstep`（全 arm）
- 完全な型: `hstep : ∀ n : Nat, TraceGood senv nDecl (readF senv n) → ∀ c : Call, TracePre senv nDecl c → ∀ v : c.Res, (step senv c).run (readF senv n) = some (some v) → FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v`、`F : PureFacts senv`（`readF_traceGood_of_step`, Arms.lean:195）
- 支払い予定: 本 Issue。REV4 §0 は未供給の arm を列挙: `chainStep` の `.letE`、`convStep` の `app`（全 arm）と `.letE`、`nestedStep`, `instStep`, `instSStep`, `loopBodyStep`, `loopRootStep`、および `PhFacts`, `SigTyPh`, `InstSFieldsDet`, `ShapeInputs`, `DomAtomic`、U-R2 extractors
- 実runから払えそうか: 不明（上記 arm は「候補経路では未供給」）
- 分類: 未供給の義務

---

## 10. DGEN（par/gen5-t2 c398021c、設計のみ、done）
Lean は無い。DGEN_FREEZE.md／T2COVER_FREEZE.md の設計文（`GeneratedAt` は §…、DGEN_FREEZE.md の行 221 周辺）。

### DG-1 被覆 (i) `dataOf` 成功、(ii) `GenWF d = true`、(iii) `P = genP env₀` と `X ∈ dom`
- 完全な型: `def GeneratedAt (P : Pkgs ι dom) (X : Name) (E : ConstantInfo) (senv : StructEnv) (p : Pkg ι dom) : Prop := ∃ (g : GenData E senv), p.toSem = genSem (semOf P) X g`（DGEN_FREEZE.md、par/gen5-t2@c398021c、設計文）
- 仮定している定理: 設計上の `closingRun_of_run` の `hGen`（CR-2）
- FG/T1: G3-GEN（GENERAL_SPEC.md:491-493）
- 支払い予定: (i) DG-COVER, (ii) DG-WFCOVER, (iii) DG-PKGASSIGN（DG-ENV と DG-ACC から）（DGEN_FREEZE の inhabitation argument）
- 実runから払えそうか: いいえ、とは言えない。DGEN_FREEZE 自身が「(i)(ii) は M5 の被覆義務、コーパス件数では払えない」「失敗時は STOP 条件」と書く
- 分類: 未供給の義務

### DG-2 `DeclConnect`（G3-DECL）
- 完全な型: Lean 命題は固定されていない（DGEN_FREEZE §2.6、設計文: 「`genPkg` の `src` が elaborated declaration X の意味であること、`ConstValue` を前件に持つ」）
- FG/T1: FG の G3-DECL（GENERAL_SPEC.md:494, :535）。`P := genP env₀` で `DeclConnect` 無しの定理は中間結果 FG-REF であり、M5 完了ではない
- 支払い予定: DC-FORM／DC-SUPPLY の study unit（dgen の done note 2833: 子 Issue は gen5 reader-bridge / package-coverage / gencall-proof / decl-bridge / boundary-audit の下）。本グループ外
- 実runから払えそうか: 不明（2698/2702 の R6: 実宣言に対する存在・適切性の一様供給なしに FG 完了とできない）
- 分類: 未供給の義務

---

## 11. DG-AUDIT
履歴は created（2846: 「DG-AUDIT/T2-AUDIT: binder/closure/axiom/vacuity audit incl. not GeneratedAt for P2 p1」）と dependencies（3083）のみ。approved note、対象SHA、Lean は、この調査では見つからなかった。前提は 0 件。DGEN_FREEZE は「`¬ GeneratedAt … (.gen t1Src)` の確認は DG-AUDIT が行う予定、それまで p₁ の排除は主張しない」と書く。

---

## 12. 数えた前提ブロック数
RR 3, CR 5, EN 8, RK 8, DO 3, SM 7, AC 9, CV 6, RT 4, DG 2, AUDIT 0 = 55 ブロック。
うち T1 台帳参照を含むもの: RR-1, RR-3, CR-3, CR-4, CR-5, SM-7。
分類: TRUSTED 境界として明示されたもの 0 ブロック。入力条件と書いたのは RR-1, RR-2, RR-3, CR-4, CR-5, EN-8, RK-5, RT-3, SM-7（RK-4 は hrun が未供給の義務、hX が入力条件）。それ以外は未供給の義務。

## 13. 読んだ文書・branch@SHA 一覧
- scripts/gen2/GENERAL_SPEC.md §1.1-1.4, §2, §3（HEAD kjob/fg-ledger1 d0ddc50b）
- 履歴 JSON: $S/h/sparkle-gen5-{dgen,dg-audit,dg-runreads,dg-closingrun,dg-env,dg-sem,dg-acc,dg-cover,dg-readertrace,dg-readkinds,dg-dataof}.json
- Lean／docs: 88771739（RunReads、履歴上は par/gen2-spec）と 144c3f1e（comment-only、commit の存在を確認）; kjob/g5cr-r6@f3a29dbb（ClosingRun, ClosingRun2, DG_CLOSINGRUN_FREEZE_R6.md, T1ND, DataBridge）; kjob/g5env-r22@b6b3206b（Env, EnvR, EnvQ, EnvStart, EnvFrame{,2,3}, EnvCache{,B,C,D,E}, DG_ENV_T2_FREEZE_R3.md, DG_ENV_T2_U9_FREEZE.md）; kjob/g5sm-u23@7af6c7cc（Sem*）; kjob/g5ac-r26@cff12a48（Acc*, DG_ACC_FREEZE_REV13.md）; kjob/g5cv-r13@44d72eaf（Cover*, DG_COVER_FREEZE_REV7.md）; kjob/g5rt-r10@6e6c880f（ReaderTrace*, DG_READERTRACE_FREEZE_REV4.md）; kjob/g5rk-r23@221d590a（ReadKinds*, DG_READKINDS_U13/U14_FREEZE.md）; kjob/g5do-r6@063056d6 と kjob/g5do-r5@945fbe9a（DataOf*, DG_DATAOF_FREEZE.md）; c398021c（DGEN_FREEZE.md）。
- 存在確認のみ（コミットが存在）: 25540b18, 86c45108, bb49da59, d0a8cf66, 945fbe9a, 44d72eaf, 6e6c880f, f3a29dbb。

## 14. 読めなかったもの／この調査では見つからなかったもの
- DG-AUDIT: 本文の note・SHA（見つからなかった）
- DG_ENV_FREEZE.md（par/gen5-t2 bd591467）の §4 の A/B/C 判断に対するユーザ決定の記録（見つからなかった）
- DG_ENV_T2_U2..U8 の個別 freeze は題名のみ。U9 と R3 のみ本文を読んだ
- DG-SEM／DG-ACC／DG-COVER／DG-READKINDS の初期 rev の各 freeze（P4-P8, REV1-REV12, U5-U12 など）は個別には読まず、最新の主要定理の署名と最新 freeze 表を読んだ。途中単位で解消された前提の履歴は一部のみ（RK, EN）
- DataOfPure／DataOfPure2 の補題群、Cover1-3 の `lo_*`／`sub_*` 補助補題、ReaderTrace の leaf 補題は前提表の対象外として署名を読んでいない
- DG-DATAOF の C-CMP／C-QWIT／T-X の Lean 定義（tree に無い旨が freeze にあるだけ）
- SM-3/SM-4 の「ACC kit が SEM の `hunf`／`hinv` を満たすこと」を直接つなぐ補題名（見つからなかった。別ブランチで import 不可と履歴にある）
- 「実runから払えそうか」を「はい」と書いたのは RK-5, SM-2, SM-5 の一部のみ。履歴・freeze の根拠が補題名で示されたもののみ
