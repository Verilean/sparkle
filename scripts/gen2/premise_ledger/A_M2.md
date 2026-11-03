# 前提台帳 A_M2（FG 側 M2 系 11 Issue）

担当 Issue: sparkle-gen2-u0-types / sparkle-gen2-uadapt / sparkle-gen2-loop-pkg / sparkle-gen2-calldec / sparkle-gen2-step-mem / sparkle-gen2-leaf / sparkle-gen2-gencall-plan / sparkle-gen2-callfield / sparkle-gen2-step / sparkle-gen2-top-contract / sparkle-gen4-oneout-probe。

## 0. 凡例と調査方法（数えたものだけを書く）

- 読み取りのみ。Lean もリポジトリも変更していない（`git show <sha>:<path>`、`git ls-tree`、`git grep` のみ）。作業 worktree は kjob/fg-ledger1（HEAD = d0ddc50b = par/gen2-spec の先端）。
- 履歴は `$S/h/<issue>.json` の "detail" 全文を読んだ。`managerctl show` は使っていない。
- 「完全な型」は `git show` で得た原文を自動で貼った（手で書き写していない）。各ブロックの先頭行コメント `-- sha:path:行範囲` が出典。
- mutant の棄却は履歴に書かれている限り signature/defeq での棄却であり、意味的反例ではない。本台帳は「不可能」「導出不能」を主張しない。履歴・freeze 文書に根拠が書かれていないものは「この調査では見つからなかった」と書く。
- 「支払い予定のIssue」の欄で、Issue タイトルだけから対応を推した場合は（タイトルのみ）と明記した。そのIssueの履歴本文は担当外のため読んでいない。
- M3/gen3 由来（T1 側）の前提は「T1 台帳を参照」と 1 行にした。
- 分類は 3 値: **TRUSTED境界** / **入力条件** / **未供給の義務**。複合のものは併記。
- 前提ブロックの総数: 28（§3 の見出し `### P-NN` を機械的に数えた値）。

## 1. Issue ごとの履歴要約

### 1.1 sparkle-gen2-u0-types（done）
- branch: par/gen2-spec。最新 approved = seq 2138。**対象SHA**: 証拠(docs) 0939cfb6、ビルド対象 6bd02a3a。
- **検証**: g2u0-chk-6bd02a3a exit 0 / 934 jobs / head=base / dirty=false / ancestry verified。8 root の #print axioms は標準のみ。KeepBodyStmt は ChildKeepsInv のもとで全 outcome について証明、DataOkB（6 Bool 行）は generated package で非空虚性あり。
- **残り**（note 原文要旨）: coverage は OPEN（outHead を N1 補題に置換）。discharge されたのは G-KEEP-BODY のみ。T1/FG/milestone の受理ではない。seq 2139 done: Open = G-KEEP-CHILD, G-SERVED, G-DATA（outHead→N1 lemma obligation は M2 acceptance 前）。
- 後続の changes_requested/doing: なし。

### 1.2 sparkle-gen2-uadapt（done）
- branch: par/gen2-spec。最新 approved = seq 2197。**対象SHA**: docs cc305538、ビルド 121c09fe。
- **検証**: g2ua-121c09fe exit 0 / 925 jobs / dirty=false / ancestry verified。Adapt と AdaptInstance が Built、5 root の axioms 標準。
- **残り**: generic G-CALLDEC / data coverage は未了。mixed-parent の instance 証明ではない（HPointAt、局所 width/count 供給、親全体の data coverage が planned）。seq 2199 done。
- 後続: なし（wording fix: maxHeartbeats のファイルスコープ、docs のみ）。

### 1.3 sparkle-gen2-gencall-plan（done、docs のみ）
- branch: par/gen2-spec。最新 approved = seq 2164。**対象SHA**: 508b365e（scripts/gen2/G3GEN_CALL_PLAN.md rev1）。Lean なし。
- **検証**: 設計レビュー。R1（点ごとの adapter U-ADAPT）と R2（Generated / ClosingRun / PortTie の named relation と run-local T1Hyp 修正案）を承認。
- **残り**: G-CALLDEC / T1 / FG は未了。M5 は「実際の成功ソースに対する Generated 被覆 + HPointAt」が必要、G-DATA-CALL は PortTie と子 package 幅の同一 run/witness 供給が必要。seq 2165 done。
- 先行の changes_requested: seq 2158（86e98a51、ordinary-only GenCallStmt が mixed parent の既存 global bridge に届かない）→ rev1 で解消。

### 1.4 sparkle-gen2-calldec（done）
- branch: par/gen2-spec。最新 approved = seq 2154。**対象SHA**: docs 5c1b78a1、ビルド b09a2c0b（Tools 本体は 30ea37f1 で Built）。
- **検証**: g2cd-b09a2c0b exit 0 / 923 jobs / dirty=false / ancestry verified、5 root の axioms 標準。callDec_of_callFactF（hargsLets は callsOk から導出）、real instance tm2_callDec + tm2_dataOk（topshare2）、callFactF_of_hPointAt_pkg（pkgS_dispatch）を確認。
- **残り**: 「Generic G-CALLDEC/data coverage remain UNSUPPLIED」。M5 への再配置は別途 dependency/acceptance 改訂が必要。seq 2155 done。
- 先行の changes_requested: seq 2142（freeze b0c759da）→ rev1 16c6ca4b で承認（seq 2144）。

### 1.5 sparkle-gen2-callfield（done）
- branch: par/gen2-spec。最新 approved = seq 2481（スコープ限定）。**対象SHA**: source 3b702f1574cca457b0f177d3861dc637a223f411、結果文書 f8164382。
- **検証**: g2cf-3b702f15 source=head=base、dirty=false、ancestry_verified、exit 0、981 jobs。CallField / OneOutCallField / PkgCompat と依存 Gen2 の Built、公理は標準のみ、sorryAx なし。Defs と GEN2_DEFS は cmp 一致。
- **残り**: 「callerL の package/hp の充足は未確認（偽とは未証明）、CallDec 全体/run 存在/comb 分岐選択/G-ONEOUT/M2 完了は未主張」。M3 InstClosed 統合時に使用箇所と統合 SHA の回帰を再確認。seq 2482 done。
- 先行: seq 2469 freeze rev1 d9e29568 approved for implementation。

### 1.6 sparkle-gen2-leaf（done）
- branch: par/gen2-spec。最新 approved = seq 2298（スコープ限定）。**対象SHA**: レビュー範囲 ac91f8e3..5b93aa2f、ビルド対象 d9fac18c。Issue 目標は seq 2289 で LeafStmt'（register leaf）に絞り直された。
- **検証**: g2lf-d9fac18c exit 0 / 927 jobs（LeafInstance Built、7 root 標準公理）、回帰 g2lf-reg-be7ef8fb exit 0 / 956 jobs（LeafInstance/MemParentInstance/QuantInstance/PkgCompat は Replayed）。
- **残り**: 旧 all-leaf LeafStmt、slotless leaf の parent consumer（sparkle-gen2-step）、seq 互換、ShipsRes/CacheShips/ServedP/StepStmt/T1 接続、generic LeafDataOk/ExtInS 供給（M5）、full T1/FG は未了。seq 2299 done。
- 先行: seq 2287 で premise 修正案（ExtInS, slots≠[]）承認。

### 1.7 sparkle-gen2-loop-pkg（done）
- branch: par/gen2-spec。最新 approved = seq 2281。**対象SHA**: docs ac91f8e3、ビルド 94ed8609（回帰 g2lp-0e4cdf99、PkgCompat g2lp-45c937c1）。
- **検証**: g2lp-94ed8609 exit 0 / 741 jobs（LoopRestrict, QuantInstance Built、8 root 標準公理）。g2lp-0e4cdf99 exit 0 / 962 jobs、g2lp-45c937c1 exit 0 / 724 jobs。
- **残り**: 「Not proof of actual successful run existence, arbitrary domain/IP coverage, generic LoopFacts/MemDec/ExtInS supply, G3-DECL or full M2/T1/FG」。seq 2282 done: G-MEMCALLS, ExtInS supply, data/MemOrigin coverage, G-CLOSES-FRESH が open。
- 先行: seq 2239 changes_requested（500bc675）→ rev2 f8622fb4 で承認（seq 2259）。

### 1.8 sparkle-gen2-step-mem（done）
- branch: par/gen2-spec。最新 approved = seq 2235。**対象SHA**: docs ea5f5cda、ビルド f1a4367f。
- **検証**: g2mp-f1a4367f exit 0 / 940 jobs / dirty=false / ancestry_verified。lm_ships（leafM, 条件付き）Built、11 root 標準公理。
- **残り**: 実 IP は sparkle-gen2-loop-pkg に移管。G-MEMCALLS, ExtInS 汎用供給, data/MemOrigin coverage, G-CLOSES-FRESH, 他 case が open。seq 2236 done。
- 先行: seq 2186 changes_requested（b71e6810）→ rev1 121c09fe 承認（seq 2194）。A4（MemOrigin）は 3535fa85 で承認（seq 2211）。

### 1.9 sparkle-gen4-oneout-probe（done）
- branch: **par/gen4-gate**。最新 approved = seq 2403（スコープ限定 probe）。**対象SHA**: source 2dede972、evidence docs 1973de8e。
- **検証**: g4oo-2dede972 exit 0 / 362 jobs / head=base=source / dirty=false / ancestry verified。callerL.instFields = []、callee pickByteH の outs 名 = ["out"]、`oneout_name_mismatch`（decide、axiom propext）。
- **残り**: 「Qualify: contradiction は pickByteH との組と inhabited index family で確定、every G-ONEOUT parent ではない」。CallField 方向を承認、定義変更なし。Pkg.comb、S4 consumer、G-ONEOUT 完了は open。seq 2404 done（以後は sparkle-gen2-step S4 / sparkle-gen2-callfield で追跡）。
- 先行: seq 2393 diagnostic（wrong namespace）、直して再ビルド。

### 1.10 sparkle-gen2-step（**未 done**、最終 note = seq 4596 doing）
- branch: par/gen2-spec（〜d0ddc50b）、以降 kjob/g2st-r1..r6（S1/S2 統合後の base = kjob/g2tc-s2 fa84af5d）。
- 最新の approved/scoped-approved 単位（seq 順、Lean 実装の対象SHAを太字）:

| seq | 単位 | 対象SHA | 検証（履歴記載） |
|---|---|---|---|
| 2313 | S6 + S1（A-COMB 定義、C1-C3、S1 reset irrelevance） | **1fdbc18d** | g2st-s6-1fdbc18d exit 0 / 973 jobs / dirty=false |
| 2466 | Pkg.comb steps 1-3、S2 / S2-c（slotless leaf） | **22417406**（result db95ef9d） | g2cp-h-682dbb1c, g2cp2-698be477 (978 jobs), g2cp3-22417406 (746 jobs) exit 0 |
| 2501 | S4-BD risk check（probe） | 323d0501 | g2bd-323d0501 exit 0 / 387 jobs |
| 2515 | S4 stage A（one-output served consumer） | **99f0de5d**（audit 579c7644） | g2s4a-99f0de5d exit 0 / 731 jobs |
| 2532 | S4 run-local fit chain | **c6951eb8** | g2fc-c6951eb8 exit 0 / 734 jobs（16 root 標準公理） |
| 2563 | S4 stage B（one-output TopShips） | **93e9994c** | g2sb-93e9994c exit 0 / 736 jobs |
| 2574, 2576 | DataBridge、P-MEM/WID docs rev3 | **5d6ca626**、docs 48775f38 | g2db-5d6ca626 exit 0 / 749 jobs（22 root 標準公理） |
| 2597 | P-MEM-4 O-copies（hnomem 名前半分を除いた 14 theorem） | **d0ef6371** | g2pm4b-d0ef6371 exit 0 / 757 jobs |
| 2723 | S3 group-parent comb consumer | **d603ac07** | g2s3c-d603ac07 exit 0 / 735 jobs / dirty=false |
| 2867, 2878 | S5 stage A/B（slotless parent）、probe | **f7e42988**、probe ec3d9b14 | g2s5-f7e42988 exit 0 / 743 jobs、g2s5p3-ec3d9b14 exit 0 |
| 2934 | NC suppliers + S5 stage C | **36342cb8** | g2nc4-36342cb8 exit 0 / 754 jobs |
| 3601 | SU-2（origin 排他）+ freeze rev1 | **a9f99953** | stv-a9f99953 exit 0 / 717 jobs / dirty=false |
| 3981, 3998 | SU-1a/b、SU-3（StepStmtCases）、SU-4（LiftShips 仮定の有限最大） | **96ac6add**（header sync bc91b107） | st3v-96ac6add exit 0 / 754 jobs / dirty=false |
| 4282 | LS-1 freeze（instFree 高さ輸送） | e8bc3012 | docs のみ |

- 後続: seq 4570 review（LS-1 実装 2be39bc4）→ seq 4592 **changes_requested**（StepReach の root 自身判定、helper unknown 負例）→ seq 4596 doing（修正を agent g2st-r6 が開始）。
- **残り**（seq 3998 / 4596 の note）: 「LiftShips 未供給、StepStmtCases は 4 row と case 制限付きで StepStmt ではない、ChildPortWidths 統合時に empty-index 幅供給と再検証が必要。Issue/M2/FG 未完」。
- 注: 全承認は「スコープ限定」。StepStmt 本体は証明されていない（note 原文: "StepStmtCases は 4 row と case 制限を持ち StepStmt ではない"）。

### 1.11 sparkle-gen2-top-contract（**未 done**、最終 note = seq 5569 todo）
- branch: kjob/g2tc-s2（Defs の TopShips を R-G に切替え、base fa84af5d）→ kjob/g2tc-ctrl → kjob/g2tc-ptop … kjob/g2tc-ptop21。
- 最新 approved: seq 5527（U7）。**対象SHA**: 22862066da68494663ad4bccf56dd944d1e16fa8（kjob/g2tc-ptop21; freeze rev14 715f85c6）。ptop21v-22862066 exit 0 / 772 jobs / dirty=false / ancestry_verified。TYPE 2 / MUTANT 5 / AXIOMS 3 標準。
- 承認単位（seq 順）:

| seq | 単位 | 対象SHA |
|---|---|---|
| 2781 | R-G 設計（TopShips の rst/clk 前提を入力メンバーシップで守る） | a966486b（TOP_CONTRACT_REVISION.md） |
| 2933 | NC suppliers（step と共有） | 36342cb8 |
| 3430 | S2: Defs 切替 + CLKIN/PROD/COMPAT（scoped） | fa84af5d（s2v-fa84af5d exit 0 / 1076 jobs） |
| 3463 / 3612 | CTRL freeze rev1 / U-TOP-CTRL（PTopPrem, ptop_inst） | 15f416f5 / 1207f0cd（tcv exit 0 / 961 jobs） |
| 3864 / 3907 / 3951 | TopShipsAt/Wit/ptop_same / ss=[] 系 4 定理 / c1,c4,guard 3 定理 | 690274a7 / ccf6d569 / 1fdaa5b0 |
| 4179 / 4337 / 4673 | TopSupply3（R1-R4, E1-E3）/ U1 / U2 | c32e8e17 / 18125e5c / e8089345 |
| 4880 / 4981 / 5067 | U3（PTopPrem 組立）/ U4 ptop_ofSlotlessRun / U5 ptop_pbh | 0ab11f69 / 8136d9dc / ddb492f0 |
| 5154 / 5340 | 監査修正 / U6 ptop_pbh_ofEx（同一 witness） | cc018880 / c5c37d2b |
| 5527 | U7 lawsQuietFalse と ¬PbhRunEx | 22862066 |

- **残り**（seq 5527, 5569）: 「非空虚 Laws・一般 PbhRunEx・具体 run・共同充足性・P-TOP/T1/FG 未供給」。seq 5569 todo: 「再開条件 = fg-final/gen3-t1-assembly の前提台帳ができ、この Issue の前提が実 run から払う 2〜3 本に選ばれたとき」。
- 先行 changes_requested（解消済）: 3815（probe の axioms 監査、反証文の限定）、4000（rev7 の完全型）、5154（U6 の run witness 対応）。


## 2. FG binder 一覧（台帳の骨組み）

出典: scripts/gen2/GENERAL_SPEC.md §1.1 / §1.2 / §1.3 / §4 / §6 と scripts/gen2/GEN2_DEFS.lean.txt（いずれも d0ddc50b = par/gen2-spec 先端）。テキストは `git show` の原文。以後のブロックは「FG/T1 への対応」欄でここの ID（F*, T*, I*, S*）を使う。

### 2.1 FG（schema）と Start — F 系

GENERAL_SPEC.md §1.1（d0ddc50b: scripts/gen2/GENERAL_SPEC.md:91-94）:

```text
-- d0ddc50b:scripts/gen2/GENERAL_SPEC.md:91-94
  ∨ RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w' )  -- :8940
  → ReflectsAll L declName parameters →                   -- G3, per route, per reached declaration (§6)
  → ∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D   -- (b, raw) related by the entry's post-processing
```
```

| ID | binder | 内容 | Lean 定義 |
|---|---|---|---|
| F1 | `∀ (L : Laws mref cref)` | 一様な実行時法則（G5）。`L.O : RefLawsAOps MkRefd mref cref`、`L.T : RefLawsATele L.O.quiet mref cref` | あり（§2.2 の `Laws`） |
| F2 | `declName parameters mctx cctx w b D w'` | 入力・結果 | — |
| F3 | `Start L mctx cctx w` | `AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`（最外コンパイルの開始条件） | あり（`Start`） |
| F4 | `RunsTo (synthesizeCombinational declName) … (b, D) w' ∨ RunsTo (synthesizeCombinationalWithParameters declName parameters) …` | 実際の成功 run（default entry :8920 / parametric entry :8940） | 型は FG schema のみ（下記 T1Stmt / StepStmt 等では `synthesizeCombinationalCore` の run を使う） |
| F5 | `ReflectsAll L declName parameters` | G3: route ごと・到達宣言ごとの shape 反映 | **この調査では Lean 定義が見つからなかった**（`git grep ReflectsAll` を HEAD と kjob/g2tc-ptop21 の Tools/Tests で実行: GENERAL_SPEC.md のみ） |
| F6 | `∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D` | 結論（(b, raw) は entry の後処理で関係づく） | `Pk` の Lean 定義は**この調査では見つからなかった**。`TopShips` はあり（§2.2） |

GENERAL_SPEC §1.1 の注記: FG は schema。route 固有部分（`ReflectsAll`、非 machine route の source package、`b ↔ raw` の後処理関係）は M4 で固定。machine route 部分は §1.3 の正確なテキスト。success のみが対象。

### 2.2 GEN2_DEFS.lean.txt の binder を持つ定義（原文）

**Laws / Start（F1, F3）**（GEN2_DEFS.lean.txt:45-53）

```lean
-- d0ddc50b:scripts/gen2/GEN2_DEFS.lean.txt:45-53
/-- The uniform runtime laws (G5): the same for every declaration. -/
structure Laws (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) where
  O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref
  T : RefLawsATele O.quiet mref cref

/-- The start conditions of an OUTERMOST compilation: admissible contexts and the depth-0 world with its cache
invariant. They are conditions on the start, not laws. -/
def Start {mref cref} (L : Laws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) : Prop :=
  AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w
```

**Laws の中身**（`RefLawsAOps` / `RefLawsATele`。Tools/ShippingChildInvA.lean@d0ddc50b）

```lean
-- d0ddc50b:Tools/ShippingChildInvA.lean:259-294
/-- The non-continuation fields of `RefLawsCore`
(`ShippingChildBndCore.lean:102-160`), each with its context quantifier
restricted to `AdmCtx`, its world quantifier to quiet worlds, and `Framed`
replaced by `FramedA Fresh`. -/
structure RefLawsAOps (Fresh : (σ : Type) → IO.Ref σ → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) where
  quiet : Void IO.RealWorld → Prop
  diag : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), Diag p → ∀ w, quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w)
  frameT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w)
  excOk : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), Op p →
    ∀ w e w', quiet w → p mctx mref cctx cref w = .error e w' → OkExc e
  frameQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), FramedA Fresh p → ∀ w,
    quiet w → quiet (endW mctx mref cctx cref p w)
  cacheSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → quiet w → quiet w'
  depthSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    quiet w → quiet w'
  frame : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), FramedA Fresh p → ∀ w, quiet w →
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w
  cacheSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → quiet w →
    cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w
  depthSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → quiet w →
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = v
```

```lean
-- d0ddc50b:Tools/ShippingChildInvA.lean:296-334
/-- The continuation-passing fields, restricted: the outer context is
admissible, the invariant implies quietness (`∀ w, I w → quiet w`, so `Keeps`
— which starts from an `I` world — only ever starts from quiet worlds), and
the continuation is asked to keep `I` ONLY in admissible contexts. NOT
derived from the old `RefLawsCore` fields (a different assumption). -/
structure RefLawsATele (quiet : Void IO.RealWorld → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) : Prop where
  telescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
  lamTelescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)
  localDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
  letDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)
```

`AdmCtx`（Tools/ShippingChildInvA.lean@d0ddc50b）:

```lean
-- d0ddc50b:Tools/ShippingChildInvA.lean:73-79
/-- **Admissible contexts**: the Meta context's `canUnfold?` callback, if any,
is inert. Nothing is asked of the Core context (audit in the design doc: its
only non-data field is the cancel token, which writes none of the three refs;
the interrupt exception's class is open item O-cancel). -/
def AdmCtx (quiet : Void IO.RealWorld → Prop) (mctx : Meta.Context) (_cctx : Core.Context) : Prop :=
  ∀ f, mctx.canUnfold? = some f → InertUnfold quiet f

```

`JQC`、`RealChildA`（Tools/ShippingChildCacheA.lean@d0ddc50b）:

```lean
-- d0ddc50b:Tools/ShippingChildCacheA.lean:101-113
/-- **A real child under the admissible boundary.** `r` is returned by a run
of the real entry on `c`, in an admissible context, from a world that is quiet
for the fixed witness `O`, whose synthesis ref holds `synthesizeChild` and
whose cache value has real-child entries only. -/
inductive RealChildA (O : RefLawsAOps Fresh mref cref) : Name → Res → Prop  -- guess: C1
  | run {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld)
      (adm : AdmCtx O.quiet mctx cctx)
      (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r')
      (synth : sv w = some synthesizeChild)
      (quiet : O.quiet w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChildA O c r

```

```lean
-- d0ddc50b:Tools/ShippingChildCacheA.lean:117-122

/-- The vertical invariant WITH its cache half: quiet, synthesis ref, depth
`D`, and the cache VALUE of the world has real-child entries only. -/
def JQC (O : RefLawsAOps Fresh mref cref) (D : Nat) (w : Void IO.RealWorld) : Prop :=
  JQ O.quiet D w ∧ CacheInvA O (cv w)

```

**パッケージ（G3-GEN の対象）— `Pkg` と 3 つの Facts 構造**（T1 の `pkg` に効く）

```lean
-- d0ddc50b:Tools/ShippingGen2Pkg.lean:33-38
inductive Pkg (ι : Type) (dom : ι → DomainConfig) where
  | gen (p : SrcPkg ι dom)
  | loop (p : SrcPkgL ι dom)
  | comb (p : CombPkg ι dom)

variable {ι : Type} {dom : ι → DomainConfig}
```

```lean
-- d0ddc50b:Tools/ShippingGen2SrcPkg.lean:38-57
/-- The generated facts of one declaration as one package: `Tests.Compiler.CDef.GenPkg` (CDefTest.lean:33) moved
to `Tools` unchanged, plus `kD`, the number of declared (non-call-result) binders. -/
structure SrcPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  ρ : ι → Type
  inh : Inhabited (HList (tys d.ss))
  inits : HList (tys d.ss)
  body : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
    Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i)
  obsR : (i : ι) → ρ i → List (Nat → Nat)
  ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)
  gen : @GenFacts d ι dom ρ inh inits body obsR ext extB src
```

```lean
-- d0ddc50b:Tools/ShippingQuadComposed.lean:102-151
/-- **The elaborator-generated facts of one declaration `X` (text-supplied, named exactly):** `inits body obsR ext extB src` are `X.machineInits`,
`X.machineBody`, `X.machineResult`, `X.machineExt`, `X.machineExtB`, `X.machineSource`, and the fields are `X.machine_ok`, `X.machine_body`,
`X.machine_inits`, `X.machine_writes`, `X.machine_result`, `X.machine_source`, and the causality of `X.machine_ext_causal` (as `HCausalOf`).  These
are the premises of `Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA` and are NOT derived generically. -/
structure GenFacts (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop where
  ok : d.ok = true
  body_eq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  init : d.initOk inits = true
  writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) d.nexts
  result : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits S)
            (ext i bools bits S) t (S.val t)).v (d.vpos j) w) o.2)
  source : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst
  causal : HCausalOf d dom ext extB
```

```lean
-- d0ddc50b:Tools/ShippingGen2Loop.lean:125-171
/-- **`LoopFacts`**: the premises of `machine_trace_of_loop_causal` as one structure (fields copied verbatim). -/
structure LoopFacts (d : MachineData) {ι : Type} (dom : ι → DomainConfig) {α : ι → Type} [∀ i, Inhabited (α i)]
    {ρ : ι → Type}
    (σ : (i : ι) → α i → HList (tys d.ss))
    (inits : HList (tys d.ss))
    (f : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Signal (dom i) (α i))
    (res : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Signal (dom i) (α i) → ρ i)
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (α i) → Nat → Signal (dom i) Bool)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop where
  ok : d.ok = true
  hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  hinit : d.initOk inits = true
  h0 : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i)),
      σ i ((f i bools bits l).val 0) = inits
  writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (l : Signal (dom i) (α i))
      (t : Nat),
      σ i ((f i bools bits l).val (t + 1)) =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits l)
            (ext i bools bits l) t (σ i (l.val t))).v (d.vpos j) w) d.nexts
  hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (L : Signal (dom i) (α i))
      (t : Nat),
      (obsR i (res i bools bits L)).map (fun g => g t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls (extB i bools bits L)
            (ext i bools bits L) t (σ i (L.val t))).v (d.vpos j) w) o.2)
  hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
```

```lean
-- d0ddc50b:Tools/ShippingGen2Loop.lean:178-197

/-- **The loop-form source package.** -/
structure SrcPkgL (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  α : ι → Type
  inh : ∀ i, Inhabited (α i)
  ρ : ι → Type
  σ : (i : ι) → α i → HList (tys d.ss)
  inits : HList (tys d.ss)
  f : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → Signal (dom i) (α i)
  res : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → ρ i
  obsR : (i : ι) → ρ i → List (Nat → Nat)
  ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → Nat → Signal (dom i) Bool
```

```lean
-- d0ddc50b:Tools/ShippingGen2CombPkg.lean:41-58
/-- **`CombFacts`**: the generated facts of a slotless declaration (FREEZE §2), the premises of
`machine_traceL_of_comb_callsRA_ran` at `ext := fun _ _ bits => bits`, `extB := fun _ bools _ => bools` (beta-reduced). -/
structure CombFacts (d : MachineData) {ι : Type} (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      List (Nat → Nat)) : Prop where
  ok : d.ok = true
  hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
            (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  hinit : d.initOk inits = true
  hnext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (t : Nat),
    inits = evalTerms (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).b (d.bpos j))
      (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).v (d.vpos j) w) d.nexts
  hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (t : Nat),
    (src i bools bits).map (fun g => g t) =
      d.outs.map fun o => enc o.1 (eval (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).b (d.bpos k))
        (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).v (d.vpos k) w) o.2)
```

```lean
-- d0ddc50b:Tools/ShippingGen2CombPkg.lean:85-93
/-- **The slotless, call-free package** (FREEZE §2). -/
structure CombPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  inits : HList (tys d.ss)
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)
  facts : CombFacts d dom inits src
```

**子インターフェース（ChildShips 系）**（GEN2_DEFS.lean.txt:57-96）

```lean
-- d0ddc50b:scripts/gen2/GEN2_DEFS.lean.txt:57-96
/-- **A combinational child run at depth `n`** (A-COMB, scripts/gen2/STEP_IFACE_FREEZE.md rev3 §2): `SeqChildRunN`
(MachineDepth.lean:64) without its clock/reset part — no input named `"clk"`/`"rst"`, no clock/reset premise on the
input stream. The same interface data (`bsC`, `outsC`, `S`) and the same `ResetN` start. -/
def CombChildRunN (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (dsn : Design) (n : Nat)
    (mc : Sparkle.IR.AST.Module) (bsC : List (Name × MixedGateBinder)) (outsC : List OutField)
    (S : (Nat → List Nat) → List (Nat → Nat)) : Prop :=
  mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
  (mc.inputs.map (·.name)).Nodup ∧
  "clk" ∉ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name) ∧
  (∀ x ∈ mc.outputs.map (·.name), x ∉ mc.inputs.map (·.name)) ∧
  (Tools.ShippingMachineCompose.argPorts mc).length = (bsC.filter fun b => b.2 != .domain).length ∧
  ∀ (T : Nat) (ins : Nat → String → Nat) (s : KT n) (vals : Nat → List Nat),
    (∀ τ, τ < T → InRange (vals τ) (bsC.filter fun b => b.2 != .domain)) →
    (∀ t, t < T → (Tools.ShippingMachineCompose.argPorts mc).map (fun p => ins t p.name) = vals (T - 1 - t)) →
    ResetN dsn n mc s →
    ∃ envs, RunOn children n mc (seedIn mc ins) T s = some envs ∧ envs.length = T ∧
      ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
        outsC[k]? = some o → (S vals)[k]? = some f → (envs[j]'hj) o.name = f j

/-- The child run: sequential or combinational (A-COMB). The two disjuncts exclude each other (`"clk"`). -/
def ChildRunN (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (dsn : Design) (n : Nat)
    (mc : Sparkle.IR.AST.Module) (bsC : List (Name × MixedGateBinder)) (outsC : List OutField)
    (S : (Nat → List Nat) → List (Nat → Nat)) : Prop :=
  SeqChildRunN children dsn n mc bsC outsC S ∨ CombChildRunN children dsn n mc bsC outsC S

/-- **ChildShips** (the IH content of `c`, for THE result `(mc, Dc)` a parent was served): for every design `dsn`
that contains `Dc`'s modules and `mc`, the child run interface at height `n`, with the interface data taken from
`c`'s own package `q`. Built-in transport: it is stated for every extending `dsn`, so the producer proves the
transport once (gap G-TRANSPORT). A-COMB: the run is `ChildRunN` (sequential or combinational); this WEAKENS the
child guarantee, and the final guarantee is preserved only once every parent consumer handles both branches. -/
def ChildShips (q : Pkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design) : Prop :=
  ∀ (dsn : Design), (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ (i : ι), ChildRunN (childMap dsn.modules) dsn n mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)

/-- Which callee output the parent's call `k` reads. Group parents read the field named by `instFields`; one-output
parents (`instFields = []`, `closeInsts`/`instStmt`, Machine.lean:280) read the callee's ONLY layout output. -/
def CallField (p q : Pkg ι dom) (k : Nat) (o : OutField) : Prop :=
  if p.d.shape.instFields = [] then q.d.shape.layout.outs = [o]
  else o.name = p.d.shape.instFields.getD k ""
```

**CallDec / MemDec（T1Hyp.dec の中身）**（GEN2_DEFS.lean.txt:98-118）

```lean
-- d0ddc50b:scripts/gen2/GEN2_DEFS.lean.txt:98-118
/-- **CallDec** (gap G-CALLDEC; the non-run conjuncts of `SeqFactsRN`, CallsLinkedTNR.lean:23): the parent `p`'s
ordinary call `k` to `c` (package `q`) has its arguments among `p`'s lets, in range for `q`'s ports, and the
parent's call-result signal at position `p.kD + k` equals `q`'s source output selected by `CallField`
(scripts/gen2/CALLFIELD_FREEZE.md §1: the call's field for a group parent, the only output for a one-output parent). -/
def CallDec (p q : Pkg ι dom) (k : Nat) : Prop :=
  (p.d.shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args, (p.d.shape.insts.map (·.2.1))[k]? = some args ∧
    args.length = q.ports.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (∀ r (hr : r < args.length), args[r] < p.d.ls.length ∧ ∃ g, (p.lsrc i bools bits)[args[r]]? = some g) ∧
      (∀ τ, InRange (valsOf (p.lsrc i bools bits) args τ) q.ports) ∧
      ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
        (q.S i (valsOf (p.lsrc i bools bits) args))[k']? = some f ∧
        ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-- The memory side of one entry: `MemFacts` of the parent's own package (it mentions the parent's call arguments,
so it is a fact of the PARENT, not a child interface; gap G-MEMCALLS supplies it). -/
def MemDec (p : Pkg ι dom) (k : Nat) (c : Name) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    MemFacts p.d.shape (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extS i bools bits) k c
```

**route 証拠 `MachineTaken`**（GEN2_DEFS.lean.txt:127-132）と、その中身 `MachineRunJQC`（Tools/ShippingServedRealA.lean:89-95）、`MachineClosesAtA`（Tools/ShippingChildRunAKids.lean:155-161）、`MachineDefines`（Tools/ShippingMachineEntry.lean:2340-2353）:

```lean
-- d0ddc50b:scripts/gen2/GEN2_DEFS.lean.txt:127-132
/-- **Route evidence of THIS run**: the machine synthesis the core run performs returned the run's result
(`MachineRunJQC`, ServedRealA.lean:86) — the machine route was TAKEN, not only read (`MachineDefines` alone says
`machineShape? = some`; it does not exclude the fall-back to the legacy route). -/
abbrev MachineTaken {mref cref} (L : Laws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (n : Nat)
    (c : Name) (shape : MachineShape) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  MachineRunJQC L.O mctx cctx n c shape raw D
```

```lean
-- d0ddc50b:Tools/ShippingServedRealA.lean:89-95
/-- The machine synthesis a core run performs returned the run's result, from a `JQC O n` world. -/
def MachineRunJQC (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    (n : Nat) (c : Name) (shape : MachineShape) (M : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (tenv : Lean.Environment), ∃ (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
      mctx mref cctx cref w9 (some (M, D)) w10 ∧ JQC O n w9
```

```lean
-- d0ddc50b:Tools/ShippingChildRunAKids.lean:155-161
/-- **The machine synthesis does not fall back — where a real compile runs it** (PREMISE; analogue
of the old `MachineClosesAt`): from a `JQC O n` world at depth `n ≥ 1`, with the compiler's own
logger, the run does not return `none`. -/
def MachineClosesAtA (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context)
    (cctx : Core.Context) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) (n : Nat) w r w', JQC O n w → 1 ≤ n →
    RunsTo (synthesizeMachineCertified
```

```lean
-- d0ddc50b:Tools/ShippingMachineEntry.lean:2340-2353
/-- **The machine boundary.** In this run the entry constant of the
declaration — computed by `entryConst` from the declaration and the
environment the run reads — is refused by both certified gates and is the
machine `shape` (by the structure projections of the environment the run
reads). -/
def MachineDefines (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ w1 ci w2 w5 envR w6 w7 envR' w8,
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w7 envR' w8 →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR)
      (userInliner envR) (structEnv envR)) = none ∧
```

**IH / 不変量（I 系）**（GEN2_DEFS.lean.txt:134-189）

```lean
-- d0ddc50b:scripts/gen2/GEN2_DEFS.lean.txt:134-189
/-- A result `r` of `c` with the package and height it ships at. -/
def ShipsRes {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ ∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2

/-- The child-cache invariant, ON THE REACHED declarations: every `sparkleChildCache` entry of a reached name ships.
Entries of other names (children the translator synthesises on other routes) are unconstrained, so their insertion
keeps it. `sparkleSubModuleCache` (the memo of route 5) is a different map and is NOT covered (gap G-MEMO). -/
def CacheShips {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, Reach c → m.get? c = some r → ShipsRes L P c r

/-- `ShipsRes` at a FIXED height `n` (what consumer 2 needs at its `n`; `ShipsRes` gives some height, G-LIFT
bridges). -/
def ShipsAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (n : Nat) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ ∃ q, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2

/-- **The cache/child invariant at depth `D`**: `JQC` and `CacheShips` on the reached names. -/
def InvAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) :
    Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w ∧ CacheShips L P Reach (cv w)

/-- **The success half of the induction hypothesis at depth `D`**: every SUCCESSFUL run of a REACHED declaration's
entry from an `InvAt D` world, in an admissible context, ships. (The all-outcome cache half is `ChildKeepsInv` /
`BodyKeepsInv`; `IHAt` alone says nothing about throwing runs.) -/
def IHAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context) (u u' : Void IO.RealWorld) (r : Res),
    AdmCtx L.O.quiet mctx cctx → InvAt L P Reach D u →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' →
    ShipsRes L P c r

/-- **All-outcome keep of the body at depth `D`** (the `BodyKeepsP` shape, ChildPinC.lean:305, with `JQP` replaced by
`InvAt`): the synthesis body of EVERY declaration, on every route, keeps `InvAt` — returning or throwing (`Keeps`
constrains `endW` of every outcome and asks `ErrOk`, ChildInv.lean:306-316). -/
def BodyKeepsInv {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Keeps mctx mref cctx cref (InvAt L P Reach D)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)

/-- **All-outcome keep of the child entry at depth `D`**, for EVERY name (`ChildSynthA`, ChildFrontCP.lean:240). -/
def ChildKeepsInv {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  Tools.ShippingChildFrontCP.ChildSynthA L.O (InvAt L P Reach D)

/-- **G-KEEP-BODY** (generalises `bodyKeepsP_of_tele`, ChildPinC.lean:329, whose components take a `StableA`
invariant): the child hook at `D` gives the body's all-outcome keep at `D`. -/
def KeepBodyStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ D, ChildKeepsInv L P Reach D → BodyKeepsInv L P Reach D

/-- **G-KEEP-CHILD** (generalises `childKeepsP_of_body`, ChildPinC.lean:346): the child entry at `D` keeps `InvAt D`
on every outcome, from the body's keep one level deeper (the nested run, including a child that throws after
partially synthesising its own children) and, for the insertion of a REACHED name's result, the SUCCESS semantics
`IHAt` of that run. -/
def KeepChildStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → BodyKeepsInv L P Reach (D + 1)) →
    IHAt L P Reach D → ChildKeepsInv L P Reach D
```

**T1Hyp（T 系: pkg / defines / closes / dec / closed と DataOk placeholder）**（GEN2_DEFS.lean.txt:191-212）

```lean
-- d0ddc50b:scripts/gen2/GEN2_DEFS.lean.txt:191-212
/-- **The hypotheses of T1 on the reached declarations.** `DataOk` is a PLACEHOLDER Prop parameter: U0 fixes it to
a concrete conjunction of Bool checks over `q.d` (GENERAL_SPEC §4.4); no unit may instantiate it so that a statement
becomes vacuous, and every unit's acceptance includes a vacuity audit (a concrete package satisfying it). -/
structure T1Hyp {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop where
  /-- G3-GEN: a package for every reached declaration. -/
  pkg : ∀ c, Reach c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q
  /-- G3-SHAPE: its shape reflection, in every admissible context. -/
  defines : ∀ c, Reach c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
    MachineDefines mctx mref cctx cref c q.d.shape
  /-- **T1 scope (route 3)**: the machine synthesis of every reached declaration returns (it does not fall back).
  Coverage obligation G-CLOSES: derive from the data (`memCallee_closesA`, Srm3Callee.lean:91, for memory callees;
  `closes_of_data`, Tools/ShippingMachineClosesData.lean, in general); declarations where it fails are route 4 (M4),
  not removed from FG. -/
  closes : ∀ c, Reach c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
    MachineClosesAtA L.O mctx cctx c q.d.shape
  /-- G-CALLDEC / G-MEMCALLS: the decodings (to be derived; GENERAL_SPEC §4.2). -/
  dec : ∀ c, Reach c → ∀ q, P c = some q → ∀ k (hk : k < q.d.shape.insts.length),
    MemDec q k (q.d.shape.insts[k]).1 ∨ ∃ q', P (q.d.shape.insts[k]).1 = some q' ∧ CallDec q q' k
  /-- Static call closure of `Reach` (its match with the translator's actual child calls is G-REACH). -/
  closed : ∀ c, Reach c → ∀ q, P c = some q → ∀ k (hk : k < q.d.shape.insts.length),
    (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1
```

**served 証拠 ServedGP / Served1P / ServedP / ServedPC と G-SERVED**（GEN2_DEFS.lean.txt:214-266）

```lean
-- d0ddc50b:scripts/gen2/GEN2_DEFS.lean.txt:214-266
/-- `ServedRealGA` (ServedRealA.lean:45-58) with `RealChildA O` replaced by `Q`; every other part VERBATIM (the
`connsG` instance, the `machPorts` map of `outs`, `∃ e ∈ outs, e.1 = k`, the same `ids`/`cache`). -/
def ServedGP (Q : Name → Res → Prop) (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  shape.instFields ≠ [] →
  ∀ k (hk : k < shape.insts.length) (mc : Sparkle.IR.AST.Module) (iname : String)
    (argWs : List String) (outs : List (Nat × String)) (outWs : List String),
    Stmt.inst mc.name iname (Tools.ShippingMachineLinkedT.connsG mc argWs outs outWs) ∈ m.body →
    outs.mapM (fun (j, _) =>
      ((machPorts declName ids cache shape.binders).map (·.name))[machNIn shape + j]?) = some outWs →
    (∃ e ∈ outs, e.1 = k) →
    moduleByName dsn.modules mc.name = some mc →
    (∃ md, (shape.instOrigins.getD k .ord).child? = some md ∧ mc = md.1) ∨
      ∃ Dc, Q (shape.insts[k]).1 (mc, Dc) ∧ ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g

/-- `ServedReal1A` (ServedRealA.lean:60-72) with `RealChildA O` replaced by `Q`; every other part VERBATIM
(`CallStmt … k args mc st`). -/
def Served1P (Q : Name → Res → Prop) (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  shape.instFields = [] →
  ∀ k (hk : k < shape.insts.length) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
    (shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
    Tools.ShippingMachineInst.CallStmt (machNIn shape) shape.insts.length shape.layout.slots.length
      ((machPorts declName ids cache shape.binders).map (·.name)) k args mc st →
    moduleByName dsn.modules mc.name = some mc →
    (∃ md, (shape.instOrigins.getD k .ord).child? = some md ∧ mc = md.1) ∨
      ∃ Dc, Q (shape.insts[k]).1 (mc, Dc) ∧ ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g

def ServedP (Q : Name → Res → Prop) (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  ServedGP Q declName shape m dsn ids cache ∧ Served1P Q declName shape m dsn ids cache

/-- **G-SERVED**: the existing producer of `MachineTraceLBX (ServedRealA O …)` (`genTrace` on the run,
QuadComposed.lean:156, through `synthesizeCombinationalCore_machine_soundRA_A`) generalised to
`X := ServedP (ShipsRes L P)`: in a run of a reached declaration from a `CacheShips` world, under both halves of the IH one level
deeper, the trace holds with every served non-memory instance shipping — THE `(mc, Dc)` of call `k`, with the same
`ids`/`cache` witness as the trace. (`CacheShips` at the end is `BodyKeepsInv`'s, not this statement's.) -/
def ServedShipsStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
    (raw : Sparkle.IR.AST.Module) (D : Design),
    Reach p.decl → P p.decl = some p → AdmCtx L.O.quiet mctx cctx → InvAt L P Reach (dv w) w →
    IHAt L P Reach (dv w + 1) → ChildKeepsInv L P Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w' →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
        p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc

/-- `PC` for consumer 2 from the served evidence (the right disjunct of `ServedGP`): the module is in the design and is
served to call `k`'s callee by a `Q` result whose modules are in the design. -/
def ServedPC (Q : Name → Res → Prop) (dsn : Design) : Name → Sparkle.IR.AST.Module → Prop :=
  fun c mc => moduleByName dsn.modules mc.name = some mc ∧
    ∃ Dc, Q c (mc, Dc) ∧ ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g
```

**TopShips と一段規則群（S 系）**（GEN2_DEFS.lean.txt:270-355）。`TopShips` は d0ddc50b 時点の旧形（`rst`/`clk` 前提が無条件）。R-G 版は §2.3。

```lean
-- d0ddc50b:scripts/gen2/GEN2_DEFS.lean.txt:270-355
/-- The top-level conclusion for package `p` at height `n`: exactly the conclusion of
`machine_ships_hierC_noHstR` (Srm33Core.lean:85-114) with `d := p.d`, `src := p.src`, `ext := p.extS`,
`extB := p.extBS`, `kD := p.kD`. -/
def TopShips (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- **The one-level rule** (M2-b): a machine-route run (route evidence `MachineTaken`) of `p.decl` whose every entry
is a memory call with `MemDec` or an ordinary call with `CallDec`, and whose trace has every served non-memory
instance shipping (`ServedP (ShipsRes L P)`, the output of G-SERVED, k ↔ instance kept), ships at the top and as a
child at some height (one more than the children's, after G-LIFT). -/
def StepStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    P p.decl = some p → DataOk p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    ∃ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D

/-- **First proof unit** (M2-a, `memParent_ships`): every entry a memory call. No served-children premise: the
trace with `ServedRealA` comes from `genTrace` on the run. Route evidence: the premise `MachineTaken`; for this case
it is also derivable from `memCallee_closesA` (Srm3Callee.lean:91) + `machineRunJQC_of_closesA` (ServedRealA.lean:97)
when `DataOk` contains `MemCalleeData`'s rows — a corollary, recorded, not a replacement of the premise. -/
def MemParentStmt {mref cref} (L : Laws mref cref) (DataOk : Pkg ι dom → Prop) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    DataOk p → p.d.shape.layout.slots ≠ [] → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) →
    ∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D

/-- **Base case** (M2-a', a separate unit): an ordinary leaf (`insts = []`) ships at every height. -/
def LeafStmt {mref cref} (L : Laws mref cref) (DataOk : Pkg ι dom → Prop) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    DataOk p → p.d.shape.insts = [] → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    ∀ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D

/-- **T1** (M3): every successful outermost compilation of a reached declaration ships, under `T1Hyp` (G3 per
reached declaration, the route-3 scope `closes`, the decodings, the static call closure). The route evidence of
each run is derived from `T1Hyp.defines`/`closes` (`machineRunJQC_of_closesA`); G-REACH, G-SERVED, G-CACHE and
G-MEMO are lemmas of its proof. -/
def T1Stmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (c : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld) (raw b : Sparkle.IR.AST.Module) (D : Design),
    Reach c → Start L mctx cctx w →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    ∃ q n, P c = some q ∧ TopShips q n c b raw D
```

### 2.3 par/gen2-spec の後で kjob/g2tc-s2 が Defs に入れた 2 つの変更（FG の骨組みが変わる箇所）

d0ddc50b の `Tools/ShippingGen2Defs.lean` と kjob/g2tc-s2@fa84af5d の差分は次の 2 つだけ（`git diff d0ddc50b fa84af5d -- Tools/ShippingGen2Defs.lean` で確認）。kjob/g2tc-s2@fa84af5d の Defs は GEN2_DEFS.lean.txt と cmp 一致（履歴 seq 3430, 3488 の note）。

(a) `InstClosed` と `ShipsRes` の 3 つ目の連言（S1 統合 = sparkle-gen3 側 → T1 台帳を参照）:

```lean
-- fa84af5d:Tools/ShippingGen2Defs.lean:131-143
    (c : Name) (shape : MachineShape) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  MachineRunJQC L.O mctx cctx n c shape raw D

/-- **Incoming-edge instance closure of a result** (G-POST, scripts/gen2/GPOST_FREEZE.md §2): every module of the
result's design is instantiated (by name) in the body of the result's top or of some module of its design. -/
def InstClosed (r : Res) : Prop :=
  ∀ g ∈ r.2.modules, ∃ h ∈ r.1 :: r.2.modules, ∃ (i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
    Sparkle.IR.AST.Stmt.inst g.name i cs ∈ h.body

/-- A result `r` of `c` with the package and height it ships at, and instance-closed (GPOST_FREEZE §2: `InstClosed`
is the THIRD conjunct, so `h.1` and `h.2.1` keep the former two parts). -/
def ShipsRes {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ (∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2) ∧ InstClosed r
```

(b) `TopShips`（R-G: `rst`/`clk` の前提を b の入力に含まれるときだけ要求）— sparkle-gen2-top-contract の成果:

```lean
-- fa84af5d:Tools/ShippingGen2Defs.lean:277-311
/-- The top-level conclusion for package `p` at height `n`: the conclusion of
`machine_ships_hierC_noHstR` (Srm33Core.lean:85-114) with `d := p.d`, `src := p.src`, `ext := p.extS`,
`extB := p.extBS`, `kD := p.kD`, and with the `rst` and `clk` premises required only when they are inputs of `b`
(scripts/gen2/TOP_CONTRACT_REVISION.md §2 R-G): with both inputs it is the old contract (L2 there); with neither
it is `TopShipsNC` (L3/L4 there). -/
def TopShips (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      ("rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0) →
      ("clk" ∈ b.inputs.map (·.name) → ∀ t, ins t "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- **The one-level rule** (M2-b): a machine-route run (route evidence `MachineTaken`) of `p.decl` whose every entry
is a memory call with `MemDec` or an ordinary call with `CallDec`, and whose trace has every served non-memory
instance shipping (`ServedP (ShipsRes L P)`, the output of G-SERVED, k ↔ instance kept), ships at the top and as a
child at some height (one more than the children's, after G-LIFT). -/
def StepStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
```

### 2.4 FG の骨組みと台帳ブロックの対応（索引）

FG の ∀/→ binder → 台帳ブロックの索引。

| FG/T1 の binder | 台帳ブロック（§3） |
|---|---|
| F1 `L : Laws` | P-01 |
| F3 `Start`（`AdmCtx`、`JQC … 0 w`） | P-02, P-03 |
| F4 `RunsTo`（core run） | P-04 |
| F6 の `(b, raw)` 関係（後処理） | P-05 |
| F5 `ReflectsAll` / T `defines` | P-06 |
| T `closes`（→ `MachineTaken`） | P-07 |
| T `pkg`（`P c = some q ∧ q.decl = c ∧ DataOk q`） | P-08, P-09, P-10, P-11, P-12, P-13 |
| T `dec`（`MemDec ∨ CallDec`） | P-16, P-17, P-18, P-19, P-21 |
| T `closed` / G-REACH | T1 台帳を参照 |
| I 系（`ShipsRes`、`CacheShips`、`InvAt`、`IHAt`、`KeepChild`、`ServedShips`） | P-22, P-24 → T1 台帳を参照 |
| S 系（`StepStmt`、`MemParentStmt`、`LeafStmt` の case 前提・追加前提） | P-14, P-15, P-20, P-23, P-25, P-26 |
| `TopShips` の結論内の実行前件 / 具体 run の存在 | P-27, P-28 |


## 3. 前提ブロック（承認済み定理で binder として残っているもの）

読み方:
- 「定理」欄は `名前 (path:行 @branch@SHA)`。branch は par/gen2-spec（d0ddc50b の祖先）、kjob/g2st-r3（96ac6add）、kjob/g2st-r5（2be39bc4）、kjob/g2tc-s2（fa84af5d）、kjob/g2tc-ptop12/14/16/19/21（0ab11f69 / 8136d9dc / ddb492f0 / c5c37d2b / 22862066）。
- 同じ前提が複数の定理に現れるため、1 前提 = 1 ブロックに束ねた（定理側は一覧）。
- 注意（型名のずれ）: par/gen2-spec では loop-pkg（94ed8609）で `SrcPkg` → `Pkg` に機械的に置換された。U0（6bd02a3a）・calldec（5c1b78a1）・uadapt（121c09fe）・step-mem（f1a4367f）の定理は当時 `SrcPkg` 版。loop-pkg の PkgCompat（g2lp-45c937c1）が `.gen` での rfl / new→old を確認している（LOOPPKG_RESULT.md「Compatibility」）。
- 注意（CallDec の版）: calldec / uadapt の定理は CallDec の旧版（名前連言 `o.name = instFields.getD k ""`）。callfield（3b702f15）で `CallField` を入れた版に変わり、`callDec_of_callFactF` / `callDec_of_hPointAt_at` / `seqFactsRN_of_callDec` は `hG : instFields ≠ []` を取る版になった（CALLFIELD_RESULT.md「Group compatibility」）。

### P-01 Laws（実行時法則 G5）
- **Lean名（binder名）**: `L : Laws mref cref`（フィールド `L.O : RefLawsAOps MkRefd mref cref`、`L.T : RefLawsATele L.O.quiet mref cref`）。旧 Tools では `O` / `T` / `RefLawsA…` として別々の binder。
- **完全な型**: §2.2（`Laws`、`RefLawsAOps`、`RefLawsATele` の原文）。定義元 = scripts/gen2/GEN2_DEFS.lean.txt:45-48（= Tools/ShippingGen2Defs.lean）と Tools/ShippingChildInvA.lean:259-334 @par/gen2-spec@d0ddc50b。
- **仮定している定理**: 本グループの全 root。例: keepBody (Tools/ShippingGen2Keep.lean:54 @par/gen2-spec@6bd02a3a)、memParent_ships (Tools/ShippingGen2MemShips.lean:87 @par/gen2-spec@94ed8609)、leaf_ships (Tools/ShippingGen2Leaf.lean:271 @par/gen2-spec@d9fac18c)、slotlessLeaf_ships (Tools/ShippingGen2SlotlessLeaf.lean:438 @par/gen2-spec@22417406)、oneOut_topShips (Tools/ShippingGen2OneOutTop.lean:340 @par/gen2-spec@93e9994c)、group_childShips (Tools/ShippingGen2GroupServed.lean:294 @par/gen2-spec@d603ac07)、stepStmtCases_of_rows (Tools/ShippingGen2StepDispatch.lean:63 @kjob/g2st-r3@96ac6add)、ptop_pbh_ofEx (Tests/Gen2/TopPbhRunEx.lean:47 @kjob/g2tc-ptop19@c5c37d2b)。
- **FG/T1 のどの binder に効くか**: F1（`∀ L : Laws`）。T1Stmt / StepStmt も `L` を取る。
- **別名・別Issueでの現れ**: `O` と `T`（genTrace、core_* 系）、`RefLawsA`、`L.O.quiet`。
- **支払い予定のIssue**: GENERAL_SPEC.md §5 M5「G5: a model of `Laws`, or an explicit TRUSTED status」。Issue 割当は履歴に書かれていない。Issue タイトル上は sparkle-gen5-boundary-audit（M5：実行モデル・名前・IR以降の境界を最終監査）が近い（タイトルのみ）。
- **実runから払えそうか**: いいえ（run から払う対象ではない。一様な法則）。履歴上の事実: `Laws` の値を 1 つ構成する経路は確認済み（Tests/Gen2/TopLawsQF.lean:33 `lawsQuietFalse` @kjob/g2tc-ptop21@22862066: `RefLawsAOps.quietFalse` / `RefLawsATele.quietFalse`）。ただしその L では `PbhRunEx` は偽（`not_pbhRunEx_lawsQuietFalse`、`pbhRunEx_quiet` は `∃ w, L.O.quiet w` を要求）。非空虚な `Laws` 値は**この調査では見つからなかった**（履歴 seq 5357, 5527: 「他の Laws の不存在・一意性は主張しない」）。
- **分類**: TRUSTED境界（候補）。GENERAL_SPEC §5 は「model または明示 TRUSTED」と書くのみで、確定した TRUSTED 宣言はこの調査では見つからなかった。未供給の義務としても扱われる。

### P-02 AdmCtx（許容コンテキスト）
- **Lean名**: `hA : AdmCtx L.O.quiet mctx cctx`。
- **完全な型**: §2.2 の `AdmCtx`（Tools/ShippingChildInvA.lean:73-79 @par/gen2-spec@d0ddc50b）。
- **仮定している定理**: keepBody の内側（`BodyKeepsInv` の `AdmCtx L.O.quiet mctx cctx → …`、GEN2_DEFS.lean.txt:167-172）、memParent_ships (MemShips.lean:87 @94ed8609)、leaf_ships (Leaf.lean:271 @d9fac18c)、slotlessLeaf_ships (SlotlessLeaf.lean:438 @22417406)、oneOut_composedNW / oneOut_childShips (OneOut.lean:260/288 @99f0de5d)、oneOut_topShips (OneOutTop.lean:340 @93e9994c)、oneOut_topShipsO (OneOutTopO.lean:334 @d0ef6371)、group_childShips (GroupServed.lean:294 @d603ac07)、oneOutSl_childShips / groupSl_childShips (SlotlessParentRun.lean:289/338 @36342cb8)、oneOutSl_topShipsNC (SlotlessTop.lean:447 @36342cb8)、slotlessLeaf_topShipsNC (TopNC.lean:306 @36342cb8)、StepStmtCases (StepDispatch.lean:48 @kjob/g2st-r3@96ac6add)、ptop_ofSlotlessRun (TopSupply7.lean:31 @kjob/g2tc-ptop14@8136d9dc)。
- **FG/T1 のどの binder に効くか**: F3 `Start` の第 1 連言。内側の run では GENERAL_SPEC §1.2 の通り「`AdmCtx` と `JQC L.O (dv w) w` を induction data として運ぶ」（T1Hyp.defines / closes も `AdmCtx` の下で ∀）。
- **別名**: `hA`、`AdmCtx O.quiet mctx cctx`（O 直渡しの旧 lemma）。
- **支払い予定のIssue**: 最外は FG の Start 前提として残る。内側の run は T1 台帳を参照。
- **実runから払えそうか**: 不明。`AdmCtx` は `mctx.canUnfold?` が inert という文脈条件で、run から導出する補題はこの調査では見つからなかった。
- **分類**: 入力条件（Start）。

### P-03 JQC（深さ付きキャッシュ不変量）
- **Lean名**: `hjqc : JQC L.O (dv w) w`（MemParentStmt' 等）。FG の Start は `JQC L.O 0 w`。
- **完全な型**: §2.2 の `JQC`（Tools/ShippingChildCacheA.lean:117-122 @par/gen2-spec@d0ddc50b）。`JQC O D w := JQ O.quiet D w ∧ CacheInvA O (cv w)`。
- **仮定している定理**: memParent_ships (MemShips.lean:87 @94ed8609)、leaf_ships (Leaf.lean:271 @d9fac18c; 本文では未使用 binder、LEAF_RESULT.md)、slotlessLeaf_ships (SlotlessLeaf.lean:438 @22417406)、StepStmtCases (StepDispatch.lean:48 @96ac6add)、ptop_ofSlotlessRun (TopSupply7.lean:31 @8136d9dc)、PbhRunAt（TopPbhRunEx.lean:33 @c5c37d2b）。oneOut_* 系の root は `JQC` を binder に持たず `ran : MachineTaken … (dv w + 1) …` と `hA` から進む（シグネチャで確認）。
- **FG/T1 のどの binder に効くか**: F3 `Start` の第 2 連言（最外 `dv w = 0`）。内側は `InvAt L P Reach D w := JQC L.O D w ∧ CacheShips …`（I 系）。
- **別名**: `InvAt` の第 1 連言、`JQC O n w9`（`MachineRunJQC` の内部）。
- **支払い予定のIssue**: 最外は Start。内側（InvAt / G-START: depth 0 でコアが sparkleChildCache を消す）は T1 台帳を参照。
- **実runから払えそうか**: 不明（上記 G-START は GENERAL_SPEC §3.2 の T1 側の義務）。
- **分類**: 入力条件（Start）。

### P-04 core run（RunsTo）
- **Lean名**: `hcore` / `hrun` : `RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1`。
- **完全な型**: GEN2_DEFS.lean.txt:300-313（StepStmt）などの前件。`RunsTo` は Tools.ShippingEntrySoundness.RunsTo。
- **仮定している定理**: memParent_ships / leaf_ships / slotlessLeaf_ships（前件）、oneOut_topShips（`hcore`）、oneOutSl_topShipsNC（`hcore`）、stepStmtCases_of_rows、ptop_ofSlotlessRun（`hrun`）、PbhRunAt。
- **FG/T1 のどの binder に効くか**: F4（FG の `RunsTo (synthesizeCombinational declName) …`）。FG/T1Stmt は `synthesizeCombinationalCore c [] false` の run を使い、T1Stmt の前件にも同じ形がある（GEN2_DEFS.lean.txt:350-352）。FG の entry run → core run の橋は**この調査では見つからなかった**（GENERAL_SPEC §1.1 の「(b, raw) は entry の後処理で関係づく」を M4 に置くのみ）。
- **別名**: `hr`（machine_children_realA' 等の旧 lemma）。
- **支払い予定のIssue**: FG の入力そのもの。entry→core の橋は M4（sparkle-gen4-fg-assembly: タイトルのみ「全成功経路をFGの単一定理へ組み立てる」）。
- **実runから払えそうか**: 入力そのもの（払う対象ではない）。
- **分類**: 入力条件。

### P-05 hpost（b と raw の後処理関係）
- **Lean名**: `hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)`。
- **完全な型**: 上記の通り（GEN2_DEFS.lean.txt:305-306, 324-325, 337-338）。
- **仮定している定理**: memParent_ships、leaf_ships、slotlessLeaf_ships、oneOut_childShips、oneOut_topShips、group_childShips、oneOutSl_*、slotlessLeaf_topShipsNC、StepStmtCases、ptop_ofSlotlessRun（各 SHA は P-02 の一覧と同じ）。
- **FG/T1 のどの binder に効くか**: F6 の「(b, raw) related by the entry's post-processing」（GENERAL_SPEC §1.1）。T1Stmt の前件（GEN2_DEFS.lean.txt:353-354）。
- **別名**: `hpost`。
- **支払い予定のIssue**: GENERAL_SPEC §1.1 は「`b ↔ raw` of the default entry's two post-processing steps」を M4 で固定すると書く。本グループの履歴に Issue の割当はない。
- **実runから払えそうか**: 不明。entry の 2 つの後処理が 2 択の disjunction になることを示す補題はこの調査では見つからなかった。
- **分類**: 入力条件（M4 で固定される関係）。

### P-06 MachineDefines（shape 反映 G3-SHAPE）
- **Lean名**: `entry` / `hdef` : `MachineDefines mctx mref cctx cref p.decl p.d.shape`。T1Hyp.defines は「全 admissible context で」。
- **完全な型**: §2.2（Tools/ShippingMachineEntry.lean:2340-2353 @par/gen2-spec@d0ddc50b）。
- **仮定している定理**: memParent_ships / leaf_ships（本文で未使用 binder）/ slotlessLeaf_ships、oneOut_topShips（`entry`）、oneOutSl_topShipsNC（`entry`）、stepStmtCases_of_rows、ptop_ofSlotlessRun（`hdef`）、PbhRunAt、machine_ships_hierC_run (Tools/ShippingGen2FitChain.lean:1073 @c6951eb8)。
- **FG/T1 のどの binder に効くか**: F5（`ReflectsAll`）と T `defines`。
- **別名**: `entry`、`MachineDefines`（SrcPkg 版と Pkg 版で shape 引数の出所が違うだけ）。
- **支払い予定のIssue**: GENERAL_SPEC §5 M5 G3-SHAPE（reader soundness: `readTerm_sound`、`readTerm_quote`、`driveShape_complete`）。Issue タイトル上は sparkle-gen5-reader-bridge（M5：production readerからMachineDefines/GateDefinesを接続）（タイトルのみ）。
- **実runから払えそうか**: 不明。GENERAL_SPEC §5 の M5 Risk に「`partial` production reader の G3-SHAPE は fuel-total reader を production に入れる必要があるかもしれない（user decision）」とある。
- **分類**: 未供給の義務。

### P-07 MachineTaken（route 証拠）と MachineClosesAtA
- **Lean名**: `ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D`（= `MachineRunJQC L.O …`）。T1Hyp.closes: `MachineClosesAtA L.O mctx cctx c q.d.shape`。
- **完全な型**: §2.2（GEN2_DEFS.lean.txt:127-132; Tools/ShippingServedRealA.lean:89-95; Tools/ShippingChildRunAKids.lean:155-161）。
- **仮定している定理**: memParent_ships、leaf_ships、slotlessLeaf_ships、oneOut_composedNW / oneOut_childShips / oneOut_topShips、group_childShips、oneOutSl_*、slotlessLeaf_topShipsNC、StepStmtCases、ptop_ofSlotlessRun（`ran`）。T1Hyp.closes は GEN2_DEFS.lean.txt:205-206。
- **FG/T1 のどの binder に効くか**: T `closes`（GENERAL_SPEC §3.2: 「route evidence は `T1Hyp.defines` + `T1Hyp.closes` から `machineRunJQC_of_closesA` (ServedRealA.lean:97) で得る」）。FG には直接の binder がない（T1Hyp 経由）。
- **別名**: `MachineRunJQC`、`MachineRanA`（core_* 系: core_instOutWidthsOk_oneA 等、Tools/ShippingGen2OneOutTop.lean:198 @93e9994c）、旧 `MachineClosesAt`。
- **支払い予定のIssue**: G-CLOSES。GEN2_DEFS.lean.txt:201-204 のコメント: 「memory callee は `memCallee_closesA`（Srm3Callee.lean:91）、一般には `closes_of_data`（Tools/ShippingMachineClosesData.lean）から導出。閉じない宣言は route 4（M4）」。G-CLOSES-FRESH（`outHead`/`hfresh`）は「M3/M4 with T1Hyp.closes; OPEN」（GENERAL_SPEC §4.3）。Issue 名は履歴にない（M3 側は T1 台帳を参照）。
- **実runから払えそうか**: 条件付きで「はい」: `machineRunJQC_of_closesA`（Tools/ShippingServedRealA.lean:97）が `MachineClosesAtA` + `MachineDefines` + `JQ` から `MachineTaken` を与える。`MachineClosesAtA` 自体の一般供給は**この調査では見つからなかった**。PKG_COMB_RESULT.md は「`MachineClosesAtA` for comb names」を open と記す。
- **分類**: 未供給の義務（T1Hyp.closes）。

### P-08 パッケージの存在と生成事実（G3-GEN / G3-DECL）
- **Lean名**: `hP : P c = some q`、`P p.decl = some p`、StepStmt の `P p.decl = some p`、T1Hyp.pkg: `∃ q, P c = some q ∧ q.decl = c ∧ DataOk q`。値としての `p : Pkg ι dom`（フィールド `gen : GenFacts …` / `facts : LoopFacts …` / `facts : CombFacts …`）。
- **完全な型**: §2.2（`Pkg`、`SrcPkg`、`GenFacts`、`LoopFacts`、`SrcPkgL`、`CombFacts`、`CombPkg`）。
- **仮定している定理**: `P` を取るもの: seqFactsRN_of_callDec (Tools/ShippingGen2Connect.lean:107 @6bd02a3a)、callDec_of_callFactF (Tools/ShippingGen2CallDec.lean:58 @5c1b78a1)、callDec_of_hPointAt_at (Tools/ShippingGen2Adapt.lean:166 @121c09fe)、callDec_of_hPointG_at (Tools/ShippingGen2CallField.lean:131 @3b702f15)、oneOut_* (OneOut.lean @99f0de5d)、StepStmtCases。`p : Pkg` を値として取るもの: 上の全 Pkg 版定理。
- **FG/T1 のどの binder に効くか**: T `pkg`（G3-GEN: 到達宣言ごとの package）と GenFacts の各フィールド（`ok`, `body_eq`, `init`, `writes`, `result`, `source`, `causal`）。G3-DECL（package の body が宣言の意味）は GENERAL_SPEC §5 で「meta-level fact, generated per declaration today」。
- **別名**: `SrcPkg`（旧、loop-pkg で `Pkg.gen`）、`Pkg.loop` (`SrcPkgL`)、`Pkg.comb` (`CombPkg`、PKG_COMB_RESULT.md)。`GenFacts`/`LoopFacts`/`CombFacts` は同じ観点の 3 版。
- **支払い予定のIssue**: GENERAL_SPEC §5 M5 G3-GEN（生成器の健全性）/ G3-DECL。Issue タイトル上は sparkle-gen5-package-coverage（成功生成すべてへのpackage存在・生成事実を証明）と sparkle-gen5-decl-bridge（生成packageと元宣言の意味を同一視する）（タイトルのみ）。
- **実runから払えそうか**: いいえ（現状）。GenFacts の注記: 「NOT derived generically」（Tools/ShippingQuadComposed.lean:102-105）。実在 instance は宣言ごとに生成された `X.machine_*` で供給: leafM（lm_ships）、quantModule（q_ships: `quant_facts` + `quant_hcausal`）、topshare2（tm2_callDec）、leaf16（leaf16_ships）、pickByteH（pbh_ships、`.comb pbhC`）。LOOPPKG_RESULT.md: 「`machine_source` が生成 loop に結び付くこと自体、quantModule 自身の意味かどうかは G3-DECL by construction で、kernel では導出していない」。
- **分類**: 未供給の義務（G3-GEN、G3-DECL）。

### P-09 DataOkB の行（U0 の具体 DataOk）と callDec 系の `hok` / `hco` / `hslots`
- **Lean名**: `DataOk p`（`DataOkB p = true`）。行: `p.d.ok`、`p.d.letsAliasOk`、`p.d.callsOk p.kD`、`ss.length = slots.length`、`outTy`、`outHead`。callDec 系の binder は個別: `hok : p.d.ok = true`、`hco : p.d.callsOk p.kD = true`、`hslots : p.d.ss.length = p.d.shape.layout.slots.length`。
- **完全な型**:

```lean
-- 6bd02a3a:Tools/ShippingGen2Data.lean:17-21
def DataOkB (p : SrcPkg ι dom) : Bool :=
  p.d.ok && p.d.letsAliasOk && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.name.toList.head? ≠ some 'i')
```

  `DataOk` は `DataOkB p = true`（同ファイル:23）。`p.d.callsOk`（Tools/ShippingCallsShape.lean:106 @d0ddc50b）と `letsAliasOk`（Tools/ShippingMachineClosesData.lean:157）と `ok`（Tools/ShippingMachineAuto.lean:217）は Bool 関数。定義元 = Tools/ShippingGen2Data.lean:17-23 @par/gen2-spec@6bd02a3a（`SrcPkg` 版）。
- **仮定している定理**: DataOkB を使う tmPkg_dataOk (Tests/Gen2/U0Check.lean @6bd02a3a)、callDec_of_callFactF (CallDec.lean:58 @5c1b78a1) と call_inRange_at / callDec_of_hPointAt_at (Adapt.lean:106/166 @121c09fe) と callDec_of_hPointG_at (CallField.lean:131 @3b702f15) の `hok` `hco` `hslots`。
- **FG/T1 のどの binder に効くか**: T1Hyp の `DataOk` placeholder（T `pkg` の `DataOk q`）。GENERAL_SPEC §4.4 の行分類（E / R? / CASE / D）。
- **別名**: `MemParentDataOk`（P-10）、`LeafDataOk`（P-11）。STEP_ROUTE_FREEZE.md §7 row 6（kjob/g2st-r3@96ac6add）: 「`DataOkB`（SrcPkg 上）から `MemParentDataOk` / `ExtInS` / `hord` / `OneOutWidth`（Pkg 上）への補題も逆向きも**見つからなかった**。含意の有無は調べていない」。
- **支払い予定のIssue**: G-DATA coverage（GENERAL_SPEC §4.3: M2 per check）— Issue 名は履歴に書かれていない。`outHead` は N1 name lemma 置換が U0 approved note の義務（seq 2138）。
- **実runから払えそうか**: 行ごとに異なる（`outHead` は「いいえ（被覆リスクあり）」、`outNameOk` 部分は run から導出可、他は不明）。U0_RESULT.md（0939cfb6）: `outNameOk` は compiler が検査する（Elab.lean:5084）ので run から導出可能（E + derivable）。`letsAliasOk` / `callsOk kD` は `Sparkle/` に現れず compiler は検査しない（D）。`outHead`（出力名が `i` で始まらない）は「A real design with an output named `i…` violates it」（U0_RESULT.md）。`ss.length = slots.length` / `outTy` は `d.ok` から出る候補だが未証明（D）。
- **分類**: 入力条件（decidable row）。coverage は未供給の義務（`outHead` は被覆リスクあり）。

### P-10 MemParentDataOk（5 行）
- **Lean名**: `hdata : MemParentDataOk p`。
- **完全な型**:

```lean
-- 94ed8609:Tools/ShippingGen2MemParent.lean:38-44
def MemParentDataOkB (p : Pkg ι dom) : Bool :=
  p.d.ok && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width) &&
  decide (∀ b ∈ p.d.shape.binders.drop p.kD, b.2 ≠ .domain)

def MemParentDataOk (p : Pkg ι dom) : Prop := MemParentDataOkB p = true
```

  定義元 = Tools/ShippingGen2MemParent.lean:38-44 @par/gen2-spec@94ed8609（Pkg 版。f1a4367f では `SrcPkg` 版で行は同じ）。
- **仮定している定理**: memParent_ships (MemShips.lean:87 @94ed8609)、memParent_topShips (MemTop.lean:45 @f1a4367f)、oneOut_composedNW / oneOut_childShips (OneOut.lean:260/288 @99f0de5d)、oneOut_topShips (OneOutTop.lean:340 @93e9994c)、oneOut_topShipsO (OneOutTopO.lean:334 @d0ef6371)、group_composedNW / group_childShips (GroupServed.lean:271/294 @d603ac07)、oneOutSl_childShips / groupSl_childShips / slotlessParent_noTouch_ofRun / oneOutSl_topShipsNC (@36342cb8)。
- **FG/T1 のどの binder に効くか**: T `pkg` の `DataOk q`（M2-a 用の具体化）。
- **別名**: DataOkB の部分集合に `binders.drop kD` の非 domain 行を足したもの（P-09 の行と重なる）。LeafDataOk は 4 行（`hdomB` 行なし）。
- **支払い予定のIssue**: coverage = G-DATA（MEMPARENT_RESULT.md: 「DATA (5 Bool rows; coverage open, G-DATA)」）。行の供給は data-supply（sparkle-gen3-data-supply: STEP_ROUTE_FREEZE.md §4）→ T1 台帳を参照。
- **実runから払えそうか**: 不明。instance 側は `decide`（lm_dataOk、q_dataOk）で供給されるが、成功 run ごとの被覆補題は**この調査では見つからなかった**。
- **分類**: 入力条件（decidable row）、coverage は未供給の義務。

### P-11 LeafDataOk（4 行）
- **Lean名**: `hdata : LeafDataOk p`。
- **完全な型**:

```lean
-- d9fac18c:Tools/ShippingGen2Leaf.lean:44-51
def LeafDataOkB (p : Pkg ι dom) : Bool :=
  p.d.ok && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)

def LeafDataOk (p : Pkg ι dom) : Prop := LeafDataOkB p = true

/-- **The register-leaf lemma**: `LeafStmt L LeafDataOk` with `ExtInS p` after the data premise and
```

  定義元 = Tools/ShippingGen2Leaf.lean:44-51 @par/gen2-spec@d9fac18c。
- **仮定している定理**: leaf_ships (Leaf.lean:271 @d9fac18c)、slotlessLeaf_ships (SlotlessLeaf.lean:438 @22417406)、slotlessLeaf_topShipsNC (TopNC.lean:306 @36342cb8)、ptop_ofSlotlessRun (TopSupply7.lean:31 @kjob/g2tc-ptop14@8136d9dc)、ptop_prem_ofRun (TopSupply6.lean:35 @kjob/g2tc-ptop12@0ab11f69; `LeafDataOk.rows` と `ss_nil_of_slotless` を使う)。
- **FG/T1 のどの binder に効くか**: T `pkg` の `DataOk q`（leaf 用の具体化）。
- **別名**: DataOkB / MemParentDataOk と行が重なる。
- **支払い予定のIssue**: LEAF_RESULT.md「No generic supply of `ExtInS`/`LeafDataOk` (M5 G3-GEN / G-DATA)」。Issue 名は履歴にない。
- **実runから払えそうか**: 不明。instance は `decide`（leaf16、pbhC: `pbh_ships` は data/case を decided）。
- **分類**: 入力条件（decidable row）、coverage は未供給の義務。

### P-12 ExtInS（package の入力延長が恒等）
- **Lean名**: `hext : ExtInS p`。
- **完全な型**:

```lean
-- 94ed8609:Tools/ShippingGen2MemParent.lean:46-50
def ExtInS (p : Pkg ι dom) : Prop :=
  (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (j : Nat), j < p.kD → p.extBS i bools bits j = bools j) ∧
  (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (j n' : Nat), j < p.kD → p.extS i bools bits j n' = bits j n')
```

  定義元 = Tools/ShippingGen2MemParent.lean:46-50 @par/gen2-spec@94ed8609。
- **仮定している定理**: memParent_ships (MemShips.lean:87 @94ed8609)、leaf_ships (Leaf.lean:271 @d9fac18c)、slotlessLeaf_ships (@22417406)、oneOut_childShips (OneOut.lean:288 @99f0de5d)、group_childShips (GroupServed.lean:294 @d603ac07)、oneOutSl_childShips / groupSl_childShips (@36342cb8)、ptop_ofSlotlessRun (@8136d9dc)。oneOut_composedNW と oneOut_topShips は `hext` を取らない（シグネチャで確認）。
- **FG/T1 のどの binder に効くか**: T `pkg`（G3-GEN の一部。`DataOk` 外の「generator-output functional equality」。MEMPARENT_RESULT.md の表で kind = 「generator-output functional equality (generic supply D-GEN/M5)」）。
- **別名**: `ExtInS`（A4/MemOrigin と別）。
- **支払い予定のIssue**: MEMPARENT_RESULT.md: 「generic supply D-GEN/M5」。G3GEN_CALL_PLAN.md §4: D-GEN は M5 first。D-GEN の設計 Issue は sparkle-gen5-dgen（done）。実供給 Issue は履歴に書かれていない（sparkle-gen5-package-coverage はタイトル上近いが未確認）。
- **実runから払えそうか**: 不明。instance は `rfl`（leaf16、pbhC）、`q_extInS`（`machineExtB` は入力族 = `rfl`、`machineExt` は `kD = 10` 以降で `extendBits`、split + `omega`）、`leafM_hext(B)`。一般供給の補題はこの調査では見つからなかった。
- **分類**: 未供給の義務。

### P-13 MemOrigin（memory 起源 + 宣言幅）
- **Lean名**: `hmo : MemOrigin p`（MemParentStmt' の第 3 前件）。
- **完全な型**:

```lean
-- 94ed8609:Tools/ShippingGen2MemParent.lean:52-56
def MemOrigin (p : Pkg ι dom) : Prop :=
  ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
    (originAt p.d.shape k).child? = some (memModule cb aw dw) ∧
    ((p.d.bsIn.drop p.kD)[k]?.map (·.2)) = some (.bits dw)

```

  定義元 = Tools/ShippingGen2MemParent.lean:52-56 @par/gen2-spec@94ed8609。
- **仮定している定理**: memParent_ships (@94ed8609)、pkg_memComposedNW (Tools/ShippingGen2MemParent.lean:75 @f1a4367f)。供給補題 `memOrigin_of_memDec`（Tools/ShippingGen2MemFacts.lean:51 @f1a4367f; `[Nonempty ι]` 付き）。
- **FG/T1 のどの binder に効くか**: T `dec` の memory 側（`MemDec` から導出）。StepStmt は MemDec ∨ CallDec を取るので MemOrigin は StepStmtCases が `memOrigin_of_memDec` で作る。
- **別名**: `memDec_origin_some [Nonempty ι]`（Tools/ShippingGen2StepCases.lean:22 @96ac6add）が対応。
- **支払い予定のIssue**: P-16（MemDec）と同じ。履歴 seq 2211: 「MemOrigin は宣言幅も主張するので、その否定は『memory でない entry』だけではない。幅不一致と empty-index の隅は coverage 義務」。
- **実runから払えそうか**: はい（`Nonempty ι` と P-16 の下で `memOrigin_of_memDec` が導出する）。empty ι では MemDec は空虚（STEP_ROUTE_FREEZE.md §1）。
- **分類**: 入力条件（case）。coverage は未供給の義務。

### P-14 case 前提（insts / instFields / slots / Nonempty ι / StepCaseOK）
- **Lean名**: `insts ≠ []` / `insts = []`、`instFields ≠ []` / `= []`、`layout.slots ≠ []` / `= []`、`[Nonempty ι]` / `¬ Nonempty ι`、`StepCaseOK p`。
- **完全な型**: 各定理の前件。`StepCaseOK` / `StepStmtCases`:

```lean
-- 96ac6add:Tools/ShippingGen2StepDispatch.lean:41-61
def StepCaseOK (p : Pkg ι dom) : Prop :=
  p.d.shape.insts = []                                                                                      -- L1, L2
  ∨ (p.d.shape.insts ≠ [] ∧ p.d.shape.instFields ≠ [] ∧ p.d.shape.layout.slots ≠ [] ∧
      ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1)                             -- M
  ∨ (p.d.shape.insts ≠ [] ∧ p.d.shape.instFields = [] ∧ p.d.shape.layout.slots ≠ [] ∧
      ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none)            -- O1

def StepStmtCases {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    P p.decl = some p → DataOk p → StepCaseOK p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    ∃ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D
```

  定義元 = Tools/ShippingGen2StepDispatch.lean:41-61 @kjob/g2st-r3@96ac6add。
- **仮定している定理**: MemParentStmt'（insts ≠ [] ∧ instFields ≠ [] ∧ slots ≠ []）— memParent_ships (@94ed8609)、LeafStmt'（insts = [] ∧ slots ≠ []）— leaf_ships (@d9fac18c)、SlotlessLeafStmt（slots = []）— slotlessLeaf_ships (@22417406)、oneOut_*（instFields = []）、group_*（instFields ≠ []）、oneOutSl_* / groupSl_*（slots = []）、StepStmtCases、memDec_origin_some / allCallDec_of_hord（`[Nonempty ι]`、Tools/ShippingGen2StepCases.lean:22/43 @96ac6add）、topShips_of_empty（`¬ Nonempty ι`、Tools/ShippingGen2StepEmpty.lean:20 @96ac6add）。
- **FG/T1 のどの binder に効くか**: FG / StepStmt（GEN2_DEFS.lean.txt:300-313）にこれらの case 前件は**ない**。StepStmt は全ケースを主張するので、case 前提は FG にない制限（GENERAL_SPEC §4.4: CASE = 「case split of the plan, not a data obligation」）。StepStmtCases は 3 形（leaf / memory / one-output）に絞っている。
- **別名**: `hins`、`hfe`、`hsimple`、`hsl`、`hsl0`、`hnoI`。
- **支払い予定のIssue**: 被覆は sparkle-gen2-step の未了部分。STEP_ROUTE_FREEZE.md §2 の case 表（kjob/g2st-r3@96ac6add）が「供給元なし」と記す行: G1/G0（instFields ≠ [] の ordinary/mixed、slots ≠ [] / = []）の `TopShips`（「none」）、O0 case S（`rst ∈ b.inputs`）の C5S `oneOutSl_topShipsS`（「not found」）、X（instFields = [] の closing 内の memory call: 「closing を located できなかった」）、D4（one-output slotless の実 Pkg: 「supplier or route 見つからず」）。
- **実runから払えそうか**: いいえ（現在）。上の行は未供給。
- **分類**: 入力条件（case 制限）。被覆は未供給の義務。

### P-15 hrst（rst が b の入力でない）と hnoRst / hnoClk
- **Lean名**: `hrst : "rst" ∉ raw.inputs.map (·.name)`。`ptop_inst` では `hnoRst : "rst" ∉ b.inputs.map (·.name)`、`hnoClk : "clk" ∉ b.inputs.map (·.name)`。
- **完全な型**: oneOutSl_topShipsNC (Tools/ShippingGen2SlotlessTop.lean:447-468 @par/gen2-spec@36342cb8) の `hrst` binder、slotlessParent_noTouch_ofRun (Tools/ShippingGen2SlotlessParentRun.lean:106 @36342cb8)、ptop_inst (Tools/ShippingGen2TopCtrl.lean:46 @kjob/g2tc-ptop19@c5c37d2b)。
- **仮定している定理**: 上記 3 つ。
- **FG/T1 のどの binder に効くか**: R-G の `TopShips`（§2.3 (b)）で `rst`/`clk` の前提を b の入力に含まれるときだけ要求するため、含まれない場合の case C。FG の binder ではなく、一段規則の case 前提。
- **別名**: `hnoR`（TopNC の C4）。
- **支払い予定のIssue**: case S（`rst ∈ b.inputs`）は C5S が見つからない（P-14）。
- **実runから払えそうか**: S5_SLOTLESS_FREEZE.md: 「Reset absence comes from the module's actual inputs (`hrst`), never from a premise on children」。run から導出する補題はこの調査では見つからなかった。
- **分類**: 入力条件（case）。


### P-16 MemDec（memory 呼び出しの分解 G-MEMCALLS）
- **Lean名**: `hmd : ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1`（MemParentStmt'）、および `hdec` の左 disjunct `MemDec p k (p.d.shape.insts[k]).1 ∨ …`。
- **完全な型**: §2.2 の `MemDec`（GEN2_DEFS.lean.txt:114-118 @par/gen2-spec@d0ddc50b）。`MemDec p k c := ∀ i bools bits, MemFacts p.d.shape (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extS i bools bits) k c`。
- **仮定している定理**: memParent_ships (MemShips.lean:87 @94ed8609)、pkg_memComposedNW (MemParent.lean:75 @f1a4367f)、memFacts_of_memDec (Connect.lean:93 @6bd02a3a; 定義そのもの)、machine_linkedT_callsServed (Consumer.lean:30 @6bd02a3a; `hcalls` の左 disjunct `MemFacts …`)、group_composedNW / group_childShips (@d603ac07)、groupSl_childShips (@36342cb8)、StepStmtCases (@96ac6add)。
- **FG/T1 のどの binder に効くか**: T `dec` の左 disjunct。
- **別名**: `MemFacts`（Tools.ShippingMachineCallsLinkedT）、G-MEMCALLS。
- **支払い予定のIssue**: GENERAL_SPEC §4.3: G-MEMCALLS は「`MemDec` from the package; M2-a」。MEMPARENT_RESULT.md は「G-MEMCALLS (generator per declaration)」として open と記す。割当 Issue は本グループの履歴に書かれていない。
- **実runから払えそうか**: 不明。履歴上の供給は宣言ごとの kernel チェック: `leafM_memcalls`（lm_memDec）、`q_memDec`（quantModule: call 0 は `combo 4 16` 引数 [7,8,9,6]、call 1 は `sync 4 16` 引数 [6,28,3,29]、generator の `memTactic` の `rfl`/`decide`）(Tests/Gen2/QuantInstance.lean:105 @94ed8609)。run から MemDec を導出する補題は**この調査では見つからなかった**。
- **分類**: 未供給の義務。

### P-17 CallDec（ordinary 呼び出しの分解 G-CALLDEC）
- **Lean名**: `hdec : CallDec p q k`（seqFactsRN_of_callDec）、`hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k`（ordinary-only: oneOut_* 系）、`hdec : ∀ k hk, MemDec … ∨ ∃ q, P … = some q ∧ CallDec p q k`（group_* / StepStmtCases）。`hcalls`（machine_linkedT_callsServed）の `SeqFactsRN` 側。
- **完全な型**: §2.2 の `CallField`（GEN2_DEFS.lean.txt:92-96）と `CallDec`（:98-112）。定義元 = scripts/gen2/GEN2_DEFS.lean.txt @par/gen2-spec@d0ddc50b（= Tools/ShippingGen2Defs.lean、callfield 3b702f15 で名前連言を `CallField` に置換）。
- **仮定している定理**: seqFactsRN_of_callDec (Connect.lean:107 @6bd02a3a; :109 @1fdbc18d で `hseq` 追加、callfield で `hG` 追加)、machine_linkedT_callsServed (Consumer.lean:30 @6bd02a3a)、oneOut_composedNW / oneOut_childShips / machine_linked_callsServed1 (OneOut.lean:260/288/158 @99f0de5d)、machine_linked_callsServed1F (FitChain.lean:903 @c6951eb8)、oneOut_topShips (OneOutTop.lean:340 @93e9994c)、oneOut_topShipsO (OneOutTopO.lean:334 @d0ef6371)、group_composedNW / group_childShips (@d603ac07)、oneOutSl_* (@36342cb8)、allCallDec_of_hord (StepCases.lean:43 @96ac6add)、stepStmtCases_of_rows (@96ac6add)。
- **FG/T1 のどの binder に効くか**: T `dec` の右 disjunct（`∃ q', P (…).1 = some q' ∧ CallDec q q' k`）。StepStmt の `hdec` 前件（GEN2_DEFS.lean.txt:309-310）。
- **別名**: `CallDecOld`（c7948139 版、Tools/ShippingGen2CallField.lean @3b702f15）、`CallFactF`（QuadCalls）、`OneOutCall`（CallField.lean:164）、`SeqFactsRN` の 6 連言のうち run 以外（GENERAL_SPEC §4.2 の表）。
- **本Issue群で確定した事実（oneout-probe）**: 旧 `CallDec` の名前連言 `o.name = p.d.shape.instFields.getD k ""` は、parent `callerL`（instFields = []）と callee `pickByteH`（出力名 ["out"]）の組に対して満たせない: `oneout_name_mismatch`（Tests/Gen4/OneOutCallDecProbe.lean @par/gen4-gate@2dede972; decide, axiom propext）。承認 note: 「inhabited な index family のもとで成立、every G-ONEOUT parent ではない」。これが `CallField`（callfield 3b702f15）の動機。
- **支払い予定のIssue**: G-CALLDEC は generic には未供給（calldec seq 2155 done note: "UNSUPPLIED in general"）。分解は P-18 と P-19。M5 側は sparkle-gen5-gencall-proof（タイトル: 生成器からLetTie/CallOut/HPointAtを一般に供給）（タイトルのみ）。
- **実runから払えそうか**: 不明。GENERAL_SPEC §4.2: 「producer-export gap。generator か、reader の call term に対する新しい generic lemma が export しなければならない」。G3GEN_CALL_PLAN.md §3: run-local の経路 G-DATA-CALL を計画（未証明）。
- **分類**: 未供給の義務（G-CALLDEC）。

### P-18 HPointAt / HPointG / CallFactF（呼び出しごとの生成残差 G3-GEN-CALL）
- **Lean名**: `hH : HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k`（callDec_of_hPointAt_at）、`hH : HPointG P p q k`（callDec_of_hPointG_at）、`hF : CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i)`（callDec_of_callFactF）、`hH : ∀ k, k < p.d.shape.insts.length → HPointAt …`（callFactF_of_hPointAt_pkg）、`hFk`（hPointAt_of_callFactF_at）。
- **完全な型**:

```lean
-- d0ddc50b:Tools/ShippingQuadHPoint.lean:14-38
/-- **The residue of ONE call `k`** (one conjunct of the `hPoint` hypothesis of `callFactF_of_fam`). -/
def HPointAt (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig} (D : ι → DomainConfig)
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (outsC : Name → List OutField)
    (bsOf : Name → List (Name × MixedGateBinder))
    (src : (i : ι) → Name → (Nat → Signal (D i) Bool) → ((j : Nat) → (n : Nat) → Signal (D i) (BitVec n)) → List (Nat → Nat))
    (k : Nat) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hk : k < dP.shape.insts.length),
      ∃ (A : Nat → Signal (D i) Bool) (B : (j : Nat) → (n : Nat) → Signal (D i) (BitVec n)),
        boolsOf (D := D i) (bsOf (dP.shape.insts[k]).1)
          (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1) = A ∧
        bitsOf (D := D i) (bsOf (dP.shape.insts[k]).1)
          (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1) = B ∧
        ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
          (outsC (dP.shape.insts[k]).1)[k']? = some o ∧ o.name = dP.shape.instFields.getD k "" ∧
          (src i (dP.shape.insts[k]).1 A B)[k']? = some f ∧
          ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => ((extB i bools bits) p).val τ) (fun p n => ((ext i bools bits) p n).val τ)
            (nP + k) (((dP.bsIn.drop nP)[k]?.map (·.2)).getD .domain) = f τ
```

```lean
-- d0ddc50b:Tools/ShippingQuadCalls.lean:223-239
def CallFactF (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig}
    (lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (outsC : Name → List OutField)
    (S : ι → Name → (Nat → List Nat) → List (Nat → Nat)) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k : Nat) (hk : k < dP.shape.insts.length),
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
      (outsC (dP.shape.insts[k]).1)[k']? = some o ∧ o.name = dP.shape.instFields.getD k "" ∧
      (S i (dP.shape.insts[k]).1 (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => ((extB i bools bits) p).val τ) (fun p n => ((ext i bools bits) p n).val τ)
        (nP + k) (((dP.bsIn.drop nP)[k]?.map (·.2)).getD .domain) = f τ
```

```lean
-- 3b702f15:Tools/ShippingGen2CallField.lean:75-87
/-- `HPointAt` at the instantiation of the adapters (Adapt.lean:169), with the name conjunct replaced by
`CallField p q k o`. `q` is a parameter: the one-output branch of `CallField` reads `q.d.shape.layout.outs`. -/
def HPointG (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hk : k < p.d.shape.insts.length),
    ∃ (A : Nat → Signal (dom i) Bool) (B : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      boolsOf (D := dom i) (pkgBsC P (p.d.shape.insts[k]).1) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) = A ∧
      bitsOf (D := dom i) (pkgBsC P (p.d.shape.insts[k]).1) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]).2.1) = B ∧
      ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
        (pkgOutsC P (p.d.shape.insts[k]).1)[k']? = some o ∧ CallField p q k o ∧
        (pkgSrc P i (p.d.shape.insts[k]).1 A B)[k']? = some f ∧
        ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ
```

  定義元 = Tools/ShippingQuadHPoint.lean:14 / Tools/ShippingQuadCalls.lean:223 @par/gen2-spec@d0ddc50b（変更なし）、`HPointG` は Tools/ShippingGen2CallField.lean:75-87 @par/gen2-spec@3b702f15。
- **仮定している定理**: callDec_of_callFactF (Tools/ShippingGen2CallDec.lean:58 @5c1b78a1)、callFactF_of_hPointAt_pkg (:112 @5c1b78a1)、callDec_of_hPointAt_at (Tools/ShippingGen2Adapt.lean:166 @121c09fe)、hPointAt_of_callFactF_at (:196 @121c09fe)、callDec_of_hPointG_at (Tools/ShippingGen2CallField.lean:131 @3b702f15)。
- **FG/T1 のどの binder に効くか**: T `dec` の供給側（CallDec の内部: output relation）。T1Hyp.dec は不変、HPointAt は supplier decomposition のみ（calldec seq 2144, uadapt seq 2197）。
- **別名**: `CallOutG`（CallField.lean:90）、`gfHb*` / `gfHv*`（生成された `X.machine_composedNR2` の group facts）、`b_topshare2_hFP`（instance の供給者）、G3-GEN-CALL t1 / t2 / t3（G3GEN_CALL_PLAN.md §2.2）。
- **支払い予定のIssue**: G3GEN_CALL_PLAN.md §4: 「G3-GEN-CALL t1/t2/t3 — M5」。Issue タイトル上は sparkle-gen5-gencall-proof / sparkle-gen5-t2-tie / sparkle-gen5-dgen（タイトルのみ; 本グループは履歴本文を読んでいない）。
- **実runから払えそうか**: 不明。CALLDEC_PROBE_RESULT.md (iii): 「generic construction correctness / coverage: NOT proved。generator の call-term reading を `MachineShape` / `body_eq` 上の lemma にしたものは**見つからなかった**」。実在 instance は topshare2 のみ（`b_topshare2_hFP`、宣言ごとに生成）。失敗経路は G3GEN_CALL_PLAN.md §5 (a)/(b)/(c)。
- **分類**: 未供給の義務。

### P-19 呼び出し対 data（`callArgsOkAt` / arity、および global の `widths` `hargs` `hw` `hlen`）
- **Lean名**: `hargsK : callArgsOkAt p.d p.kD k q.portWidths = true`、`hlenK : (p.d.shape.insts[k]).2.1.length = q.ports.length`（pointwise 版）。global 版: `widths : Nat → List Nat`、`hargs : callArgsOk p.d p.kD widths = true`、`hw`、`hlen`。
- **完全な型**:

```lean
-- 121c09fe:Tools/ShippingGen2Adapt.lean:72-77
/-- The k-th slice of `callArgsOk` (Tools/ShippingPortsMatchRaw.lean:199), against a width list `ws`. -/
def callArgsOkAt (d : MachineData) (nDecl k : Nat) (ws : List Nat) : Bool :=
  (List.range ws.length).all fun j =>
    decide ((((d.shape.insts[k]?).bind fun c => c.2.1[j]?).bind fun a =>
      (d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]?).map
        fun bn => (kindTy bn.2).bitWidth) = ws[j]?)
```

```lean
-- 5c1b78a1:Tools/ShippingGen2CallDec.lean:58-70
theorem callDec_of_callFactF (P : Pkgs ι dom) (p q : SrcPkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hP : P (p.d.shape.insts[k]).1 = some q)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hF : CallFactF p.d p.kD p.lsrc p.extS p.extBS (pkgOutsC P) (fun i => pkgS P i))
    (hok : p.d.ok = true) (hco : p.d.callsOk p.kD = true)
    (hslots : p.d.ss.length = p.d.shape.layout.slots.length)
    (widths : Nat → List Nat) (hargs : callArgsOk p.d p.kD widths = true)
    (hw : ∀ (k : Nat) (hk : k < p.d.shape.insts.length), widths k =
      ((pkgBsC P (p.d.shape.insts[k]).1).filter fun b => b.2 != .domain).map fun b => (kindTy b.2).bitWidth)
    (hlen : ∀ (k : Nat) (hk : k < p.d.shape.insts.length), (p.d.shape.insts[k]).2.1.length =
      ((pkgBsC P (p.d.shape.insts[k]).1).filter fun b => b.2 != .domain).length) :
    CallDec p q k :=
```

  定義元 = Tools/ShippingGen2Adapt.lean:72-79 @par/gen2-spec@121c09fe と Tools/ShippingGen2CallDec.lean:58-70 @par/gen2-spec@5c1b78a1。
- **仮定している定理**: call_inRange_at (Adapt.lean:106)、callDec_of_hPointAt_at (:166) @121c09fe、callDec_of_hPointG_at (CallField.lean:131 @3b702f15)、callDec_of_callFactF (CallDec.lean:58 @5c1b78a1)。
- **FG/T1 のどの binder に効くか**: T `dec`（CallDec の InRange 連言と arity 連言）。
- **別名**: G-DATA-CALL（G3GEN_CALL_PLAN.md §2.2）、PortTie（D-PORT: 未設計の relation）、`hNIn` / `argsN`（b_quadAll）。
- **支払い予定のIssue**: G3GEN_CALL_PLAN.md §4: G-DATA-CALL は M3（T1 台帳を参照）、D-PORT は M3 前の read-only 分析、T1Hyp.decH 分割案は「M3 freeze で review」。
- **実runから払えそうか**: 不明。計画は run-local（`ClosingRun` + `PortTie` + `ChildShips` の port 連言）。PortTie は `connsG` / `closeInstsG` から含意されない（「補題を見つけるか証明する」）と G3GEN_CALL_PLAN.md §2.1 が書く。instance 側は per-k の `decide` と `b_quadAll` の `argsN` + `hNIn`（tm2_callDec_at、UADAPT_RESULT.md）。
- **分類**: 未供給の義務（D 行、coverage 未了）。

### P-20 `stepStmtCases_of_rows` の 4 つの row 前提（DataOk placeholder の強化）
- **Lean名**: `hLeafRow`、`hMemRow`、`hOneRow`、`hWRow`。
- **完全な型**:

```lean
-- 96ac6add:Tools/ShippingGen2StepDispatch.lean:63-68
theorem stepStmtCases_of_rows {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop)
    (hLeafRow : ∀ q, DataOk q → LeafDataOk q ∧ ExtInS q)
    (hMemRow : ∀ q, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hOneRow : ∀ q, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hWRow : ∀ q, DataOk q → ∀ k, OneOutWidth P q k) :
    StepStmtCases L P DataOk :=
```

  定義元 = Tools/ShippingGen2StepDispatch.lean:63-68 @kjob/g2st-r3@96ac6add。
- **仮定している定理**: stepStmtCases_of_rows（これ 1 つ）。
- **FG/T1 のどの binder に効くか**: T `pkg` の `DataOk q`（placeholder）が含意すべき強い行。`DataOkB` は SrcPkg 上の旧定義（P-09 の注）。
- **別名**: P-10 / P-11 / P-12 / P-25 の 4 前提を `DataOk` から導く形に束ねたもの。
- **支払い予定のIssue**: sparkle-gen3-data-supply（STEP_ROUTE_FREEZE.md §4: 「`hrow` と `hord`/`hW` row の供給は data-supply」）→ T1 台帳を参照。
- **実runから払えそうか**: 不明。STEP_ROUTE_FREEZE.md §7 row 6 の通り DataOkB からの含意はこの調査では見つからなかった。seq 3601 の approved note: 「`hMemOriginRow`/`hCallRow` を FG や共有定義へ追加しない」。
- **分類**: 入力条件（DataOk の強化）。供給は未了。

### P-21 `hseq`（served module が clk 入力を持つ）
- **Lean名**: `hseq : ∀ mc, ServedPC (ShipsAt L P n) dsn c mc → "clk" ∈ mc.inputs.map (·.name)`。
- **完全な型**: seqFactsRN_of_callDec (Tools/ShippingGen2Connect.lean:109-116 @par/gen2-spec@1fdbc18d)。
- **仮定している定理**: seqFactsRN_of_callDec（A-COMB 後、1fdbc18d で追加）。
- **FG/T1 のどの binder に効くか**: なし（T1/FG の前提ではない）。seq 2313 の approved note: 「hseq は sequential-only の明示制限で、一般には供給されず T1/FG の新しい仮説ではない。S3 は served module ごとに分岐するか、制限した PC を使う必要がある」。
- **別名**: S3 の `CombFactsRN` / `seqPC` / `combPC` 分岐（Tools/ShippingGen2GroupComb.lean:239-295 @d603ac07）。S3 の group_childShips (GroupServed.lean:294 @d603ac07) には `hseq` binder がない（AUDIT OK: 「no hseq binder (control found it)」、seq 2713 note）。
- **支払い予定のIssue**: S3（sparkle-gen2-step）で hseq の代わりに分岐する形に置換済み（d603ac07）。seqFactsRN_of_callDec 自体は残る。
- **実runから払えそうか**: 不要（置換済み）。
- **分類**: 未供給の義務（seqFactsRN_of_callDec 単体として）。S3 の group_childShips では消えている。

### P-22 G-SERVED の trace（`ServedP (ShipsRes L P)`）
- **Lean名**: `h : MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc`。
- **完全な型**: §2.2 の `ServedP`（GEN2_DEFS.lean.txt:242-244）と `ServedShipsStmt`（:246-260）。
- **仮定している定理**: machine_linked_callsServed1 / oneOut_composedNW / oneOut_childShips (OneOut.lean:158/260/288 @99f0de5d)、machine_linked_callsServed1F (FitChain.lean:903 @c6951eb8)、oneOut_topShips (OneOutTop.lean:340 @93e9994c)、oneOut_topShipsO (OneOutTopO.lean:334 @d0ef6371)、oneOutSl_childShips / oneOutSl_topShipsNC (@36342cb8)、stepStmtCases_of_rows (@96ac6add)、topShips_of_empty (StepEmpty.lean:20 @96ac6add)。
- **FG/T1 のどの binder に効くか**: I 系（G-SERVED: `ServedShipsStmt`）。StepStmt の `h` 前件（GEN2_DEFS.lean.txt:311-312）。
- **別名**: `ServedRealA`（旧）、`ServedP (ShipsAt L P n)`（P-23）。
- **支払い予定のIssue**: T1 台帳を参照（sparkle-gen2-step の note seq 2564: 「G-SERVED (M3 sparkle-gen3-served)」）。
- **実runから払えそうか**: T1 台帳を参照。
- **分類**: 未供給の義務（T1 側）。

### P-23 G-LIFT（`LiftShips`）と `ShipsAt` 版の trace
- **Lean名**: `hlift : LiftShips L P`（servedP_lift_of_liftShips、liftTrace_of_liftShips）、および `h : MachineTraceLBX (ServedP (ShipsAt L P n) …)`（group_childShips / groupSl_childShips）。
- **完全な型**:

```lean
-- 96ac6add:Tools/ShippingGen2StepLift.lean:24-27
/-- G-LIFT (a), per result. A HYPOTHESIS of this file; no supplier exists. -/
def LiftShips {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) : Prop :=
  ∀ (c : Name) (r : Res) (m n : Nat) (q : Pkg ι dom), m ≤ n → RealChildA L.O c r → P c = some q → q.decl = c →
    ChildShips q m r.1 r.2 → ChildShips q n r.1 r.2
```

  定義元 = Tools/ShippingGen2StepLift.lean:24-27 @kjob/g2st-r3@96ac6add（原文のコメント: "A HYPOTHESIS of this file; no supplier exists"）。group_childShips の `h` は GroupServed.lean:305-306 @par/gen2-spec@d603ac07。
- **仮定している定理**: servedP_lift_of_liftShips (StepLift.lean:36)、liftTrace_of_liftShips (:85) @kjob/g2st-r3@96ac6add、group_childShips (GroupServed.lean:294 @d603ac07)、group_composedNW (:271)、groupSl_childShips (SlotlessParentRun.lean:338 @36342cb8)。
- **FG/T1 のどの binder に効くか**: StepStmt の `h`（`ShipsRes` 版）から `ShipsAt L P n`（固定高さ）版への橋。GENERAL_SPEC §3.2 / §4.3 / §5 item 5 の G-LIFT。
- **別名**: `LiftShipsInstFree`（Tools/ShippingGen2StepLiftInstFree.lean:85 @kjob/g2st-r5@2be39bc4）。これは instFree 結果に限定した**別の弱い文**で、`liftShipsInstFree_proved` により証明済み。ただし seq 4592 で changes_requested（StepReach の root 自身判定）。`LiftShips` を供給するものではない（原文コメント）。
- **支払い予定のIssue**: 未割当（STEP_ROUTE_FREEZE.md §7 row 1: 「`ChildShips q m → ChildShips q n` (m ≤ n) の statement も proof も**見つからなかった**。反例も構成していない」）。GENERAL_SPEC §5 item 5: G-LIFT が偽なら height 異質 kid state の semantics 変更でユーザー判断。
- **実runから払えそうか**: 不明（上記。この調査では見つからなかった）。
- **分類**: 未供給の義務（G-LIFT）。

### P-24 ChildKeepsInv（G-KEEP-CHILD）
- **Lean名**: `hC : ChildKeepsInv L P Reach D`（keepBody の `KeepBodyStmt := ∀ D, ChildKeepsInv … D → BodyKeepsInv … D`）。
- **完全な型**: §2.2 の I 系（GEN2_DEFS.lean.txt:164-189）。keepBody = Tools/ShippingGen2Keep.lean:54 @par/gen2-spec@6bd02a3a。
- **FG/T1 のどの binder に効くか**: I 系（G-EXC / `KeepChildStmt`）。
- **別名**: G-EXC、G-KEEP-CHILD。
- **支払い予定のIssue / 実run / 分類**: T1 台帳を参照（M3）。

### P-25 `hW : ∀ k, OneOutWidth P p k`（G-ONEOUT-WID）
- **Lean名**: `hW`。供給側の局所版: `hcw : callWidthsStrict p.d p.kD kidOuts = true`、`hkid`、`hsimple`（oneOutWidth_of_strict）。
- **完全な型**:

```lean
-- c6951eb8:Tools/ShippingGen2FitChain.lean:891-896
/-- The binder of call `k`'s result has the bit width of the callee package's ONLY layout output (the unique output, not a field
name). `kindTy`: Tools/ShippingMachineEntry.lean:232. (S4_CONSUMER_FREEZE.md §5, approved rev2, unchanged.) -/
def OneOutWidth (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length) (q : Pkg ι dom), P (p.d.shape.insts[k]).1 = some q →
    ∀ o : OutField, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth
```

```lean
-- 5d6ca626:Tools/ShippingGen2DataBridge.lean:123-129
theorem oneOutWidth_of_strict (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom)
    (kidOuts : Nat → List Sparkle.IR.Machine.OutField)
    (hcw : Tools.ShippingCallWidthsStrict.callWidthsStrict p.d p.kD kidOuts = true)
    (hsimple : p.d.shape.instFields = [])
    (hkid : ∀ k (hk : k < p.d.shape.insts.length) (q : Tools.ShippingGen2.Pkg ι dom),
      P (p.d.shape.insts[k]).1 = some q → kidOuts k = q.d.shape.layout.outs) :
    ∀ k, Tools.ShippingGen2.OneOutWidth P p k :=
```

  定義元 = Tools/ShippingGen2FitChain.lean:891-897 @par/gen2-spec@c6951eb8、Tools/ShippingGen2DataBridge.lean:123-130 @par/gen2-spec@5d6ca626。
- **仮定している定理**: machine_linked_callsServed1F (FitChain.lean:903 @c6951eb8)、oneOutWidthAt (OneOutTop.lean:289 @93e9994c)、oneOut_topShips (:340 @93e9994c)、oneOut_topShipsO (OneOutTopO.lean:334 @d0ef6371)、oneOutSl_topShipsNC (SlotlessTop.lean:447 @36342cb8)、stepStmtCases_of_rows の `hWRow`（P-20）。
- **FG/T1 のどの binder に効くか**: StepStmt の one-output case 用の追加前提（GEN2_DEFS には無い）。S4_WID_SUPPLY.md が T1Hyp 欄 `wid` を提案したが「未適用・未承認」（seq 2574, 2576）。
- **別名**: G-ONEOUT-WID、`RunFacts.wid`、`hkidW1`（core_instOutWidthsOk_oneA, OneOutTop.lean:198）。
- **支払い予定のIssue**: sparkle-gen3-data-supply（STEP_ROUTE_FREEZE.md §4: 「`hord`/`hW` row supply」）→ T1 台帳を参照。
- **実runから払えそうか**: 不明。DataBridge の `oneOutWidth_of_strict` は decided row `callWidthsStrict` から `∀ k, OneOutWidth P p k` を与えるが、row 自体が追加前提（"extra premise under an abstract P"）。呼び出しの存在（`P c = some q`）は row からは出ず `hdec` から来る（DataBridge の docstring）。seq 2569 note: 「『impossible without compiler change』は『既存 export では供給されない; bridges unproved』へ訂正」。
- **分類**: 未供給の義務（G-ONEOUT-WID）。

### P-26 `hnomem`（名前半分を含む）と `hord`（起源半分）— P-MEM
- **Lean名**: `hnomem : ∀ x ∈ p.d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true`（oneOut_topShips、oneOutWidthAt、core_*A 系）。置換先: `hord : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none`（oneOut_topShipsO、oneOutWidthAtO、oneOutSl_topShipsNC）と row `OneOutNoMemRow p = true`。
- **完全な型**:

```lean
-- 5d6ca626:Tools/ShippingGen2DataBridge.lean:36-38
/-- **The P-MEM row** of a package (implication form: memory parents, whose `instFields ≠ []`, pass it). -/
def OneOutNoMemRow (p : Tools.ShippingGen2.Pkg ι dom) : Bool :=
  !p.d.shape.instFields.isEmpty || p.d.shape.instTagged.all (fun x => x.2.child?.isNone)
```

  `hord_of_row`（Tools/ShippingGen2DataBridge.lean:57 @5d6ca626）は `OneOutNoMemRow p = true`、`instFields = []`、`k < insts.length` から `hord` を与える。`hnomem` の原文: Tools/ShippingGen2OneOutTop.lean:343-344 @par/gen2-spec@93e9994c。
- **仮定している定理**: hnomem 版: oneOut_topShips (:340)、oneOutWidthAt (:289)、core_callPorts_oneA (:51) @93e9994c。hord 版: oneOut_topShipsO (OneOutTopO.lean:334)、oneOutWidthAtO (:282) @d0ef6371、oneOutSl_topShipsNC (@36342cb8)、allCallDec_of_hord (StepCases.lean:43 @96ac6add)。
- **FG/T1 のどの binder に効くか**: T `dec` の「memory 起源でない」側（one-output closing では memory を持てない、という case 前提）。StepStmt には対応する binder がない。
- **別名**: P-MEM、P-MEM-4（名前半分の除去: seq 2597 で 14 theorem の O-copies を限定受理）。
- **支払い予定のIssue**: hord row = sparkle-gen3-data-supply（STEP_ROUTE_FREEZE.md §4）→ T1 台帳を参照。名前半分は O-copies で除去済み（d0ef6371）。
- **実runから払えそうか**: 名前半分は不要（chain は起源半分しか使わない: S4_PMEM4_FREEZE.md §1）。S4_PMEM4_FREEZE.md §0 は「名前半分は、memory placeholder 名の ordinary callee を持つ正当な one-output parent で FALSE（collPlainCD_nomem_false, Tests/Compiler/MemNameCollisionPlainCertTest.lean:177-180）」と記す（この台帳ではそのテストファイルは読んでいない）。起源半分の row の被覆は不明（seq 2566 / 2569 note: 「run 経路は不十分、MemFlag は未証明の plan」）。
- **分類**: 入力条件（row）。coverage は未供給の義務。

### P-27 `TopShips` 結論内の実行前件（R-G）と `PTopPrem`
- **Lean名**: `TopShips` の ∀ 内の前件（SourceInputs、regs 固定、`rst`/`clk` の守り付き前提、`st0 r = f.init`、`ResetNk n raw D kids`、`ins` の幅、`st0` の幅）。`PTopPrem p n declName b raw D ids cache regs i bools bits T ins st0 kids`（これらから `rst`/`clk` の守りを除いたもの）。
- **完全な型**: R-G の `TopShips` は §2.3 (b)（Tools/ShippingGen2Defs.lean:277-311 @kjob/g2tc-s2@fa84af5d）。`PTopPrem`:

```lean
-- c5c37d2b:Tools/ShippingGen2TopCtrl.lean:29-43
/-- The execution premises of the inner telescope of `TopShips`, without the `rst`/`clk` guard premises. -/
def PTopPrem {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) (ids : List FVarId) (cache : IO.Ref (ExprStructMap String))
    (regs : List String) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (kids : String → KT n) : Prop :=
  (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
      (fun j => (p.extBS i bools bits j).val (T - 1 - t))
      (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) ∧
  (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) ∧
  (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
    p.d.shape.layout.slots[k]? = some f → st0 r = f.init) ∧
  ResetNk n raw D kids ∧
  (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) ∧
  (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body → st0 x < 2 ^ declWidth b x)
```

  定義元 = Tools/ShippingGen2TopCtrl.lean:29-44 @kjob/g2tc-ptop19@c5c37d2b。
- **仮定している定理**: ptop_inst (TopCtrl.lean:46 @c5c37d2b; `hprem`)、ptop_prem_ofRun (TopSupply6.lean:35 @kjob/g2tc-ptop12@0ab11f69)、ptop_ofSlotlessRun (TopSupply7.lean:31 @kjob/g2tc-ptop14@8136d9dc)、ptop_pbh (Tests/Gen2/TopPbhInst.lean:32 @kjob/g2tc-ptop16@ddb492f0)、ptop_pbh_ofEx (Tests/Gen2/TopPbhRunEx.lean:47 @kjob/g2tc-ptop19@c5c37d2b)。
- **FG/T1 のどの binder に効くか**: FG の結論 `TopShips …` の内側の前件（結論の消費者が満たすべき条件。FG の ∀ binder ではない）。非空虚性（P-TOP）の対象。
- **別名**: c1..c6（TOP_CTRL_FREEZE.md の PTopPrem の 6 連言: c1 SourceInputs、c2 regs 固定、c3 init、c4 ResetNk、c5 ins 範囲、c6 st0 範囲）。
- **支払い予定のIssue**: sparkle-gen2-top-contract（本 Issue。seq 5569 todo）。
- **実runから払えそうか**: 一部のみ（履歴の証明済み条件付き補題）。`ss = []` で c2/c3（ptop_c23_of_ss_nil）、st0 = 0 で c6、c1/c5 は同じ `ins`（exists_ins_c1c5_ofRun、U2）、c4 は `resetNk_ofRun`（U3）。slotted（regs ≠ []）の c2/c3 は**この調査では見つからなかった**。履歴 seq 3814-3816: `ptop_regs_unsat`（ss.length = 1 かつ b に入力 x があると regs = [x] で c2 が偽、`∀ regs` の形の `hprem` は供給不能）は seedIn 述語の反証であり TopShips の反証ではない。
- **分類**: 入力条件（保証の前件）。供給は未供給の義務（P-TOP 未完: 履歴 seq 5527）。

### P-28 具体 run の存在と共同充足性（`PbhRunEx L` / `PbhRunAt`）
- **Lean名**: `hex : PbhRunEx L`（ptop_pbh_ofEx）。内訳 `PbhRunAt`: `AdmCtx`、`JQC L.O (dv w) w`、`RunsTo (synthesizeCombinationalCore pbhPkg.decl [] false) …`、`hpost`、`MachineDefines`、`MachineTaken`。
- **完全な型**:

```lean
-- c5c37d2b:Tests/Gen2/TopPbhRunEx.lean:33-45
def PbhRunAt {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  AdmCtx L.O.quiet mctx cctx ∧ JQC L.O (dv w) w ∧
  RunsTo (synthesizeCombinationalCore pbhPkg.decl [] false) mctx mref cctx cref w (raw, D) w1 ∧
  (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
  MachineDefines mctx mref cctx cref pbhPkg.decl pbhPkg.d.shape ∧
  MachineTaken L mctx cctx (dv w + 1) pbhPkg.decl pbhPkg.d.shape raw D

def PbhRunEx {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) : Prop :=
  ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld) (raw b : Sparkle.IR.AST.Module) (D : Design),
    PbhRunAt L mctx cctx w w1 raw b D
```

  定義元 = Tests/Gen2/TopPbhRunEx.lean:33-45 @kjob/g2tc-ptop19@c5c37d2b。
- **仮定している定理**: ptop_pbh_ofEx (:47 @c5c37d2b)、ptop_pbh (Tests/Gen2/TopPbhInst.lean:32 @kjob/g2tc-ptop16@ddb492f0)、ptop_ofSlotlessRun (@8136d9dc)、pbh_ships (Tests/Gen2/SlotlessLeafInstance.lean:45 @par/gen2-spec@22417406)、q_ships (Tests/Gen2/QuantInstance.lean:125 @par/gen2-spec@94ed8609)、leaf16_ships / lm_ships（instance）。
- **FG/T1 のどの binder に効くか**: F3 + F4 + F5 + T `closes` の同時充足（実在の run が前提を満たすこと = instance の非空虚性）。FG の binder そのものではなく、「条件付き instance が空虚でない」ことの証拠にあたる。
- **別名**: `MachineRunJQC`（P-07）、「run existence」（各 *_RESULT.md の Not claimed 欄）。
- **支払い予定のIssue**: sparkle-gen2-top-contract（P-TOP）。再開条件は seq 5569（前提台帳で選ばれたとき）。
- **実runから払えそうか**: **この調査では見つからなかった**（seq 5357 以降の各 note: 「具体 run・共同充足性・非空虚 Laws は、辿った候補経路では供給元が見つからなかった」）。履歴上の事実は否定のみ: `lawsQuietFalse` では `PbhRunEx` は偽（`not_pbhRunEx_lawsQuietFalse`、Tests/Gen2/TopLawsQF.lean @kjob/g2tc-ptop21@22862066）。
- **分類**: 未供給の義務。


## 4. 集計（§3 のブロックを数えた値）

- 前提ブロック数: 28（P-01 … P-28）。
- 分類（各ブロックの「分類」欄を数えた）:
  - TRUSTED境界（候補）: 1（P-01）。
  - 入力条件のみ: 5（P-02, P-03, P-04, P-05, P-15）。
  - 入力条件 + coverage は未供給の義務: 8（P-09, P-10, P-11, P-13, P-14, P-20, P-26, P-27）。
  - 未供給の義務: 14（P-06, P-07, P-08, P-12, P-16, P-17, P-18, P-19, P-21, P-22, P-23, P-24, P-25, P-28）。
- 「T1 台帳を参照」と 1 行にしたもの: P-22（G-SERVED）、P-24（G-KEEP-CHILD）。一部が T1 側の供給に依存: P-03（内側の `InvAt`）、P-19（G-DATA-CALL）、P-20 / P-25 / P-26（sparkle-gen3-data-supply）。
- 「実runから払えそうか」の判定語: 「条件付きではい」1（P-07: `machineRunJQC_of_closesA`）、「はい」1（P-13: `Nonempty ι` の下の `memOrigin_of_memDec`）、「いいえ（現状）」2（P-08, P-14）、「入力そのもの」4（P-02, P-03, P-04, P-05 の最外）、「不要（置換済み）」1（P-21）、それ以外は「不明」または「この調査では見つからなかった」。
- **要注意点（履歴の記載に基づく）**:
  1. 本グループの定理は 2 世代の定義にまたがる。par/gen2-spec 先端（d0ddc50b）の `TopShips` は `rst`/`clk` 前提が無条件の旧形、kjob/g2tc-s2（fa84af5d）の Defs は R-G 形と `InstClosed` 付き `ShipsRes`（§2.3）。承認済みの step 系定理のうち oneOut_topShips（93e9994c）などは旧 `TopShips` に対する証明。P-TOP（`TopShips` の非空虚性）は未完。
  2. `StepStmt` 本体は証明されていない。承認されたのは `StepStmtCases`（3 形に case 制限、4 つの row 前提つき）と各部品（P-14, P-20）。group 親（instFields ≠ []）の `TopShips`、case S の one-output slotless top（C5S）、instFields = [] の closing 内の memory call（case X）、one-output slotless の実 Pkg（D4）は、STEP_ROUTE_FREEZE.md §2/§7 に「供給元なし」と記録されている。
  3. 全 `Pkg` 定理は instance ごとに生成された `X.machine_*` を前提とするため、G3-GEN / G3-DECL は instance（leafM, quantModule, topshare2, leaf16, pickByteH）でしか供給されていない（P-08）。
  4. 具体 run の存在（P-28）は誰も供給していない。`lawsQuietFalse` では偽であることだけが証明済み（P-01, P-28）。
  5. 履歴の mutant 棄却はすべて signature/defeq 棄却であり、意味的反例ではない（本台帳は不可能性を主張していない）。

## 5. 読んだ文書・branch@SHA 一覧

履歴（全 11 件、`$S/h/<issue>.json`、括弧内は JSON の要素数。job-linked 等も数える）: sparkle-gen2-u0-types（10 件）、sparkle-gen2-uadapt（16）、sparkle-gen2-gencall-plan（6）、sparkle-gen2-calldec（18）、sparkle-gen2-callfield（11）、sparkle-gen2-leaf（16）、sparkle-gen2-loop-pkg（48）、sparkle-gen2-step-mem（39）、sparkle-gen4-oneout-probe（7）、sparkle-gen2-step（211 件、最終 note seq 4596 まで全文）、sparkle-gen2-top-contract（163 件、最終 note seq 5569 まで全文）。

文書（`git show` で読んだもの）:
- scripts/gen2/GENERAL_SPEC.md @d0ddc50b（全文）、scripts/gen2/GEN2_DEFS.lean.txt @d0ddc50b（全文）。
- scripts/gen2/U0_RESULT.md @0939cfb6、scripts/gen2/G3GEN_CALL_PLAN.md @508b365e、scripts/gen2/CALLDEC_PROBE_RESULT.md @5c1b78a1、scripts/gen2/UADAPT_RESULT.md @cc305538、scripts/gen2/CALLFIELD_RESULT.md @f8164382、scripts/gen2/LEAF_RESULT.md @5b93aa2f、scripts/gen2/LOOPPKG_RESULT.md @ac91f8e3、scripts/gen2/MEMPARENT_RESULT.md @ea5f5cda。
- scripts/gen4/ONEOUT_CALLDEC_RESULT.md @par/gen4-gate@1973de8e、Tests/Gen4/OneOutCallDecProbe.lean @par/gen4-gate@2dede972。
- scripts/gen2/PKG_COMB_RESULT.md、S4_STAGEA_RESULT.md、S4_STAGEB_RESULT.md @d0ddc50b（全文）、scripts/gen2/S4_PMEM4_FREEZE.md @d0ef6371（§0-§4）、scripts/gen2/STEP_ROUTE_FREEZE.md @kjob/g2st-r3@96ac6add（§1-§5、§7-§9）、scripts/gen2/S5_SLOTLESS_FREEZE.md @d0ddc50b（見出しと `hrst` の行のみ）。

Lean（`git show <sha>:<path>` で該当部を読んだもの; 行番号は §3 の各ブロックに記載）:
- par/gen2-spec@6bd02a3a: Tools/ShippingGen2{Keep,Connect,Consumer,Data}.lean。
- par/gen2-spec@5c1b78a1: Tools/ShippingGen2CallDec.lean。par/gen2-spec@121c09fe: Tools/ShippingGen2Adapt.lean。par/gen2-spec@3b702f15: Tools/ShippingGen2CallField.lean。
- par/gen2-spec@d9fac18c: Tools/ShippingGen2Leaf.lean。par/gen2-spec@94ed8609: Tools/ShippingGen2{MemParent,MemShips,Loop,CombPkg}.lean、Tests/Gen2/QuantInstance.lean（署名のみ）。par/gen2-spec@f1a4367f: Tools/ShippingGen2{MemParent,MemShips,MemTop,MemFacts}.lean（署名のみ）。
- par/gen2-spec@1fdbc18d: Tools/ShippingGen2Connect.lean（`seqFactsRN_of_callDec`）。@22417406: Tools/ShippingGen2SlotlessLeaf.lean、Tests/Gen2/SlotlessLeafInstance.lean（署名のみ）。
- par/gen2-spec@99f0de5d: Tools/ShippingGen2OneOut.lean。@c6951eb8: Tools/ShippingGen2FitChain.lean。@93e9994c: Tools/ShippingGen2OneOutTop.lean。@5d6ca626: Tools/ShippingGen2DataBridge.lean。@d0ef6371: Tools/ShippingGen2OneOutTopO.lean（署名のみ）。
- par/gen2-spec@d603ac07: Tools/ShippingGen2{GroupComb,GroupServed}.lean（署名のみ）。@36342cb8: Tools/ShippingGen2{SlotlessParent,SlotlessParentRun,TopVacuity,TopNC,SlotlessTop}.lean（署名のみ）。
- kjob/g2st-r3@96ac6add: Tools/ShippingGen2Step{Cases,Empty,Lift,Dispatch}.lean。kjob/g2st-r5@2be39bc4: Tools/ShippingGen2StepLiftInstFree.lean（該当部のみ）。
- kjob/g2tc-s2@fa84af5d: Tools/ShippingGen2Defs.lean（差分）。kjob/g2tc-ptop19@c5c37d2b: Tools/ShippingGen2{Defs,TopCtrl}.lean、Tests/Gen2/TopPbhRunEx.lean。kjob/g2tc-ptop12@0ab11f69→8136d9dc(kjob/g2tc-ptop14): Tools/ShippingGen2TopSupply{6,7}.lean（署名のみ）。kjob/g2tc-ptop16@ddb492f0: Tests/Gen2/TopPbhInst.lean。kjob/g2tc-ptop21@22862066: Tests/Gen2/TopLawsQF.lean。
- par/gen2-spec@d0ddc50b: Tools/ShippingChildInvA.lean、Tools/ShippingChildCacheA.lean、Tools/ShippingServedRealA.lean、Tools/ShippingChildRunAKids.lean、Tools/ShippingMachineEntry.lean、Tools/ShippingQuadComposed.lean、Tools/ShippingQuadHPoint.lean、Tools/ShippingQuadCalls.lean、Tools/ShippingCallsShape.lean、Tools/ShippingMachineAuto.lean、Tools/ShippingMachineClosesData.lean（定義部のみ）、Tools/ShippingGen2{Pkg,SrcPkg}.lean。

## 6. 読めなかったもの・この調査では見つからなかったもの

- **見つからなかった**: `ReflectsAll` と `Pk` の Lean 定義（HEAD と kjob/g2tc-ptop21 の Tools/Tests を `git grep`）。FG の entry run → core run の橋。生成 package の汎用供給（G3-GEN）。`MachineClosesAtA` の一般供給。非空虚な `Laws` 値。具体 run の存在（`PbhRunEx L`）。G-LIFT の statement / proof（STEP_ROUTE_FREEZE.md §7 row 1）。group 親の `TopShips`、C5S、case X、D4（同 §2 / §7）。
- **読まなかった**: sparkle-gen3-* / sparkle-gen4-*（oneout-probe 以外）/ sparkle-gen5-* の履歴（他グループ。「タイトルのみ」と書いた箇所はタイトルしか見ていない）。`managerctl show`。ビルドログ（~/git/.kjob-state）。reviewer の feedback ファイル（/tmp/*review*.txt）。
- **全文は読まず履歴 note 経由で知ったもの**: TOP_CTRL_FREEZE.md、TOP_CONTRACT_REVISION.md、S4_FIT_FREEZE.md / S4_FIT_RESULT.md、S4_WID_SUPPLY.md、S4_PMEM_FREEZE.md、S3_GROUP_FREEZE.md、S5_SLOTLESS_FREEZE.md（見出し以外）、STEP_S6_RESULT.md、STEP_ROUTE_FREEZE.md §6/§10、STEP_LIFT_FREEZE.md、CALLFIELD_FREEZE.md、LOOPPKG_FREEZE.md、MEMPARENT_FREEZE.md。TopSupply2-5・TopSame・TopSupply* の Check ファイル（本文）。
- **署名のみで本文を読まなかった Lean**: 上記 §5 で「署名のみ」と書いたもの。したがって「この定理が使わない binder」の判断は、履歴 / RESULT 文書の記述（例: LEAF_RESULT.md の「JQC・run・MachineDefines は未使用 binder」）に依っている。
- **確認していない記述**: S4_PMEM4_FREEZE.md §0 の `collPlainCD_nomem_false`（Tests/Compiler/MemNameCollisionPlainCertTest.lean:177-180）は、その freeze 文書の記述を引用したのみで、テストファイルは読んでいない。

