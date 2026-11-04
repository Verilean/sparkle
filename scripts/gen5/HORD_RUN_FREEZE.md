# HORD_RUN: hord / hrow を取らない closingRun 系（FG 台帳 A.P-26・C.CR-1）

Issue: `sparkle-ledger-hord-run`（親 `sparkle-ledger-shorten`、ユーザー判断 2026-11-05「候補 C を先行、まず A.P-26 + C.CR-1」）。
base: f5de62a0（par/aud-ua4-hrowfree）。実装: `Tools/ShippingGen5ClosingRun3.lean`、検査: `Tests/Gen5/ClosingRun3Check.lean`。
台帳（受入済み）: FG 91 / T1 57。この文書は台帳を変えない。

## 0. 減算表

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | A.P-26（`hord` 起源半分。名前半分は O-copies で除去済み、FG 台帳 §9.3 `:769`）、C.CR-1（`hrow`、`closingRun0_of_run` では `hord`） |
| 消える条件 | §2 の 6 つの文の受理（reviewer: 前提の除去）と exact-head build exit 0。FG の closingRun 系の定理に `hord` / `hrow` の束縛変数が残らないこと（§3 の BINDERS） |
| 残る条件（動かない） | C.CR-2 `hGen`、A.P-24（`hIH` / `hKI`）、`T1HypND`（T1 の行）、非空虚性（A.P-27 / A.P-28）、depth0 `stop` |
| root theorem | `closingRun0_of_runR`（depth 0）、`closingRun_of_runR`（depth ≥ 1）。部品は `closingShared_of_runR`、`hord_of_runReadsAt` |
| 台帳への効果 | 一般 FG の **非リーフ −2**（91 → 89、非リーフ 29 → 27）。**リーフ 62 は動かない**。重ねて数えていた行の除去（T1L-04 は T1 側で除去済み、877c1498）。IP 限定の成果ではない |
| 新しい TRUSTED / law / コンパイラ変更 | なし |

## 1. 何を変えるか

旧定理（`closingShared_of_run`・`closingRun0_of_run`、`Tools/ShippingGen5ClosingRun2.lean`、`closingRun_of_run`、`Tools/ShippingGen5ClosingRun.lean`、`closingRun_of_run_ga`・`ClosingPremises`）は、`DataOk` を満たす **全パッケージ `q`** の上の `hord`（または `hrow`）を仮説に取る。証明の中での使い道は、run 自身のパッケージ `p` での 1 か所（`soundX_ships_at` の最後の引数）だけ。

新定理は、その 1 か所を run から出す:
`hrr : RunReadsAt … p.d.shape …`（`runReads_of_run` の結果）の `shapeEq : machineShape? … = some p.d.shape` に、
コンパイラの最終ゲートを読む `machineShape?_noMemRow`（hrow-gate 877c1498、`Tools/ShippingGen3HrowGate.lean:109`）を当てて
`noMemRowS p.d.shape = true`、`hord_of_rowS`（`Tools/ShippingGen2DataBridge.lean:43`）で `hord` の当該の場合。

**結論の型は旧定理と同じ。仮説は旧定理から `hord` / `hrow` の 1 つを除いただけ**（他の束縛変数・順序・名前は同じ）。
したがって新定理は旧定理より強く、旧定理は新定理から（`hord` を捨てて）出る。
「全パッケージ上 → この run の `p` だけ」という意味の変更は、新定理の仮説には現れない（run 局所の事実は証明の中で導く）。
旧定理・定義・既存ファイルは変えない。

## 2. 凍結する文（Lean の字面。`Tests/Gen5/ClosingRun3Check.lean` §1 の Expected と同じ）

共通の `variable`: `{ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}`。

```lean
theorem hord_of_runReadsAt {mctx : Meta.Context} {cctx : Core.Context} {X : Name}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6)
    (hf : shape.instFields = []) (k : Nat) (hk : k < shape.insts.length) :
    (shape.instOrigins.getD k .ord).child? = none

theorem closingShared_of_runR (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D

theorem closingRun0_of_runR (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D

theorem closingRun_of_runR (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D

-- closingRun_of_run_gaR: closingRun_of_run_ga の字面から (hrow : …) の 1 行を除いたもの（GA / hGA の形はそのまま）
-- ClosingPremisesR: ClosingPremises の field から hrow を除いたもの（他の 10 field は同名・同順・同型）
theorem closingRun_nonempty_of_premisesR … (h : ClosingPremisesR L P Reach DataOk mctx cctx X p w w' raw D Gen) :
    Nonempty (ClosingRun L P Reach mctx cctx X p Gen w w' raw D)
```

## 3. 行との対応

| 台帳の行 | 旧定理の束縛変数 | 新定理での扱い | 検査 |
|---|---|---|---|
| A.P-26（起源半分） | `closingShared_of_run` / `closingRun0_of_run` の `hord` | 無し。`hord_of_runReadsAt hrr` で証明の中に出す | BINDERS: 新 = 旧 − `hord`、`hord`/`hrow`/`hDp` が無い |
| C.CR-1 | `closingRun0_of_run` の `hord`、`closingRun_of_run` / `closingRun_of_run_ga` の `hrow`、`ClosingPremises.hrow` | 無し（同上） | BINDERS: 新 = 旧 − `hrow`。FIELDS: `ClosingPremisesR` = `ClosingPremises` − `hrow` |
| （残る）C.CR-2 | `hGen` | そのまま | TYPE |
| （残る）A.P-24 | `hIH` / `hKI` | そのまま | TYPE |
| （残る）T1 の行 | `hT : T1HypND …` | そのまま。`DataOk` は `hT.pkg` が使うので型の引数に残る（`hord` のための `DataOk p` の取り出しは消えた） | TYPE |

## 4. 検査（`Tests/Gen5/ClosingRun3Check.lean`）

* TYPE 6（Expected は本文書 §2 から書いた）と、旧定理 4 本の再受理（対照、同じ比較器）。
* MUTANT 9: 旧定理の文（`hord`/`hrow` 付き）4 本を新定理に対して棄却、1 点変異 5 本。棄却は signature / defeq によるもので、意味の反例ではない。
* BINDERS 4 + FIELDS 1（上表）。
* REACH 6: 新定理の閉包が `machineShape?_noMemRow` に届き、旧定理（`hord`/`hrow` 版）に届かない。T1Hyp の field・BodyStepC・ofReduceBool に届かない（ClosingRun2Check の検出器と対照を流用）。
* AXIOMS 7: 標準の 3 つだけ。

## 5. 主張しないこと

* 非空虚性（前提の具体的な値は作っていない）。`hGen` / `GeneratedAt`、`hIH` / `hKI`、depth0 `stop`、T1 / FG の完成。
* コンパイラのゲート（Elab.lean の最終ゲート、hrow-gate）が効く tree での結果。共有 tree への統合はユーザーの merge（hrow-gate と aud-ua4-hrowfree）。
* リーフの減少。台帳の −2 は非リーフ（重ねて数えた行）の除去。

## 6. A.P-24（`hIH` / `hKI`）: T1 の行から供給する（候補 2、別の判定）

`Tools/ShippingGen5ClosingRun4.lean`、検査 `Tests/Gen5/ClosingRun4Check.lean`。

### 6.1 減算表

| 項目 | 内容 |
|---|---|
| 消える台帳 ID | A.P-24（B.F-1、C.CR-3、C.AC-8 を統合済みの 1 行）。closingRun 系の `hIH` / `hKI` の束縛変数 |
| 消える条件 | §6.2 の 3 つの文の受理と、下の数え方（§6.3）の reviewer の確認 |
| 残る条件 | T1 の行: `hT : T1Hyp`（T1L-06..10、`dec` = T1L-09 を含む）、`hrows`（T1L-05）、`hStep`（T1L-03）。C.CR-2 `hGen`、非空虚性、depth0 `stop` |
| root theorem | `closingRun0_of_runT1`、`closingRun_of_runT1`（部品 `ihKI_of_rows`） |
| 台帳への効果 | 数え方 (a) なら一般 FG の非リーフ −1（89 → 88）。数え方 (b) なら −1 +1 = 0。リーフは動かない |

### 6.2 文

`closingRun0_of_runT1` / `closingRun_of_runT1` は、§2 の `closingRun0_of_runR` / `closingRun_of_runR` の字面から
`(hIH : …) (hKI : …)` を除き、`(hT : T1HypND L P Reach DataOk)` を次の 3 行で置き換えたもの（他は同じ）:

```lean
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk)
```

```lean
theorem ihKI_of_rows (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1Hyp L P Reach DataOk)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hStep : StepStmt L P DataOk) :
    ∀ D, 1 ≤ D → IHAt L P Reach D ∧ ChildKeepsInv L P Reach D
```

証明は `ih_allPF`（`Tools/ShippingGen2T1.lean:197`、承認済み）に、前提なしの `keepChild_proved`・`limitStmt_proved`、
hrow-gate の `servedShips0_run`（`hrow` なし）・`postFacts_of_run`（`hrows` だけ）を渡すだけ。新しい補題・前提はない。

### 6.3 数え方（reviewer に確認すること）

* `dec`（`T1Hyp` と `T1HypND` の差）: FG 台帳は `T1Hyp.dec` を既に A.P-17（T1L-09 の親、PA）として数えている。`T1Hyp` を取ることで FG に新しい行は増えない（読み）。
* `hStep`（T1L-03）: FG 台帳の A.P-14 / A.P-22 の読みが T1L-03 を指す。A.P-22 は「T1 側で数えているので FG に重ねて数えない」として除いた（§12.7、reviewer 承認）。
* `hrows`（T1L-05）: **FG 台帳に対応する行が見つからなかった。**
  * (a) A.P-22 と同じ規則（T1 の行は T1 台帳で数え、FG に重ねて数えない）を当てるなら、増える行は 0 で、A.P-24 が消えて −1。
  * (b) FG の束縛変数ごとに数えるなら、`hrows` が FG の非リーフに 1 行増え、純差分は 0。
* どちらでも、この定理は FG の closingRun 系から T1 の帰納法の結論（`IHAt` / `ChildKeepsInv`）を仮定として取り除く。循環はない: `ih_allPF` は closingRun 系の定理を使わない（ClosingRun4Check は型の検査だけ。閉包の検査は §4 の REACH に無い。必要なら足す）。
