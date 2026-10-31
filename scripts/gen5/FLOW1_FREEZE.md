# FG 流れ 1 freeze（実 run の読み → ClosingRun）— DESIGN ONLY, no Lean yet

Issue `sparkle-gen5-dg-closingrun`、job flow1-a、ブランチ `kjob/flow1-a`、base `f3a29dbb`（= kjob/g5cr-r6）。
ユーザー了承（2026-10-31）の進め方に従い、台帳 §5 の流れ 1 の全単位を 1 つの freeze にまとめる。reviewer の承認は流れ 1 回。

台帳（読んだ版）: FG 側 `kjob/fg-ledger3` dd624a27（`scripts/gen2/PREMISE_LEDGER.md`、`premise_ledger/C_M5dg.md`、`D_M5t2.md`）、
T1 側 `kjob/t1-ledger2`（`scripts/gen3/PREMISE_LEDGER.md`）。台帳の現在件数: **FG 110 / T1 62**。ID は `C.RK-5` のように「部分ファイル.見出し」。

書き方の約束:
- 「未供給」「この調査では供給元・経路が見つからなかった」は、読んだ範囲の記述で、不可能・導出不能の主張ではない。
- mutant（実装後の Check）は signature/defeq での棄却であって意味的反例ではない。
- 条件付き定理は中間結果であり、完了と書かない。この流れだけでは `ClosingRun` の前提は全部は消えない。T1 / FG / M5 / Issue は完了しない。
- **この文書の型は source から読み写したもので、Lean では elaborate していない**（Lean は承認後。型の修正が要れば実装時に変更要求として報告し、黙って足さない）。
- 禁止事項は守る: コンパイラ / `Tools/ShippingGen2Defs.lean` / `T1Hyp` / `T1HypND` / `Elab*.lean` の編集なし、新 TRUSTED / law なし、FG 縮小なし、`GenWF` 強化なし、
  sorry / axiom / native_decide なし。`stop_of_run` 不変。新 Lean は新規ファイル（`lakefile.lean` の `lean_lib` 追加のみ）。

## 0. 調べたこと（この流れが何を持っているか）

| 根拠 | 場所 | 状態 |
|---|---|---|
| `runReads_of_run`（C.RR-1..3 の供給側） | `Tools/ShippingGen5RunReads.lean:181`（この base にある） | built・承認済み（g5rr3-88771739） |
| `closingShared_of_run` / `closingRun0_of_run` | `Tools/ShippingGen5ClosingRun2.lean:70,127`（この base） | built・承認済み（cr6v-f3a29dbb） |
| `callTie_of_closingRun0_one` / `callTie_of_closingShared_one` / `servedCall_of_closingShared_one` | `Tools/ShippingGen5T2TieCR.lean`、`kjob/g5tt-sync` 632f365d（`kjob/g5tt-cr6` 456699fc + header 同期） | built・承認済み（ttcr6-456699fc、seq3923/3925）。**この base には無い** |
| `callTie_of_closingShared_one_ex` / `callTie_of_closingShared_group_kidW` / `calleePkg_of_t1ND` / `servedCall_of_closingShared_group` | `Tools/ShippingGen5T2TieCR2.lean`、同 `kjob/g5tt-sync` 632f365d | 同上 |
| `readMachine_agrees_runReads_of_head_self`（U13、`R : RunReadsAt …` を前提に取る） | `Tools/ShippingGen5ReadKindsU13.lean`、`kjob/g5rk-r23` 5cbcdc6a（U13 承認 25540b18 + header 同期）。**この base には無い** | built・承認済み（rk22v-25540b18） |
| U14 freeze（readkinds） | `kjob/g5rk-r23` 221d590a、docs のみ、純減 0 で保留 | **使わない**（下の §4 参照） |

局所統合（`git merge-tree` で確認した事実）: `kjob/g5tt-sync` は base に対して衝突なし。`kjob/g5rk-r23@5cbcdc6a` は `lakefile.lean` のみ add/add 衝突（Lean ファイルの衝突なし）。

## 1. 単位の選別（前提が減る単位だけ）

台帳 §5 の候補 ID のうち、型で示せたもの:

| 候補 | 判定 | 理由 |
|---|---|---|
| C.RK-5（`R : RunReadsAt …`、readkinds の前提） | **U2 に入れる** | `runReads_of_run` が `R` を作る。`R` は台帳で「分類: 入力条件（RR-1..RR-3 に帰着）」の指し示し行 |
| D.T-5（`hsh : ClosingShared …`） | **U1 に入れる** | `closingRun0_of_run` が `hsh`（= `.shared`）を作る |
| D.T-8（`hT2_FIELD` / `FieldRowAt`）、D.T-9（`houtTy`） | **U1 に入れる**（T-5 の下流） | 台帳は両方「組み立て済み、末端は T-5（T-9 は T-5 / T-6）」。`_ex` / `_group_kidW` は `FieldRowAt` と `houtTy` を `hsh` から導出し、binder に持たない |
| C.CR-1（`hrow`/`hord`）、C.CR-2（`hGen`）、C.CR-3（`hIH`/`hKI`）、非空虚性、depth0 `stop` | **入れない** | この流れでは減らない。供給元・経路が見つからなかった（R6 freeze §2、T2TIE_NEXT_FREEZE_R0 §1 rows 7,9,10,12,13）。**増えもしない**（下の §5 で既存 ID との対応を示す） |
| 「U-B / U-C 包装」「`ClosingPremises`」等 | 入れない | 包装は供給に数えない（reviewer 承認済みの判断） |

## 2. 単位 U1: 実 run から `CallTie` まで（`hsh` を run 側の前提に置き換える）

新規ファイル: `Tools/ShippingGen5Flow1Tie.lean`（namespace `Tools.ShippingGen5Flow1Tie`）、`Tests/Gen5/Flow1TieCheck.lean`。
imports: `Tools.ShippingGen5T2TieCR2`（→ `T2TieCR`、`ClosingRun2`、`T1ND` を含む）。`set_option autoImplicit false`。

ambient（`Tools/ShippingGen5T2TieCR2.lean` と同一、逐語）:
```lean
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
```
`ClosingRun0` / `closingRun0_of_run` は `Tools.ShippingGen5ClosingRun2.` で修飾する。

使う既存補題（実名・branch@SHA）:
- `Tools.ShippingGen5ClosingRun2.closingRun0_of_run`（kjob/flow1-a = g5cr-r6@f3a29dbb、ClosingRun2.lean:127）
- `Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_one_ex`（kjob/g5tt-sync@632f365d、T2TieCR2.lean:83）
- `Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_group_kidW`（同、:101）

### U1a 一人出力（`instFields = []`）
```lean
theorem callTie_of_run_one_ex
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (h1 : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hOW : OneOutWidth P p k) :
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk
```
証明: `Tools.ShippingGen5T2TieCR2.callTie_of_closingShared_one_ex hT hR hP
  (Tools.ShippingGen5ClosingRun2.closingRun0_of_run L P Reach DataOk hord hT hR hP hs hd0 hIH hKI hrun Gen hGen).shared h1 k hk hnone hDG_SEM hOW`。
（`closingRun0_of_run` の binder 並びを逐語でそのまま渡す。`ClosingRun0.shared` は field。）

### U1b group parent（`instFields ≠ []`）
```lean
theorem callTie_of_run_group_kidW
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR')
    (hG : p.d.shape.instFields ≠ []) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_SEM : ∀ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q → GenExtAtCall p q k hk)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) :
    ∃ q : Pkg ι dom, P (p.d.shape.insts[k]'hk).1 = some q ∧ CallTie p q k hk
```
証明: `callTie_of_closingShared_group_kidW hT hR hP (closingRun0_of_run … ).shared hG k hk hnone hDG_SEM hkidW`（同じ `closingRun0_of_run` の引数）。
（`hord` は group では使われないが、`closingRun0_of_run` が要求するので binder に残す。台帳 C.CR-1 / T-12 の `hord` と同じ行。）

### U1 の台帳差分
両形（U1a, U1b）が揃って初めて T-5 の `hsh` が FG 側の `CallTie` 組み立てのどの経路にも出なくなる。U1a だけ、または U1b だけでは T-5 は消えない（もう一方の経路で `hsh` が残る）。

| 台帳 ID | U1 の前後 | 説明 |
|---|---|---|
| D.T-5（`hsh` / `hDG_CLOSINGRUN` = `ClosingShared`/`ClosingRun0`） | **消える（-1）**。前提としては run 側の前提（下表）に置き換わる | `ClosingShared` を `closingRun0_of_run` が作る。台帳の分類も「dg-closingrun の `ClosingRun.shared` の指し示し行」 |
| D.T-8（`FieldRowAt`） | **消える（-1）**（T-5 の下流の組み立て済み行） | `FieldRowAt` は `servedCall_of_closingShared_{one,group}` が `hsh` から導出。U1 の binder に無い |
| D.T-9（`houtTy`） | **消える（-1）**（末端が T-5 / T-6 の組み立て済み行。T-6 は残る） | `houtTy_of_closingND` が `hT` と `hsh`（run 由来）から導出。U1 の binder に無い |
| 増える前提 | **0 ブロック** | 新 binder はすべて既存 ID に対応（下表）。新しい名前・型を持つ前提は無い |

U1 の新 binder と既存台帳 ID の対応（binder の数は増えるがブロック数は増えない）:

| U1 の binder | 既存 ID | 状態（変わらない） |
|---|---|---|
| `hord` | C.CR-1（T-12 に束ねられた行） | 未供給。経路が見つからなかった |
| `Gen`/`hGen` | C.CR-2（T-12） | 未供給 |
| `hIH`, `hKI` | C.CR-3（T-12） | 未供給 |
| `hs`, `hd0`, `hrun` | T-12 の statement-level 行（FG の `Start`/`RunsTo` 仮定そのもの）、C.RR-1/RR-2 | 入力条件 |
| `hT` | D.T-6 / C.CR-4（T1 台帳） | T1 側。不変 |
| `hDG_SEM`, `hOW`, `hkidW` | D.T-1, D.T-3, D.T-4 | 不変（これらは U1 以前から `_ex` / `_group_kidW` の binder） |

注: 台帳が T-8/T-9 を独立ブロックと数えているのでそれに従って -1 ずつとしたが、両者は「組み立て済み」行で、T-5 の下流であるにすぎない。
数え方は reviewer が確認する（最小の読み: T-5 のみ -1、最大の読み: T-5/T-8/T-9 の -3）。**実装前は何も消えたとは数えない。**

## 3. 単位 U2: `R : RunReadsAt` を run 側の前提に置き換える（readkinds U13 の上に）

新規ファイル: `Tools/ShippingGen5Flow1Reads.lean`（namespace `Tools.ShippingGen5Flow1Reads`）、`Tests/Gen5/Flow1ReadsCheck.lean`。
imports: `Tools.ShippingGen5ReadKindsU13`、`Tools.ShippingGen5RunReads`。`set_option autoImplicit false`。
open（`Tools/ShippingGen5RunReads.lean:12-31` の open を逐語、さらに）: `Tools.ShippingMachineCommand`、`Tools.ShippingGen5ReadKinds`。
`variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}`（RunReads.lean と同じ）。

使う既存補題:
- `Tools.ShippingGen5RunReads.runReads_of_run`（kjob/flow1-a = f3a29dbb、RunReads.lean:181）
- `Tools.ShippingGen5ReadKindsU13.readMachine_agrees_runReads_of_head_self`（kjob/g5rk-r23@5cbcdc6a）

```lean
theorem readMachine_agrees_of_run {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X) :
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape
```
証明: `obtain ⟨b, ci, envR, envR', w5, w6, R, -⟩ := runReads_of_run O hA hw hc hr entry closes`、続いて
`⟨b, ci, envR, envR', w5, w6, R, readMachine_agrees_runReads_of_head_self hk hHead hrun R h0s hX⟩`（U13 の結論 2 つ組を `And` に分ける）。
`JQC O (D₀+1) w5` は結論に出さない（U13 が要らない）。

### U2 の台帳差分
| 台帳 ID | U2 の前後 | 説明 |
|---|---|---|
| C.RK-5（`R : RunReadsAt …`） | **消える（-1）** | `R` は `runReads_of_run` が作る。台帳の分類は「入力条件（RR-1..RR-3 に帰着）」の指し示し行 |
| 増える前提 | **0 ブロック** | 新 binder `O`, `hA`, `hw`, `hc`, `hr`, `entry`, `closes` は C.RR-1（`hA`/`hw`/`hc`）、C.RR-2（`hr`）、C.RR-3（`entry`/`closes`）に対応。これらは既存ブロックで、U1 の `hs`/`hd0`/`hrun`/`hT.defines`/`hT.closes` と同じ行 |
| 残る | `hk`, `hHead`, `h0s`, `hrun`（readMachine の run）, `hX` | 不変。U14 は使わない（§4） |

注: U2 は binder の個数を増やす（1 → 7）。ブロック数が減るのは、増えた binder が C.RR-1..3 として既に数えられている行だから。`h0s`（run 開始 world の tie、DG-ENV C0）は `ws` と `w` の 2 つの run の間の tie で、U2 でも残る。

## 4. 使わないもの

- readkinds U14 freeze（221d590a）: 純減 0・reviewer 保留中。この流れの単位に入れない。承認後に統合する場合は別途 branch@SHA を書く。
- `kjob/g5env-*`（dg-env）: この流れは使わない。`MachineDefinesR`（EnvR）への置き換えは入れない。

## 5. 流れ全体の台帳差分

| 項目 | 予定 |
|---|---|
| FG 側から消える ID | C.RK-5（U2）、D.T-5、D.T-8、D.T-9（U1）。読み方により最小 -2、最大 -4（§2 の注） |
| FG 側に増える ID（新しい名前・型） | **0** |
| 前提台帳の現在件数 | FG 110 / T1 62 |
| 流れ完了後の予定（実装・承認後、数え方の確認後に確定） | FG 106..108 / T1 62（T1 側の ID は変わらない: `hT`、`IHAt` 等は不変） |
| 残る（この流れでは減らない） | C.CR-1（`hrow`/`hord`）、C.CR-2（`hGen`）、C.CR-3（`hIH`/`hKI`）、非空虚性、depth0 `stop`、`hk`/`hHead`/`h0s`（readkinds）、T-1/T-3/T-4（`hDG_SEM`, `hOW`, `hkidW`）、T-6/T-7 |
| 現時点（freeze 提出時）の実際の件数変化 | **FG -0 +0 / T1 -0 +0**（Lean 未実装。消えたとは数えない） |

純減の根拠は「`hsh`・`R` という、実 run から作れる結論を前提として取っていた binder を、その run の既存前提（既に台帳にある行）に置き換える」ことであり、
新しい供給（`hord`/`hGen`/`hIH`/`hKI`/非空虚性/`stop` の経路）を作ったわけではない。これらは未供給のまま。

## 6. 実装・検証計画（承認後）

- 単位ごとに Lean を commit（U1 → U2）。各 commit 後 Issue は `doing` のまま、note に「build は coder」と書く。header 同期だけの変更は review に出さない。
- **局所統合（coder が担当、私は実施しない）**: U1 の build には `kjob/g5tt-sync` 632f365d（衝突なし）、U2 の build には `kjob/g5rk-r23` 5cbcdc6a（`lakefile.lean` のみ衝突）が必要。
  両 branch を取り込んだ作業 branch の SHA は coder が note に書く。この時点で私は止まる。
- Pod build は `kjob lake build Tools.ShippingGen5Flow1Tie`、`Tests.Gen5.Flow1TieCheck`、`Tools.ShippingGen5Flow1Reads`、`Tests.Gen5.Flow1ReadsCheck` を 1 つずつ。
- Check（ClosingRun2Check と同じ方式、凍結型から独立に書く）: 独立 Expected 型と同一 reducible comparator（正対照・負対照: `hsh` を持つ型 / `R` を持つ型は受理されない）、
  well-typed 1 点 mutant（`hs`/`hd0`/`hrun`/`hGen`/`hord` を落とす、`ws`↔`w` の取り違え、結論の `r.shape = shape` を落とす 等。signature/defeq 棄却）、
  closure（`closingRun0_of_run`、`callTie_of_closingShared_one_ex`、`callTie_of_closingShared_group_kidW`、`runReads_of_run`、`readMachine_agrees_runReads_of_head_self` に到達することを assert、未解決名は throw と負例）、
  axioms 標準のみ、sorry なし。
- 実装時に型が通らない場合は、前提を足さず変更要求として報告する。
