# AUDIT carrier freeze（B-AUD: g / ds / S の 1 本の固定と D.E-1〜9, D.E-12 の完全型）

Issue: `sparkle-audit-carrier`（親 `sparkle-ledger-shorten`）。base: `par/ledger-shorten` 628f30c5。docs only。Lean のソースは編集していない。
読んだもの: `LEDGER_SHORTEN_PLAN.md`（B-AUD、E0）、`PREMISE_LEDGER.md` §8.2/§8.3、`premise_ledger/D_M5t2.md` §5、`kjob/g5ba-r16`（`BOUNDARY_AUDIT_FREEZE.md` と U2〜U8、`Tools/ShippingGen5NameKids{,2..7}.lean`）、`Tools/ShippingGen5FG.lean`（`TgtRun`）、`Tools/ShippingSrm15Graph.lean`、`Tools/ShippingSrm3Callee.lean`、`Tools/ShippingCallsMemPinned.lean`、`Tools/ShippingDesignWriterRun.lean`。
「見つからなかった」は、この調査では供給元・経路が見つからなかったという意味で、不可能・導出不能とは書かない。mutant はこの文書では使っていない。
この文書は新しい前提・law・TRUSTED 境界・FG/保証の変更を提案しない。台帳: FG 103（U1 −3 は受理待ちで FG 100）/ T1 56（今回 0/0）。

## 0. 結論（先に）
1. 9 行の共通の理由「`g`, `ds`, `S` not fixed」は、次の 1 本の固定で解消できる（型の固定として。証明の供給ではない）。
   - `P := GP (envAt cref w)`、`Reach := TgtRun P declName`（PREMISE_LEDGER §8.3 の Q-F2 と同じ）。
   - `S c := (P c).map (·.d.shape)`（パッケージの shape。`T1Hyp.defines` が `MachineDefines` と結ぶもの）。
   - `ds : List (Name × MachineData)` と `B : Nat` を束縛する（`g := graphOf ds`）。`ds`, `B` は新しい束縛変数であり、それを述べる命題は E-7（`FirstOcc` による被覆）と E-8（`hnd`, `hr`）に既にある。
2. その carrier の上で、E-1〜9 と E-12 の完全型が `autoImplicit false` で elaborate できた（§2、§6）。
3. carrier を `Reach := TgtRun` に固定すると、scratch で次が証明できた（公理は標準 3 つのみ）: `ReachClosed` は `TgtRun` の構成子から無条件、`ReachSpans` は `GraphAgrees` から導出、`OrdPath` 版の E-9 は `TgtRun` 版の `GraphAgrees` から導出、E-1・E-2 は E-5 から導出。よって 9 行は葉 5 行（E-3, E-4, E-6, E-7, E-8）と派生 4 行（E-1, E-2, E-5, E-9）に分かれる（見込み。台帳の数は変えない。§5）。
4. D.E-4 のうち B5 だけがユーザー判断の候補（別資料 `scripts/gen5/AUDIT_B5_DECISION.md`）。B3/B4 は技術的な供給の問題で、判断は要らない。この freeze は B5 の判断を待たない。
5. 後続の最初の単位（§4 の U-A1）は NameKids U1〜U7（`kjob/g5ba-r16`）を base に統合してから実装する（base `par/ledger-shorten` には NameKids の Lean ファイルがない）。統合は coder の作業。

## 1. carrier（g / ds / S を束縛する完全型）

| 記号 | 型 | 出どころ（実 run から作れる形） |
|---|---|---|
| `P` | `Pkgs ι dom` | `GP (envAt cref w)`（FG_CONNECT の run `EntryWitness` の開始世界 `w`） |
| `Reach` | `Name → Prop` | `TgtRun P declName`（`Tools/ShippingGen5FG.lean:26`。top と、到達宣言の ordinary 呼び出し先の最小述語） |
| `S` | `Name → Option MachineShape` | `SOf P := fun c => (P c).map (fun q => q.d.shape)` |
| `ds` | `List (Name × MachineData)` | 新しい束縛。`FirstOcc ds c d` で `P c` の `d` に結ぶ（E-7）。run から `ds` を作る補題は、この調査では見つからなかった |
| `g` | `CallGraph` | `graphOf ds`（`Tools/ShippingSrm15Graph.lean`） |
| `B` | `Nat` | `declRank` の fuel（E-8 の `hr`） |
| `L` | `Laws mref cref` | E-3 と E-4 の B3/B4 だけが使う（`RealChildA L.O …`, `KidTA L.O …`） |

closing run との関係: `ClosingRun.run` は `RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'`（`Tools/ShippingGen5ClosingRun.lean`）。E-12 の `raw`, `D` はこの run のもの。E-1〜9 の `S` の `sp` は、`T1Hyp.defines` と `RunReadsAt.shapeEq`（`machineShape? … = some shape`）で run に結ばれる、という経路が候補だが、`P c = some q` と run の結び付けは A.P-06（`MachineDefines`）の行で、この freeze では供給しない。

## 2. D.E-1〜9, D.E-12 の完全型（scratch で elaborate 済み）
以下のソースは `audit_scratch.lean`（スクラッチ。ソースツリー外。NameKids U1〜U7 の本文を同じファイルの先頭に連結）から写した。名前 `MemTagsNamed`, `kidNameAt` は `Tools.ShippingGen5NameKids2`、`GraphAgrees`, `ReachSpans`, `OrdPath` は `…NameKids3`。
```lean
namespace Tools.ShippingGen5AuditCarrier
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm7Rank (CallGraph callees declRank InClass kidModName)
open Tools.ShippingSrm15Graph (graphOf FirstOcc)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids2 (MemTagsNamed kidNameAt)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachSpans OrdPath ReachClosed)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.ModuleName (ofDecl)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- carrier S: the shape of the package -/
def SOf (P : Pkgs ι dom) : Name → Option MachineShape := fun c => (P c).map (fun q => q.d.shape)

section Rows
variable (P : Pkgs ι dom) (Reach : Name → Prop)

def AuditE1 : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
      memKey (originAt sp k) ≠ none → memKey (originAt sp k) = memKey (originAt sp k') →
      (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1

def AuditE2 : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length), memKey (originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c

def AuditE3 (L : Laws mref cref) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length), (originAt sp k).child? = none →
      ∀ y : Tools.ShippingChildInv.Res,
        Tools.ShippingChildCacheA.RealChildA L.O (sp.insts[k]'hk).1 y →
        y.1.name = ofDecl (sp.insts[k]'hk).1

/-- B3 / B4 (with the `namesK` of `machineClosesAtA_of_memKids'`), per reached shape -/
def AuditE4_B3B4 (L : Laws mref cref) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∃ (nk : Nat → Nat) (outsK namesK : Nat → List String),
      (∀ (k : Nat) (hk : k < sp.insts.length) (y : Tools.ShippingChildInv.Res),
        Tools.ShippingCallsMemA.KidTA L.O (originAt sp k) (sp.insts[k]'hk).1 y →
        Tools.ShippingMemCloses.ChildIfaceP (kidNameAt sp k) (nk k) (outsK k) (namesK k) y.1 y.2) ∧
      (∀ (k : Nat), k < sp.insts.length → ofDecl c ∉ namesK k) ∧
      (∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
        ¬ ((sp.insts[k]'hk).1 = (sp.insts[k']'hk').1 ∧ memKey (originAt sp k) = memKey (originAt sp k')) →
        kidNameAt sp k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k')

def AuditE4_B5 : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (gi : Nat) (k : Nat), k < sp.insts.length → ∀ o ∈ sp.layout.outs,
      o.name ≠ s!"inst{gi}_{kidNameAt sp k}"

def AuditE5 (ds : List (Name × MachineData)) (B : Nat) (top : Name) : Prop :=
  GraphAgrees (graphOf ds) Reach (SOf P) ∧ ReachSpans (graphOf ds) top Reach ∧
  InClass (graphOf ds) B top = true ∧
  (∀ c, Reach c → ∀ sp, SOf P c = some sp → MemTagsNamed sp)

def AuditE6 : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
      (senv : StructEnv) (ai : Bool),
      Tools.ShippingReaderFuel.machineShapeF n sm ps ci senv ai = some (some sp)

def AuditE7 (ds : List (Name × MachineData)) : Prop :=
  ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ SOf P c = some d.shape

def AuditE8 (ds : List (Name × MachineData)) (B : Nat) (top : Name) : Prop :=
  (ds.map Prod.fst).eraseDups.length = ds.length ∧
  (declRank (graphOf ds) B top).isSome = true

def AuditE9 (ds : List (Name × MachineData)) (top : Name) : Prop :=
  GraphAgrees (graphOf ds) (OrdPath (graphOf ds) top) (SOf P)
end Rows

/-- E-12 over the core run of the entry start -/
def AuditE12 (declName : Name) (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) : Prop :=
  ∀ (w2 : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w2 →
    (∀ x ∈ D.modules, x.name ≠ raw.name) ∧ D.topModule = raw.name

```

行との対応:
| 行 | 型 | 備考 |
|---|---|---|
| D.E-1 | `AuditE1 P Reach` | `hmemSame`（U1 `hsep_of_kidNames` の前提）。`MemTagsNamed` から出る（U2 `hmemSame_of_memTagsNamed`） |
| D.E-2 | `AuditE2 P Reach` | `hself`。U3 `hself_all_reached` が `AuditE5` から出す |
| D.E-3 | `AuditE3 P Reach L` | `hn` の B7 部分。`hn_kidNameAt`（`nameK := kidNameAt`）は U2 で証明済みなので残るのはこの型 |
| D.E-4 B3/B4 | `AuditE4_B3B4 P Reach L` | `namesK` を存在量化。`hkid`（`ChildIfaceP`）が同じ `namesK` を縛るので型に含めた。`hkid` が D.E の別の行か T1 台帳のどこかの行かは、この調査では見つからなかった |
| D.E-4 B5 | `AuditE4_B5 P Reach` | `hfresh`（`outHead` はより強い版）。ユーザー判断の候補 |
| D.E-5 | `AuditE5 P Reach ds B top` | `hg ∧ hsp ∧ hin ∧ hmem` |
| D.E-6 | `AuditE6 P Reach` | `hF`。U4 `hmem_of_machineShapeF` の前提 |
| D.E-7 | `AuditE7 P Reach ds` | `hfo`。U5 `graphAgrees_of_firstOcc` の前提 |
| D.E-8 | `AuditE8 ds B top` | `hnd ∧ hr`。U6 `inClass_graphOf` の前提 |
| D.E-9 | `AuditE9 P ds top` | `OrdPath` 上の `GraphAgrees`。U7 `reachClosed_ordPath` の前提 |
| D.E-12 | `AuditE12 declName mctx cctx w` | `hno ∧ htop`（`writer_prints_endpoint_artifact` の前提）を core run `(raw, D)` の上で。E-12 は g/ds/S に依存せず、台帳の本文にも「carriers not fixed」の語はない。9 行の束に入れた理由は PLAN の B-AUD が 10 行としたため |

elaborate の出力（`#check`）は全 11 定義が型検査を通った（`error` 0。警告 1 つは NameKids3 既存の未使用変数 `r`）。ビルド: 依存を `kjob lake build`（9 ターゲット、779 jobs、exit 0）してから `kjob lake env lean` で elaborate した。

## 3. D.E-4: ユーザー判断が要るものを分ける
| 項 | ユーザー判断 | 理由 |
|---|---|---|
| B3 `hparentD` | 要らない | 親宣言名が子の設計のモジュール名に現れない、という call-graph/設計内容の事実。供給の問題（§4 U-A5） |
| B4 `hdisjD` | 要らない | 同上（2 つの子の設計の名前の互いに素） |
| B5 `hfresh` | 要る候補 | 出力名と配線名 `inst{gi}_…` の衝突。コンパイラ本体の検査は見つからなかった。範囲縮小・コンパイラ変更・証明のどれを採るかの判断。資料: `scripts/gen5/AUDIT_B5_DECISION.md` |
この freeze は B5 を決めない。B5 の判断を待たずに他の行は進む。

## 4. 後続の証明単位（行ごと）
| 単位 | 行 | 使う既存定理 | 見込みの差分 | 止まりそうな箇所 |
|---|---|---|---|---|
| U-A1 派生 | E-1, E-2, E-5(hsp), E-9 | NameKids3 `reach_of_ordEdges`, `hself_all_reached`、NameKids2 `hmemSame_of_memTagsNamed`、`Srm12Corr.instTagged_mem_idx`、`TgtRun.call` | 新規 Lean 1 ファイル 約 60 行。scratch で下記 8 定理が elaborate 済み（§6）。前提の増減 0。派生 4 行（E-1, E-2, E-5, E-9）は、葉が揃えば消える | NameKids U1〜U7（`kjob/g5ba-r16`）が base に無い。統合（coder）が先。`hself_all_reached` に未使用の暗黙引数 `r` があり `(r := 0)` が要る（型の変更ではない） |
| U-A2 hF | E-6 | NameKids4 `hmem_of_machineShapeF`、A.P-06 `MachineDefines`、C.CV-4（`h_C_CV4`） | `hF` を `h_A_P06` と `h_C_CV4` から作る。`machineShape? = some sp` を取り出す 3 つの run（`getConstInfo`, `getEnv`×2）の存在が新しい前提になり得る（+1 の見込み。未計数） | `h_C_CV4` の固定値 `false [] true` と `hF` の量化する `sm ps ai` の一致を Lean で確認していない |
| U-A3 ds | E-7, E-8 | NameKids5 `graphAgrees_of_firstOcc`、U8 freeze `graphAgrees_of_mem`（Lean 未実装）、NameKids6 `inClass_graphOf` | `ds` を `TgtRun` から作る補題が要る（供給元はこの調査では見つからなかった）。`hr`（呼び出しグラフの階数が定まる＝非再帰）の供給元も見つからなかった | `Reach` が有限で列挙できること。再帰がないことの根拠 |
| U-A4 B7 | E-3 | `Srm12Corr.kidTA_name`、`Srm4Core5` の `ChildIfaceP.name`、`LeafMissCoh` の `KeyTop` | `RealChildA L.O c y → y.1.name = ofDecl c` を run から。見込みは未計数 | 無条件の定理は見つからなかった（`BOUNDARY_AUDIT_FREEZE` §1.2 B7） |
| U-A5 B3/B4 | E-4 | `ChildIfaceP.desNames`, `machineClosesAtA_of_memKids'` | 子の設計内容（モジュール名集合）に関する事実。B7 の結果と call-graph の階数に依存 | 設計内容の供給元が見つからなかった |
| U-A6 B5 | E-4 | — | ユーザー判断後 | §3 |
| U-A7 G7-a | E-12 | `writer_prints_endpoint_artifact`、`ClosingRun.shared` の `CloseCalls`, `closeMachine` | `D = d₀`, `raw = closeMachine …` からの `hno`/`htop` の導出が候補（調べていない） | `CloseCalls` の本文を読んでいない |

## 5. E0 の 4 条件
| # | 条件 | この単位の状況 |
|---|---|---|
| 1 | 出力（型・carrier・定理名）を後続がそのまま使う。後続を Issue として先に登録し、依存を張る | 使う: `SOf`、`Audit*` 11 定義（§2）、U-A1 の 8 定理。**後続 Issue はまだ登録していない**（他 Issue の状態を変えない規則のため）。登録は reviewer/coder の承認後。未登録の間は E0 を満たしたと書かない |
| 2 | 消える行 ID と見込み差分を「解除:」「条件付き台帳:」で書く | 解除（見込み）: E-1, E-2, E-5, E-9（派生 4 行）。残る葉: E-3, E-4, E-6, E-7, E-8（5 行）。E-12 は別。条件付き台帳: FG 見込み −4（派生の組み立てが受理され、葉の型が変わらない場合）。台帳の現在値は変えない |
| 3 | 後続の最初の 1 単位の freeze を、受理から 1 往復以内に出す | U-A1 は scratch で elaborate 済みなので、受理後に freeze を出せる。ただし base に NameKids が無いので、統合の完了が前提。出せなければ止めて理由を書く |
| 4 | 新しい前提が増えるならその数を後続の減算見込みと並べる | 増える見込み: U-A2 の run 存在 +1（未計数）、`ds` の束縛 0（E-7 の内容）。減算見込み 4。見込み（4）が増分（≤1）より大きいので、暫定的に例外の条件を満たす。ただし U-A3 の `hr`/有限性が新前提になると変わる |

## 6. scratch の検証（Lean は編集していない）
- `kjob lake env lean`（スクラッチファイル 1 本、ソースツリー外）で elaborate。`#print axioms` は下の 8 定理（`auditE5_of_parts` は `auditE5_tgtRun` 経由）すべて `[propext, Classical.choice, Quot.sound]`。`sorry` なし。
- 下の定理は、U-A1 の候補の本文（承認後の単位で使う）。
```lean
section Derive
variable (P : Pkgs ι dom) (top : Name)

private theorem memKey_none_of_child {o : InstOrigin} (h : o.child? = none) : memKey o = none := by
  cases o with
  | ord => rfl
  | field i => rfl
  | mem cb aw dw => simp [InstOrigin.child?] at h

theorem reachClosed_tgtRun : ReachClosed (TgtRun P top) (SOf P) := by
  intro c hc sp hS k hk hch
  simp only [SOf] at hS
  cases hP : P c with
  | none => rw [hP] at hS; cases hS
  | some q =>
    rw [hP] at hS
    have e : q.d.shape = sp := Option.some.inj hS
    subst e
    exact TgtRun.call hc hP k hk hch

theorem reachSpans_tgtRun {g : CallGraph} (hg : GraphAgrees g (TgtRun P top) (SOf P)) :
    ReachSpans g top (TgtRun P top) := by
  intro c hc
  induction hc with
  | top => exact OrdPath.refl
  | @call c' q hc' hq k hk ord ih =>
    have h1 := hg c' hc'
    simp only [SOf, hq] at h1
    exact OrdPath.step ih ⟨q.d.shape.instTagged, originAt q.d.shape k, h1,
      Tools.ShippingSrm12Corr.instTagged_mem_idx q.d.shape hk, memKey_none_of_child ord⟩

theorem tgtRun_iff_ordPath {g : CallGraph} (hg : GraphAgrees g (TgtRun P top) (SOf P)) (c : Name) :
    TgtRun P top c ↔ OrdPath g top c :=
  ⟨reachSpans_tgtRun P top hg c,
   fun h => reach_of_ordEdges hg (reachClosed_tgtRun P top) TgtRun.top h⟩

theorem auditE9_of_tgtRun {ds : List (Name × MachineData)}
    (hg : GraphAgrees (graphOf ds) (TgtRun P top) (SOf P)) : AuditE9 P ds top :=
  fun c hc => hg c ((tgtRun_iff_ordPath P top hg c).2 hc)

end Derive

section Derive2
variable (P : Pkgs ι dom) (Reach : Name → Prop)

theorem auditE1_of_E5 {ds B top} (h : AuditE5 P Reach ds B top) : AuditE1 P Reach :=
  fun c hc sp hS k hk k' hk' hne hkey =>
    hmemSame_of_memTagsNamed sp (h.2.2.2 c hc sp hS) k hk k' hk' hne hkey

theorem auditE2_of_E5 {ds B top} (h : AuditE5 P Reach ds B top) : AuditE2 P Reach :=
  fun c hc sp hS k hk hm => hself_all_reached (r := 0) h.2.2.1 h.1 h.2.1 c hc sp hS k hk hm

theorem auditE5_of_parts {ds B top} (hfo : AuditE7 P Reach ds) (hnr : AuditE8 ds B top)
    (hsp : ReachSpans (graphOf ds) top Reach) (hF : AuditE6 P Reach) : AuditE5 P Reach ds B top :=
  ⟨Tools.ShippingGen5NameKids5.graphAgrees_of_firstOcc hfo, hsp,
   Tools.ShippingGen5NameKids6.inClass_graphOf hnr.1 hnr.2,
   Tools.ShippingGen5NameKids4.hmem_of_machineShapeF hF⟩

-- the all-reached name facts of U3 in the carrier shape (the E-1 / E-2 consumer)
#check @Tools.ShippingGen5NameKids3.sepK_parent_all_reached
end Derive2

/-- full chain for Reach := TgtRun: E-7, E-8, E-6 (and nothing about ReachSpans) give E-5, E-9 -/
theorem auditE5_tgtRun {P : Pkgs ι dom} {top : Name} {ds : List (Name × MachineData)} {B : Nat}
    (hfo : AuditE7 P (TgtRun P top) ds) (hnr : AuditE8 ds B top) (hF : AuditE6 P (TgtRun P top)) :
    AuditE5 P (TgtRun P top) ds B top ∧ AuditE9 P ds top := by
  have hg := Tools.ShippingGen5NameKids5.graphAgrees_of_firstOcc hfo
  exact ⟨auditE5_of_parts P _ hfo hnr (reachSpans_tgtRun P top hg) hF, auditE9_of_tgtRun P top hg⟩

```
- 注意: これらの証明は `Reach := TgtRun` でのみ成り立つ。`Reach` を別の述語に固定する場合は E-9 と `ReachSpans` の派生は成り立たない。

## 7. この freeze が主張しないこと
9 行のどれの供給も、非空虚性も、`ds`/`hr` の供給元も、run と `P c = some q` の結び付けも主張しない。型の固定と、導出関係（派生 4 行）の scratch での確認だけである。FG・T1・M5 の完了は主張しない。
