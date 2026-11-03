# GATE carrier freeze（B-GATE: ReflectsAll の gate route の 1 本の carrier と 8 行の完全型）

Issue: `sparkle-gen4-gate-supply`（束 B-GATE。親 `sparkle-ledger-shorten`）。base: `par/ledger-shorten` 628f30c5。docs only。Lean のソースは編集していない（scratch は §9）。
読んだもの: `LEDGER_SHORTEN_PLAN.md`（B-GATE、E0）、`PREMISE_LEDGER.md` §8.2/§8.3、`premise_ledger/B_M4.md` §2、`GENERAL_SPEC.md` §1.1/§6、既存の B-AUD 版 `AUDIT_CARRIER_FREEZE.md`（par/aud-int 610a43a3。書式だけ参照）、`kjob/g4gate-g6`（0fb0d739）の `Tools/ShippingGen4{Iface,GateLeaf,GateIface,GatePortW,GateOutTy,FirstLeaf,InstParent}.lean` と `scripts/gen4/GATE_*_FREEZE.md`、`Tools/ShippingGateDefines.lean`、`Tools/ShippingGateParentRunG.lean`、`kjob/g5dc-r23`（0fcce4e7）の `Tools/ShippingGen5FG.lean`。
「見つからなかった」は、この調査では供給元・経路が見つからなかったという意味で、不可能・導出不能とは書かない。mutant はこの文書では使っていない（使うときは signature/defeq での棄却であって意味的反例ではない）。
この文書は新しい前提・law・TRUSTED 境界・FG/保証の変更を提案しない。§8 の Pkg / T1Hyp の route 拡張は「事前レビューの対象として明示する」だけで、決めない。台帳: FG 95 / T1 56（今回 0/0）。

## 0. 結論（先に）
1. **base のドリフト（重要）。** 受理済みの gate 系 Lean（`kjob/g4gate-g6` の U-G1 `ChildIface`、U-G2 `GateLeaf`、`FirstLeaf`、U-G7a T2）は、旧 base（d0ddc50b）の `ShipsRes` / `ChildShips` に対して書かれている。base（628f30c5）の `Tools/ShippingGen2Defs.lean` は S1 / S3 の後で、`ChildShips` に第 1 連言 `ChildPortWidths`（Defs:83、使用 :93）、`ShipsRes` に第 3 連言 `InstClosed`（Defs:148 付近）が入っている。実際に base へ持ち込んで `kjob lake build` すると、`GateLeaf`（`gate_combChildRunN`）は通るが、`Iface` / `GateIface` / `FirstLeaf` / `InstParent` は型エラーになった（§1。`GateOutTy` は自身の変更なしで、直した `GateIface` の上で通った）。すなわち、gate 系の既存の受理は base 上では U-G1R / U-G2R の再検証が要る。直しは小さい（変更行 5〜45 行、前提の増減 0。ただし instance 付き親の T2 だけは新しい入力 `ChildPortWidthsI J m` が要る。§5）。
2. **carrier は 1 本。** `GateTable := Name → Option GateRec`（`GateRec` = route 2 の `GateData` または route 1 の `FirstData`）。既存の `GateLeaf` を「データ `GateData` ＋ 5 つの反射 Prop（`Old` / `Peel` / `He` / `Hb` / `Hv`）」に分け、各反射 Prop を台帳の行（B.G-3/4/5/6）に 1 対 1 で対応させる。`Q` は表から作る（`gateQ`）。
3. **8 行の完全型を、この carrier の上で `autoImplicit false` のもと elaborate できた**（§3、§9）。主定理 `gateReflects_shipsResI` を scratch で証明できた: `GateReflects`（7 つの行述語の連言）と `RealChildA` から、`Q := gateQ GT` に対する `ShipsResI`（`InstClosed` つき）が出る。公理は標準 3 つのみ。これにより **B.G-9 の `Q` / `hQ` は前提ではなく定義＋補題になる**（`hQ` は `gateLeaf_outTy` から出る）。
4. **証明では消えない行がある。** B.G-1/3/4/5/6/7 は「宣言の値についての反射」で、`GateDefines` の説明（`Tools/ShippingGateDefines.lean` の header）のとおり、生成器が宣言ごとの binder として束縛するもので、証明で払う設計ではない。したがって 8 行のうち、型の固定のあとに証明で消せる見込みがあるのは B.G-9（−1、ただし §8 の事前レビューが通る場合）だけで、残りの 6 行＋D.D-1 は「`GateReflects` という 1 つの名前付き条件に束ねる」ことまでが技術的な成果になる。束ねた結果を台帳で何行と数えるかは数え方の変更なので、reviewer / ユーザーの判断事項（§7 の C-1）。この freeze は数を変えない。
5. **`GateReflects` だけでは空虚に成り立つ**（`gateReflects_empty`: 表が空でも成り立つ）。「到達した gate 経路の宣言は表に載る」という被覆の連言（`GateCovers`）は、`ReflectsAll` の型に到達宣言 `Reach` が入っていないため（`ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop`、`Tools/ShippingGen5FG.lean:30`、kjob/g5dc-r23）まだ型を書けない。これは D.D-1 の残りとして残し、§8 の事前レビュー項目 P2 に挙げる。
6. 後続の最初の単位 U-GC0（base への移送と U-G1R / U-G2R）は、この freeze の承認後 1 往復以内に freeze を出せる（型は scratch で確認済み。§6）。

## 1. base のドリフト（U-G1R / U-G2R の根拠）
`git diff kjob/g4gate-g6 par/ledger-shorten -- Tools/ShippingGen2Defs.lean` の関係部分:
| 定義 | 旧 base（g6） | base 628f30c5 | 影響 |
|---|---|---|---|
| `ChildShips q n mc Dc` | `∀ dsn, … ChildRunN …` | `ChildPortWidths q mc ∧ ∀ dsn, …`（Defs:92-96、`ChildPortWidths` は :83） | `ChildShipsI` に第 1 連言が必要 |
| `ShipsRes L P c r` | `RealChildA ∧ ∃ q n, …` | `RealChildA ∧ (∃ q n, …) ∧ InstClosed r`（Defs:148） | `ShipsResI` に第 3 連言が必要 |

base に `kjob/g4gate-g6` の 7 ファイルを（コミットせずに）置いて build した結果:
| ファイル | 旧 g6 の判定 | base での結果 | 直し（scratch で build まで通した） |
|---|---|---|---|
| `Tools/ShippingGen4Iface.lean`（U-G1） | 受理済み | 型エラー（`ChildShipsI` / `ShipsResI` を使う箇所） | 下の diff。`childShipsI_ofPkg` は `Iff.rfl` のまま、`shipsResI_iface` は `and_congr_left` を足すだけ |
| `Tools/ShippingGen4GateLeaf.lean`（`gate_combChildRunN`） | 受理済み | 変更なしで通った | なし（`ChildShips` を使わないため） |
| `Tools/ShippingGen4GateIface.lean`（U-G2） | 受理済み | 型エラー | `gateLeaf_childPortWidthsI`（GatePortW:29 の本体）を `gateLeaf_childShips` の前に置き、`ChildShipsI` の第 1 連言に使う。`gateLeaf_shipsResI` に `InstClosed y` を引数で足し、`_of_real` は `hm : y.2.modules = []` から `InstClosed` を作る補題 `instClosed_of_nil` で払う（変更 約 30 行） |
| `Tools/ShippingGen4GatePortW.lean` | 受理済み | 上の移動で空になる | `ChildPortWidthsI` は Iface へ、定理は GateIface へ移す |
| `Tools/ShippingGen4GateOutTy.lean` | 受理済み | 変更なしで通った | なし |
| `Tools/ShippingGen4FirstLeaf.lean` | 受理済み | 型エラー | `firstLeaf_childPortWidthsI` を `firstLeaf_childShips` の前に移し、同じ形で `InstClosed` を足す（変更 約 45 行） |
| `Tools/ShippingGen4InstParent.lean`（U-G7a） | T1/InstCore/T2 を条件付き部品として承認 | T1 は通る。T2 `instParent_childShipsI` は型エラー | `ChildShipsI J (k+1) m …` の第 1 連言 `ChildPortWidthsI J m` を作る材料が `InstCore` に無い。scratch では仮説 `(hpw : ChildPortWidthsI J m)` を足すと通る（§5 の差 D5） |
Iface の diff（これで 5 行）:
```diff
 def ChildShipsI (I : ChildIface ι) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design) : Prop :=
+  ChildPortWidthsI I mc ∧
   ∀ (dsn : Design), ...
 def ShipsResI ... : Prop :=
-  RealChildA L.O c r ∧ ∃ (I : ChildIface ι) (n : Nat), Q c = some I ∧ I.decl = c ∧ ChildShipsI I n r.1 r.2
+  RealChildA L.O c r ∧ (∃ (I : ChildIface ι) (n : Nat), Q c = some I ∧ I.decl = c ∧ ChildShipsI I n r.1 r.2) ∧ InstClosed r
 -- shipsResI_iface: `and_congr_right fun _ => and_congr_left fun _ => ?_` (本体は同じ)
+def ChildPortWidthsI (I : ChildIface ι) (mc : Sparkle.IR.AST.Module) : Prop :=   -- GatePortW.lean:22 から Iface へ移す
+  (Tools.ShippingMachineCompose.argPorts mc).map (fun p => p.ty.bitWidth) =
+    I.ports.map (fun b => (Tools.ShippingMachineEntry.kindTy b.2).bitWidth)
```
注意: この移送は「バイト同一の移送」ではないので、旧 U-G2 の承認（GATE_U2_FREEZE D1）の範囲外。U-GC0 として別に freeze する（§6）。ここで確認したのは、直しが小さく、前提の増減が 0 であること（`InstClosed` は空の `modules` から自明、`ChildPortWidthsI` は既存の証明の移動）。

## 2. carrier（1 本）
| 記号 | 型 | 出どころ |
|---|---|---|
| `GateData` | 構造体（`decl value domE bs kb kv vw bpos vpos srt e`。反射 Prop を含まない） | `GateLeaf`（`kjob/g4gate-g6` `Tools/ShippingGen4GateIface.lean:30`）から 5 つの Prop フィールドを除いたもの |
| `GateData.Old / Peel / He / Hb / Hv` | `GateLeaf.old / peel / he / hb / hv` と同じ文（`g.value` 等で書き直しただけ） | B.G-3 / 4 / 5 / 6 |
| `FirstData` | 構造体（`decl dn names n fe`） | `FirstLeaf`（`Tools/ShippingGen4FirstLeaf.lean:36`）から `hwf`, `hn` を除いたもの |
| `GateRec` | `mixed (g : GateData) ∣ first (f : FirstData)` | route 2 / route 1。B.G-1 の統合先 B.G-8 / F-6 / F-7 が route 1 側 |
| `GateTable` | `Name → Option GateRec` | route table の gate 部分。供給元は D.D-1 の構成（§8 P2） |
| `GateRec.iface ι` / `gateQ ι GT` | `ChildIface ι` / `IfaceMap ι` | `GateLeaf.ifaceOf g (.bitVector g.srt.width)` と `FirstLeaf.ifaceOf`。出力型は `gateLeaf_outTy`（GateOutTy:21）が幅 ≠ 1 で与える `bitVector srt.width`、route 1 は `first_full_outputs`（`bitVector n`） |
| `mref cref` | `ST.Ref …` | `EntryDefines` の添字。`ReflectsAll` の `Laws mref cref` と同じ |
`mctx cctx` は carrier に入れない。`EntryDefines` は文脈に依らない（`EntryDefines.ctx`、`Tools/ShippingReflectCtx.lean:85`）ので、行の型は `∀ mctx cctx` で書く（どれか 1 つで払えば全部で払える）。
`ι` は `GateLeaf` 自体には現れない（ファントム）。`ChildIface ι` と `IfaceMap ι` にだけ現れる。

## 3. 8 行の完全型（carrier 上、scratch で elaborate 済み。出力は §9）
| 行 | ledger の文 | carrier 上の型（名前は §3.1 の Lean） |
|---|---|---|
| B.G-1 `entry`（B.G-8, F-6, F-7 を含む） | gate / first-gate の `EntryDefines` | `GateEntryRow mref cref GT := ∀ c r, GT c = some r → r.decl = c ∧ ∀ mctx cctx, EntryDefines mctx mref cctx cref c r.value`。route 1 の追加データ（F-7 `hwf` / `hn`）は `GateFirstDataRow GT`。B.G-1 の 1 行に束ねたもの（B_M4 の別名表のとおり） |
| B.G-3 `GateLeaf.old` | 旧 first gate が受理しない | `GateOldRow GT := ∀ c g, GT c = some (.mixed g) → g.Old`、`g.Old := ∀ d : DefinitionVal, d.value = g.value → certifiedShape? false [] (.defnInfo d) = none` |
| B.G-4 `GateLeaf.peel` | mixed gate の peel | `GatePeelRow GT`、`g.Peel := mixedGatePeel g.value = some (g.bs, quote g.domE (…bpos…) (…vpos…) g.e)` |
| B.G-5 `GateLeaf.he` | 式の整形 | `GateHeRow GT`、`g.He := g.e.WF g.kb g.kv g.vw` |
| B.G-6 `GateLeaf.hb` / `hv` | 位置の束縛型 | `GateHbvRow GT`、`g.Hb ∧ g.Hv`（2 フィールドを 1 述語に束ねた。台帳の「2フィールド」と同じ範囲） |
| B.G-7 `hw1` | 幅 ≠ 1 | `GateWidthRow GT := ∀ c g, GT c = some (.mixed g) → g.srt.width ≠ 1`。幅 1 の供給元はこの調査では見つからなかった（GateOutTy header と同じ） |
| B.G-9 `Q` / `hQ` | route table | `Q` は前提ではなく `gateQ ι GT`。`hQ` は `gateReflects_shipsResI` の中で `gateLeaf_outTy`（幅 ≠ 1）から出る。route table の assembler は `gateQ` そのもの（gate 部分）。他 route の部分は B-PARAM / fallback の `Q` で、この freeze は触らない |
| D.D-1 `ReflectsAll` | 型だけ（Gen5FG:30） | gate 成分 `GateReflects mref cref GT`（上の 7 述語の連言）。`ReflectsAll` への埋め込みは §8 P2（被覆 `GateCovers` が未固定のため、`∃ GT, GateReflects GT ∧ GateCovers …` の形にできる、というところまで） |
行の述語の表現上の注意: 台帳は B.G-3〜6 を `GateLeaf` の「フィールド」として記録している。ここでは `GateLeaf` を `GateData.toLeaf`（5 つの Prop を引数に取る）で作る形に分け、`toLeaf_data : (GateLeaf.data g).toLeaf g.old … = g` が `rfl` で通ること（scratch）で、旧 `GateLeaf` と同じ情報であることを確認した。

### 3.1 carrier と 8 行の Lean（scratch から写した。`kjob lake env lean` で elaborate 済み）
```lean
import Tools.ShippingGen4GateOutTy   -- base-ported (§1)
import Tools.ShippingGen4FirstLeaf   -- base-ported (§1)
set_option autoImplicit false

namespace Tools.ShippingGen4GateCarrier
open Lean Meta Sparkle.Compiler.Elab
open Sparkle.IR.Type (HWType)
open Tools.ShippingGen2
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildInv (Res)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingUnifiedSource (SType Term quote)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingEntrySoundness (FExpr quoteDecl)

variable {ι : Type}
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- the data of a mixed gate leaf WITHOUT the five reflected facts (those are the rows B.G-3..6) -/
structure GateData where
  decl : Name
  value : Lean.Expr
  domE : Lean.Expr
  bs : List (Name × MixedGateBinder)
  kb : Nat
  kv : Nat
  vw : Nat → Nat
  bpos : Nat → Nat
  vpos : Nat → Nat
  srt : SType
  e : Term srt

def GateData.Old (g : GateData) : Prop :=
  ∀ d : Lean.DefinitionVal, d.value = g.value → certifiedShape? false [] (.defnInfo d) = none
def GateData.Peel (g : GateData) : Prop :=
  mixedGatePeel g.value = some (g.bs, quote g.domE (fun j => inputExpr g.bs.length (g.bpos j)) (fun j => inputExpr g.bs.length (g.vpos j)) g.e)
def GateData.He (g : GateData) : Prop := g.e.WF g.kb g.kv g.vw
def GateData.Hb (g : GateData) : Prop := ∀ j, j < g.kb → ∃ name, g.bs[g.bpos j]? = some (name, .bool)
def GateData.Hv (g : GateData) : Prop := ∀ j, j < g.kv → ∃ name, g.bs[g.vpos j]? = some (name, .bits (g.vw j))

def GateData.toLeaf (g : GateData) (old : g.Old) (peel : g.Peel) (he : g.He) (hb : g.Hb) (hv : g.Hv) : GateLeaf ι :=
  ⟨g.decl, g.value, g.domE, g.bs, g.kb, g.kv, g.vw, g.bpos, g.vpos, g.srt, g.e, old, peel, he, hb, hv⟩

def GateLeaf.data (g : GateLeaf ι) : GateData :=
  ⟨g.decl, g.value, g.domE, g.bs, g.kb, g.kv, g.vw, g.bpos, g.vpos, g.srt, g.e⟩

/-- first-gate leaf data WITHOUT hwf / hn -/
structure FirstData where
  decl : Name
  dn : Name
  names : List Name
  n : Nat
  fe : FExpr

def FirstData.value (f : FirstData) : Lean.Expr := quoteDecl f.dn f.names f.n f.fe
def FirstData.toLeaf (f : FirstData) (hwf : f.fe.WF f.names.length f.n) (hn : 0 < f.n) : FirstLeaf ι :=
  ⟨f.decl, f.dn, f.names, f.n, f.fe, hwf, hn⟩

/-- one entry of the gate table: route 2 (mixed gate) or route 1 (first gate) -/
inductive GateRec
  | mixed (g : GateData)
  | first (f : FirstData)

def GateRec.decl : GateRec → Name
  | .mixed g => g.decl
  | .first f => f.decl
def GateRec.value : GateRec → Lean.Expr
  | .mixed g => g.value
  | .first f => f.value
noncomputable def GateRec.iface (ι : Type) : GateRec → ChildIface ι
  | .mixed g => ⟨g.decl, g.bs, [GateLeaf.outField (.bitVector g.srt.width)], fun _ => gateS g.bs g.e g.bpos g.vpos⟩
  | .first f => ⟨f.decl, Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n, [GateLeaf.outField (.bitVector f.n)], fun _ => gateS (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n) (Tools.ShippingUnifiedSource.ofF f.n f.fe) (fun _ => 0) (fun j => j + 1)⟩

abbrev GateTable := Name → Option GateRec

noncomputable def gateQ (ι : Type) (GT : GateTable) : IfaceMap ι := fun c => (GT c).map (GateRec.iface ι)

/-- B.G-1 (and B.G-8, F-6, F-7 merged): naming, entry, and for route 1 the two data facts -/
def GateEntryRow (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) (GT : GateTable) : Prop :=
  ∀ c r, GT c = some r → r.decl = c ∧ ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context), EntryDefines mctx mref cctx cref c r.value
def GateFirstDataRow (GT : GateTable) : Prop :=
  ∀ c f, GT c = some (.first f) → f.fe.WF f.names.length f.n ∧ 0 < f.n
def GateOldRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.Old
def GatePeelRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.Peel
def GateHeRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.He
def GateHbvRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.Hb ∧ g.Hv
def GateWidthRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.srt.width ≠ 1

def GateReflects (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) (GT : GateTable) : Prop :=
  GateEntryRow mref cref GT ∧ GateFirstDataRow GT ∧ GateOldRow GT ∧ GatePeelRow GT ∧ GateHeRow GT ∧ GateHbvRow GT ∧ GateWidthRow GT


theorem realChildA_ctx {O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref} {c : Name} {y : Res}
    (h : RealChildA O c y) : ∃ (_ : Lean.Meta.Context) (_ : Lean.Core.Context), True := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr => exact ⟨mctx', cctx', trivial⟩

theorem gateReflects_shipsResI (L : Laws mref cref) (GT : GateTable) (hG : GateReflects mref cref GT)
    (c : Name) (r : GateRec) (hr : GT c = some r) {y : Res} (h : RealChildA L.O c y) :
    ShipsResI L (gateQ ι GT) c y := by
  obtain ⟨hE, hF, hO, hP, hH, hBV, hW⟩ := hG
  obtain ⟨hd, hent⟩ := hE c r hr
  obtain ⟨mctx0, cctx0, -⟩ := realChildA_ctx h
  cases r with
  | mixed g =>
    have hd' : g.decl = c := hd
    subst hd'
    let leaf : GateLeaf ι := g.toLeaf (hO _ g hr) (hP _ g hr) (hH _ g hr) (hBV _ g hr).1 (hBV _ g hr).2
    have hw1 : leaf.srt.width ≠ 1 := hW _ g hr
    have entry : EntryDefines mctx0 mref cctx0 cref leaf.decl leaf.value := hent mctx0 cctx0
    apply gateLeaf_shipsResI_of_real L leaf (gateQ ι GT) entry h
    intro ty hty
    obtain ⟨w, hw, hout⟩ := gateLeaf_outTy L.O leaf entry h hw1
    rw [hout] at hty
    have hty' := List.singleton_inj.mp hty
    have hty2 : ty = .bitVector w := by
      have := congrArg Sparkle.IR.AST.Port.ty hty'
      exact this.symm
    subst hty2
    have hw' : w = g.srt.width := hw
    subst hw'
    simp [gateQ, hr, GateRec.iface, GateLeaf.ifaceOf, leaf, GateData.toLeaf]
  | first f =>
    have hd' : f.decl = c := hd
    subst hd'
    obtain ⟨hwf, hn⟩ := hF _ f hr
    let leaf : FirstLeaf ι := f.toLeaf hwf hn
    have entry : EntryDefines mctx0 mref cctx0 cref leaf.decl (quoteDecl leaf.dn leaf.names leaf.n leaf.fe) :=
      hent mctx0 cctx0
    apply firstLeaf_shipsResI_of_real L leaf (gateQ ι GT) entry h
    simp [gateQ, hr, GateRec.iface, FirstLeaf.ifaceOf, leaf, FirstData.toLeaf]

#print axioms gateReflects_shipsResI

theorem gateReflects_empty : GateReflects mref cref (fun _ => none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c r h <;> cases h

theorem toLeaf_data (g : GateLeaf ι) : (GateLeaf.data g).toLeaf g.old g.peel g.he g.hb g.hv = g := rfl

theorem gateQ_none (GT : GateTable) (c : Name) (h : GT c = none) : gateQ ι GT c = none := by simp [gateQ, h]

end Tools.ShippingGen4GateCarrier

```

## 4. 主定理（scratch で証明済み）
```lean
theorem gateReflects_shipsResI (L : Laws mref cref) (GT : GateTable) (hG : GateReflects mref cref GT)
    (c : Name) (r : GateRec) (hr : GT c = some r) {y : Res} (h : RealChildA L.O c y) :
    ShipsResI L (gateQ ι GT) c y
```
- 証明は `GateRec` の場合分け。route 2: `g.toLeaf` で `GateLeaf` を作り、`gateLeaf_outTy`（幅 ≠ 1）で `ty = .bitVector srt.width` を出し、`gateLeaf_shipsResI_of_real`（§1 の base 版）に渡す。route 1: `firstLeaf_shipsResI_of_real`。`EntryDefines` の文脈は `RealChildA` を `cases` して取る（`realChildA_ctx`）。
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`。`sorry` なし。
- これは **供給ではない**: `GateReflects`（反射）と `RealChildA`（run）を仮定したときの導出で、`GateReflects` を払う定理ではない。

## 5. instance 付きの gate 親: leaf との差
leaf（`GateLeaf` / `FirstLeaf`）は、宣言の値の反射から run の結果（モジュール）の事実までを `gate_combChildRunN`（GateLeaf:221）が証明する。instance 付き親（U-G7a、`Tools/ShippingGen4InstParent.lean`）は構造が違う。
| # | 差 | leaf | instance 付き親（base 上の状態） |
|---|---|---|---|
| D1 | モジュール事実の出どころ | 反射 Prop から `childFull_of_realA` で証明 | `InstCore m c bsP sel wOut`（7 フィールドの Prop 構造体、InstParent:32）は **仮説**。反射 Prop から作る定理はこの調査では見つからなかった |
| D2 | 宣言の反射 | `entry ＋ old ＋ peel ＋ he ＋ hb ＋ hv` | `GateDefines mctx mref cctx cref f bs body`（`Tools/ShippingGateDefines.lean:72`）＋ `tag` / `hscalar` / `accept` / `MixedGateSel` / `ChildBnd`（`gate_parent_runG`、`Tools/ShippingGateParentRunG.lean:64`。どちらも header は WRITTEN, NOT BUILT）。`gateDefines_of_entry`（:42）は旧前提から `GateDefines` を作る向きだけ |
| D3 | callee | なし | `hcallee`: callee の `CombChildRunN`（`ChildShipsI I k c Dc` から取る）。callee が leaf なら `gateLeaf_childShips` で払えるが、`k` と `Dc` の対応は `ShipsResI` の `∃ n` 側で合わせる必要がある |
| D4 | 出力名・design | `y.2.modules = []` | T2 の結論 `⟨m.name, c :: Dc.modules⟩`（ユーザー判断 (b)）。`InstClosed` は自明にならない（`c` が `m` の body の `inst` に現れることが必要） |
| D5 | ポート幅 | `gateLeaf_childPortWidthsI` で証明 | base の `ChildShips` の第 1 連言 `ChildPortWidthsI J m`。`InstCore` に材料が無く、scratch では仮説 `hpw` を足すと T2 が通った。供給元はこの調査では見つからなかった |
| D6 | 残る OPEN（g6 の記録） | — | 実設計 `r.2` の `modules` が `c :: Dc.modules` を含む linkage、leaf `noClk` の供給元、world 層 |
carrier への取り込み: `GateRec` に第 3 の構成子 `inst (p : InstData)` を足す案があるが、`InstCore` が仮説で、D5 の入力もあるため、**この freeze では足さない**。型の固定は route 1 / 2 の leaf まで。instance 付き親は後続の単位 U-GC5（§6）として、D1・D4・D5 を埋める freeze を別に出す。

## 6. 後続の証明単位（行ごと）
| 単位 | 行 | 使う既存定理（file:line） | 見込みの差分 | 止まりそうな箇所 |
|---|---|---|---|---|
| **U-GC0** base への移送と U-G1R / U-G2R | （行ではない。前提） | `ChildIface` 等 `kjob/g4gate-g6:Tools/ShippingGen4Iface.lean:23-57`、`gateLeaf_*` `…GateIface.lean:74-96`、`firstLeaf_*` `…FirstLeaf.lean:156-199`、`gate_combChildRunN` `…GateLeaf.lean:221` | 新規 7 ファイル（既存 g6 の内容＋§1 の直し 約 120 行）。前提の増減 0 | 旧承認はバイト同一の移送だったが今回は直しを含む。lakefile は union（lean_lib 追加のみ） |
| **U-GC1** carrier と主定理 | B.G-9（`Q`/`hQ`）、D.D-1 の gate 成分の型 | §3.1 の 142 行（scratch 通過）。`gateLeaf_shipsResI_of_real`、`gateLeaf_outTy`（GateOutTy:21）、`firstLeaf_shipsResI_of_real`（FirstLeaf:176） | 新規 1 ファイル 約 140 行＋Check。B.G-9 の `Q`/`hQ`: −1（見込み。§8 P1 が通る場合） | 閉包監査: 既知の reviewer 指摘（未知名を黙って skip しない）を最初から入れる。`gateLeaf_outTy` と主定理を root に含める |
| U-GC2 B.G-1 | `entry`（route 1 / 2） | `EntryDefines.of_env`（`Tools/ShippingInlineSoundness.lean:61`）、`of_inline`（:78）、`EnvDefines`（`Tools/ShippingEntrySoundness.lean:1650`） | 供給できれば −1。見込みは未計数 | `EnvDefines` を一般の宣言で払う定理はこの調査では見つからなかった。反射 binder として残る可能性が高い |
| U-GC3 B.G-3/4 | `Old` / `Peel` | `GateDefines`（ShippingGateDefines.lean:72）、`mixedShape_cond`（:110）、`gateDefines_of_entry`（ParentRunG:42） | `GateDefines` 1 つから `Peel` と、`entry` が与える `d` についての `Old` を出す向きの補題が候補。見込みは未計数 | **`Old` は「その値を持つ全ての `d`」についての全称**で、`GateDefines` は `entry` の `dv` 1 つについてなので、`Old` の方が強い。`gate_combChildRunN` が `old` を使うのは `entry` の `d` に対してだけか、は読んでいない（GateLeaf:225, :238）。前提の型を弱める変更になるので、やる場合は別 freeze（reviewer） |
| U-GC4 B.G-5/6/7 | `He` / `Hb` / `Hv` / `hw1` | `Peel` から `bs` の形は出る。`e.WF` と位置の束縛は peel の出力 `quote …` から読み出す定理 | 見込みは未計数 | pick の個別インスタンスのみ供給済み（`Tests/Gen4/GateLeafInstance.lean`）。一般の供給元はこの調査では見つからなかった。幅 1 は未供給（GateOutTy header） |
| U-GC5 instance 付き親 | （B.G-10 は XC。台帳外） | `instParent_combChildRunN`（InstParent:234）、`instParent_childShipsI`（:358）、`gate_parent_runG`（ParentRunG:64） | D1・D4・D5（§5）を埋める。T2 は `hpw` の入力が増える | `InstCore` を反射から作る定理が見つからなかった。台帳に行が無いので E0 の減算には数えない |
| U-GC6 被覆 `GateCovers` | D.D-1 の残り | — | `ReflectsAll` の型の拡張を伴うなら §8 P2 | 事前レビュー |

## 7. E0 の 4 条件
| # | 条件 | この単位の状況 |
|---|---|---|
| 1 | 出力を後続がそのまま使う。後続を Issue として先に登録し依存を張る | 使う: §3.1 の名前（`GateData` `FirstData` `GateRec` `GateTable` `gateQ` `Gate*Row` `GateReflects`）と §4 の定理、§1 の移送。**後続 Issue はまだ登録していない**（他 Issue の状態を変えない規則。担当はこの Issue だけ）。登録は reviewer / coder の承認後。未登録の間は E0 を満たしたと書かない |
| 2 | 消える行 ID と見込みの純差分 | **C-1 の判断で変わる（下）。** 条件付き台帳（見込み。受理されるまで現在値は変えない）: (A) 数え方を変えない場合 FG −1（B.G-9。U-GC1 受理＋§8 P1 が通る場合）。残り B.G-1/3/4/5/6/7 と D.D-1 は反射 binder として残る。(B) 反射を `GateReflects` 1 本として D.D-1 の成分に数える規則（R-G）を reviewer / ユーザーが承認した場合: B.G-1/3/4/5/6/7/9 の 7 行が D.D-1 の成分として吸収され FG −7（D.D-1 は残る）。(B) は R0 と同種の数え方の変更で、この freeze は提案しない（判断資料の要否は reviewer に聞く） |
| 3 | 後続の最初の 1 単位の freeze を受理から 1 往復以内に出す | U-GC0（移送と直し）の freeze は、§1 のとおり scratch で build まで確認済みなので、承認後すぐ出せる。U-GC1 も型は §3.1 で確定済み。出せなければ止めて理由を書く |
| 4 | 増える前提と減算見込みを並べる | 増える見込み: ① U-GC1 は 0（`GateReflects` は既存の行の連言）、② U-GC0 は 0、③ 被覆 `GateCovers`（D.D-1 の残りとして既存だが、型を書くと名前付き条件が 1 つ見える。新しい前提としては数えない。未計数）、④ U-GC5 の `hpw`（T2 の入力 +1。ただし B.G-10 は台帳外）。減算見込み: (A) 1、(B) 7。(A) では見込み 1 が増分 0 より大きいので例外の条件を満たすが、B.G-9 の減算は §8 P1 に依存する。**B-GATE の主要な減算は C-1 次第であり、(A) のままでは「純減 1」以外は期待できない**、と reviewer に明示する |
- **C-1（reviewer / ユーザーへの質問）:** 反射 premise（UN-R）を、同じ名前付き述語 `GateReflects` の成分として 1 本に数える（R-G）か、行ごとに数えるか。台帳の `GateDefines` の扱い（「生成器が binder として束縛、証明しない」）に合わせると、(B) が整合的だが、数え方の変更であり承認が要る。

## 8. Pkg / T1Hyp の route 拡張: 事前レビューの対象（決めない）
| 項 | 内容 | 影響する共有定義 | なぜ要るか |
|---|---|---|---|
| P1 | T1 側の IH と consumer は `Pkgs`（`ShipsRes L P`）を取る（`CacheShips` Defs:154、`ShipsAt` :160、`IHAt` :171）。gate の結果は `IfaceMap`（`ShipsResI L Q`）で出る。`shipsResI_iface`（Iface:52）は `Pkgs.iface P` に対する同値だけで、gate 表の `Q` から `Pkgs` は作れない（gate には `MachineData` が無い） | `Tools/ShippingGen2Defs.lean`（`ShipsRes`、`CacheShips`、`IHAt`、`ShipsAt`）と、それを使う `T1Hyp` / `T1HypND` の `pkg` フィールド | T1 と FG の接続で `ShipsRes` の代わりに `ShipsResI`（または `P.iface` と `gateQ` の合成）を使う必要がある。共有定義の変更なので、この freeze では提案だけ |
| P2 | `ReflectsAll` の型に到達宣言が入っていない（Gen5FG:30）。gate 成分の被覆 `GateCovers`（到達した gate 経路の宣言は表に載る）を書くには、(a) `ReflectsAll` の型に `Reach` / `P` を足す（`EntryWitness` と `FG_CONNECT` の文が変わる）、(b) `ReflectsAll` の内部で表の閉包から到達を定義する（instance 付き親が表に入らないと閉じない）、のどちらかが要る | `Tools/ShippingGen5FG.lean`（`EntryWitness`、`FG_CONNECT`、`ReflectsAll` binder）。FG の文に関わる | 空の表で `GateReflects` が成り立つ（`gateReflects_empty`）ため、被覆が無いと gate 成分は保証にならない |
| P3 | `T1Hyp` に gate 用のフィールドが無い（B_M4 G-1: census seq 2342）。`T1Hyp.defines` の gate 版が要るかは、P1 の選択次第 | `Tools/ShippingT1Hyp.lean` 系 | P1 の後 |
この freeze の範囲では、Pkg / T1Hyp / `Elab*.lean` / 共有定義は編集しない。

## 9. 検証（scratch。ソースツリーにコミットしていない）
- 環境: `kjob lake build`（`Tools.ShippingGen4Iface` → `…GateIface` → `…GateOutTy` → `…FirstLeaf` → `…InstParent`）を 1 つずつ。依存は `Tools.ShippingGen4GateLeaf` 以下で、base の 700 jobs 前後、各 30〜60 秒。移送した 7 ファイルは作業コピー（未コミット、後で削除）。
- carrier の scratch: `kjob lake env lean`（スクラッチ 1 ファイル、ソースツリー外）で elaborate。`#check` 出力（抜粋）:
```
GateEntryRow : ST.Ref IO.RealWorld State → ST.Ref IO.RealWorld Core.State → GateTable → Prop
GateFirstDataRow : GateTable → Prop
GateOldRow : GateTable → Prop
GatePeelRow : GateTable → Prop
GateHeRow : GateTable → Prop
GateHbvRow : GateTable → Prop
GateWidthRow : GateTable → Prop
GateReflects : ST.Ref IO.RealWorld State → ST.Ref IO.RealWorld Core.State → GateTable → Prop
gateQ : (ι : Type) → GateTable → IfaceMap ι
@gateReflects_shipsResI : ∀ {ι : Type} {mref cref} (L : Laws mref cref) (GT : GateTable),
  GateReflects mref cref GT → ∀ (c : Name) (r : GateRec), GT c = some r → ∀ {y : Res}, RealChildA L.O c y → ShipsResI L (gateQ ι GT) c y
@gateReflects_empty : ∀ {mref cref}, GateReflects mref cref fun x => none
@toLeaf_data : ∀ {ι : Type} (g : GateLeaf ι), (GateLeaf.data g).toLeaf ⋯ ⋯ ⋯ ⋯ ⋯ = g
```
- `#print axioms`: `gateReflects_shipsResI` `gateReflects_empty` は `[propext, Classical.choice, Quot.sound]`、`toLeaf_data` は `[propext]`。`sorry` なし。
- 警告: 移送した GateIface / FirstLeaf の未使用変数 `g`（既存コード由来）。
- **まだ確認していないこと:** `Tests/Gen4/*Check.lean`（TYPE / MUTANT / CLOSURE / AXIOMS）の base 上での再実行。U-GC0 の単位で行う。`gate_combChildRunN` が `old` を `entry` の `d` にしか使わないか（U-GC3）。`InstCore` を反射から作る経路。

## 10. この freeze が主張しないこと
8 行のどれの供給も、`GateReflects` の非空虚性も、被覆も、run と `GT c = some r` の結び付けも、instance 付き親の供給も主張しない。型の固定と、`Q`/`hQ` が前提でなく導出になること、base のドリフトの記録だけである。FG・T1・M4 の完了は主張しない。
