# AUDIT RUNSEXIST 調査（B-AUD: 非 top の RunsExistAt を既存定理から導く経路）

状態: 調査の結果。Lean は scratch のみ（コミットしない。全文は付録）。台帳: FG 95 / T1 56（今回 FG -0 +0 / T1 -0 +0）。mutant はなし（signature / defeq での棄却も行っていない）。

## 1. 結論
- 非 top の `RunsExistAt L c`（U-A2 freeze の `RunsExistAt`）は、`TgtRun` で到達した `c` について、**既存の定理と、既存の `T1Hyp` の 2 つの行（`defines`、`closes`）だけから** scratch で導けた（`runsExist_tgtRun`、sorry なし、公理は `propext, Classical.choice, Quot.sound`）。新しい前提は使っていない。
- したがって U-A2 の「+1 の候補」は、この調査の範囲では **+0 にできる**。E-6 の −1 は、`defines` / `closes` が既存行のままであること、および top の入口が下記 §4 の範囲であることを条件に確定する。条件付きの結果であり、受理済みではない。
- 範囲外（この調査では未確認）: top が `synthesizeCombinationalWithParameters` の枝（`parameters ≠ []`）の場合。

## 2. 経路（file:line）
1. **`RealChildA` から 3 つの run**（`runsExist_of_realChildA`）: `RealChildA.run`（`Tools/ShippingChildCacheA.lean:105`）は `AdmCtx` と `RunsTo (synthesizeCombinational c) …` を持つ。`synthesizeCombinational_parts`（`Tools/ShippingGateChildComb.lean:139`）で core の run を取り、`Tools.ShippingEntryReadsLinked.core_chain` で `getConstInfo c` と `getEnv` の run を得る。2 つ目の `getEnv` は 1 つ目を再利用（`runsExist_top` と同じ）。結論は `RunsExistAt` の `∃` そのもの（context は `RealChildA` の `adm`）。
2. **親の `RealChildA` から callee の `RealChildA`**（`kid_realChildA`）: `RealChildA.run` の run を `machineRanA_main`（`Tools/ShippingParentRanA.lean:64`）に渡す。引数は `L.T`（`Laws` のフィールド）、`MachineDefines`（`T1Hyp.defines`）、`MachineClosesAtA`（`T1Hyp.closes`、`Tools/ShippingGen2Defs.lean:219` 付近）、`hw : JQ`（`RealChildA.run` の `quiet`/`synth`）、`CacheInvA`（`cache`）。結論の `MachineRanA`（`ParentRanA.lean:47`）の `insts ≠ []` の枝に `ChildrenRealA`（`Tools/ShippingChildRunAKids.lean:51`）があり、k 番目は `instOrigins.child? = some y ∨ RealChildA O (insts[k]).1 y`。`TgtRun.call` の `ord`（`child? = none`）で左を除くと `RealChildA`。`insts = []` の枝は `k < insts.length` と矛盾する。この手順は `deepChild_ifaceA'`（`ShippingSeqChildDeepConsumerA.lean:66`）と同じ筋で、その `d.ok`・`hbody` などの前提は `machineRanA_main` には要らない。
3. **`TgtRun` 上の帰納法**（`tgtRun_realChildA`）: `TgtRun.top` は 4 の `RealChildA declName`、`TgtRun.call`（`ShippingGen5FG.lean:26`）は 2 で進む。`TgtRun.call` の `hq : P c = some q`、`hk`、`ord` がそのまま 2 の前提になる。
4. **top の `RealChildA`**（`top_realChildA`）: `Start L mctx cctx w`（`AdmCtx ∧ JQC L.O 0 w`、`ShippingGen2Defs.lean:52`）と `EntryWitness` の第 1 枝の run `synthesizeCombinational declName` から `RealChildA.of_jqc`（`ShippingChildCacheA.lean:160`）。
5. **合成**（`runsExist_tgtRun`）: 3 の `RealChildA` を 1 に渡す。

## 3. 他の候補の判定
| 候補 | 判定 |
|---|---|
| `RealChildA` / `RealChild`（`ShippingChildInv.lean:453`） | 出る。run は `RealChildA.run` / `RealChild.inv`（`ShippingChildInv.lean:831`）から取れる。`RealChild` は `AdmCtx` を持たない（`InvW` のみ）ので `RunsExistAt` の context 条件には `RealChildA` を使う |
| `ChildrenShipsI`（`ClosingRun.shared`、`ShippingGen2ServedRun.lean:342`） | 出る。`insts ≠ []` の枝で `RealChildA` を持つ。ただし `ClosingRun` を非 top の `c` に対して作るには `closingRun_of_run` の前提（`InvAt`、`IHAt`、`ChildKeepsInv` など）が必要で、今回の経路（`machineRanA_main`）の方が前提が少ない |
| `ChildIfaceP`（`ShippingMemClosesKids.lean:167`） | 使っていない。callee の run 存在ではなくインターフェース（port 名・幅）の述語 |
| `ReadsAt` / C0（`ShippingGen5Env.lean:29`） | 使っていない。`ReadsAt` は world の環境の一致で、run の存在は言わない |
| `runReads_of_run`（`ShippingGen5RunReads.lean:181`） | 使っていない。親の core run から `RunReadsAt` を作る（run を入力に取る）。非 top の run はこの定理の入力側で、出力側ではない |
| `MachineDefines`（`ShippingMachineEntry.lean:2345`） | 使っているが run の存在は言わない（「任意の run について」の形） |

## 4. 前提の一覧と台帳
- 使った前提: `L.T`（`Laws` の既存フィールド）、`T1Hyp.defines`、`T1Hyp.closes`（`TgtRun` 上、いずれも既存の行）、top の `Start` と `EntryWitness` の第 1 枝（A.P-04 の run）。**新しい前提は 0**。
- `defines` は `h_A_P06` と同じ（`AdmCtx` 上の `MachineDefines`）。`closes` の台帳上の行 ID は、この調査では対応付けを確認していない（`T1Hyp.closes` の行として数えられているはず）。`closes` が台帳に無い、または別の形なら、その分が +1 になる。この点は coder が台帳で確認する。
- 台帳の見込み（受理後）: E-6 −1、非 top の run 存在 +0 → FG 正味 −1（条件付き）。条件付き台帳: FG −1 +0。受理済みの台帳は変えない。
- 範囲外: top の `parameters ≠ []` の枝は経路を確認していない。この調査では、その枝の `RealChildA declName`（または 3 つの run）の供給元・経路は見つからなかった。`hF` が `[]` 固定の `MachineDefines` から作られる限り、この枝は U-A2 の範囲外のまま。

## 5. 主張しないこと
- 受理済みの台帳の変更、`defines` / `closes` の充足、`parameters ≠ []` の枝、FG / T1 / M5 の完了は主張しない。
- 示したのは、scratch の elaborate（sorry なし、標準公理のみ）で、上記の前提から非 top の `RunsExistAt` が出ること。U-A2 の `auditE6_of_defines` の第 3 仮定を `runsExist_tgtRun` で置き換える形の freeze は別単位（coder / reviewer の判断）。

## 付録: scratch の全文（ソースツリー外、`LEAN_PATH` を直接指定して `lean` で elaborate）
```lean
import Tools.ShippingGen5FG
import Tools.ShippingEntryReadsLinked
import Tools.ShippingParentRanA
set_option autoImplicit false
namespace Tools.ShippingGen5AuditCarrier
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildBndCore Tools.ShippingChildVCA Tools.ShippingChildDepthC Tools.ShippingChildCacheA Tools.ShippingChildInvA Tools.ShippingParentRanA Tools.ShippingChildRunAKids
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

def RunsExistAt (L : Laws mref cref) (c : Name) : Prop :=
  ∃ (mctx' : Meta.Context) (cctx' : Core.Context),
    Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' ∧
    ∃ (w1 : Void IO.RealWorld) (ci : ConstantInfo) (w2 w5 : Void IO.RealWorld) (envR : Environment)
      (w6 w7 : Void IO.RealWorld) (envR' : Environment) (w8 : Void IO.RealWorld),
      RunsTo (getConstInfo c) mctx' mref cctx' cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx' mref cctx' cref w5 envR w6 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx' mref cctx' cref w7 envR' w8

/-- (S1) any RealChildA gives the three runs -/
theorem runsExist_of_realChildA (L : Laws mref cref) {c : Name} {y : Res}
    (h : RealChildA L.O c y) : RunsExistAt L c := by
  obtain ⟨M', D'⟩ := y
  cases h with
  | run mctx cctx w w' adm cache synth quiet hr =>
    obtain ⟨M, D₁, w1, hcore, -, -⟩ := Tools.ShippingGateChildComb.synthesizeCombinational_parts hr
    obtain ⟨s, w1, envR, ci, w2, w3, w4, -, hg, he, -, -⟩ := Tools.ShippingEntryReadsLinked.core_chain hcore
    exact ⟨mctx, cctx, adm, _, ci, _, _, envR, _, _, envR, _, hg, he, he⟩

/-- (S2) a RealChildA of a package's declaration has a RealChildA for every ordinary callee -/
theorem kid_realChildA (L : Laws mref cref) {c : Name} {y : Res} {shape : MachineShape}
    (defines : ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx → Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c shape)
    (closes : ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx → MachineClosesAtA L.O mctx cctx c shape)
    (h : RealChildA L.O c y) (k : Nat) (hk : k < shape.insts.length)
    (ord : (shape.instOrigins.getD k .ord).child? = none) :
    ∃ y', RealChildA L.O (shape.insts[k]).1 y' := by
  cases h with
  | run mctx cctx w w' adm cache synth quiet hr =>
    obtain ⟨M', D'⟩ := y
    obtain ⟨M, D₁, w1, hcore, -, -⟩ := Tools.ShippingGateChildComb.synthesizeCombinational_parts hr
    have hw : JQ L.O.quiet (dv w) w := ⟨quiet, synth, rfl⟩
    have ran := machineRanA_main L.O adm L.T hcore (defines mctx cctx adm) (closes mctx cctx adm) hw
      (Or.inr (fun c r h => cache c r h))
    obtain ⟨tenv, b, w9, w10, -, t, t', d₀, -, -, hm⟩ := ran
    rcases hm with ⟨hnil, -⟩ | ⟨hne, children, -, hreal⟩
    · exact absurd hnil (by intro h0; rw [h0] at hk; simp at hk)
    · obtain ⟨-, hall⟩ := hreal
      obtain ⟨y', -, hy'⟩ := hall k hk
      rcases hy' with h1 | h1
      · rw [ord] at h1; cases h1
      · exact ⟨y', h1⟩

/-- (S3) induction along TgtRun -/
theorem tgtRun_realChildA (L : Laws mref cref) (P : Pkgs ι dom) (declName : Name)
    (defines : ∀ c, TgtRun P declName c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c q.d.shape)
    (closes : ∀ c, TgtRun P declName c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape)
    (top : ∃ y, RealChildA L.O declName y) :
    ∀ c, TgtRun P declName c → ∃ y, RealChildA L.O c y := by
  intro c hc
  induction hc with
  | top => exact top
  | @call c0 q hc0 hq k hk ord ih =>
    obtain ⟨y0, hy0⟩ := ih
    exact kid_realChildA L (defines c0 hc0 q hq) (closes c0 hc0 q hq) hy0 k hk ord

/-- (S4) the top: EntryWitness's first branch -/
theorem top_realChildA (L : Laws mref cref) (declName : Name) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (r : Res) (hst : Start L mctx cctx w)
    (hrun : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w r w') :
    ∃ y, RealChildA L.O declName y :=
  ⟨r, RealChildA.of_jqc L.O hst.1 hst.2 hrun⟩

theorem runsExist_tgtRun (L : Laws mref cref) (P : Pkgs ι dom) (declName : Name)
    (defines : ∀ c, TgtRun P declName c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c q.d.shape)
    (closes : ∀ c, TgtRun P declName c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c q.d.shape)
    (top : ∃ y, RealChildA L.O declName y) :
    ∀ c, TgtRun P declName c → RunsExistAt L c := fun c hc =>
  let ⟨_, h⟩ := tgtRun_realChildA L P declName defines closes top c hc
  runsExist_of_realChildA L h
end Tools.ShippingGen5AuditCarrier
#print axioms Tools.ShippingGen5AuditCarrier.runsExist_tgtRun
#print axioms Tools.ShippingGen5AuditCarrier.top_realChildA
```

`#print axioms`: `runsExist_tgtRun`、`top_realChildA` とも `[propext, Classical.choice, Quot.sound]`。
