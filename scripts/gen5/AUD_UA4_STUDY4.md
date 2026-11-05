# U-A4 / U-A5 調査 4: DataRes2 の 5 field の供給（具体 DataOk、noMemName）

- Issue: sparkle-aud-ua4。base: f0f6a8d8（STUDY3 承認済み）。文書のみ（Lean のソースは編集していない。scratch は `kjob lake env lean`、ソースツリーに入れていない）。
- 台帳: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。受入の数は動かさない。
- 「見つからなかった」は、この調査では供給元・経路が見つからなかったという意味で、不可能・導出不能の証明ではない。mutant は使っていない（signature/defeq での棄却も意味的反例の主張もしていない）。

## 0. 結論（先に）

1. **`noMemName` は不要にできる（scratch で確認）。しかも名前半分は偽になりうる**: 台帳 A.P-26 と `Tests/Compiler/MemNameCollisionPlainCertTest.lean:178` の `collPlainCD_nomem_false` は、memory placeholder 名（`SparkleMem.sync.4.8`）の ordinary callee を持つ正当な one-output 親で「名前半分 `memChild? x.1 = none`」が偽だと記す（このテストは自分では build していない。記載を読んだ）。STUDY3 の `noMemName` を DataOk に足すと、そうした設計を除くことになり（FG の縮小にあたる）、足してはならない。調べると `core_kids_facts_ranA`（Tools/ShippingParentTailsA.lean:48）で `hnomem` が使われるのは 1 箇所（`nomem_tag`、起源半分 `.1` だけを読む）なので、起源半分だけを仮定する複製 `core_kids_facts_ranAO` / `deepChild_ifaceAO`（差分は binder 型・補題名・改名の 3+4 行、証明は verbatim）を作った。これで `MachPrem3`（one-output 枝は起源半分のみ）、`q_induct3`、`auditE3_of_t1hyp3` が通った（§3）。**`noMemName` は E-3/B3 の道から消える（新前提 +1 は発生しない）**。
2. **`hdomB` / `outTy` / `callsOk` / `ss.length` は、既存の行 T1L-12（`hMemRow : DataOk q → MemParentDataOk q ∧ ExtInS q`）から出る**（`MemParentDataOk.rows`、Tools/ShippingGen2MemData.lean:19 が 5 行を返す。scratch `dataRes3_of_rows`）。T1L-12 は無条件（∀ q）の行なので、葉・calls 親のどちらにも使える。T1L-11（`LeafDataOkB`）は `hdomB` を持たないので使わない。
3. **`noMemRow`（起源半分）は T1L-04（`hrow`）がそのまま当たる**（`OneOutNoMemRow`）。
4. **`leafAlias`（`insts = [] → letsAliasOk = true`）は、`Pkg` 上の既存行に見つからなかった**。`letsAliasOk` は `DataOkB`（`SrcPkg` 上、T1L-32）にだけ在り、`LeafDataOkB`（T1L-11）にも `MemParentDataOkB`（T1L-12）にも無い。`ok` からも出ない（`MachineData.ok` の 22 conjunct に alias 条件は無い）。探した別経路: `Tools/Prototype/DGenConnect.lean` の `dgen_connect_gen` は `ok`/`hbody`/`MachineDefines` と `ShippedToProto`・`GenReadsShape` 等の open 前提から `letsAliasOk` を出すが、それらの前提は台帳の既存行にこの調査では対応を確認できなかった。**新しい前提 +1（T1 側）の見込み**。完全な型は `scripts/gen5/AUD_UA4_FREEZE.md`。
5. **正味（条件付き台帳）**: E-3 −1、B3 −1（`DataRes3` が T1L-12 / T1L-04 / 新 row で払える場合）、新規 T1 +1（`leafAlias`）。E-12 の `hsep(b)` 部分は STUDY2 のとおり件数未確定。受入の数は動かさない。

## 1. DataRes の 5 field の表

| field | 払い元 | 判定 |
|---|---|---|
| `callsRows` の `callsOk kD` | `MemParentDataOk.rows`（T1L-12 経由）。T1L-39 は別行で残る | 既存行で払える（T1L-12） |
| `callsRows` の `ss.length = slots.length` | 同上。T1L-40 は K1（Pkg.ok から導出、kjob/k1-pa）で別途解消済みの行 | 既存行で払える |
| `callsRows` の `hdomB` | `MemParentDataOk.rows` の 5 つ目（T1L-12） | 既存行で払える（具体 DataOk に MemParentDataOk を含める＝T1L-12 の内容） |
| `outTy` | `MemParentDataOk.rows` の 4 つ目（T1L-12）。`Pkg.ok` からは出ない（`ok` は `o.ty` を見ない） | 既存行で払える |
| `leafAlias` | `Pkg` 上に無い | **新しい前提（+1、T1）** |
| `noMemRow` | T1L-04 | 既存行で払える |
| `noMemName` | 偽になりうる。不要（§3 の O-copy） | 前提から除去 |

注意: T1L-12 / T1L-04 自体は未供給の義務（`DataOk` の強化は、LEDGER_SHORTEN_PLAN §3 によれば「ユーザーは今回選ばなかった」束）。ここで言う「払える」は、これらの行が成り立つとしたときに `DataRes3` の 4 field が出るという意味で、行そのものの供給は何も進んでいない。また T1L-39 は T1L-12 から出る形になるが、T1L-39 を台帳から消す主張はしない（reviewer の判断）。

## 2. 具体 DataOk 側の事実（読んだ範囲）
- `DataOkB`（Tools/ShippingGen2Data.lean:17、`SrcPkg`）: `ok ∧ letsAliasOk ∧ callsOk kD ∧ ss.length ∧ outTy ∧ outHead`。`hdomB` は無い。
- `LeafDataOkB`（Gen2Leaf:44）: `ok ∧ callsOk ∧ ss.length ∧ outTy`。`letsAliasOk`・`hdomB` は無い。
- `MemParentDataOkB`（Gen2MemParent:38）: 上に `hdomB` を足したもの。`letsAliasOk` は無い。
- STEP_ROUTE_FREEZE §7 row 6: `DataOkB` から `MemParentDataOk` / `ExtInS` / `hord` / `OneOutWidth` への補題も逆向きも見つからなかった（含意の有無は未調査）。従って「T1L-12 を仮定する DataOk」は `DataOkB` とは別の強化で、`letsAliasOk` を持たない。

## 3. scratch（`set_option autoImplicit false`、sorry なし、`kjob lake env lean` exit 0）
import: Gen2Data, Gen2MemData, Gen2DataBridge, Srm4Core5, Gen5NameKids3, CacheCoherentRun, SeqChildDeepConsumerA, Srm12Corr, Gen5AuditUA1（各 `kjob lake build` exit 0）。ファイル本体 = (a) 2 つの複製、(b) STUDY2 §3 のコード、(c) 下の新規部分。`#print axioms closesAtA_of_closes / leafCloses_of_data / q_induct3 / machPrem3_of_t1hyp / auditE3_of_t1hyp3 / dataRes3_of_rows / auditE3_of_rows` = すべて `[propext, Classical.choice, Quot.sound]`。

(a) 複製（元の定理の差分のみ）: `core_kids_facts_ranA` → `core_kids_facts_ranAO`: binder `hnomem` を `(hnomemO : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true)` に、本体 1 箇所 `nomem_tag hnomem hk'` を `notag_at hnomemO hk'` に。`deepChild_ifaceA'` → `deepChild_ifaceAO`: 同じ binder 変更と、`core_kids_facts_ranAO` の呼び出しに差し替え。それ以外は verbatim。

(c) 新規部分（STUDY3 §3.1 の closes 補題、`MachPrem3`＝`MachPrem2` の第 3 disjunct を起源半分のみにしたもの、`q_induct3`、`DataRes3`、`ConcRows`、`dataRes3_of_rows`、`auditE3_of_rows`）:

```lean

/-! ## STUDY3 -/
section S3
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- (2) direction: MachineCloses ⇒ MachineClosesAtA (any O, any context). -/
theorem closesAtA_of_closes (O : RefLawsAOps MkRefd mref cref) (mctx : Lean.Meta.Context)
    (cctx : Lean.Core.Context) (c : Name) (sh : MachineShape)
    (h : MachineCloses mctx mref cctx cref c sh) : MachineClosesAtA O mctx cctx c sh := by
  intro tenv b n w r w' _ _ hr
  exact h (Tools.ShippingChildInv.profLogIO b) w r w' hr
#print axioms closesAtA_of_closes

/-- leaf `MachineCloses` from `letsAliasOk` (existing `closes_of_data`), every context. -/
theorem leafCloses_of_data (c : Name) (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = []) (hal : d.letsAliasOk = true)
    (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) :
    MachineCloses mctx mref cctx cref c d.shape :=
  Tools.ShippingMachineClosesData.closes_of_data d ok hbody
    (by simp [MachineData.letsOk, hno, hal]) mctx mref cctx cref
#print axioms leafCloses_of_data

/-- leaf `MachineCloses` from `lets = 0` (existing `machineCloses_of_noLets`). -/
theorem leafCloses_of_noLets (c : Name) (sh : MachineShape) (h : sh.layout.lets = 0) (hi : sh.insts = [])
    (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) :
    MachineCloses mctx mref cctx cref c sh :=
  Tools.ShippingMachineEntry.machineCloses_of_noLets h hi
end S3
section Q
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingCacheCoherentRun (IsMem)
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
def MachPrem3 {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    (O : RefLawsAOps MkRefd mref cref) (c : Name) (sp : MachineShape) : Prop :=
  ∃ d : MachineData, d.shape = sp ∧ d.ok = true ∧
    d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    (∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width) ∧
    MachineDefines mctx mref cctx cref c d.shape ∧
    ((d.shape.insts = [] ∧ ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
        MachineCloses mctx' mref cctx' cref c d.shape) ∨
     (∃ nDecl : Nat, d.callsOk nDecl = true ∧ d.ss.length = d.shape.layout.slots.length ∧
        (∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) ∧ d.shape.insts ≠ [] ∧ d.shape.instFields ≠ [] ∧
        ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
          Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape) ∨
     (∃ nDecl : Nat, d.callsOk nDecl = true ∧ d.ss.length = d.shape.layout.slots.length ∧
        (∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain) ∧ d.shape.insts ≠ [] ∧
        (∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true) ∧
        ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
          Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape))

set_option maxHeartbeats 4000000 in
theorem q_induct3 {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach S)
    (hS : ∀ c, Reach c → ∃ sp, S c = some sp)
    (hprem : ∀ c, Reach c → ∀ sp, S c = some sp → MachPrem3 (mctx := mctx) (cctx := cctx) O c sp)
    (hcl : ReachClosed Reach S) :
    ∀ c, Reach c → ∀ y, RealChildA O c y → QY g c y := by
  obtain ⟨r0, h0, -, -⟩ := Tools.ShippingSrm7Rank.inClass_rank hin
  have key : ∀ r c, Reach c → declRank g B c = some r → ∀ y, RealChildA O c y → QY g c y := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ih =>
      intro c hc hr y hy
      obtain ⟨sp, hSc⟩ := hS c hc
      -- kids
      have kids : ∀ (k : Nat) (hk : k < sp.insts.length) (y' : Res),
          Tools.ShippingCallsMemA.KidTA O (originAt sp k) (sp.insts[k]'hk).1 y' → KidOK g c y' := by
        intro k hk y' hkid
        rcases hkid with h1 | ⟨hch, hrc⟩
        · obtain ⟨cb, aw, dw, hmo⟩ : ∃ cb aw dw, originAt sp k = .mem cb aw dw := by
            cases ho : originAt sp k with
            | ord => rw [ho] at h1; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1
            | field i => rw [ho] at h1; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at h1
            | mem cb aw dw => exact ⟨cb, aw, dw, rfl⟩
          rw [hmo] at h1
          simp only [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?, Option.some.injEq] at h1
          subst h1
          exact memModule_kidOK g c cb aw dw
        · have he := ordEdge_of_idx hg hc hSc hk hch
          obtain ⟨r1, h1, hlt⟩ := rank_of_ordEdge hr he
          have hc' : Reach (sp.insts[k]'hk).1 := hcl c hc sp hSc k hk (by simpa using hch)
          obtain ⟨hn, hd, ho⟩ := ih r1 hlt _ hc' h1 y' hrc
          refine ⟨?_, ho⟩
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inr ⟨_, strictDesc_of_edge he, hn⟩
          · rcases hd a ha with hm | ⟨c'', hs, hnm⟩
            · exact Or.inl hm
            · exact Or.inr ⟨c'', strictDesc_of_edge_left he hs, hnm⟩
      obtain ⟨d, hdS, ok, hbody, outTy, entry, hcase⟩ := hprem c hc sp hSc
      subst hdS
      rcases hcase with ⟨hno, closes⟩ | ⟨nDecl, hC, hslots, hdomB, hins, hfne, closes⟩ | ⟨nDecl, hC, hslots, hdomB, hins, hnomemO, closes⟩
      · have I := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O d ok hbody hno outTy entry closes hy
        refine ⟨I.name, ?_, ?_⟩
        · intro a ha; rw [I.design] at ha; simp at ha
        · intro a ha mn i cs hm
          rw [I.design] at ha
          have : a = y.1 := by simpa using ha
          subst this
          have := List.all_eq_true.mp I.seqOk _ hm
          simp [Sparkle.IR.OptCheck.seqStmtOk] at this
      · have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
            Tools.ShippingCallsMemA.KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y' →
            ∀ a ∈ y'.1 :: y'.2.modules, a.name ≠ ofDecl c :=
          fun k hk y' hkid => kidOK_hsep hin hsp hc (kids k hk y' hkid)
        obtain ⟨-, -, -, -, M, D, -, -, -, -, hpost, hdes, hMn, hb, -, hinst, hreal, -⟩ :=
          Tools.ShippingSrm4Core5.deepChild_ifaceA'M O T d ok hbody hC hslots hdomB hins hfne outTy hsep entry closes hy
        have hname : y.1.name = ofDecl c := by
          rcases hpost with e | e
          · rw [e, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
          · rw [e, Tools.ShippingMachineDepthRun.mergeChecked_name, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
        refine ⟨hname, ?_, ?_⟩
        · intro a ha
          rw [hdes] at ha
          obtain ⟨k, hk, y', hkid, hor, -⟩ := hreal a ha
          have K := kids k hk y' hkid
          refine K.1 a ?_
          rcases hor with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ h
        · intro a ha mn i cs hm
          rcases List.mem_cons.mp ha with rfl | ha
          · rw [hb] at hm
            obtain ⟨mc, hmc⟩ := hinst mn i cs hm
            obtain ⟨hmem, hnm⟩ := moduleByName_spec hmc
            exact ⟨mc, by rw [hdes]; exact hmem, hnm⟩
          · rw [hdes] at ha
            obtain ⟨k, hk, y', hkid, hor, hcov⟩ := hreal a ha
            have K := kids k hk y' hkid
            have ha' : a ∈ y'.1 :: y'.2.modules := by
              rcases hor with rfl | h
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ h
            obtain ⟨g2, hg2, hn2⟩ := K.2 a ha' mn i cs hm
            obtain ⟨g', hg', hn'⟩ := hcov g2 (List.mem_cons_of_mem _ hg2)
            exact ⟨g', by rw [hdes]; exact hg', hn'.trans hn2⟩
      · have hch : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none := by
          intro k hk
          exact Tools.ShippingChildInv.notag_at hnomemO hk
        have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
            RealChildA O (d.shape.insts[k]).1 y' →
            ∀ a ∈ y'.1 :: y'.2.modules, a.name ≠ ofDecl c :=
          fun k hk y' hrc => kidOK_hsep hin hsp hc (kids k hk y' (Or.inr ⟨hch k hk, hrc⟩))
        obtain ⟨-, -, -, -, M, D, -, -, -, -, hpost, hdes, hMn, hb, -, hinst, hreal, -⟩ :=
          Tools.S4Deep.deepChild_ifaceAO O T d ok hbody hC hslots hdomB hins outTy hnomemO hsep entry closes hy
        have hname : y.1.name = ofDecl c := by
          rcases hpost with e | e
          · rw [e, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
          · rw [e, Tools.ShippingMachineDepthRun.mergeChecked_name, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
        refine ⟨hname, ?_, ?_⟩
        · intro a ha
          rw [hdes] at ha
          obtain ⟨k, hk, y', hrc, hor, -⟩ := hreal a ha
          have K := kids k hk y' (Or.inr ⟨hch k hk, hrc⟩)
          refine K.1 a ?_
          rcases hor with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ h
        · intro a ha mn i cs hm
          rcases List.mem_cons.mp ha with rfl | ha
          · rw [hb] at hm
            obtain ⟨mc, hmc⟩ := hinst mn i cs hm
            obtain ⟨hmem, hnm⟩ := moduleByName_spec hmc
            exact ⟨mc, by rw [hdes]; exact hmem, hnm⟩
          · rw [hdes] at ha
            obtain ⟨k, hk, y', hrc, hor, hcov⟩ := hreal a ha
            have K := kids k hk y' (Or.inr ⟨hch k hk, hrc⟩)
            have ha' : a ∈ y'.1 :: y'.2.modules := by
              rcases hor with rfl | h
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ h
            obtain ⟨g2, hg2, hn2⟩ := K.2 a ha' mn i cs hm
            obtain ⟨g', hg', hn'⟩ := hcov g2 (List.mem_cons_of_mem _ hg2)
            exact ⟨g', by rw [hdes]; exact hg', hn'.trans hn2⟩
  intro c hc y hy
  obtain ⟨r, hr, -⟩ := rank_of_reach h0 (hsp c hc)
  exact key r c hc hr y hy

#print axioms q_induct3
end Q

section S6
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- the SOf of AuditUA1 (Tools/ShippingGen5AuditUA1.lean:31) -/
def SOf' (P : Pkgs ι dom) : Name → Option MachineShape := fun c => (P c).map (fun q => q.d.shape)

/-- Named residual facts about `DataOk` (NOT derived), second version with the one-output branch. -/
structure DataRes3 (DataOk : Pkg ι dom → Prop) : Prop where
  callsRows : ∀ q, DataOk q → q.d.shape.insts ≠ [] →
    q.d.callsOk q.kD = true ∧ q.d.ss.length = q.d.shape.layout.slots.length ∧
      (∀ b ∈ q.d.shape.binders.drop q.kD, b.2 ≠ .domain)
  outTy : ∀ q, DataOk q → ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width
  leafAlias : ∀ q, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true
  /-- the one-output row (origin half), `OneOutNoMemRow` (Tools/ShippingGen2DataBridge.lean) -/
  noMemRow : ∀ q, DataOk q →
    (!q.d.shape.instFields.isEmpty || q.d.shape.instTagged.all (fun x => x.2.child?.isNone)) = true

theorem machPrem3_of_t1hyp {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (R : DataRes3 DataOk) (hA : AdmCtx L.O.quiet mctx cctx) :
    ∀ c, Reach c → ∀ sp, SOf' P c = some sp → MachPrem3 (mctx := mctx) (cctx := cctx) L.O c sp := by
  intro c hc sp hS
  obtain ⟨q, hq, hdecl, hdo⟩ := H.pkg c hc
  subst hdecl
  simp only [SOf', hq, Option.map_some, Option.some.injEq] at hS
  subst hS
  refine ⟨q.d, rfl, q.ok, q.body_eq, R.outTy q hdo, ?_, ?_⟩
  · exact H.defines _ hc q hq mctx cctx hA
  · by_cases hno : q.d.shape.insts = []
    · refine Or.inl ⟨hno, fun mctx' cctx' => ?_⟩
      exact leafCloses_of_data _ q.d q.ok q.body_eq hno (R.leafAlias q hdo hno) mctx' cctx'
    · obtain ⟨hC, hsl, hdom⟩ := R.callsRows q hdo hno
      have hcl : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx L.O.quiet mctx' cctx' →
          MachineClosesAtA (mref := mref) (cref := cref) L.O mctx' cctx' q.decl q.d.shape :=
        fun mctx' cctx' hA' => H.closes _ hc q hq mctx' cctx' hA'
      by_cases hf : q.d.shape.instFields = []
      · refine Or.inr (Or.inr ⟨q.kD, hC, hsl, hdom, hno, ?_, hcl⟩)
        have hrow := R.noMemRow q hdo
        rw [hf] at hrow
        have hall : q.d.shape.instTagged.all (fun x => x.2.child?.isNone) = true := by
          simpa using hrow
        intro x hx
        exact List.all_eq_true.mp hall x hx
      · exact Or.inr (Or.inl ⟨q.kD, hC, hsl, hdom, hno, hf, hcl⟩)
#print axioms machPrem3_of_t1hyp

/-- E-3 (B7) for the real run, from `T1Hyp` + the named residuals + the carriers (`hin`, `hsp`, `hg`). -/
theorem auditE3_of_t1hyp3 {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (R : DataRes3 DataOk) (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf' P)) :
    ∀ c, Reach c → ∀ sp, SOf' P c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      (originAt sp k).child? = none → ∀ y : Tools.ShippingChildInv.Res, RealChildA L.O (sp.insts[k]'hk).1 y →
        y.1.name = ofDecl (sp.insts[k]'hk).1 := by
  have hS : ∀ c, Reach c → ∃ sp, SOf' P c = some sp := by
    intro c hc
    obtain ⟨q, hq, -, -⟩ := H.pkg c hc
    exact ⟨q.d.shape, by simp [SOf', hq]⟩
  have hcl : ReachClosed Reach (SOf' P) := by
    intro c hc sp hSc k hk hch
    obtain ⟨q, hq, -, -⟩ := H.pkg c hc
    simp only [SOf', hq, Option.map_some, Option.some.injEq] at hSc
    subst hSc
    exact H.closed c hc q hq k hk hch
  exact auditE3_of_q hcl (q_induct3 L.O L.T hin hsp hg hS (machPrem3_of_t1hyp H R hA) hcl)
#print axioms auditE3_of_t1hyp3
end S6
section Conc
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- The existing rows (T1L-12 `hMemRow`, T1L-04 `hrow`) plus the one fact found in no row for `Pkg` (`leafAlias`, named). -/
structure ConcRows (DataOk : Pkg ι dom → Prop) : Prop where
  hMemRow : ∀ q, DataOk q → MemParentDataOk q ∧ ExtInS q
  hrow : ∀ q, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
  leafAlias : ∀ q, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true

theorem dataRes3_of_rows {DataOk : Pkg ι dom → Prop} (C : ConcRows DataOk) : DataRes3 DataOk where
  callsRows := fun q hq _ => by
    obtain ⟨-, hc, hs, -, hd⟩ := MemParentDataOk.rows (C.hMemRow q hq).1
    exact ⟨hc, hs, hd⟩
  outTy := fun q hq => by
    obtain ⟨-, -, -, ho, -⟩ := MemParentDataOk.rows (C.hMemRow q hq).1
    exact ho
  leafAlias := C.leafAlias
  noMemRow := C.hrow
#print axioms dataRes3_of_rows

/-- the end-to-end: `T1Hyp` + the existing rows + `leafAlias` + `AdmCtx` + carriers give E-3 -/
theorem auditE3_of_rows {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (C : ConcRows DataOk) (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf' P)) :
    ∀ c, Reach c → ∀ sp, SOf' P c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      (originAt sp k).child? = none → ∀ y : Tools.ShippingChildInv.Res, RealChildA L.O (sp.insts[k]'hk).1 y →
        y.1.name = ofDecl (sp.insts[k]'hk).1 :=
  auditE3_of_t1hyp3 H (dataRes3_of_rows C) hA hin hsp hg
#print axioms auditE3_of_rows
end Conc
```

## 4. 台帳
- 受入: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- **条件付き台帳**: E-3（B7 の hn）−1、B3 −1（条件: T1L-12・T1L-04 が成り立つこと、および `leafAlias` の新 row が承認・供給されること）。新規 T1 +1（`leafAlias`、freeze 文書で reviewer 承認待ち）。差し引き、E-3/B3 の −2 に対し +1。E-12 `hsep(b)` は件数未確定。
- 「前提を足すことになるか」: 足すのは `leafAlias` の 1 行のみ。`noMemName`（偽になりうる）は足さない。TRUSTED/law/FG の変更はしていない。

## 5. 次
reviewer: AUD_UA4_FREEZE.md（`leafAlias` の完全な型と数の変化）の承認。承認後、E-3/B3 の Lean 実装（複製 2 本＋`q_induct3` 等）を新規ファイルに置く単位を別途起こす。
