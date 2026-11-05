# U-A4 / U-A5 調査 3: MachPrem の実供給と T1Hyp.closes との対応

- Issue: sparkle-aud-ua4。base: a58cd0e1（par/aud-ua4-study2、STUDY2 承認済み）。文書のみ（Lean のソースは編集していない。scratch は Pod 内の build 出力（`kjob lake build` 済みの olean）を `lean` に読ませて elaborate、ソースツリーに入れていない）。
- 種別: 調査（freeze ではない）。台帳: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- 「見つからなかった」は、この調査では供給元・経路が見つからなかったという意味で、不可能・導出不能の証明ではない。mutant は使っていない（signature/defeq での棄却の検査はしていない。意味的反例の主張もしていない）。

## 0. 結論（先に）

1. **`MachPrem` の各 field のうち、既存の定理で出せるものは 5 つ**: `MachineData`（`Pkg.d`）、`ok`（`Pkg.ok`）、`body`（`Pkg.body_eq`）、`entry`（`T1Hyp.defines`）、calls の `closes`（`T1Hyp.closes` がそのまま `MachineClosesAtA` の形で合う）。`T`（`RefLawsATele`）と `O`（`RefLawsAOps`）は `Laws` の field `L.T` / `L.O`（Gen2Defs:46-48）で、`toAOps` 系の補題は要らない。
2. **`MachineCloses` と `MachineClosesAtA` の関係**: `MachineCloses ⇒ MachineClosesAtA` は scratch で通った（`closesAtA_of_closes`、§3）。**逆（`T1Hyp.closes` から葉の `MachineCloses`）は出せなかった**: `MachineClosesAtA` は `JQC O n w ∧ 1 ≤ n` の world と `profLogIO b` だけを見るので、任意の world と任意の logger を見る `MachineCloses` は出ない（この調査では逆向きの経路は見つからなかった）。葉の `MachineCloses` は **`closes_of_data`（`d.letsOk` = `insts = []` ∧ `letsAliasOk`）** で出る（`leafCloses_of_data`、§3）。葉に必要な事実は `letsAliasOk = true` だけで、`DataOkB`（SrcPkg 用）は持つが `LeafDataOkB` / `MemParentDataOkB` は持たない。
3. **出せない（足りない事実）は 5 つに分かれる**（§1 の表、Lean の型は §3 の `DataRes2`）: (a) `callsOk kD` と `ss.length = slots.length`（台帳の既存行 T1L-39 / T1L-40 に当たる）、(b) `binders.drop kD` が domain でない（`DataRows` の 3 つ目。**T1 台帳に一般の calls 親向けの行は見つからなかった**。T1L-12 の `MemParentDataOk` は持つ）、(c) `outTy`（対応する T1 行は見つけていない）、(d) 葉の `letsAliasOk`（T1L-32 の `DataOkB` が持つ。具体 `DataOk` に入るかは A.P-20 の未了）、(e) **one-output 親（`instFields = []`）の `hnomem`**（origin 半分は T1L-04 `hrow` = `OneOutNoMemRow` がそのまま当たる。**名前半分 `memChild? x.1 = none` は既存の行に見つからなかった**）。
4. **STUDY2 の `MachPrem` の穴を 1 つ見つけた**: calls の枝が `instFields ≠ []`（group / memory 親）だけだった。`T1Hyp` は `insts ≠ [] ∧ instFields = []`（one-output 親、`CallField`）を許すので、その枝が無いと `hprem` が出せない。`deepChild_ifaceA'M`（Srm4Core5:44）は `hfne` を要求する。**その枝には元の `deepChild_ifaceA'`（SeqChildDeepConsumerA:66、`hnomem` 版）を使えて、`declRank` 帰納（`q_induct2`）も通った**（§3）。`MachPrem2` はその第 3 の disjunct を足したもの。
5. **合わせた scratch**（§3 の `auditE3_of_t1hyp`）: `T1Hyp` ＋ 名前付き残り `DataRes2`（5 field）＋ `AdmCtx`（Start から）＋ carrier（`hin`, `hsp`, `hg`）から、E-3 の文 `y.1.name = ofDecl (sp.insts[k]).1` が出る。sorry なし。`#print axioms` はすべて `[propext, Classical.choice, Quot.sound]`。B3 は `q_induct2` の `QY` から STUDY2 の `b3_of_q` がそのまま使える（同じ `QY`）。
6. **台帳は動かさない**（受入の数は不変）。`DataRes2` の各 field が既存の台帳行に当たるか、新しい前提になるかは §2。**条件付き台帳**: E-3 −1、B3 −1（`DataRes2` の (b)(c)(d)(e名前) が既存行に当たる、または具体 `DataOk` に入る場合）。(b)(c)(e名前) が既存行に当たらなければ、その数だけ +k（最大 +3、未確定）。E-12 の `hsep(b)` 部分は STUDY2 のとおり件数未確定。ユーザー判断は、新しい前提を足す場合（+k）にのみ必要になる見込み（今回は足していないので判断資料は書いていない）。

## 1. MachPrem の field ごとの供給表

`MachPrem2`（§3）の各 field を、既存の行から出せるかで分類。「T1Hyp」は Gen2Defs:207 の `T1Hyp L P Reach DataOk`。

| field | 出せるか | 補題 / 足りない事実の Lean の型 | 台帳の行 |
|---|---|---|---|
| `MachineData`（`∃ d, d.shape = sp`） | **出せる** | `T1Hyp.pkg`（`P c = some q`）の `q.d`、`SOf P c = (P c).map (·.d.shape)`（AuditUA1:31）で `d.shape = sp` は `rfl` | T1L-06（A.P-08） |
| `d.ok = true` | **出せる** | `Pkg.ok`（Gen2Pkg:88） | — |
| `d.shape.body = quote …` | **出せる** | `Pkg.body_eq`（Gen2Pkg:94） | — |
| `outTy : ∀ o ∈ outs, o.ty.bitWidth = o.width` | **出せない**（`DataOk` が持つ場合は出る） | 足りない事実: `∀ q, DataOk q → ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width`（`DataOkB` / `LeafDataOkB` / `MemParentDataOkB` の 4 行目に在るが、`T1Hyp` の `DataOk` は抽象 Prop） | FG A.P-09 に `outTy` の読み。**T1 側に対応する行は見つけていない**（PREMISE_LEDGER §、A.P-09 の行） |
| `entry : MachineDefines mctx mref cctx cref c d.shape` | **出せる**（`AdmCtx` の下） | `T1Hyp.defines c hc q hq mctx cctx hA`。`hA : AdmCtx L.O.quiet mctx cctx` は `Start`（Gen2Defs:56）の第 1 成分 | T1 の field（C.RR-3） |
| `hC : d.callsOk nDecl = true`（`nDecl := q.kD`） | **出せない** | `∀ q, DataOk q → q.d.shape.insts ≠ [] → q.d.callsOk q.kD = true`。`DataOkB` / `LeafDataOkB` / `MemParentDataOkB` は持つ | **T1L-39**（A.P-09 の読み） |
| `hslots : d.ss.length = slots.length` | **出せない** | `∀ q, DataOk q → … → q.d.ss.length = q.d.shape.layout.slots.length` | **T1L-40** |
| `hdomB : ∀ b ∈ binders.drop nDecl, b.2 ≠ .domain` | **出せない** | `∀ q, DataOk q → … → ∀ b ∈ q.d.shape.binders.drop q.kD, b.2 ≠ .domain`（`DataRows` の 3 つ目、PostFacts:56-60 に「`DataOkB` に無い、UNSUPPLIED」）。`MemParentDataOkB` は持つ（`MemParentDataOk.rows`、Gen2MemData:16） | T1L-12 は memory 親のみ。**一般の calls 親向けの行は見つからなかった**（T1 台帳 §で `DataRows` は T1L-39/40 の 2 conjunct のみ） |
| `hins : d.shape.insts ≠ []` | 場合分け（`by_cases`） | 葉（`insts = []`）か calls（`≠ []`）かの分割。事実ではない | — |
| `hfne : d.shape.instFields ≠ []` | **場合分け**（出ない場合がある） | `instFields ≠ []`（group / memory 親）か `= []`（one-output 親）。`= []` の枝は `MachPrem2` の第 3 disjunct（下の `hnomem`） | — |
| `hnomem`（one-output 親、origin 半分） | **出せる**（行がある） | `OneOutNoMemRow`（DataBridge:37）= `(!instFields.isEmpty \|\| instTagged.all (·.2.child?.isNone)) = true`。`instFields = []` の下で `∀ x ∈ instTagged, x.2.child?.isNone = true` がそのまま出る（scratch） | **T1L-04**（`hrow`、A.P-26 / C.CR-1 と同じ行） |
| `hnomem`（one-output 親、名前半分） | **出せない** | `∀ q, DataOk q → insts ≠ [] → instFields = [] → ∀ x ∈ q.d.shape.instTagged, (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true` | FG A.P-26 は「名前半分は O-copies で除去済み」と記す。**この `deepChild_ifaceA'` 経路では再び要る。既存行には見つからなかった**（新しい前提なら +1） |
| 葉の `closes : ∀ mctx' cctx', MachineCloses …` | **出せない**（`letsAliasOk` があれば出る） | `closes_of_data`（ClosesData:226）が `d.letsOk`（`insts = []` ∧ `letsAliasOk`）から出す（`leafCloses_of_data`）。足りない事実: `∀ q, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true`。別経路: `layout.lets = 0` なら `machineCloses_of_noLets`（MachineEntry:2371） | T1L-32（`DataOkB` が `letsAliasOk` を持つ。ただし T1L-32 は registry、具体 `DataOk` は A.P-20 の未了） |
| calls の `closes : ∀ mctx' cctx', AdmCtx → MachineClosesAtA O …` | **出せる** | `T1Hyp.closes c hc q hq mctx' cctx' hA'` がそのまま合う（`q.d.shape` で型が一致、scratch で確認） | **T1L-08**（G-CLOSES、A.P-07） |
| `T : RefLawsATele O.quiet mref cref` | **出せる** | `L.T`（`Laws` の field、Gen2Defs:48） | — |
| `O : RefLawsAOps MkRefd mref cref` | **出せる** | `L.O`（Gen2Defs:47）。`toAOps` 系の補題は不要 | — |

## 2. closes の対応（葉の `MachineCloses` と calls の `MachineClosesAtA`）

- 定義（Tools/ShippingMachineEntry.lean:2363, Tools/ShippingChildRunAKids.lean:158）:
  - `MachineCloses mctx mref cctx cref c sh := ∀ {tenv} logProf w r w', RunsTo (synthesizeMachineCertified … logProf c sh) … → r ≠ none`（任意の world と任意の logger）。
  - `MachineClosesAtA O mctx cctx c sh := ∀ {tenv} b n w r w', JQC O n w → 1 ≤ n → RunsTo (synthesizeMachineCertified … (profLogIO b) c sh) … → r ≠ none`（`JQC` の world と `profLogIO b` に限る）。
- **含意の向き: `MachineCloses ⇒ MachineClosesAtA`**（`logProf := profLogIO b` と取るだけ。`closesAtA_of_closes`、§3、追加の前提なし）。逆は、この調査では出せなかった（`MachineCloses` は `JQC` でない world でも要る）。
- **葉**（`seqChild_of_realA`、SeqChildIfaceA:167）は `MachineCloses`（全 ctx）を要る。`seqChild_ifaceA` が `closesM` を 2 箇所で使う（`hrun9` での `hne` と `synthesizeCombinationalCore_machine_sound`、後者は `RunsTo` の world を選べない）ので、`AtA` に差し替えるには新しい Lean（`synthesizeCombinationalCore_machine_sound` の `AtA` 版）が要る。この調査ではそこまでしていない。代わりに `closes_of_data` 経由（`letsAliasOk`）で葉の `MachineCloses` が出ることを確かめた。
- **calls**（`deepChild_ifaceA'M` / `deepChild_ifaceA'`）は `∀ mctx' cctx', AdmCtx → MachineClosesAtA`。`T1Hyp.closes` と型が一致する（同じ `L.O`、`q.d.shape`）。

## 3. scratch（`set_option autoImplicit false`、sorry なし）

import: `Tools.ShippingGen2Data`, `Tools.ShippingGen2MemData`, `Tools.ShippingSrm4Core5`, `Tools.ShippingGen5NameKids3`, `Tools.ShippingCacheCoherentRun`, `Tools.ShippingSeqChildDeepConsumerA`, `Tools.ShippingSrm12Corr`（`kjob lake build` 済み、exit 0）。本体は STUDY2 §3 のコード（再現して通ることを確認した）に、下の 3 つを足したもの。`#print axioms closesAtA_of_closes / leafCloses_of_data / q_induct2 / machPrem2_of_t1hyp / auditE3_of_t1hyp` = すべて `[propext, Classical.choice, Quot.sound]`。

### 3.1 closes（§2）

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
```

### 3.2 one-output 枝（`MachPrem2`、`q_induct2`）

`MachPrem2` は STUDY2 の `MachPrem` の最後に第 3 の disjunct を足したもの:

```lean
def MachPrem2 {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
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
        (∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
          (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true) ∧
        ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
          Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape))
```

`q_induct2` は STUDY2 の `q_induct` の複製で、(i) `MachPrem` → `MachPrem2`、(ii) `rcases hcase with … | ⟨nDecl, hC, hslots, hdomB, hins, hnomem, closes⟩` を足す、(iii) `key` の最後（`final` の `intro c hc y hy` の直前）に下の枝を足す。他は同一。`deepChild_ifaceA'` は `RealChildA` の子を返すので、`kids` の `Or.inr ⟨hch, hrc⟩`（普通の子）で `KidOK` を取る。

```lean
      · have hch : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none := by
          intro k hk
          have := (hnomem _ (Tools.ShippingSrm12Corr.instTagged_mem_idx d.shape hk)).1
          simpa using this
        have hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
            RealChildA O (d.shape.insts[k]).1 y' →
            ∀ a ∈ y'.1 :: y'.2.modules, a.name ≠ ofDecl c :=
          fun k hk y' hrc => kidOK_hsep hin hsp hc (kids k hk y' (Or.inr ⟨hch k hk, hrc⟩))
        obtain ⟨-, -, -, -, M, D, -, -, -, -, hpost, hdes, hMn, hb, -, hinst, hreal, -⟩ :=
          Tools.ShippingSeqChildDeepConsumerA.deepChild_ifaceA' O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes hy
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
```

### 3.3 T1Hyp から（`MachPrem2` の供給と E-3）

```lean
section S6
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

/-- the SOf of AuditUA1 (Tools/ShippingGen5AuditUA1.lean:31) -/
def SOf' (P : Pkgs ι dom) : Name → Option MachineShape := fun c => (P c).map (fun q => q.d.shape)

/-- Named residual facts about `DataOk` (NOT derived), second version with the one-output branch. -/
structure DataRes2 (DataOk : Pkg ι dom → Prop) : Prop where
  callsRows : ∀ q, DataOk q → q.d.shape.insts ≠ [] →
    q.d.callsOk q.kD = true ∧ q.d.ss.length = q.d.shape.layout.slots.length ∧
      (∀ b ∈ q.d.shape.binders.drop q.kD, b.2 ≠ .domain)
  outTy : ∀ q, DataOk q → ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width
  leafAlias : ∀ q, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true
  /-- the one-output row (origin half), `OneOutNoMemRow` (Tools/ShippingGen2DataBridge.lean) -/
  noMemRow : ∀ q, DataOk q →
    (!q.d.shape.instFields.isEmpty || q.d.shape.instTagged.all (fun x => x.2.child?.isNone)) = true
  /-- the name half: no kid of a one-output parent is named like a memory module -/
  noMemName : ∀ q, DataOk q → q.d.shape.insts ≠ [] → q.d.shape.instFields = [] →
    ∀ x ∈ q.d.shape.instTagged, (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true

theorem machPrem2_of_t1hyp {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (R : DataRes2 DataOk) (hA : AdmCtx L.O.quiet mctx cctx) :
    ∀ c, Reach c → ∀ sp, SOf' P c = some sp → MachPrem2 (mctx := mctx) (cctx := cctx) L.O c sp := by
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
        exact ⟨List.all_eq_true.mp hall x hx, R.noMemName q hdo hno hf x hx⟩
      · exact Or.inr (Or.inl ⟨q.kD, hC, hsl, hdom, hno, hf, hcl⟩)
#print axioms machPrem2_of_t1hyp

/-- E-3 (B7) for the real run, from `T1Hyp` + the named residuals + the carriers (`hin`, `hsp`, `hg`). -/
theorem auditE3_of_t1hyp {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk) (R : DataRes2 DataOk) (hA : AdmCtx L.O.quiet mctx cctx)
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
  exact auditE3_of_q hcl (q_induct2 L.O L.T hin hsp hg hS (machPrem2_of_t1hyp H R hA) hcl)
#print axioms auditE3_of_t1hyp
end S6
```

名前付き残り `DataRes2` の 5 field が、この調査で既存の行から出せなかった事実のすべて（`T1Hyp` の `DataOk` が抽象 Prop なので、`DataOk` の具体化に依存する）。

## 4. 台帳への当たり

| `DataRes2` の field | 既存の行 | 判定（Lean の型の同値は確認していない） |
|---|---|---|
| `callsRows` の `callsOk kD`, `ss.length = slots.length` | T1L-39, T1L-40 | 当たる（名前と役割） |
| `callsRows` の `hdomB`（`.domain` 行） | T1L-12（memory 親のみ） | **一般の calls 親には当たらない**（見つからなかった）。具体 `DataOk` が持てば当たる（A.P-20 の未了） |
| `outTy` | FG A.P-09 の読みのみ | **T1 側に当たる行を見つけていない**（FG 側の A.P-09 / A.P-20 の枠） |
| `leafAlias`（`letsAliasOk`） | T1L-32（`DataOkB`） | 当たる可能性（`DataOkB` は持つ。`LeafDataOkB` は持たない。具体 `DataOk` の選び方次第） |
| `noMemRow` | T1L-04 | 当たる |
| `noMemName` | なし | **見つからなかった**。新しい前提なら +1 |

- 受入済みの数は動かさない: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- **条件付き台帳**: E-3（B7 の hn）−1、B3（inst 先 ＋ 名前）−1 の見込み。条件は `DataRes2` の `hdomB`・`outTy`・`leafAlias` が具体 `DataOk`（A.P-20）または既存行に入ること、`noMemName` が既存行に当たること（当たらなければ +1）。E-12 の `hsep(b)` 部分は STUDY2 のとおり件数未確定。受理待ちであり、受入の数には入れない。

## 5. 次

- reviewer: §1 の表（特に `hdomB` / `outTy` / `noMemName` の「既存行に見つからなかった」の読み）、§2 の含意の向き（`MachineCloses ⇒ MachineClosesAtA` のみ）、§0-4 の `instFields = []` 枝の指摘と `MachPrem2` の第 3 disjunct。
- 続く作業: (1) 具体 `DataOk`（A.P-20）が `hdomB` / `outTy` / `letsAliasOk` を持つか、持たせるなら freeze（reviewer の承認が要る: 前提の追加・付け替え）。(2) `noMemName` の供給（`T1Hyp.dec` の `MemDec` との関係、`Reach` の名前）を調べる。(3) 葉の `AtA` 版（`synthesizeCombinationalCore_machine_sound` の複製）が要るかは、(1) の結果次第。
