# U-A4 / U-A5 調査 2: B3 の inst 先、DescProv の供給経路、E-3 の組み立て

- Issue: sparkle-aud-ua4。base: par/aud-ua4-decision 46706a9f。文書のみ（Lean のソースは編集していない。scratch は `kjob lake env lean` で elaborate、ソースツリーに入れていない）。
- 種別: 調査（freeze ではない）。台帳: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- 「見つからなかった」は、この調査では見つからなかったという意味で、不可能の証明ではない。mutant は使っていない（signature/defeq での棄却の検査はしていない）。

## 0. 結論（先に）

1. **DescProv は、共有定義を変えずに、既存の定理の出力から出せた（UA7C §3 の止まりを越えた）。** 経路は (a) 寄り: `deepChild_ifaceA'M`（Tools/ShippingSrm4Core5.lean:44）の出力 `hreal`「run の design の module はどれかの子の結果の module（top か design）」と `hinst`「top の inst 先は design にある」を、**declRank の帰納**で使う。`RealChildA.run` の入れ子の `CloseCalls` は要らない（run の構造ではなく、既存定理が run から取り出した子の事実を使う）。
2. **hsep の循環は無い。** `deepChild_ifaceA'M` の前提 `hsep` は、`y.2.modules = D.modules`（`synthesizeCombinational_designL` の「top と同名の module が design に無ければ」）にだけ使われる。`hsep`（子の結果の名前が `ofDecl c` でない）は、**子の帰納仮定**（子 `c'` の top の名前は `ofDecl c'`、design の名前はメモリか `c'` の strict descendant）と `strictDesc_irrefl`（UA7C §4）から作る。
3. **B3 の inst 先の部分は DescProv に帰着し、同じ帰納で閉包も出た**（下の `OutClosedY`）: 子の top と design の module の body の `Stmt.inst` の先は、子の design の module 名のどれか。したがって `ns := (子の top :: design の module).map name` と取れば、`ChildIfaceP` の `desNames` と `closed` の欄、および B3 `ofDecl c ∉ ns` が出る（`b3_of_q`）。B3 の残りは DescProv だけ、という期待は成り立った。ただし `ChildIfaceP` の他の欄（`nIn`, `outs`, `memOk` など）はこの調査の対象外。
4. **E-3 の declRank 帰納の組み立ても通った**（`q_induct` → `auditE3_of_q`）。仮定は名前付きで §3 に列挙。`#print axioms` はすべて `[propext, Classical.choice, Quot.sound]`、sorry なし。
5. **残る仮定（この調査では供給元を確認していない）**: `MachPrem`（§3）= 各 reached 宣言の `MachineData` と `seqChild_of_realA` / `deepChild_ifaceA'M` の前提（`hC`, `hslots`, `hdomB`, `hins`, `hfne`, `outTy`, `entry`, `closes`）。`closes` は葉で `MachineCloses`、calls で `MachineClosesAtA` の形で置いた（`T1Hyp.closes` との対応は UA4 STUDY §1.3 のとおり未確認）。`RefLawsATele`（`T`）も引数。これらは既存の `T1Hyp.pkg` / `DataOk` / `Laws` から出る見込みだが**接続は未確認**。
6. **ユーザー判断は要らない**（UA7C §5 の P1 共有定義の変更 / P2 新しい文は不要になった: 新しい前提・law・共有定義の変更は 0）。台帳は動かさない。**条件付き台帳**: `MachPrem` の接続が既存の行から払えれば、E-3（B7）−1、B3 −1、E-12 の `hsep(b)` 部分（UA7B/UA7C）が消える見込み（件数は未確定。接続が新前提を要するなら +k）。受入の数は変えない。

## 1. B3 の inst 先
`ChildIfaceP.closed`（Tools/ShippingMemClosesKids.lean:181）は「b :: design の module の body の `Stmt.inst mn …` なら `mn ∈ names`」。名前の集合 `names` は存在量化されている（AuditE4_B3B4）ので、`names := (b :: design.modules).map name` と取れば、必要なのは「inst 先は b :: design の module 名」＝ design が閉じていること。

- 既存の `InstClosed`（Gen2Defs:142）は**入る向き**（design の各 module はどこかから instantiate される）で、出る向きの閉包ではない。`ChildShips`（Gen2Defs:92）の `RunOn`/`ResetN` も、深さ 0 の run は inst を見ない（MachineDepth:27, :52）ので、閉包の根拠にならない（この調査では使えなかった）。
- 出る向きの閉包は、**`deepChild_ifaceA'M` の `hinst`（`∀ mn i conns, inst mn i conns ∈ M.body → ∃ mc, moduleByName D.modules mn = some mc`）と `hreal` の最後の conjunct（子の top と design の module の名前は D.modules に全て在る）** から、子ごとの閉包を帰納で積み上げて出た（`q_induct` の `OutClosedY`）。葉は `ChildIfaceG.seqOk`（body は assign/register のみ、inst なし）と `design.modules = []`。メモリ子は `memModule` の body に inst が無い。
- よって B3 の追加分（inst 先）は DescProv（名前の部分）と同じ帰納で払われる。**B3 の残りは DescProv だけ**。

## 2. DescProv の供給経路
UA7C §3 の止まり: `RealChildA.run` は入れ子の `CloseCalls` を持たない。
- 候補 (a)「出力の生成側から名前を出す」: `designWith` / `closeInsts` / `dedup` の名前の付け方を直接読む代わりに、**それを既に読んでくれている `deepChild_ifaceA'M` の `hreal`** を使えた。`hreal : ∀ g ∈ D.modules, ∃ k y', KidTA … y' ∧ (g = y'.1 ∨ g ∈ y'.2.modules) ∧ …`。つまり design の各 module は「子の結果の module」。子が `KidTA` なので、(i) メモリ origin なら `memModule`（`IsMem`）、(ii) そうでなければ `RealChildA` の `c' = (insts[k]).1`。
- (ii) は `ordEdge_of_idx`（`GraphAgrees` から `OrdEdge g c c'`）と `rank_of_ordEdge` で rank が下がるので、declRank の強い帰納で `RealChildA O c' y' → QY g c' y'` を使える。
- 帰納で運ぶ述語 `QY g c y := y.1.name = ofDecl c ∧ DescProvY g c y ∧ OutClosedY y`。
- (b) 名前だけの帰納（ClosingRun の InvAt を要らない弱い形）としても読めるが、実際には (a) の道具（既存定理の出力）で足りた。ClosingRun / `CacheShips` は使っていない。
- 結果: DescProv を `Laws`/`InvAt` に足す必要が無い。UA7C §5 の P1（共有定義の変更）/ P2（新しい文）は不要。

## 3. scratch（`set_option autoImplicit false`、sorry なし）
import は `Tools.ShippingSrm4Core5`, `Tools.ShippingGen5NameKids3`, `Tools.ShippingCacheCoherentRun`（`kjob lake build` 済み、各 exit 0）。`#print axioms q_induct / auditE3_of_q / b3_of_q` = `[propext, Classical.choice, Quot.sound]`。

**仮定（名前付き、供給は未確認）**
- `hin : InClass g B top = true`, `hsp : ReachSpans g top Reach`, `hg : GraphAgrees g Reach S`, `hcl : ReachClosed Reach S`, `hS : ∀ c, Reach c → ∃ sp, S c = some sp` — AuditE5/E-7/E-8 と `T1Hyp.closed`（既存の行、U-A1〜U-A3）。
- `hprem : ∀ c, Reach c → ∀ sp, S c = some sp → MachPrem O c sp` — 上記 5.。`O`, `T`（`RefLawsAOps`, `RefLawsATele`）, `mctx`, `cctx` は引数。
- `ChildIfaceP` の他の欄は扱っていない（`hkid` の供給元は AUDIT_CARRIER_FREEZE §2 のとおり未確認のまま）。

**mutant**: 扱っていない。

```lean
def StrictDesc (g : CallGraph) (a b : Name) : Prop := ∃ x, OrdEdge g a x ∧ OrdPath g x b

theorem strictDesc_irrefl {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach)
    {c : Name} (hc : Reach c) : ¬ StrictDesc g c c := by
  rintro ⟨x, he, hp⟩
  obtain ⟨r0, h0, -, -⟩ := Tools.ShippingSrm7Rank.inClass_rank hin
  obtain ⟨r, hr, -⟩ := rank_of_reach h0 (hsp c hc)
  obtain ⟨r1, h1, hlt⟩ := rank_of_ordEdge hr he
  obtain ⟨r2, h2, hle⟩ := rank_of_reach h1 hp
  rw [hr] at h2
  have := Option.some.inj h2
  omega

theorem ordPath_cons {g : CallGraph} {x y b : Name} (he : OrdEdge g x y) (hp : OrdPath g y b) :
    OrdPath g x b := by
  induction hp with
  | refl => exact OrdPath.step OrdPath.refl he
  | step _ e ih => exact OrdPath.step ih e

theorem strictDesc_of_edge_left {g : CallGraph} {a x b : Name} (h1 : OrdEdge g a x) (h2 : StrictDesc g x b) :
    StrictDesc g a b := by
  obtain ⟨y, he, hp⟩ := h2
  exact ⟨x, h1, ordPath_cons he hp⟩

theorem strictDesc_of_edge {g : CallGraph} {a x : Name} (h1 : OrdEdge g a x) : StrictDesc g a x :=
  ⟨x, h1, OrdPath.refl⟩

theorem ordEdge_of_idx {g : CallGraph} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hg : GraphAgrees g Reach S) {c : Name} (hc : Reach c) {sp : MachineShape} (hS : S c = some sp)
    {k : Nat} (hk : k < sp.insts.length) (hch : (originAt sp k).child? = none) :
    OrdEdge g c (sp.insts[k]'hk).1 := by
  refine ⟨sp.instTagged, originAt sp k, ?_, Tools.ShippingSrm12Corr.instTagged_mem_idx sp hk, ?_⟩
  · rw [hg c hc, hS]; rfl
  · cases ho : originAt sp k with
    | ord => rfl
    | field i => rfl
    | mem cb aw dw => rw [ho] at hch; simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?] at hch

theorem moduleByName_spec {ms : List Sparkle.IR.AST.Module} {mn : String} {mc : Sparkle.IR.AST.Module}
    (h : Sparkle.IR.Machine.moduleByName ms mn = some mc) : mc ∈ ms ∧ mc.name = mn := by
  unfold Sparkle.IR.Machine.moduleByName at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

section Q
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingCacheCoherentRun (IsMem)
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- the name fact (UA7C `DescProv`, §4) -/
def DescProvY (g : CallGraph) (c : Name) (y : Res) : Prop :=
  ∀ a ∈ y.2.modules, IsMem a ∨ ∃ c', StrictDesc g c c' ∧ a.name = ofDecl c'

/-- instantiation targets of the result's modules are names of the result's design -/
def OutClosedY (y : Res) : Prop :=
  ∀ a ∈ y.1 :: y.2.modules, ∀ mn i cs, Stmt.inst mn i cs ∈ a.body → ∃ g' ∈ y.2.modules, g'.name = mn

def QY (g : CallGraph) (c : Name) (y : Res) : Prop :=
  y.1.name = ofDecl c ∧ DescProvY g c y ∧ OutClosedY y

/-- a kid result, seen from its parent `c` -/
def KidOK (g : CallGraph) (c : Name) (y : Res) : Prop :=
  (∀ a ∈ y.1 :: y.2.modules, IsMem a ∨ ∃ c', StrictDesc g c c' ∧ a.name = ofDecl c') ∧ OutClosedY y

theorem kidOK_hsep {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) {c : Name} (hc : Reach c)
    {y : Res} (h : KidOK g c y) : ∀ a ∈ y.1 :: y.2.modules, a.name ≠ ofDecl c := by
  intro a ha e
  rcases h.1 a ha with ⟨cb, aw, dw, ea⟩ | ⟨c', hd, hn⟩
  · rw [ea, Tools.ShippingCacheCoherentRun.memModule_name] at e
    exact Tools.ShippingModuleName.ofDecl_ne_ofMem c cb aw dw e.symm
  · rw [hn] at e
    have := Tools.ShippingModuleName.ofDecl_injective e
    subst this
    exact strictDesc_irrefl hin hsp hc hd

theorem memModule_kidOK (g : CallGraph) (c : Name) (cb : Bool) (aw dw : Nat) :
    KidOK g c (Sparkle.Compiler.MachMemory.memModule cb aw dw) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    left
    simp [Sparkle.Compiler.MachMemory.memModule] at ha
    rcases ha with rfl | rfl <;> exact ⟨cb, aw, dw, rfl⟩
  · intro a ha mn i cs hm
    simp [Sparkle.Compiler.MachMemory.memModule] at ha
    rcases ha with rfl | rfl <;> simp [Sparkle.Compiler.MachMemory.memModule] at hm

/-- Named premises (NOT discharged here): for a reached `c` with shape `sp`, the machine data and the
hypotheses of `seqChild_of_realA` (leaf) / `deepChild_ifaceA'M` (calls), minus `hsep`. -/
def MachPrem {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
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
          Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape))

theorem q_induct {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach S)
    (hS : ∀ c, Reach c → ∃ sp, S c = some sp)
    (hprem : ∀ c, Reach c → ∀ sp, S c = some sp → MachPrem (mctx := mctx) (cctx := cctx) O c sp)
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
      rcases hcase with ⟨hno, closes⟩ | ⟨nDecl, hC, hslots, hdomB, hins, hfne, closes⟩
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
  intro c hc y hy
  obtain ⟨r, hr, -⟩ := rank_of_reach h0 (hsp c hc)
  exact key r c hc hr y hy
end Q

section Cor
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildInv (Res)
open Tools.ShippingCacheCoherentRun (IsMem)
open Sparkle.IR.AST (Stmt)
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- AuditE3 (E-3 / B7) from the induction, with `Q` as a named hypothesis. -/
theorem auditE3_of_q {O : RefLawsAOps MkRefd mref cref} {g : CallGraph} {Reach : Name → Prop}
    {S : Name → Option MachineShape} (hcl : ReachClosed Reach S)
    (Q : ∀ c, Reach c → ∀ y, RealChildA O c y → QY g c y) :
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      (originAt sp k).child? = none → ∀ y : Res, RealChildA O (sp.insts[k]'hk).1 y →
        y.1.name = ofDecl (sp.insts[k]'hk).1 := by
  intro c hc sp hS k hk hch y hy
  exact (Q _ (hcl c hc sp hS k hk (by simpa using hch)) y hy).1

/-- B3 for an ordinary kid: with `ns := names of the kid's top and design`, the design-name field,
the inst-target field of `ChildIfaceP`, and `ofDecl c ∉ ns` all follow from `QY` of the kid. -/
theorem b3_of_q {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) {c c' : Name} (hc : Reach c)
    (he : OrdEdge g c c') {y : Res} (hq : QY g c' y) :
    let ns := (y.1 :: y.2.modules).map (·.name)
    (∀ a ∈ y.2.modules, a.name ∈ ns) ∧
    (∀ a ∈ y.1 :: y.2.modules, ∀ mn i cs, Stmt.inst mn i cs ∈ a.body → mn ∈ ns) ∧
    ofDecl c ∉ ns := by
  intro ns
  refine ⟨fun a ha => List.mem_map.mpr ⟨a, List.mem_cons_of_mem _ ha, rfl⟩, ?_, ?_⟩
  · intro a ha mn i cs hm
    obtain ⟨g', hg', rfl⟩ := hq.2.2 a ha mn i cs hm
    exact List.mem_map.mpr ⟨g', List.mem_cons_of_mem _ hg', rfl⟩
  · intro hmem
    obtain ⟨a, ha, e⟩ := List.mem_map.mp hmem
    have K : KidOK g c y := by
      refine ⟨?_, hq.2.2⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr ⟨c', strictDesc_of_edge he, hq.1⟩
      · rcases hq.2.1 a ha with hm | ⟨c'', hs, hnm⟩
        · exact Or.inl hm
        · exact Or.inr ⟨c'', strictDesc_of_edge_left he hs, hnm⟩
    exact kidOK_hsep hin hsp hc K a ha e
end Cor
```

## 4. 台帳 / 判断
- 今回増やした前提: 0。減らしたもの: 0。受入済み: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- 条件付き台帳: §0-6。`MachPrem` の接続次第。
- ユーザー判断: 不要（P1/P2 は不要になった）。B4 は承認済みの案 (3)。
- 次: reviewer: §2 の経路（`hsep` の循環が無いこと、`hreal` の読み）、§3 の仮定の列挙。続く調査: `MachPrem` を `T1Hyp.pkg`/`DataOk`/`Laws` から出す接続（`MachineCloses` と `MachineClosesAtA` の対応を含む）。その後に freeze（`QY` 帰納の Lean 化は新規ファイル、前提の増減が無ければ review 不要の分担）。
