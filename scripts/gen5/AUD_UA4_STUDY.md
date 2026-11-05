# U-A4 / U-A5 調査: E-3（B7 子の名前）と E-4 の B3 / B4 の供給元

- Issue: sparkle-aud-ua4（親 sparkle-ledger-shorten）。base: par/aud-ua7c 69f8b5f7。文書のみ（Lean のソースは編集していない）。
- 種別: 調査（freeze ではない）。台帳: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- 用語: `AuditE3` / `AuditE4_B3B4` は scripts/gen5/AUDIT_CARRIER_FREEZE.md §2。(b) = UA7B/UA7C の「子の design の module 名が `ofDecl declName` でない」。「見つからなかった」は不可能の証明ではない。

## 0. 結論（先に）

1. **E-3（B7）は、`Reach` の宣言がすべて machine route の `Pkg` を持つ（`T1Hyp.pkg`、Tools/ShippingGen2Defs.lean:207-210）ことから、gate/memo/legacy の経路を考えずに済む。** machine の葉は無条件に近い形で出る（`seqChild_of_realA` の `ChildIfaceG.name`、Tools/ShippingSeqChildIfaceA.lean:167）。calls を持つ machine は `deepChild_ifaceA'M`（Tools/ShippingSrm4Core5.lean:44）の `M.name = ofDecl c` と `post_name`（Tools/ShippingSrm5Deep.lean:38）から出るが、**その前提に UA7B/UA7C の (b) 型の `hsep`（その宣言自身の子の結果の module 名が `ofDecl c` でない）が入る**。よって E-3 は (b) の供給元（`DescProv`）が無い範囲で、この調査では完結しない（§1）。UA7B の (a) で使った事実（`ChildIfaceP.name`）とは**逆向き**: UA7B は `hname` を使う側、E-3 は `hname` を出す側。
2. **E-4 の B3 は UA7C の (b) と同じ未供給部分を含む**（§2）。B3 は (b)（design の module 名）に加えて、子と子の design の inst 先の名前も含む（`ChildIfaceP.closed`）。**重複させず、UA7C の `DescProv` に任せる**。`DescProv` が供給されたときに B3 に残る追加分（inst 先）は、この調査では供給元・経路が見つからなかった。
3. **E-4 の B4 は、現行の型のままでは、共有する子孫がある宣言（例 `mixDeep`）で偽になる**（§3）。`ChildIfaceP.desNames` が design の module 名を `namesK` に入れるので、2 つの子の design に同じ名前の module があれば、`namesK` の取り方によらず B4 の第 2 conjunct が成り立たない（scratch `b4_refuted`）。リポジトリの既存文書（docs/parallel/A-shared-descendant.md、Tools/ShippingCallsKidsS.lean ヘッダ）も同じ指摘で、`hdisjD` は `mixDeep` で偽、と書いている。供給の問題ではなく**文の範囲の問題**で、台帳に載せている文が全プログラムで成り立つとは限らない。選択肢は §5（ユーザー判断が要る可能性。新しい law・範囲縮小・文の変更は行っていない）。
4. 台帳は動かさない（FG 94 / T1 54、今回 0 / 0）。新しい前提は足していない。

## 1. E-3（B7）: `RealChildA O c y → y.1.name = ofDecl c`

### 1.1 `Reach` の中身
`T1Hyp.pkg : ∀ c, Reach c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q`、`T1Hyp.defines`（`MachineDefines`）、`T1Hyp.closes`（`MachineClosesAtA`）、`T1Hyp.closed`（ordinary 呼び出し先も `Reach`）。E-3 の `c` は `(sp.insts[k]).1` で `child? = none`、`T1Hyp.closed` により `Reach c`、よって `Pkg` を持つ。`Pkg.ok` / `Pkg.body_eq` は定理（Tools/ShippingGen2Pkg.lean:88, :94）。

### 1.2 経路ごとの表
| 場合 | 使う定理 | file:line | 結果 |
|---|---|---|---|
| callee が葉（`insts = []`） | `seqChild_of_realA` の `.name` | Tools/ShippingSeqChildIfaceA.lean:167 | 前提: `d.ok`, `hbody`, `hno`, `outTy`, `MachineDefines`, `MachineCloses`。scratch `e3_leaf` で elaborate。`T1Hyp.closes` は `MachineClosesAtA` で、`MachineCloses`（Tools/ShippingMachineEntry.lean:2363）との対応は**この調査では確認していない** |
| callee が calls を持つ | `deepChild_ifaceA'M` + `dropZW_name`/`mergeChecked_name`（`post_name` 相当） | Tools/ShippingSrm4Core5.lean:44; Tools/ShippingSrm5Deep.lean:38 | scratch `e3_calls`。前提に **`hsep`: その callee `c` の各子 `y'` の `y'.1 :: y'.2.modules` の名前が `ofDecl c` でない** が入る |
| 名前を `ChildIfaceP.name` で | `hname_of_iface` | Tools/ShippingSrm15Graph.lean:58 | `ChildIfaceP (ofDecl callee) …` を仮定に取る（出す側ではない） |
| `KeyTop`（cache の entry の名前） | `keyTop_empty`, `keyTop_insert` | Tools/ShippingLeafMissCoh.lean:43, :66, :69 | 挿入する entry の名前が `ofDecl n` のときに保たれる条項。ヘッダに「葉以外の entry は導いていない」とある（:21-29）。**cache の条項で `RealChildA` の名前を出す定理ではない** |
| gate / memo / legacy / parametric | `first_child_name`（Tools/ShippingGateDesignWalk.lean:1182）ほか | | `Pkg`（machine route）の `Reach` では使わない（§1.1） |

### 1.3 具体的に供給されていないもの
1. calls を持つ callee の `hsep`（上表）。callee `c` の子の結果の名前が `ofDecl c` でない、という (b) と同型の事実。子の自身の名前は E-3 を `c` の子に再適用（`declRank` の帰納法。`T1Hyp.closes` は全 reached 宣言に与えられているので、帰納仮定は `closes` ではなく E-3 そのもの）、**子の design の名前は `DescProv`（UA7C §4）が要る**。
2. `deepChild_ifaceA'M` の他の前提 `hC`, `hslots`, `hdomB`, `hins`, `hfne`, `outTy`: `DataOk`（`T1Hyp.pkg`）や `Pkg` の事実（Tools/ShippingGen2PostFacts.lean:56-60 の `DataRows`）から出ると見込むが、**この調査では接続を確認していない**。
3. `RefLawsATele`（`T`）: `Laws` の field と見込むが、確認していない。

### 1.4 scratch の結果
`e3_leaf`, `e3_calls`（`hsep` を仮定のまま）が `set_option autoImplicit false` で通った。axiom は標準 3 つのみ。

## 2. E-4 の B3（hparentD）

- 型: `∀ k, ofDecl c ∉ namesK k`（Tools/ShippingCallsMemPinned.lean:255、`callsPureGP_of_memKids'` :225 の前提。Tools/ShippingCallsKidsD.lean:130 も同じ）。使い所: `hparentD k hk (e ▸ full.closed g hin mn i conns hm)`（Tools/ShippingCallsKidsD.lean:316）。**`namesK k` は `ChildIfaceP` の `names`: design の module 名（`desNames`）と、子と design の inst 先（`closed`）の和集合を含む**（Tools/ShippingMemClosesKids.lean:167-180）。
- よって B3 ⇒ (i) 子の design の module 名が `ofDecl c` でない（UA7C の (b) の design 部分）、(ii) 子と design の module の body に `Stmt.inst (ofDecl c) …` がない。scratch `b3_gives_hsepB`, `b3_gives_instTargets`（axiom は標準 3 つ）。
- (i) は **UA7C の未供給部分（`DescProv`）と同じ**。UA7C `hsepB_of_descProv` が `DescProv` と `strictDesc_irrefl` から出す。重複させない。
- (ii) 子の module の inst 先: 子 `c'` の graph の callee（`GraphAgrees` / `InstBwd`）が `c` でないこと。`strictDesc_irrefl` と同じ入力で `c' → x` かつ `c ⇝ c'` なら `x ≠ c` が出る見込み。design の module については、その module が `ofDecl c''`（`c''` は `c` の strict descendant）であること（`DescProv`）が先に要る。**`DescProv` なしでは供給元が見つからなかった**。
- 供給元の候補（項目ごと）:
  | 項目 | 候補 | 状態 |
  |---|---|---|
  | design の名前 | `DescProv` + `strictDesc_irrefl`（UA7C） | UA7C と同じ未供給 |
  | 子自身の inst 先 | `GraphAgrees` + `strictDesc_irrefl`（UA7C §4） | 出る見込み。**scratch では未実施** |
  | design の module の inst 先 | `DescProv` が前提 | 同上 |
  | `namesK` の選択 | `namesK k := 子の b::design の名前 ∪ inst 先` を存在量化で与える（AuditE4_B3B4 の存在量化） | 具体形は未構築 |

## 3. E-4 の B4（hdisjD）

- 型: `¬(同じ callee ∧ 同じ memKey) → kidNameAt sp k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k'`（Tools/ShippingCallsMemPinned.lean:256-262。`machineClosesAt_of_kidsD`、Tools/ShippingCallsKidsD.lean:133 は `callee ≠ callee'` の形）。使い所は 1 箇所: 「2 つの visited module が同名なら等しい」の、異なる callee 由来の枝の refutation（docs/parallel/A-shared-descendant.md §1）。
- **第 2 conjunct は、2 つの子の design が同名の module を持つと偽。** `desNames`（Tools/ShippingMemClosesKids.lean:177）により、各 design の module 名は `namesK` に入るので、共通の子孫 module `g1.name = g2.name` があれば `∀ x ∈ namesK k, x ∉ namesK k'` が成り立たない。scratch `b4_refuted`（`ChildIfaceP` 2 つと `g1 ∈ d1.modules`, `g2 ∈ d2.modules`, `g1.name = g2.name` から `¬ (∀ x ∈ ns1, x ∉ ns2)`、axiom は標準 3 つ）。
- 共有する子孫がある例: `mixDeep → {mid2 → midH → rcH, midH → rcH, cnt}`（Tests/Compiler/NoPortsMixDeepTest.lean:6）。既存文書の指摘: 「callees が子孫を共有する parent では `hdisjD` は偽」（Tools/ShippingCallsKidsS.lean:11-15、docs/parallel/A-shared-descendant.md §0）。この調査では `mixDeep` の design の中身を再測定していない（既存文書の記述に依る）。`AuditE4_B3B4` は `∃ namesK` なので、`namesK` の選択で逃げる余地は `desNames` により無い。
- したがって B4 は「供給元が見つからない」ではなく、**共有する子孫を持つ宣言を含む `Reach` では、この型のままでは成り立たない**。供給の対象は「共有する子孫が無い宣言」に限られる（その判定は call-graph の性質: 2 つの callee の `OrdPath` 到達集合が互いに素）か、文を `CacheAgrees` 型（Tools/ShippingCallsKidsS.lean `MachineClosesAtS`、`Agree` / `CacheAgrees`）に変える必要がある。後者は cache の終端 world の性質で、`InvW` から出ない（同ファイル :40-47）。
- 共有しない場合の供給元の候補: 互いに素の判定を `GraphAgrees` / `ReachSpans` 上の有限性（`Reach` の列挙）から出す経路は、この調査では見つからなかった（U-A3 の `Reach` の有限性と同じ未供給）。さらに design の名前の集合は `DescProv`（UA7C）が前提。

## 4. scratch での elaborate（`set_option autoImplicit false`、`kjob lake env lean`）
ソースツリーには入れていない。import は `Tools.ShippingSrm4Core5`（`kjob lake build` 済み、exit 0、655 jobs）。`sorry` なし。`#print axioms`: `b4_refuted`, `b3_gives_hsepB`, `b3_gives_instTargets`, `e3_leaf`, `e3_calls` はすべて `[propext, Classical.choice, Quot.sound]`。mutant は扱っていない。

```lean
theorem b4_refuted {nm1 nm2 : String} {n1 n2 : Nat} {o1 o2 ns1 ns2 : List String}
    {b1 b2 : Sparkle.IR.AST.Module} {d1 d2 : Sparkle.IR.AST.Design}
    (h1 : ChildIfaceP nm1 n1 o1 ns1 b1 d1) (h2 : ChildIfaceP nm2 n2 o2 ns2 b2 d2)
    {g1 g2 : Sparkle.IR.AST.Module} (hg1 : g1 ∈ d1.modules) (hg2 : g2 ∈ d2.modules)
    (e : g1.name = g2.name) : ¬ (∀ x ∈ ns1, x ∉ ns2) := by
  intro h
  exact h g1.name (h1.desNames g1 hg1) (e ▸ h2.desNames g2 hg2)

/-- B3 contains the design part of UA7C's (b). -/
theorem b3_gives_hsepB {nm : String} {n : Nat} {o ns : List String}
    {b : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {c : Name}
    (h : ChildIfaceP nm n o ns b d) (hB3 : ofDecl c ∉ ns) :
    ∀ g ∈ d.modules, g.name ≠ ofDecl c := fun g hg e => hB3 (e ▸ h.desNames g hg)

/-- B3 also forces the instantiation targets of the child and of its design. -/
theorem b3_gives_instTargets {nm : String} {n : Nat} {o ns : List String}
    {b : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {c : Name}
    (h : ChildIfaceP nm n o ns b d) (hB3 : ofDecl c ∉ ns) :
    ∀ g ∈ b :: d.modules, ∀ i conns, Sparkle.IR.AST.Stmt.inst (ofDecl c) i conns ∉ g.body :=
  fun g hg i conns hm => hB3 (h.closed g hg _ i conns hm)


section E3
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- E-3 for a machine LEAF callee: from `seqChild_of_realA` (`ChildIfaceG.name`). -/
theorem e3_leaf {c : Name} (O : RefLawsAOps MkRefd mref cref) (d : MachineData)
    (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hno : d.shape.insts = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O c y) : y.1.name = ofDecl c :=
  (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O d ok hbody hno outTy entry closes h).name
end E3

section E3calls
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingMachineAuto Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- E-3 for a machine callee WITH calls: `deepChild_ifaceA'M` gives `M.name = ofDecl c` and the post-processing
shape of `y.1`; the premise `hsep` is UA7B/UA7C (b)/B3-type (not supplied here). -/
theorem e3_calls {c : Name} (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ []) (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape k) (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ ofDecl c)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Lean.Meta.Context) (cctx' : Lean.Core.Context), AdmCtx O.quiet mctx' cctx' →
      Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O c y) : y.1.name = ofDecl c := by
  obtain ⟨-, -, -, -, M, -, -, -, -, -, hpost, -, hMn, -⟩ :=
    Tools.ShippingSrm4Core5.deepChild_ifaceA'M O T d ok hbody hC hslots hdomB hins hfne outTy hsep entry closes h
  rcases hpost with e | e
  · rw [e, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
  · rw [e, Tools.ShippingMachineDepthRun.mergeChecked_name, Tools.ShippingMachineDepthRun.dropZW_name]; exact hMn
end E3calls
```
(上の `e3_leaf` / `e3_calls` は `section E3` / `E3calls` 内。`open` と `variable` は scratch のとおり。注: `b4_refuted` の docstring の前の `/-- … -/` 行は省略。)

## 5. 新しい前提・判断が要る点と台帳
- 今回の調査が増やした前提: **0**。減らしたものも 0。受入済み: FG 94 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
- 条件付き台帳: E-3 の −1 は主張しない（`hsep` の (b) = `DescProv` が未供給）。B3 の −1 も主張しない（同上）。B4 は上記のとおり文の範囲の問題で、−1 の見込みを書かない。
- **ユーザー判断が要る可能性のある点: B4**。選択肢（いずれも未実施。新しい law / 範囲縮小 / 文の変更に当たるので、実施前に reviewer と user の判断）:
  1. B4 を「共有する子孫が無い宣言に限る」文にする（FG の縮小に当たる）。
  2. B4 を `CacheAgrees` 型（`MachineClosesAtS` の経路）に置き換える（文が変わり、cache の終端 world の性質が新しい前提になる。件数は未計数）。
  3. 現状の文を残し、共有する子孫を持つ宣言では FG が空虚（偽の前提）であることを台帳に明記する（前提が偽であるプログラムでは定理が何も言わない扱い）。
  判断資料の md はこの調査では書いていない（reviewer の評価後、必要なら別途）。
- 次: reviewer: §1 の表（特に `MachineCloses` と `MachineClosesAtA` の対応が未確認）、§2 の「B3 ⊇ UA7C (b)」の読み、§3 の「`desNames` により B4 の第 2 conjunct が共有する子孫で偽」の読みと `mixDeep` の測定の要否。続く調査の候補: `DescProv` の供給（UA7C §5 の P1 / P2 の判断が先）、`hC` 〜 `outTy` の `DataOk` からの接続、E-3 の `declRank` 帰納の組み立て。
