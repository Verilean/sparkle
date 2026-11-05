# U-A7 調査: D.E-12（G7-a `hno` / `htop`）を closeMachine / CloseCalls の本文から導く経路

- Issue: sparkle-aud-ua7（親 sparkle-ledger-shorten）。base: par/aud-runsexist 19336e4c。文書のみ（Lean のソースは編集していない）。
- 種別: 調査（freeze ではない）。台帳の現在値は変えない: FG 94 / T1 55（今回 0/0）。
- 結論（先に）: **leaf 枝（`insts = []`、`raw = closeMachine …`、`D = d₀`）と、calls 枝（`CloseCalls`）の `htop` と `hno` の後半は、在る定理だけで導けた**（scratch で `autoImplicit false` のもと、証明まで通った。下記 §4）。この調査では、calls 枝の `hno` に要る「子の module の名前が親の名前でない」（`hsep`）の供給元が見つからなかった。E-12 の行の −1 は、その供給元と、machine 経路以外の経路の扱いが決まるまで見込みに入れない（§6）。

## 1. `hno` / `htop` が言っていること、使う定理

E-12 の完全型（scripts/gen5/AUDIT_CARRIER_FREEZE.md:112-117、`AuditE12`）:

```lean
∀ w2 raw D, RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w2 →
    (∀ x ∈ D.modules, x.name ≠ raw.name) ∧ D.topModule = raw.name
```

- `hno`: core run が返した design `D` の module のどれも、返された module `raw` と同じ名前でない（`raw` は `D` に入っていない）。
- `htop`: `D` の `topModule` は `raw` の名前である。
- 使う定理（file:line）:
  - `Tools.ShippingDesignWriterRun.writer_prints_endpoint_artifact`（Tools/ShippingDesignWriterRun.lean:119）。前提 `hno` `htop`（:127-128）。本文では `hno' : ∀ x ∈ D.modules, x.name ≠ D.topModule`（:146）と `hbt`（:148）を作り、`hier_artifact` と `toVerilogDesignChecked_hier` に渡す（:150-152）。同ファイル :23-24 の注釈は 37 件中 37 件で測定済みとある（測定であって証明ではない）。
  - `PostFactsStmt`（Tools/ShippingGen2PostFacts.lean:39 から。結論 `(∀ x ∈ Dg.modules, x.name ≠ raw.name) ∧ InstClosed (M', Dg')`、:56）。`hno` と同じ文が、statement として結論側に出る。これを `ihAt_stepPF`（Tools/ShippingGen2T1.lean:164）が `hPF` として使う。供給する producer はまだ無い（ShippingGen2T1.lean:160 の注記: "no producer yet"）。
  - 台帳の行: scripts/gen2/PREMISE_LEDGER.md の D.E-12（`git show par/fg-ledger-sync:scripts/gen2/PREMISE_LEDGER.md` の 243 行、733 行）。「`hno`/`htop` が全成功 run で成り立つかは、この調査では見つから(なかった)」。
- `raw`, `D` は `ClosingRun.run` の core run のもの。`ClosingRun.shared` の最後の枝（Tools/ShippingGen5ClosingRun.lean:65-67）が、`raw` と `D` を次の 2 つに分ける:
  - leaf: `shape.insts = [] ∧ children = [] ∧ raw = closeMachine shape.layout t' ∧ D = d₀`
  - calls: `shape.insts ≠ [] ∧ CloseCalls shape t (closeMachine shape.layout t') d₀ children raw D ∧ ChildrenShipsI …`

## 2. 項目ごとの経路

| 項目 | 在る定理 / 経路 | file:line | 結果 |
|---|---|---|---|
| (a) `raw.name = ofDecl declName`（leaf） | `closeMachine_name`、`closeLets_name`、`transition_closed` の `m.name = ofDecl declName` | Tools/ShippingSeqChildIface.lean:66, :52; Tools/ShippingTransitionClosed.lean:35（結論の最後） | 在る |
| (b) `d₀ = Design.empty (ofDecl declName)` | `synthesizeMixedCertified_returns`（`d = st.design`）と `transition_closed`（`st.design = (CircuitM.init (ofDecl declName)).design`、内部は `harness_closed` Tools/ShippingHarnessClosed.lean:107、「the run adds no sub-module」） | Tools/ShippingMixedEntrySoundness.lean:434; Tools/ShippingTransitionClosed.lean:35 | 在る |
| (c) `htop`（leaf） | (a) + (b) + `Design.empty` の定義（Sparkle/IR/AST.lean:443、`Module.empty` は :340） | | 在る（§4 `e12_leaf`） |
| (d) `hno`（leaf） | (b) から `D.modules = []` | | 在る（§4 `e12_leaf`） |
| (e) `htop`（calls） | `CloseCalls.some` の `d = designWith children d₀` と `m.name = m₀.name`（Tools/ShippingMachineEntry.lean:957）、`designWith` は `{ d with modules := … }`（Sparkle/IR/Machine.lean:302）で `topModule` を変えない | | 在る（§4 `e12_calls`） |
| (f) `hno`（calls） | `designWith_modules` + `mem_visited`（Tools/ShippingDesignWithG.lean:57, :68）で、`D` の module は `children` の module（子自身か子の design の module）に限られる。そこから「子の module の名前は `ofDecl declName` でない」が要る | | 前半は在る。後半の前提 `hsep'` は §3 |
| (g) calls 枝の `hsep'` の供給元 | 同じ形の仮定が `deepChild_ranA` などの前提 `hsep`（`∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ ofDecl c`）として在る（Tools/ShippingSeqChildDeepFactsA.lean:62, :103, :142, :203; Tools/ShippingSrm4Core6.lean:177）。これらでは仮定のまま | | **この調査では供給元・経路が見つからなかった**（§3） |
| (h) `partial def` | `closeMachine`、`closeLets`、`CloseCalls`、`closeInsts`、`designWith` は全て total な `def`（Sparkle/IR/Machine.lean）。`synthesizeMixedCertified` の中の `emitLeaves` などは `MetaM` で、その結果は `synthesizeMixedCertified_returns` / `harness_closed` が「`Returns` の run がある」という形で受ける。**partial で見えない箇所に当たらなかった**（Elab.lean:2247-2249 のコメントは、旧経路の `partial` を「証明できない」と言っているが、本経路の harness はその外） | | 全域化の候補は無し |

## 3. 前提として残るもの（この調査で分かった範囲）

1. **データ前提**（`transition_closed` の `positive`, `e`, `he`, `hb`, `hv`, `hbody`）。`seqChild_ifaceA`（Tools/ShippingSeqChildIfaceA.lean:38）は同じものを `d.ok = true` と `hbody`（`MachineData` / `Pkg`）から作っている（:63-100 付近）。ClosingRun 側に同じ `d.ok` と `hbody` が在るかは、この調査では確認していない（`Pkg.ok` / `Pkg.body` が候補）。
2. **machine 経路の証拠**: `raw`/`D` を `ClosingRun.shared` の枝に結ぶこと。`MachineTaken`（Tools/ShippingGen2Defs.lean:136）や `T1Hyp.defines/closes` が候補で、すでに T1 の行。新しい前提としては数えていない。
3. **calls 枝の `hsep'`**: 「子の module（と子の design の module）に、親の名前 `ofDecl declName` を持つものがない」。呼び出しグラフが親に戻らない（非巡回）ことに近い。D.E-8 / D.E-9（`graphOf`, `OrdPath`）が関係するかもしれないが、**この調査では結び付ける補題を見つけていない**。memory 子（`child? = some md`）の場合の同じ条件も同様。
4. **経路の範囲**: `AuditE12`（上記の型）は `declName` の core run すべてについて言う。本調査が扱ったのは machine 経路（`shape` が `machineShape?` の出力で `synthesizeMachineCertified = some`）だけ。gate（route 1/2）、memo（route 5）、legacy（route 6）、parametric（route 7）の run は、`ROUTE_CENSUS.md` の表のとおり別経路で、この調査では扱っていない（`PostFactsStmt` は `MachineTaken` を前提に持つので machine 経路に限られる）。`AuditE12` の型に経路の guard が無いので、そのまま machine 経路の補題では閉じない。型に guard を足すか、他経路の補題を探すかは reviewer / ユーザーの判断（この調査では型を変えない）。

## 4. scratch での elaborate（`set_option autoImplicit false`、`kjob lake env lean`、exit 0、axioms = propext, Classical.choice, Quot.sound）

import: `Tools.ShippingTransitionClosed`, `Tools.ShippingSeqChildIface`, `Tools.ShippingDesignWithG`, `Tools.ShippingMachineEntry`。
どちらも `sorry` なし。`#print axioms` は両方 `[propext, Classical.choice, Quot.sound]`。

```lean
theorem e12_leaf {tenv : Lean.Environment} {logProf : String → IO Unit} {declName : Name}
    {bs : List (Name × MixedGateBinder)} {body : Lean.Expr}
    {t t' raw : Sparkle.IR.AST.Module} {d₀ D : Design} {lay : Layout}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName bs body) (t, d₀))
    (hcl : closeLets lay.lets t = some t')
    (positive : PositiveBinders bs)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {srt : SType} (e : Term srt) (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (hbody : body = quote dom (fun j => inputExpr bs.length (bpos j))
      (fun j => inputExpr bs.length (vpos j)) e)
    (hraw : raw = closeMachine lay t') (hD : D = d₀) :
    (∀ x ∈ D.modules, x.name ≠ raw.name) ∧ D.topModule = raw.name := by
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hDd, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  obtain ⟨-, -, -, -, hdes, hname⟩ :=
    transition_closed nd len hrun hm nameLegal positive e he hb hv hbody
  have hnm : raw.name = Sparkle.IR.ModuleName.ofDecl declName := by
    rw [hraw, closeMachine_name, closeLets_name hcl, ← hname]
  have hd : D = Design.empty (Sparkle.IR.ModuleName.ofDecl declName) := by
    rw [hD, hDd, hdes]; rfl
  refine ⟨?_, ?_⟩
  · intro x hx; rw [hd] at hx; simp [Design.empty] at hx
  · rw [hd, hnm]; rfl

theorem e12_calls {tenv : Lean.Environment} {logProf : String → IO Unit} {declName : Name}
    {shape : MachineShape} {t t' raw : Sparkle.IR.AST.Module} {d₀ D : Design}
    {children : List (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
      shape.binders shape.body) (t, d₀))
    (hcl : closeLets shape.layout.lets t = some t')
    (positive : PositiveBinders shape.binders)
    {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {srt : SType} (e : Term srt) (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, shape.binders[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, shape.binders[vpos j]? = some (name, .bits (vw j)))
    (hbody : shape.body = quote dom (fun j => inputExpr shape.binders.length (bpos j))
      (fun j => inputExpr shape.binders.length (vpos j)) e)
    (hcc : CloseCalls shape t (closeMachine shape.layout t') d₀ children raw D)
    (hsep : ∀ c ∈ children, ∀ g ∈ c.1 :: c.2.modules,
      g.name ≠ Sparkle.IR.ModuleName.ofDecl declName) :
    (∀ x ∈ D.modules, x.name ≠ raw.name) ∧ D.topModule = raw.name := by
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hDd, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  obtain ⟨-, -, -, -, hdes, hname⟩ :=
    transition_closed nd len hrun hm nameLegal positive e he hb hv hbody
  obtain ⟨-, -, hrn, -, -, -, -, -, -, -, -, hDe, -⟩ := CloseCalls.some hcc
  have hnm : raw.name = Sparkle.IR.ModuleName.ofDecl declName := by
    rw [hrn, closeMachine_name, closeLets_name hcl, ← hname]
  have hd0 : d₀ = Design.empty (Sparkle.IR.ModuleName.ofDecl declName) := by
    rw [hDd, hdes]; rfl
  have hmods : d₀.modules = [] := by rw [hd0]; rfl
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hDe] at hx
    obtain ⟨-, hv⟩ := Tools.ShippingDesignWithG.designWith_modules (children := children) hmods
    obtain ⟨c, hc, hxc⟩ := Tools.ShippingDesignWithG.mem_visited.mp (hv x hx)
    rw [hnm]
    exact hsep c hc x (by rcases hxc with h | h <;> simp [h])
  · rw [hDe, hnm, hd0]; rfl
```

注: これは scratch の結果で、ソースツリーには入れていない。台帳の行を消す根拠にはまだならない（§6）。

## 5. 新しい前提の数

- 今回の調査が増やす前提: **0**（leaf 枝は新しい前提なし）。
- calls 枝で `hsep'` が必要。これは現在の台帳のどの行にも結び付けていない。台帳の行に当たるのは「新しい前提 1（`hsep'`）」と数える（相殺しない）。ただし、これが台帳の既存の行（D.E-8 / E-9 など）で払えると分かれば 0 になる。この調査では分かっていない。

## 6. 台帳の見込み（E-12 −1 の条件）

- 条件付き台帳: FG 見込み −1（E-12）を **主張しない**。−1 になる条件は次の 3 つが全て満たされること:
  1. データ前提（§3-1）が ClosingRun の文脈で供給されること。
  2. calls 枝の `hsep'`（§3-3）に供給元ができる（既存の行から出る、または新しい前提 +1 として受理される）。この場合、差し引きは −1 + 1 = 0 になりうる。
  3. `AuditE12` が machine 経路以外の run も含むことの扱い（§3-4）が決まること。
- 受入済みの台帳: FG 94 / T1 55（今回 0 / 0）。

## 7. 次

- reviewer: この調査の読みの確認（特に §3-4 の `AuditE12` の範囲と §3-3）。
- 続く単位の候補（承認が要る）: (i) leaf 枝の補題を新規ファイルに置く証明単位（新しい前提 0）。(ii) calls 枝の `hsep'` の供給元の調査（E-8 / E-9 / `RealChildA` の名前の事実）。mutant は扱っていない。
