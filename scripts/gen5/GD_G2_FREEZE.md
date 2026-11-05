# G2 の型（freeze。Lean 実装の前に置く。未 elaborate）

Issue `sparkle-gd-g2`（agent gd2）。設計: `scripts/gen5/GENDATA_ROADMAP.md`（7c223331）§4 G2。base は kjob/gd01 6d4d3120（G0/G1/W1）。

**承認済みの設計の中で前提を増やさない単位**（共通ルール 14）。前提は既存の CV-4（inline 仮説 `hbr`）のみ。新しい前提・law・TRUSTED 境界・共有定義の変更は無い。台帳: FG 104 / T1 54（今回 FG -0 +0 / T1 -0 +0）。reviewer の freeze には当たらず、review に出さない。

置く場所: `Tools/ShippingGen5GDCover2.lean`（新規、import `Tools.ShippingGen5GDCover0`, `Tools.ShippingGen5GDCover1`）、`Tests/Gen5/GDCover2Check.lean`（新規）、`lakefile.lean` に `lean_lib` 2 つ。namespace `Tools.ShippingGen5GDCover2`（open は GDCover1 と同じ）。

## 型

```lean
-- (1) shapePost の run 等式を unfold して binders を数える。LenOk は st.names.size = st.kinds.size を与える
theorem shapePost_binders_len {allowInsts : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (h : shapePost allowInsts p m st v = some sp) (hl : st.LenOk) :
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

-- (2) G1 の witness から（結論は ShapePre の bs）
theorem dataOfFront_len_of_witness {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat}
    {p : ShapePre} {en : Lean.Expr} {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (w : StateSideWitness E senv sp n p en st0 env st1 st v) :
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets

-- (3) production から。p は G0 peel_of_machineShape の (bs, e) と同じ
theorem dataOfFront_len_of_production
    (hbr : <CV-4 の inline 形、G1 と同じ文>)
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp) :
    ∃ (d : DefinitionVal) (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      E = .defnInfo d ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length = bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets
```

(2) は `dataOfFront` の guard `shape.binders.length == p.1.length + shape.insts.length + nSlots + nLets`（`DataOf.lean:69`、`dataOfFront_some` が使う形）の条件そのもの。(3) は `shapePre` の unfold で `p.bs = bs`、`E = .defnInfo d` を得る。

## 計画
- `shapePost` の do-ブロックを `Option.bind_eq_some_iff` / `split` で剥がし、`binders` の `List.length_append` / `length_zip` / `length_map` / `length_range`、`st.names.size = st.kinds.size`（LenOk）、`sp.insts = st.insts.toList`、`sp.layout.slots` は `machSlotFields` の長さ（kinds.length）が要る。ここで `machSlotFields`/`kinds` の長さ補題が既存に無ければ、G1 の `sp.layout.slots.length = st.kinds.size` 節（witness の一部）を使う（(1) ではなく (2) 側で）。(1) が単独で通らない場合は (1) に当該節を仮説として足す形に変えるが、新しい前提にはならない（witness が持つ節）。意味が変わる場合は止めて報告。
- 新しい前提・sorry・axiom・native_decide は使わない。

## Check（`Tests/Gen5/GDCover2Check.lean`）
独立の Expected TYPE（上の型を別記述）、正例（具体的な witness を使う使用例の型検査）と負例（長さ式の `+` 項の欠落/置換の mutant は **signature/defeq での棄却であって意味的反例ではない**）、閉包（依存定理の列挙）、`#print axioms` が標準のみ、COUNTS 行。
