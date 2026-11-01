# G0 + G1 + W1 の型（freeze。Lean 実装の前に置く。未 elaborate）

Issue `sparkle-gd-g01w1`（agent gd01）。設計は `scripts/gen5/GENDATA_ROADMAP.md`（kjob/gdrm2 7c223331、reviewer が設計段階として承認）§4 の G0 / G1 / W1。base は par/gd-int f18eb040。

**この単位は承認済みの設計の中で新しい前提を足さない単位**（共通ルール 14）なので reviewer の freeze は要らない。新しい前提・law・TRUSTED 境界・共有定義の変更は無い。CV-4（C.CV-4 = T1L-43）は今の文のまま inline 仮説 `hbr` で取る。
台帳: FG 102 / T1 54（今回 FG -0 +0 / T1 -0 +0）。C.CV-5 は「条件付き・未計上」。reviewer の留保（A4 / SigTyPh / G7 / G8 / G10 の解消・減算は未承認、T1L-51 の表記差と §7 の重複監査は未解決、W1/W3 の binder・domain 一致を確認するまで減算しない）はそのまま。

型は名前と形を base の定義から書いた案で、**この時点では elaborate していない**。elaborate で binder の細部（namespace、暗黙引数）が変わる場合は、意味を変えない範囲でこの文書の末尾に追記する。意味が変わる場合は止めて報告する。

## 置く場所

- `Tools/ShippingGen5GDCover0.lean`（新規、import `Tools.ShippingGen5AccGenDataKit`）: G0
- `Tools/ShippingGen5GDCover1.lean`（新規、import `Tools.ShippingGen5Cover5`, `Tools.ShippingGen5DataOfDims`）: G1, W1
- `Tests/Gen5/GDCover0Check.lean`, `Tests/Gen5/GDCover1Check.lean`（新規）
- `lakefile.lean` に `lean_lib` を 4 つ追加。

## G0（`Tools.ShippingGen5Acc` の namespace）

```lean
open Classical in
noncomputable def genDataC
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (env₀ : Environment) (E : ConstantInfo) : Option (GenData dataOf E (structEnv env₀)) :=
  if h : ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
      dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true
  then some ⟨h.choose, h.choose_spec.2.2, h.choose_spec.1, h.choose_spec.2.1⟩ else none

theorem genDataC_isSome_iff (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (env₀ : Environment) (E : ConstantInfo) :
    (genDataC dataOf env₀ E).isSome = true ↔
      ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
        dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true

-- ReachCover を (S)(D)(W) に分ける。K は genDataC を genData₀ にした mkKit（他の部品は任意で、mkKit と同じ binder）
theorem reachCover_iff_sdw {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (ordCallees : (d : MachineData) → List (Fin d.shape.insts.length))
    (genSem : (Q : Name → Option (SemPkg ι dom)) → Name → {E : ConstantInfo} →
      GenData dataOf E (structEnv env₀) → SemPkg ι dom)
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordCallees d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : …mkKit の hloc と同じ…) (hdecl : …) (hd : …) (Reach : Name → Prop) :
    ReachCover (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d)
        (genDataC dataOf env₀) ordCallees genSem hmem hev hloc hdecl hd) Reach ↔
      ∀ c, Reach c → ∃ E : ConstantInfo, entry₀ env₀ c = some E ∧
        ∃ d : MachineData, machineShape? false [] E (structEnv env₀) = some d.shape ∧
          dataOf E (structEnv env₀) d.shape = some d ∧ GenWF d = true

-- B1。ロードマップの `E.value` は「E が defnInfo のときの value」の略記なので、defnInfo の存在を結論に入れる
theorem peel_of_machineShape {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp) :
    ∃ d : DefinitionVal, E = .defnInfo d ∧
      ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
        mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e)
```

- 新しい前提: なし。`genDataC` は classical choice のみ。
- `peel_of_machineShape` が `machineShape?` の unfold で通らない場合は、止まる点（どの腕・どの `split` で残るか）を結果 md に書き、G0 の残り（`genDataC` / `genDataC_isSome_iff` / `reachCover_iff_sdw`）を先に出す。

## G1（`Tools.ShippingGen5GDCover1`）

`machineShapeF_state_side`（Cover5.lean:55）の 11 節を、`sm := false`, `ps := []`, `ci := E`, `ai := true` で述語にする（節の本文は Cover5 と同じ。節を増減しない）。

```lean
def StateSideWitness (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape) (n : Nat)
    (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr) : Prop :=
  shapePre false [] E senv = some p ∧
  machNormF n senv p.e = some en ∧
  (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
  (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n)
      = some (some (env, st1)) ∧
  (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
  shapePost true p (shapeMid senv p en) st v = some sp ∧
  st.LenOk ∧
  sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
  sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

theorem stateSide_of_production
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))      -- C.CV-4。Cover5.lean:97 と同じ文
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr), StateSideWitness E senv sp n p en st0 env st1 st v
```

`st` を保つ（REV7 の規則）。`∃ st, st.LenOk ∧ …` の形（T5/T6）は使わない。

## W1（同じファイル）

```lean
theorem shapeAgree_witness
    (hbr : <CV-4 と同じ文>) {E senv sp} (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : dataOfAt lvl E senv sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st

-- carrier を固定しない版（tin / fl は任意）。dataOfFrom_dims は tin / fl について一般なので、同じ証明
theorem shapeAgree_witness_from
    (hbr : <CV-4 と同じ文>) {E senv sp} (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hd : dataOfFrom lvl E senv sp tin fl = some d) :
    ∃ n p en st0 env st1 st v, StateSideWitness E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st
```

- d 側の `hsp hss hls hn` は `dataOfAt_dims` / `dataOfFrom_dims`（g5do-r6）から取り、`shapeAgree_of_sides`（Cover5 T4）で `st` 側と束ねる。state 側の `st` と `ShapeAgree d st` の `st` は同一（別々の存在量化にしない）。
- `shapeAgree_witness_from` は D3（carrier の再定義）を選ぶものではない。carrier の選択は W1 の確認 (c) の対象として残す。
- 新しい前提: なし（`hbr` は既存の C.CV-4。今の文）。**消える行: なし（C.CV-5 は確認 (a)〜(e) の結果を `GDCOVER01_RESULT.md` に書くまで条件付き・未計上）。**

## Check（他の単位と同じ形）

`Tests/Gen5/GDCover0Check.lean` / `GDCover1Check.lean`:
- TYPE: 独立に書いた `Expected…`（Pi 型は `checkTypeOfConst`、定理は `checkExpected`）。
- BODY: `StateSideWitness`、`genDataC` の値を独立の lambda と比較。
- 正負対照: walker の制御（`AccCheck.walkerControls`）と未知定数の制御（root / helper value / helper type の 3 負例 + clean 1 正例）。
- MUTANT（**signature / defeq での棄却であって意味的反例ではない**）: 例 — `genDataC_isSome_iff` から `GenWF d = true` を落とす / 片方向のみ / `dataOf` の項を落とす、`reachCover_iff_sdw` から `entry₀` の項を落とす、`peel_of_machineShape` から `E = .defnInfo d` を落とす、`stateSide_of_production` から `hbr` を落とす / `st` を `LenOk` だけに忘れる形に変える、`shapeAgree_witness` で `ShapeAgree d st'` の `st'` を別の存在に分ける / `hd` を落とす / 結論から `StateSideWitness` を落とす。単独と複合は別に数える。
- CLOSURE: `AccCheck.closureReport`、禁止定数 `sorryAx / ofReduceBool / trustCompiler`、期待する supplier を root と別に固定、未知定数 0。
- AXIOMS: 標準の 3 つのみ（`genDataC` が `Classical.choice` を使う）。
- 最後に `GEN5 GDCOVER01 COUNTS: TYPE … / BODY … / MUTANT … (single … + compound …)` の行。

## W1 の確認 (a)〜(e)

結果（一致 / 食い違い）は Lean の後で `scripts/gen5/GDCOVER01_RESULT.md` に表で書く。この freeze では確認の対象と読む場所だけを固定する:
(a) C.CV-5 の行（`C_M5dg.md` §8、par/fg-ledger-sync 3b459613）と Cover5 の `shapeAgree_of_*` の binder、(b) d の量化、(c) carrier（`dataOfAt` / `dataOfAtP`）、(d) g5do-r6 の dims が base に入っていて build できるか、(e) C.DO-3 との重複。
