# DG-READERTRACE freeze rev14 — U-R12（`machineShapeF_reach` / `ShapeInputs` / C-QWIT への接続）の単位列と型（文書のみ、review に出す）

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt16` f1d8b228（U-R8 + U-R11b `readF_traceGood` 全燃料、Pod build 済み、clean build `rtv-f1d8b228` は coder が実行中）。
`DG_READERTRACE_FREEZE.md`（rev0 §5）、`..._REV5.md`（U-R12 行、未調査だった）、`..._REV13.md` の続き。**このコミットでは Lean を書かず elaborate もしていない。** 以下の Lean は読んだファイルに合わせた未 elaborate の型で、elaborate 後に見つかった誤りは addendum で直す（黙って直さない）。
用語: 「見つからなかった / 未供給」は「この調査で辿った経路では供給元・経路が見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant（後続の Check）は signature / defeq での棄却で意味的反例ではない。条件付きの結果は中間結果。
reviewer の結論 (a)(b)(c)（この Issue の 4246 以降の記録）に従う: 純減 0 の単位は証明 bridge に限る / 既存 ID と完全な型・domain で照合できない前提は新規・強化として数える / TraceGood 単独の FG 減少数は出さない。

**台帳: FG 104 / T1 54（今回 FG -0 +0 / T1 -0 +0）。この rev14 は台帳を 1 行も変えない。** §5 の候補は**提案であって採用ではなく、数えていない**。review に出す理由は、§5 に新しい名前付き条件の候補（台帳の追加案）が含まれ、U-R12 全体の目標・範囲（§4 の G8 との切り分け）を書いているため（共通ルール 14 の「目標・範囲、前提の追加」に該当）。

## 0. 読んだもの

`ShippingReaderFuelShape.lean`（`shapePre / shapeMid / shapePost / shapeStart / shapeRootLet / shapeBody / shapeW / machineShapeF`）、`ShippingReaderFuelShapeR5.lean`（`shapePre_facts / shapeStart_inv / shapeBody_inv / machineShapeF_steps` と各 `*_lenOk`）、`ShippingGen5Cover5.lean`（`machineShapeF_state_side`、T3）、`ShippingGen5Cover6.lean`（`FReachC`、`reserved_reachC`）、`ShippingGen5ReaderTrace{,Ctl,Let,Loop,Nested,Chain,Dispatch}.lean`（`TrInv / TracePre / TracePost / TraceGood / EnvPh / bindLet_reach / trInv_bindLet / trInv_bindLetNamed / trInv_reserved / chain_basic_trace / readF_traceGood*`）、`ShippingLetsReaderInv.lean`（旧 `Pre / Post / Good`、`readF_good`）、`ShippingLetsReaderInvBase.lean`（`RdOk / EnvOk / Adv`）、`Elab.lean`（`mixedGatePeel / machRoot / machLoopAsLet / inlFoldNat / machNormNode`）、`MachRawSurface.lean`（`rootFloat / zeroLit`）、`MachTupleIn.lean`（`packTupleInputs`）、`Tools/Prototype/{PreprocLetOk,NormRangeLetOk,NormNodeRangeLetOk}.lean`（`LetOk` 側の前処理 range の既存の試み）、`Tools/Assume/N3Extern.lean`、`scripts/gen5/GENDATA_ROADMAP.md`（`git show 7c223331:`）§3 G8・§5・§7、`kjob/fg-ledger-int:scripts/gen2/PREMISE_LEDGER.md` の C.CV-1…6 / C.RT-1…4 / C.RK-8 の行。

**読み取りで分かった点（elaborate はしていない）。**
1. `machineShapeF` の reader 呼び出しは 3 箇所の段だけ: `shapeStart`（`run? = some` のとき `wConv (units) 0 dom {}` の後 `machReserve`）、`shapeRootLet` の fold（`wLoopRoot env v st` か `wConv env 0 v st` の後 `machBindLet`／`machBindLetNamed`）、`shapeBody`（`wChain (regs 0 :: env) body st` の後 `ws` 追記、または `wConv env 0 root st`）。すべて `wtab senv n` の `blk` 項目 = `readF senv n` の呼びなので、`hT : TraceGood senv nDecl (readF senv n)` がそのまま当たる（R5 の `*_lenOk` が `readF_good` で同じ形をしている）。
2. 呼び出し側の義務は、`TracePre = Pre ∧ PhPre`。`PhPre` は `TrInv`、`EnvPh`、入力式の `NoPh` と `BvarLt (d + env.length + nDecl)`。`Pre`（旧側）は `RdOk st`、`EnvOk st.lets.size env`、`LetOk 0 e`。`LetOk 0 e` は `noPh_letOk`（U-R1）。`RdOk` / `EnvOk` は旧 `Post`（`ConvOut` = `Adv ∧ LetOk`）から運ぶ。`reserved` の `RdOk` は `ShippingLetsReaderInv.lean:770` と同じ `adv_dom (adv_refl _)` で足りる見込み（読み取り）。
3. 範囲の数字は rev0 の `MidInputs` と一致する: shapeStart の `env = rootLets.map (fun _ => .unit)` は長さ `rootLets.length`、`d = 0` なので `BvarLt (rootLets.length + nDecl) dom`。rootLet の k 番目は `env.length = k` なので `BvarLt (k + nDecl) v`。`shapeBody` の chain は `regs 0 :: env` で長さ `rootLets.length + 1`。`run? = none` の root は `BvarLt (rootLets.length + nDecl)`。
4. **rev0 の `MidInputs` にあった `DomAtomic dom` は、現在の `CtlPh / PhPre / trInv_reserved` のどこにも使われない**（`DomAtomic` の定義も tree に無い）。`DomPh` は reader 出力 `dom'` の `InRange` / `NoLoose` で、`trInv_reserved` が `ExprPh` の出力から作る。この rev14 は `MidInputs` から `DomAtomic` を外す（**弱める変更**。`ShapeInputs` を満たすべき入力は減る）。
5. `ShapeInputs`（`shapeMid senv p en` の各部の範囲）の供給元は `shapePre` の `packTupleInputs d.value`（**`partial def`**）→ `mixedGatePeel` → `machNormF`（fuel 版の正規化。`rawNode` / `machNormNode` / `instantiate1` を呼ぶ）→ `inlFoldNat` → `zeroLit`（`Expr.replace`）→ `rootFloat`（`partial def`）→ `machLoopAsLet` → `machRoot`。**`Tools/Prototype/` に、同じ列の `LetOk`（`_machLet` 不在）版の保存補題の試みがある**（`PreprocLetOk`: `inlFoldNat / machLoopAsLet / machRoot` は前提なしで証明済み、`zeroLit` は `ZeroLitAgrees` 付き。`NormRangeLetOk / NormNodeRangeLetOk`: `machNormF` は `RawNodeRange`・`LiftScalarRange`・`BoolMapRange` 等の名前付き前提つき）。ただし**型が `LetOk` で、`TraceGood` が要る `NoPh` / `BvarLt` ではない**（rev5 §0 の 3 点目と同じ）。`NoPh` / `BvarLt` 版は、この調査では供給元が見つからなかった。
6. `TraceGood` の結論（`FReachC`、`PhPost`）に「出力が `quote` の像である」は入っていない（GENDATA_ROADMAP §5）。この rev14 で `TracePost` は変えない（§4）。

## 1. U-R12 の単位の列

新規ファイル（既存ファイル・共有定義・`Tools/Assume/*` は編集しない。`lakefile.lean` に `lean_lib` 追加のみ）。Namespace `Tools.ShippingGen5ReaderTrace`。Opens: `Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6 Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv`（名前空間は elaborate 時に確認）。`set_option autoImplicit false`。

| 単位 | ファイル | 内容 | 使う既存定理（branch@SHA = `kjob/rt16`@f1d8b228 の tree） | 新しい前提 | 台帳差分 |
|---|---|---|---|---|---|
| **U-R12a** | `Tools/ShippingGen5ReaderTraceShape.lean`（+ `Tests/Gen5/ReaderTraceShapeCheck.lean`） | `MidInputs`（改訂）、`ShapeCarry`、`shapeStart_trace`、`shapeRootLet_trace`、`rootLets_trace`、`shapeBody_trace` | `trInv_empty`、`trInv_reserved`（Nested）、`bindLet_reach`・`trInv_bindLet`・`envPh_cons_val`・`envPh_cons_regs`・`envPh_mono`（Trace/Let）、`trInv_bindLetNamed`（Loop）、`bindLetNamed_reach`（Ctl）、`reachC_ws`、`reachC_trans`、`noPh_letOk`、`machReserve_some`、`shapeStart_inv`・`shapeBody_inv`（R5）、`rdOk_init`・`adv_dom`・`rdOk_lets`（LetsReaderInv）、`chain_basic_trace` 系の `hT` の使い方 | **なし**（`hT` と `MidInputs` を仮定にするだけ） | 0 / 0 |
| **U-R12b** | 同 `…Shape.lean`（続き）または `…ShapeReach.lean` | `machineShapeF_reach`（U-E3b）、`machineShapeF_reach_of_premises`（`readF_traceGood_of_premises` で `hT` を作る）、`machineShapeF_ranges`（G8 向けの射影） | U-R12a、`machineShapeF_state_side`（Cover5）、`fullInv_reachC`・`fullInv_empty`（Cover6）、`readF_traceGood_of_premises`（Dispatch） | **なし**。`hIn : ShapeInputs` は**定理の仮定**（台帳の行ではない。供給は U-R12c） | 0 / 0 |
| **U-R12c** | `Tools/ShippingGen5ReaderTraceShapeIn.lean`（+ Check） | `ShapeInputs` の供給の**前提なしで証明できる部分**: `mixedGatePeel_ph`、`inlFoldNat_ph`、`machLoopAsLet_ph`、`machRoot_ph`（`inlSpine`・`machRootLets`・`machRunApp?` 経由）、`shapeMid_ph`（これらの合成）、`shapeInputs_of`（条件付きの組み立て、§5 の名前付き条件を仮定に取る） | `rootFloat_ph`（Let、`RootFloatAgrees`）、`lift01_ph`、`machRunApp?_ph`・`inlSpine_ph`・`inlSpine_ph0`（Extract）、`bvarLt_mono` | §5 の候補 N1〜N4 を**仮定として名前を付けて取る**（台帳に載せるかは §5 の判断まで保留） | 0 / 0（§5 の採用で別途） |
| U-R12d | （Lean なし。文書） | G8 との対応表と、台帳で消える候補の条件（§3、§4） | — | — | 0 / 0 |

順序: U-R12a → U-R12b は前提を増やさず、`ShapeInputs` を仮定にしたまま進められる。U-R12c の前提なし部分も同様。**§5 の条件（N1〜N4）を台帳に載せる / 分解する / 先送りする判断は、reviewer の 1 回の判断として §6 に出す。** 承認されるまで、U-R12c は前提なし部分だけを置き、`shapeInputs_of` の仮定は `Prop` の名前（`def` ではなく後述の `NormFPh` 等）のまま置く。

## 2. 完全な型

### 2.1 U-R12a

```lean
/-- rev0 §5 の `MidInputs` から `DomAtomic dom` を外したもの（弱める変更。§0 の 4 点目）。 -/
def MidInputs (nDecl : Nat) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)

def ShapeInputs (nDecl : Nat) (senv : StructEnv) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (n : Nat) : Prop :=
  ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
    MidInputs nDecl senv p en

/-- 3 段の間で運ぶ不変条件: 旧側の `Pre` の部品 (`RdOk`, `EnvOk`) と新側 (`TrInv`, `EnvPh`)。 -/
def ShapeCarry (senv : StructEnv) (nDecl : Nat) (env : List MachVal) (st : MachRead) : Prop :=
  RdOk st ∧ EnvOk st.lets.size env ∧ TrInv senv nDecl st ∧ EnvPh nDecl st env

theorem shapeCarry_empty (senv : StructEnv) (nDecl : Nat) : ShapeCarry senv nDecl [] ({} : MachRead)

theorem shapeStart_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true)
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)) :
    FReachC nDecl ({} : MachRead) st0 ∧ ShapeCarry senv nDecl [] st0

theorem shapeRootLet_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    (hs : ShapeCarry senv nDecl s.1 s.2)
    (hn : NoPh a.2.2 = true) (hb : BvarLt (s.1.length + nDecl) a.2.2 = true)
    {s' : List MachVal × MachRead} (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s')) :
    FReachC nDecl s.2 s'.2 ∧ ShapeCarry senv nDecl s'.1 s'.2 ∧ s'.1.length = s.1.length + 1

theorem rootLets_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (l : List (Name × Lean.Expr × Lean.Expr)) (env : List MachVal) (st : MachRead)
    (hs : ShapeCarry senv nDecl env st)
    (hl : ∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), l[k]? = some x →
        NoPh x.2.2 = true ∧ BvarLt (env.length + k + nDecl) x.2.2 = true)
    {env' : List MachVal} {st' : MachRead}
    (hr : (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st'))) :
    FReachC nDecl st st' ∧ ShapeCarry senv nDecl env' st' ∧ env'.length = env.length + l.length

theorem shapeBody_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid) (env : List MachVal) (st1 : MachRead)
    (hs : ShapeCarry senv nDecl env st1) (hlen : env.length = m.rootLets.length)
    (hrun : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh b = true ∧ BvarLt (m.rootLets.length + 1 + nDecl) b = true)
    (hroot : m.run? = none → NoPh m.root = true ∧ BvarLt (m.rootLets.length + nDecl) m.root = true)
    {st : MachRead} {v : Lean.Expr} (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))) :
    FReachC nDecl st1 st ∧ TrInv senv nDecl st ∧
    (m.wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)
```
証明の道筋（読み取り）: `shapeStart` — `run? = none` は `shapeStart_inv` の左で `st0 = {}`、`FReachC.refl`、`shapeCarry_empty`。`some` は `cConv` を `hT` で当て（`TracePre` = `⟨⟨rdOk_init, EnvOk(units)⟩, ⟨trInv_empty, EnvPh(units), noPh, bvarLt⟩⟩`、units は `val`/`state` を含まないので `EnvPh` は空虚）、`ExprPh` の出力を `trInv_reserved` に渡し、`RdOk` は `adv_dom`。`shapeRootLet` — `Signal.loop` 腕は `loopRoot_trace` 経由（`hT`）で `RootPh`、`envPh_cons_root` と `envPh_mono`（旧 env を新状態へ）。通常腕は `hT` の `conv` 呼びと `bindLet_reach`/`trInv_bindLetNamed`（`!st.loops.isEmpty && machIsSlot v'` の 2 択）。`machTailV`/`machHandleV` の `none, none` 以外は `failO`（成功 run の仮定と矛盾）。`rootLets_trace` — `satp_foldO` 型の帰納（`l` の長さで、env の長さが 1 ずつ増えることを運ぶ）。`shapeBody_trace` — `run? = some` は `chain` 呼び（`hT`、`envPh_cons_regs`）と `reachC_ws`（`ChainPh` の `ws` 範囲）、`wrap? = none` のときの `v` は `ChainPh` の `InRange`/`NoLoose`（`lets` が同じなので状態を `ws` 追記したものに移しても `InRange` は不変）。`run? = none` は `conv` 呼びの `ExprPh`。`wrap? ≠ none` の `v`（`mkAppN c (params.push v)`）の範囲は**この型に入れない**（rev0 と同じ）。

### 2.2 U-R12b

```lean
theorem machineShapeF_reach {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs nDecl senv sm ps ci n) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv senv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)
```
rev0 §5 との差: (i) `F : PureFacts senv`・`G : PhFacts senv` の仮定を `hT` に置き換える（`readF_traceGood` が `F` と名前付き仮説を内部で使う。U-R4 当時の `PhFacts` は rev5 で `LiftAgrees` 等に再割当済み）、(ii) 末尾に `NoLoose 0 v` を足す、(iii) `ShapeInputs` が `MidInputs` の改訂版（§2.1）。最初の 11 連言は `machineShapeF_state_side`（Cover5, T3）の本文そのまま。証明: `machineShapeF_state_side h` から出発し、`hIn` を `shapePre`/`machNormF` の等式に当て、`shapeStart_trace → rootLets_trace → shapeBody_trace`。`FReachC nDecl {} st0` は `shapeStart_trace` の第 1 成分。`TrInv senv nDecl st` は `shapeBody_trace`。

```lean
theorem machineShapeF_reach_of_premises (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hi1 : Inst1Agrees) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env)) {n : Nat} {sm : Bool}
    {ps : List (String × Nat)} {ci : ConstantInfo} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (h : machineShapeF n sm ps ci (structEnv env) ai = some (some sp))
    (hIn : ShapeInputs nDecl (structEnv env) sm ps ci n) :
    <machineShapeF_reach の結論と同じ。senv := structEnv env>

/-- G8 向けの射影（`TrInv` と `RangeInv` を展開しただけ。新しい内容なし）。 -/
theorem machineShapeF_ranges {nDecl : Nat} {senv : StructEnv} {st : MachRead} (hTr : TrInv senv nDecl st) :
    (∀ j nm kd v, st.lets[j]? = some (nm, kd, v) → InRange nDecl st j v ∧ NoLoose 0 v) ∧
    (∀ w ∈ st.ws, w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2) ∧
    (∀ d, st.dom = some d → InRange nDecl st st.lets.size d ∧ NoLoose 0 d)
```
`machineShapeF_ranges` は `hTr.1`（`FullInv.RangeInv`）と `hTr.2`（`CtlPh` の `LetsNoLoose`、`DomPh`）の射影。

### 2.3 U-R12c（前提なし部分の型。`shapeInputs_of` は §5 の判断後に確定）

```lean
theorem mixedGatePeel_ph {L : Nat} : ∀ (e : Lean.Expr) (bs : List (Name × MixedGateBinder)) (b : Lean.Expr),
    mixedGatePeel e = some (bs, b) → NoPh e = true → BvarLt L e = true →
    NoPh b = true ∧ BvarLt (L + bs.length) b = true
theorem inlFoldNat_ph {L : Nat} : ∀ e, NoPh e = true → BvarLt L e = true → NoPh (inlFoldNat e) = true ∧ BvarLt L (inlFoldNat e) = true
theorem machLoopAsLet_ph {L : Nat} : ∀ e, NoPh e = true → BvarLt L e = true → NoPh (machLoopAsLet e) = true ∧ BvarLt L (machLoopAsLet e) = true
theorem machRoot_ph {L : Nat} {projs} {e : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true) :
    -- (rootLets, sel, run?, root) := machRoot projs e []
    let r := machRoot projs e []
    (∀ k x, r.1[k]? = some x → NoPh x.2.2 = true ∧ BvarLt (k + L) x.2.2 = true) ∧
    (∀ dom αs ie b, (r.2.2.1.bind machRunApp?) = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (r.1.length + L) dom = true ∧ NoPh b = true ∧ BvarLt (r.1.length + 1 + L) b = true) ∧
    (NoPh r.2.2.2 = true ∧ BvarLt (r.1.length + L) r.2.2.2 = true)
```
`inlFoldNat`・`machLoopAsLet`・`machRoot` は total な構造再帰で、`Tools/Prototype/PreprocLetOk.lean` に `LetOk` 版が前提なしで証明済み（同じ方法で `NoPh` / `BvarLt` 版を書く見込み。未 elaborate）。`machRoot_ph` の `wrap?` 腕（`root.getAppArgs.back?` を run に取る）は `shapeMid_ph` 側で扱う。`machRoot` が `L` を保つ形（`rootLets` の k 番目に `k + L`）は、`letE` を 1 つ剥がすたびに束縛が 1 増えることから（`BvarLt` の `letE` の `L + 1`）。

## 3. R-in / R-nl / R-dom の readF 呼び出し側の義務を払う単位

| 義務 | 何か | 払う単位 | 条件 |
|---|---|---|---|
| R-in（`shapeStart` の `dom`） | `NoPh dom`、`BvarLt (rootLets.length + nDecl) dom`、`EnvPh`（units で空虚）、`TrInv {}` | U-R12a `shapeStart_trace` | `MidInputs` の run 節（`hIn`） |
| R-in（root let） | k 番目の値の `NoPh` / `BvarLt (k + nDecl)`、`EnvPh` は前段の出力から運ぶ | U-R12a `shapeRootLet_trace` / `rootLets_trace` | `MidInputs` の rootLets 節 |
| R-in（body） | `chain` の `body`（`BvarLt (rootLets.length + 1 + nDecl)`）または `conv` の root | U-R12a `shapeBody_trace` | `MidInputs` の run / root 節 |
| 旧側 `Pre`（`RdOk`、`EnvOk`） | readF の旧不変条件 | U-R12a（`ShapeCarry` で運ぶ） | なし |
| R-nl（`LetsNoLoose st`） | 最終状態の let 値が loose bvar を持たない | `TrInv`（`CtlPh` の 5 番目）。U-R12b の結論 | `ShapeInputs` |
| R-dom（`DomPh`） | `st.dom` が範囲内・loose-free | `TrInv`（`CtlPh` の 4 番目）。`shapeStart` では `trInv_reserved` | `ShapeInputs` |
| `MidInputs` の `p.bs.length ≤ nDecl` | `j - d - |env| < nDecl` の算術用 | **U-R12a/b では使わない**（trace に効かない）。`ShapeInputs` に入れたまま `nDecl` の同定（`sparkle-gen5-dg-dataof`）に渡す | — |
| `ShapeInputs` そのもの | `shapeMid` の各部の範囲 | U-R12c（§5 の条件つき） | N1〜N4 |

注意: 上の「払う」は「`hIn : ShapeInputs` と `hT` の下で U-R12b の結論が出る」の意味。`hT` は 6 つの既存の名前付き仮説（`LiftAgrees`、`RootFloatAgrees`、`Inst1Agrees`、`EnvTypesFVarFree`、`SigTyClosed`、`InstSFieldsDet`）の下で `readF_traceGood_of_premises` が出す。これらが真であることは主張しない。

## 4. GENDATA_ROADMAP の G8（`QuoteGood`、C-QWIT）との対応

**結論: U-R12 の結論（`FReachC`、`TrInv`、範囲）から「reader の出力が `quote` の像である」は出ない。G8 の入力のうち範囲の部分だけを U-R12 が供給し、`quote` の像であること・sort・`dom'` の一致は G8 に残る。** この rev14 は `TracePost` を変えず（roadmap §5 の選択肢 (B)＝別述語 `QuoteGood` を同じ骨格で新規ファイルに立てる、を採る。(A)＝`TracePost` に quote の連言を足す、は readertrace の承認済みの型を変えるので採らない）。

| G8 の入力（GENDATA_ROADMAP §3 G8、§4 G8） | U-R12 が満たすか | 根拠 / 残り |
|---|---|---|
| `shapePost_pack` で body を `machCanonAp (machPack dom' (lfs ++ outF ++ slotF))` に固定 | 満たさない（U-R12 の範囲外） | G8 / G6 側。`machineShapeF_reach` の `shapePost … = some sp` 等式をそのまま使う |
| 各 field の値が `machClose kI n k 0 (…)` に入る前に**範囲内・loose-free** | **満たす**（`machineShapeF_ranges`: let 値の `InRange`/`NoLoose 0`、`ws` の `InRange`、`wrap? = none` のときの出力 `v`、`dom`） | G8 の証明が `machClose_machIn / machInstOut / machSlot / machLet`（Cover）と組み合わせる。**この調査では G8 が `machClose` についてほかに何を要るか読んでいない**（`machClose_bvar` の前提は REV7 S5 が「root bvar のみ」と記録） |
| 各 pushed field が `Term` の `quote` の像である（C-QWIT 本体） | **満たさない** | 7 本の `readF` 本体にわたる別の帰納（`QuoteGood`）。`app` 腕の extractor 補題（U-R2、Extract）と `chain`/`conv` の glue（`satp_*`、`envPh_*`、`reachC_*`）は共有できるが、`QuotePost` の型は G7（D2）の確認後に G8 の freeze で固定する |
| 各 field に sort（`machField dom' kind`）が付く | 満たさない | G8。`kind` は `ShapePre.outs` / `st.kinds` から来る |
| `st.dom` が R5-R6 の合成に一致（G5） | 満たさない | `dom` の範囲（`DomPh`）は満たすが、**一致**は G5 |
| `d.shape = sp`、`nDecl = kDOf d`（行 6b） | 満たさない | `sparkle-gen5-dg-dataof` |
| `hbr`（`ShapeFuelBridge`、C.CV-4） | 満たさない | `sparkle-gen5-reader-bridge`。U-R12b の `machineShapeF n …` は燃料版の run |

G8 が U-R12 の骨格をどう再利用するか: `shapeStart_trace`／`rootLets_trace`／`shapeBody_trace` は `TraceGood` 専用の型で置く（この freeze の型）。G8 は同じ 3 段の分解（`machineShapeF_steps`）を `QuoteGood` で別に組む。共有するのは `ShapeMid` の 4 つの成分の取り方（`MidInputs` 型の入力条件）と `ShapeCarry` に当たる旧側の不変条件。**3 段の補題を呼び出し表の述語についてパラメータ化する案は、型が複雑になるので採らない**（G8 の freeze で必要なら別途）。

## 5. 新しい前提の候補（提案であって採用ではない。数えていない）

U-R12c の `shapeInputs_of` は、`ShapeInputs` を次の候補から組む。**reviewer の結論 (b)：既存 ID と完全な型・domain で照合できないものは新規・強化として数える。** 下の「照合」は読んだ範囲で、台帳そのものを再計数していない。

| ID（候補） | 文 | 何の呼び出しを覆うか | 既存行との照合 | 台帳の候補 |
|---|---|---|---|---|
| N1 `DeclValuePh env` | `∀ d, (env の defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true`（宣言の値は閉じていて、placeholder の fvar を含まない） | `shapePre` の `d.value` | `EnvTypesFVarFree`（型の fvar 不在）は値を覆わない。`SigTyClosed` は `instS` の型のみ。**値の版は見つからなかった**。DG-ENV の環境条件（owner 候補 `sparkle-gen5-dg-env`）。kernel の `addDecl` の事実の見込み | FG +1 見込み（DG-ENV と統合できれば ±0 の可能性。未確認） |
| N2 `PackTupleInputsPh` | `∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true → NoPh (packTupleInputs e) = true ∧ BvarLt L (packTupleInputs e) = true`（N3 と同じ書き方に合わせた、2026-11-02 coder） | `shapePre` の `packTupleInputs`（**`partial def`**、`liftLooseBVars` と `instantiate1` を呼ぶ） | 既存の `LiftAgrees`（T1L-50）・`Inst1Agrees` は `liftLooseBVars`/`instantiate1` 側。**`packTupleInputs` 自体の Ph 版は見つからなかった**。ユーザー方針（`partial def` は振る舞いのモデル + 本番との一致を前提）に従うなら、fuel twin + 一致の前提（C.CV-4 型）になる | 新規（+1 見込み。型は C.CV-4 `ShapeFuelBridge` の一般化に吸収できる可能性があるが未確認） |
| N3 `NormFPh senv` | `∀ (L n : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true → machNormF n senv e = some en → NoPh en = true ∧ BvarLt L en = true`（`L` は束縛変数の上限で、全称で量化する。reviewer 指摘 2026-11-02 で明記） | `machNormF`（`rawNode`、`machNormNode`、`instantiate1`、`machLiftScalarN`・`machBoolMap` の partial 2 本。この 2 本は par/ptot-m4 965fe51b で全域化済み・一致定理受理済みだが、この base には入っていない） | **`LetOk` 版の分解（`RawNodeRange`、`LiftScalarRange`、`BoolMapRange`、`NodeCorr` 等、`Tools/Prototype/`）はあるが、型が違い再利用できない**（`LetOk` ≠ `NoPh` ∧ `BvarLt`）。`Inst1Agrees` が `machNormF` の `instantiate1` 腕を覆う見込みだが、他の腕は照合できていない | 新規（1 本にまとめれば +1 見込み。helper ごとに分解すれば +2〜+4 の見込みで、狭くなる。分解は未調査） |
| N4 `ZeroLit`（`zeroLit` = `Expr.replace`） | `NoPh` / `BvarLt L` を保つ | `shapeMid` の `zeroLit` | `ZeroLitAgrees0`（T1L-54、`Tools/Assume/N3Extern.lean`）が `Expr.replace` の等式を覆う。**その domain が `inlNatLit` / `canonicalNatLitValue?` を使う `zeroLit` の呼びに十分かは照合していない**。足りれば Ph 版は構造補題（前提なし）。足りなければ強化 | 照合まで 0 として扱わず、未照合＝新規／強化の可能性ありと記録（数えない） |

既存の名前付き条件で足りるもの: `rootFloat`（`RootFloatAgrees`、T1L-52 → `rootFloat_ph`）、`inlFoldNat`・`machLoopAsLet`・`machRoot`・`mixedGatePeel`（前提なしの構造補題、§2.3）。

**候補を合計した台帳の見込み: FG +0〜+4、T1 +0（採用方式しだい、未計数）。** 採用しない場合は `ShapeInputs` が U-R12b の仮定のまま残り、**FG 受理は未達**。

## 6. 台帳で消える候補の行と、その条件（今回は 1 行も数えない）

`kjob/fg-ledger-int:scripts/gen2/PREMISE_LEDGER.md` の行（FG 104 の内訳そのものは再計数していない）:

| 行 | 内容 | 消えるための条件（すべて満たすまで数えない） |
|---|---|---|
| C.RT-1 | `hT : TraceGood senv nDecl (readF senv n)`（帰納仮定） | (1) clean build `rtv-f1d8b228` 合格、(2) `readF_traceGood_of_premises` の仮定が**既存の行だけ**であること（6 つの名前付き仮説はすべて既存の行）、(3) 台帳の行の型・domain（`n`、`senv`、`nDecl` の量化）が `readF_traceGood` と一致すること。**これは U-R12 の前でも成り立ち得る**ので reviewer が確認する |
| C.RT-4 | `hstep`（全 arm） | 同上（`step_trace` が全 arm を閉じている。f1d8b228）。C.RT-1 と同一の義務の粗い束かどうかは未確認（二重計上しない） |
| C.RT-2 | `hpre : TracePre …`（`ShapeInputs`＝R-in の担当と記録されている行） | U-R12a + U-R12b が合格し、かつ `ShapeInputs` が**台帳の行として置換**されたとき（`hIn` が仮定のままなら、行は `ShapeInputs` に付け替わるだけで消えない） |
| C.CV-2 | `hnl : LetsNoLoose st`（run-local の `st`） | U-R12b の結論 `TrInv senv nDecl st`（`CtlPh` の `LetsNoLoose`）が、台帳の `st` と**同じ**（`machineShapeF_state_side` の同一 witness の最終状態）であり、`ShapeInputs` の供給が済んでいること（N1〜N4 の扱いが決まっていること） |
| C.CV-3 | `hi : FullInv nDecl st`／`FReachC` | 同上（U-R12b の `FReachC` 3 連と `TrInv.1`） |
| C.CV-6 | `hcb`、R-in、R-dom | R-in / R-dom の部分のみ。`hcb`（B3 = src-argw）は覆わないので、行を分割しない限り消えない（行の分割は 104 を変えるので行わない） |
| C.RK-8 / C.DO-3 の C-QWIT 部分 | reader 完全性 / C-QWIT | **U-R12 では消えない**（§4）。G8 の合格後 |

C.CV-2 と C.CV-3 が 2 行として別個に消えるか、または粗い束の同一義務かは、rev5 §3 の未確認 (3) のままで、台帳の行の全文との照合が要る。**今回の判断では数えない。**

## 7. Check の予定（Lean 実装後）

`Tests/Gen5/ReaderTraceShapeCheck.lean`、`Cover6Check` / `ReaderTraceDispatchCheck` の形。TYPE（`MidInputs`・`ShapeInputs`・`ShapeCarry` の `def` の値を含む、本ファイルの型を Tools を見ずに書き直して比較）、MUTANT（signature / defeq 棄却のみ: `BvarLt` の `k + nDecl` を `nDecl` に、`shapeBody_trace` の `FReachC` を落とす、`machineShapeF_reach` の `TrInv` を `FullInv` に、`FReachC nDecl {} st0` を落とす、`MidInputs` の run 節の `+ 1` を落とす等。意味的反例ではない）、AXIOMS（標準 3 つのみ）、CLOSURE。ビルドは `kjob lake build` を 1 つずつ。Lean コミット後は `doing` のまま「clean build は coder」。

## 8. 主張しないこと

* `ShapeInputs` の成立、N1〜N4 の真偽、`readF_traceGood` の仮定である 6 つの名前付き仮説の真偽。
* C-QWIT（`QuoteGood`）、`d'.ok`（G9）、`dom'` の一致（G5）、行 6b・`nDecl = kDOf d`、`hbr`（C.CV-4）、`LetQuoteEq`（C.CV-1）、B3、実 run と FG。
* 台帳の行が消えること（§6 の条件が揃うまで数えない）。TraceGood 単独の FG 減少数。
* 新しい law / TRUSTED 境界 / コンパイラ・共有定義の変更 / FG の変更は**採用していない**（§5 は提案のみ）。`GenWF` は強化しない。

## 9. reviewer への依頼

承認を求める文は 3 つ:
1. §1 の U-R12a / U-R12b の型（§2.1、§2.2）と、**`DomAtomic` を `MidInputs` から外す変更**（§0 の 4 点目。弱める変更で、`ShapeInputs` の入力条件は減る）。`ShapeInputs` は定理の仮定であり台帳の行ではない。
2. §2.3 の前提なし部分（U-R12c の構造補題）と、§5 の N1〜N4 を**候補としてのみ**登録すること（採用・分解・先送りは別の判断）。
3. §4 の切り分け（U-R12 は G8 の範囲の入力を供給するが C-QWIT 本体を供給しない。`TracePost` は変えない）。

N1〜N4 の扱い（採用する / helper ごとに分解する / `ShapeInputs` を 1 つの名前付き前提のまま FG に載せる / 先送りする）は、この rev14 の承認とは分け、reviewer が 1 回で選べるよう次の rev で U-R12a/b の build 結果を添えて出す。**先送りの場合の影響: U-R12a/b は進む。FG 受理側で `ShapeInputs` が残る。**

## 10. 追記（rt18、2026-11-01）: `shapeStart_trace` と U-R12b は rev14 の型のままでは進められない（review に出す）

**台帳: FG 104 / T1 54（今回 FG -0 +0 / T1 -0 +0）。この追記は台帳を 1 行も変えない。**以下の選択肢のうち、台帳に影響し得るもの（選択肢 B）は採用せず、数えていない。

### 10.1 実装したもの（rev14 の型どおり。新しい前提なし）

`Tools/ShippingGen5ReaderTraceShape.lean`（+ `Tests/Gen5/ReaderTraceShapeCheck.lean`、`lakefile.lean` に `lean_lib` 2 件）、コミット 8ba8bf09、Pod build 済み（`kjob lake build` を 1 つずつ）:
`MidInputs`（`DomAtomic` なしの rev14 版）、`ShapeInputs`、`ShapeCarry`、`shapeCarry_empty`、`shapeRootLet_trace`、`rootLets_trace`、`shapeBody_trace`。
COUNTS: `Tools.ShippingGen5ReaderTraceShape` exit 0（771 jobs）/ `Tests.Gen5.ReaderTraceShapeCheck` exit 0（773 jobs）: TYPE 7（3 つの `def` は値で、4 つの定理は型で比較）、MUTANT 5（signature / defeq での棄却で、意味的反例ではない）、AXIOMS 7（標準 3 つのみ）、CLOSURE OK 5214 constants from 7 roots（sorryAx なし。Check 内の sorry 警告は in-memory の負の対照）。Tools 側に sorry / axiom / native_decide なし。clean build は coder。

### 10.2 実装できていないもの: `shapeStart_trace`（したがって `machineShapeF_reach`、`machineShapeF_reach_of_premises`）

**事実（Lean のコードを読んだ範囲）。** `shapeStart` は `wConv (units) 0 dom {}` の結果 `(dom', stc)` の**状態 `stc` を捨て**、`machReserve … dom' … ({} : MachRead)` を**空の状態 `{}`** に対して実行する（`ShippingReaderFuelShape.lean` の `shapeStart`）。したがって `st0 = reserved {} dom' body kinds inits`。`TrInv senv nDecl st0` の `DomPh` は `InRange nDecl st0 st0.lets.size dom'` を要し、`st0.lets.size = 0`、`st0.insts.size = 0` なので、`dom'` が `_machLet` / `_machInst` を**一つも含まない**ことが要る。一方 `hT` が与えるのは `InRange nDecl stc stc.lets.size dom'`（捨てられた `stc` に対する範囲）で、`stc.lets.size` / `stc.insts.size` は 0 とは限らない（`conv` は let を束縛し得る）。`RdOk st0` の `LetOk 0 dom'` も同じ理由で `hT` からは出ない。
この調査では、`hT`・`MidInputs` の rev14 版・既存の補題から、`InRange nDecl {} 0 dom'` を出す経路は見つからなかった（不可能という主張ではない）。

**rev14 §0 の 4 点目の訂正。** 「`DomAtomic` は `CtlPh / PhPre / trInv_reserved` のどこにも使われない」は、上の理由で**誤り**だった。`DomAtomic`（rev0 `DG_READERTRACE_FREEZE.md` §3.3、F4）は、まさにこの「`shapeStart` が `dom` の変換状態を捨てる」ことへの入力条件として置かれたもの（`DomAtomic e := (∃ j, e = .bvar j) ∨ (∃ c ls, e = .const c ls)`）で、`CtlPh` ではなく `shapeStart_trace` の証明で使う。rev14 でこれを外した変更（「弱化」）は、`shapeStart_trace` の結論を支えなくする。

`shapeRootLet_trace` / `rootLets_trace` / `shapeBody_trace` は `dom'` を使わないので、この問題の影響を受けず、上のとおり実装済み。

### 10.3 選択肢

| 案 | 内容 | 台帳 | 影響・コスト | 可逆性 |
|---|---|---|---|---|
| A（推奨） | `MidInputs` の run 節に `DomAtomic dom` を戻す（rev0 の形）。`shapeStart_trace` では `readF senv (n'+1) (conv units 0 dom {})` を `dom` が bvar / const の場合に直接展開し、`dom' = machIn (j - rootLets.length)`（`j < rootLets.length` は `convBvar` が `unit` で失敗するので成功 run と矛盾）または `dom' = dom`（const）で、状態 `stc = {}` を示す。`InRange nDecl {} 0 dom'` は `inRange_machIn`（`j - len < nDecl` は `BvarLt (len + nDecl)` から）と const の自明性 | 0 / 0（`ShapeInputs` は定理の仮定で台帳の行ではない。ただし `ShapeInputs` が**強くなる**ので、U-R12c の供給側でも「受理されたソースの `dom` が bvar か const」を示す必要がある。**この調査では、その供給元は確認していない**。N1〜N4 と同じく別の判断に残す） | 追加の証明は `readF` の bvar / const 腕の 1 段展開のみ（trace 不要）。`MidInputs` の型が rev14 から変わる（`DomAtomic` を戻す） | 可逆（型を再び弱めればよい） |
| B | `dom'` の範囲を出力側の名前付き条件にする: `∀ dom' stc, machConvF n senv (units) 0 dom {} = some (some (dom', stc)) → InRange nDecl {} 0 dom'`（`n` に依存。`ShapeInputs` の節か `shapeStart_trace` の仮定） | 新規の条件（FG +1 見込み。既存行との照合は未、数えない） | 証明は軽いが、リーダーの出力についての新しい前提になる。ユーザー方針（前提の追加を避ける）に反し得る | 可逆 |
| C | `shapeStart_trace` を諦め、`DomPh` を `ShapeCarry` から外す | — | `TrInv` の定義（承認済み・共有）の変更になるので不可（FG の縮小にも当たり得る） | — |
| D | 判断を待つ間 U-R12a の残りと U-R12b は止める | 0 / 0 | U-R12b（`machineShapeF_reach`）、C.RT-2 / C.CV-2 / C.CV-3 の台帳候補（§6）が止まる | — |

推奨は A。理由: 新しい前提を増やさず、rev0 の設計意図（F4）に戻すだけで、証明の追加も `readF` の 1 段展開に限られるため。ただし `ShapeInputs` を満たすべき入力が増える（強化）ので、reviewer の判断が要る。

### 10.4 reviewer への依頼

1. 10.2 の訂正（rev14 §0 の 4 点目の取り下げ）の確認。
2. 10.3 の A / B / D の選択（C は不可）。A なら、`MidInputs` に `DomAtomic dom` を戻した型で、`shapeStart_trace` / U-R12b を実装してよいか。
3. 10.1 の実装済み部分（rev14 の型どおり、新しい前提なし）の Lean レビューは、clean build（coder）の後。

### 10.5 主張しないこと

`ShapeInputs` / `DomAtomic` が受理されたソースで成り立つこと。`hT` の 6 つの名前付き仮説の真偽。台帳の行が消えること。U-R12c の構造補題（`mixedGatePeel_ph` 等）は未着手（この追記の判断とは独立で、前提なし部分として後で進められる）。

## 11. 追記（rt19、2026-11-01）: §10 案 A の実装結果（新しい前提なし）

**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。**

実装（Lean コミット 389c4097、`Tools/ShippingGen5ReaderTraceShape.lean` / `Tests/Gen5/ReaderTraceShapeCheck.lean`）: `DomAtomic`、`MidInputs`（run 節に `DomAtomic dom` を戻した版、rev0 §5 の位置）、`shapeStart_trace`（`DomAtomic` 付き）、`machineShapeF_reach`、`machineShapeF_reach_of_premises`、`machineShapeF_ranges`。U-R12a の残りはない（U-R12c は未着手で別の単位）。
`shapeStart_trace` の道筋: `shapeStart_inv` で `dom'`/`stc` を取り、`dom` が bvar なら `convBvar_trace`（空の units 環境、`r.2 = st`）、const なら `readF` の catch-all 腕の 1 段展開で `stc = {}`。以後 `hT`（conv 呼び）で `dom'` の範囲と `LetOk 0 dom'` を得て `trInv_reserved` と `adv_dom` に渡す。
検証（kjob lake build を 1 つずつ、exit 0）: Tools 771 jobs / Check 773 jobs。COUNTS: TYPE 12、MUTANT 8（signature/defeq での棄却で意味的反例ではない）、AXIOMS 12（標準のみ）、CLOSURE 9758 constants from 12 roots（unknown 0、sorryAx なし）。clean build は coder。
主張しないこと: `ShapeInputs`（`DomAtomic dom` を含む）が受理されたソースで成り立つこと（供給は未証明のまま。U-R12c / N1〜N4 の判断に残る）、`hT` の 6 つの名前付き仮説の真偽、台帳の行が消えること。
