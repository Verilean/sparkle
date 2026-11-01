# DG-READERTRACE freeze rev20（D-b: `DomKeep` と `DomAtomic` 除去、hbs 除去 `nDeclOfCi` の完全型。文書のみ）

対象 Issue: `sparkle-rt-rev20`（親 `sparkle-gen5-dg-readertrace`）。base: `par/rt-dom-survey` 6a52d257。根拠: `RT_DOM_SURVEY.md` §1.3 / §2.3、`DG_READERTRACE_FREEZE_REV19.md`。
**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。** Lean の source tree は編集していない。コンパイラ・共有定義・TRUSTED 境界・law・FG/保証は変えず、`GenWF` も強化しない。
rev19 の署名 `shapeInputs_of_direct` は変えない（残る）。ここで足すのは**新規ファイルに置く primed 版**だけ。
用語: 「見つからなかった」は「この調査で辿った経路では見つからなかった」の意味で、不可能・導出不能の主張ではない。scratch の elaborate は**型が通ること**の確認で、定理が証明できること・条件が真であることの確認ではない（証明は `sorry`、ただし `bs_len_eq` / `hbs_of_nDeclOfCi` は scratch 内で実際に証明が通った）。

## 1. D-b-1: `DomKeep`

```
def DomKeep (h : Hs) : Prop :=
  ∀ (c : Call) (v : c.Res), h c = some (some v) →
    ∀ d : Lean.Expr, (callSt c).dom = some d → (callOut c v).dom = some d
theorem readF_domKeep (senv : StructEnv) (n : Nat) : DomKeep (readF senv n)
```

**量化の形。** `TraceGood`（`Ctl.lean:99`）は `∀ c, TracePre → ∀ v, h c = some (some v) → TracePost`。`DomKeep` は同じ `∀ c … ∀ v, h c = some (some v) → …` で、`TracePre` 前件を持たない。`senv` / `nDecl` は `dom` の保存に使わないので引数にしない（`RT_DOM_SURVEY` §1.3 の草稿の `senv` と `callOutTy c` は、`Call.Res` が正しい名前なので直した）。

**決定: 独立の帰納にする（`TraceGood` の拡張にしない）。**
1. `TracePost` / `TraceGood` に `DomKeep` の連言を足すと、既存の `TraceGood` を使う全定理（Dispatch の `readF_traceGood*`、Shape、Cover 系）の型が変わる。共有に近い既存の承認済みの文の変更になる。
2. `DomKeep` は `TracePre`（`TrInv` / `EnvPh` / `NoPh` / `BvarLt`）を要さず、`dom` の 1 フィールドだけの不変条件。前提なしで全入力について言える（見込み。証明は未実施）。
3. 先例: `GoodE`（`ShippingGen3ArgSupply3.lean:262`、「`TraceGood` 無関係の fuel 帰納、premise なし」）が同じ型の独立不変条件。
4. `CtrlEq` / `FReachC` は `dom` を自由にしている（`Cover6.lean` ヘッダ）ので、`FReachC` からは出ない。
独立にした代償: 7 腕の場合分けを再度書く（`TraceGood` の腕ファイルより軽い見込み。行数は見積もらない）。

**7 腕の表。** 「書く箇所」は `Elab.lean` の行（reader の鏡像 `ShippingReaderFuelDefs.lean` の行を併記）。`dom` を書くのは conv(bare register)・inst・instS・loopRoot の 4 箇所と `machReserve`（nested から）の計 5 箇所で、どれも「設定済みなら同じ値のときだけ通る」検査の後で書く。

| 腕 | `dom` を書く箇所（Elab / Defs） | 保存の理由 |
|---|---|---|
| conv | bare register 腕 Elab 3927-3933（検査 3927-3929、書き込み 3933）/ Defs 313-318（`domGuard`）。`.state b n` 腕 Elab 3898 は `st.dom` を読むだけ | 先に `machConv … dom st` を呼ぶ（帰納仮定で `dom = some d` が残る）→ 検査で `d0 ≠ dom'` なら失敗、通れば `dom' = d`、書くのは `some dom' = some d`。他の腕（`bvar` / `app` の分配 / `lam` / `forallE` / `letE` / 定数）は再帰（conv / nested / inst / instS / loopRoot の各腕）と `{ st with lets := … }` / `instStruct := …` のみで `dom` に触れない |
| nested | 直接は書かない。`machReserve` Elab 3708-3716（検査 3708-3710、書き込み 3716）/ Defs 405 の `optK (machReserve …)` | `machConv … dom st`（帰納仮定）→ `shared` 枝は `machChain`（chain 腕の帰納仮定）→ なければ `machReserve`（検査後 `some dom'`、`dom'` は検査で `d` に等しい）→ `machChain … { st with inInner := true }`（record 更新は `dom` を保つ）→ 最後の `{ st with ws, inInner, nested }` も保つ |
| inst | `domain` 引数 Elab 4066-4068 / Defs 418-420 | `machConv … arg st` が `dom = some d` を保つ（帰納仮定）→ `some d` の枝は `d ≠ v'` なら失敗、通れば状態は変わらない。`none` 枝（書き込み）は入力が `some d` の状態では到達しない。他の引数は `lets` の更新のみ |
| instS | `domain` 引数 Elab 4105-4107 / Defs 448-450 | inst と同じ形（`instS` の foldlM） |
| chain | 直接は書かない（Elab 4135-4180） | `machConv`（conv 腕）/ `machLoopRoot`（loopRoot 腕）/ `machChain` 自身（帰納仮定）の連鎖と `{ st with lets := … }` のみ |
| loopBody | 直接は書かない（Elab 4182-4203） | `machConv`（conv 腕）の連鎖と `{ st with lets }` / `{ st with ws }` のみ |
| loopRoot | Elab 4215-4217（検査）と 4235（書き込み `dom := some dom'`）/ Defs 572（`domGuard`）、585 | `machConv … dom st`（帰納仮定）→ 検査 → `shared` 枝は `machLoopBody … { st with ws := #[] }`（loopBody 腕の帰納仮定。`{ st' with ws := st.ws }` は保つ）→ なければ `some dom'`（検査で `d` に等しい）を書いて `machLoopBody`（帰納仮定）、最後の `{ st with loopWs, loopDepth }` も保つ |

`readF` は fuel 付きなので、証明は `n` についての帰納（`fuel` の `n+1` で `step` の 7 腕を展開、`n = 0` は `none` で空）。`GoodE` と同じ型の帰納で、`TraceGood` の仮説（`hla` / `hrf` / `hI` / `hD` / `hS` / `PureFacts`）は使わない見込みで、**新しい前提を足さない**。証明が詰まる場合（たとえば腕が `dom` を書き換える経路が見つかる場合）は、そこで止まって coder に報告する（自動受理しない）。

## 2. D-b-2: `DomAtomic dom` を外した `MidInputs'` / `shapeStart_trace'` / `ShapeInputs'` / `machineShapeF_reach'`

新規ファイル（案: `Tools/ShippingGen5ReaderTraceDomKeep.lean`、`Tools/ShippingGen5ReaderTraceShape2.lean`、`Tools/ShippingGen5ReaderTraceDirect2.lean`、`lakefile.lean` に `lean_lib` 追加）に置く。既存の `DomAtomic` / `MidInputs` / `ShapeInputs` / `shapeStart_trace` / `machineShapeF_reach` / `shapeInputs_of` / `shapeInputs_of_direct` は**変更しない**（共有定義を変えない。下流が既存名を使い続けられる）。

* `MidInputs'` は `MidInputs` から run 節の `DomAtomic dom` の連言を落としただけ（他は同一）。`ShapeInputs'` は `MidInputs'` を使う。
* `DomForm d := ∃ r, machDom? 0 d = some r`（`machDom?` は `Elab.lean:4269`。`_machIn i` の fvar か `defaultDomain` の const のときだけ `some`。`machDom?` を直接参照し、形の二重定義を避ける）。
* `shapeStart_trace'` は、`stc = {}` を `DomAtomic` から出す代わりに、reserve 後の状態の `dom` が `DomForm` であるという仮説 `hform : ∀ d, st0.dom = some d → DomForm d` を取る。`DomForm` なら `InRange nDecl stc … dom'`（`hT` が `dom` の変換結果について出す）から、状態によらない `InRange nDecl {} 0 dom'`（`_machIn i` は `i < nDecl` を `InRange` から取る、const は自明）を作り、`{}` への `trInv_reserved` を使える（見込み。`DG_DOMATOMIC_SURVEY.md` §3.3）。`hdom` 仮説も `DomAtomic` を落とした 2 連言になる。
* 順序の依存: `hform` は後段（`shapePost`）の情報なので、`shapeStart_trace'` 自身では作れない。`machineShapeF_reach'` が供給する。

**`machineShapeF_reach'` の流れ（成功・`shapePost` の `machDom?`・`DomKeep` から変換後 `dom'` の形を供給する）。**
1. `machineShapeF_state_side h` で `p en st0 env st1 st v` と `h0 h1 h2 h3`（`h3 : shapePost … st v = some sp`）を取る（成功から。既存の `machineShapeF_reach` と同じ）。
2. `hIn p en hp hen`（`ShapeInputs'`）で `hrl hrun hroot` を取る。
3. `hform` の用意: `st0.dom = some d` のとき、`rootLets_domKeep`（`h1`）→ `shapeBody_domKeep`（`h2`）の順に `DomKeep (readF senv n)`（`readF_domKeep`）を使って `st.dom = some d`。`shapePost_domForm h3` で `DomForm d`。（`shapePost` は `domE ← st.dom <|> machTypeDom? …` から `machDom?` を要するので、`st.dom = some d` なら `domE = d`、`machDom? … d = some _`。）
4. `shapeStart_trace'` に `hform` を渡して `R0 C0`。以降（`rootLets_trace` / `shapeBody_trace`）と結論は既存の `machineShapeF_reach` と同一。`run? = none` のときは `st0 = {}`（`dom = none`）で `hform` は空虚。
この流れは**型の確認のみ**で、証明は実施していない。`hT : TraceGood` は従来どおり仮説。結論の型は `machineShapeF_reach` と一字一句同じ（scratch で確認、§5）。

## 3. hbs の除去: `nDeclOfCi`

* `nDeclOfCi ci := ((mixedGatePeel (packTupleInputs d.value)).map (·.1.length)).getD 0`（`.defnInfo d` のとき、それ以外は 0）。`generator`（`ShippingMachineCommand.lean:459-460`）の `nDecl := bsIn.length` と同じ関数・同じ入力。
* `bs_len_eq : shapePre sm ps ci senv = some p → p.bs.length = nDeclOfCi ci`、`hbs_of_nDeclOfCi`（等式から `≤`）。**scratch で証明まで通った**（`shapePre_facts`、`subst`、`simp [nDeclOfCi, hpeel]`）。これは `hbs` の型の文が `nDecl := nDeclOfCi ci` なら定理になることだけを示す。
* `shapeInputs_of'`（`shapeInputs_of` から `hdom` を外し結論を `ShapeInputs'` にしたもの。`hbs` は一般の `nDecl` の仮説のまま残す）と、`shapeInputs_of_direct'`（`nDecl := nDeclOfCi ci`、`hdom` / `hbs` の binder を除き、`{nDecl}` も無くす）。証明の見込み: rev19 の `shapeInputs_of_direct` と同じ流れで、`hbs := hbs_of_nDeclOfCi …`、`hdom` の連言を作らない。
* **付け替え先。** `kDOf d = nDeclOfCi ci`（`hnD : nDecl = kDOf d`、DG-DATAOF の義務、FG 台帳 C.EN-6 の隣、`ShapeAgree` / `rowC_of_reader` の `hnD`）。`hbs` は消えるが、**同じ内容が `hnD` に移る**（`RT_DOM_SURVEY` §2.3）。`d.nIn = nDeclOfCi ci + insts.length` は generator の知識（`ShippingR5Check.lean:29`）で、この freeze は供給しない。

## 4. 台帳

消える行 0、増える行 0。binder の除去と付け替え:

| 項目 | 台帳の行か | 今回の扱い |
|---|---|---|
| `hdom : … DomAtomic dom`（`shapeInputs_of_direct` / `shapeInputs_of` の binder） | 元から行ではない | `ShapeInputs'` から `DomAtomic` を外し、primed 版に binder は無い。`DomKeep` は新しい前提ではなく定理（`readF_domKeep`、前提なしの見込み）。FG/T1 の増減 0 |
| `hbs : p.bs.length ≤ nDecl`（`shapeInputs_of_direct` の binder） | 元から行ではない | `nDecl := nDeclOfCi ci` で `bs_len_eq` が定理に。binder 除去。減算 0 |
| `hnD : nDecl = kDOf d`（DG-DATAOF）、`d.nIn` の同定 | 既存の義務（FG 台帳 C.EN-6 / DG-DATAOF 側、`hnD` はすでに未供給の名前付き前提） | `hbs` の内容の付け替え先。新しい行ではない。行数の増減 0 |
| `DomAtomicRun`（D-a、FG +1 見込み） | — | **採らない**。D-b を実装して閉じなかったときだけ別の freeze で扱う（`RT_DOM_SURVEY` §1.3） |

台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。
reviewer の承認が要る範囲（分担）: 「primed の型で `DomAtomic` を `DomForm`（`machDom?`）+ `DomKeep` に置き換えること」「`nDecl := nDeclOfCi ci` で `hbs` を `hnD` へ付け替えること」。この 2 点は台帳の付け替え・目標にあたるので review に出す。

## 5. scratch の elaborate

`Scratch/Rev20Sig.lean`（worktree 内、**コミットしない**。`lakefile.lean` の `lean_lib «Scratch.Rev20Sig»` もコミットしない）を `kjob lake build Scratch.Rev20Sig` で elaborate: `Build completed successfully (791 jobs)`、exit 0（Pod 内）。`set_option autoImplicit false`、import は `Tools.ShippingGen5ReaderTraceDirect` のみ。警告は `declaration uses \`sorry\`` 9 件（意図した型のみの定理 9 個）と既存ファイルの lint のみ、エラーなし。sorry は scratch のみ。

ソース（`#check` / `#print` を除く全文）:

```lean
import Tools.ShippingGen5ReaderTraceDirect
set_option autoImplicit false

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderLenOk

/-! ## File 1: DomKeep -/

def DomKeep (h : Hs) : Prop :=
  ∀ (c : Call) (v : c.Res), h c = some (some v) →
    ∀ d : Lean.Expr, (callSt c).dom = some d → (callOut c v).dom = some d

theorem readF_domKeep (senv : StructEnv) (n : Nat) : DomKeep (readF senv n) := by
  sorry

theorem shapeRootLet_domKeep (senv : StructEnv) (n : Nat) (hK : DomKeep (readF senv n))
    (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    {s' : List MachVal × MachRead} (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s'))
    (d : Lean.Expr) (hd : s.2.dom = some d) : s'.2.dom = some d := by
  sorry

theorem rootLets_domKeep (senv : StructEnv) (n : Nat) (hK : DomKeep (readF senv n)) :
    ∀ (l : List (Name × Lean.Expr × Lean.Expr)) (env : List MachVal) (st : MachRead)
      {env' : List MachVal} {st' : MachRead},
    (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
    ∀ d : Lean.Expr, st.dom = some d → st'.dom = some d := by
  sorry

theorem shapeBody_domKeep (senv : StructEnv) (n : Nat) (hK : DomKeep (readF senv n))
    (m : ShapeMid) (env : List MachVal) (st1 : MachRead) {st : MachRead} {v : Lean.Expr}
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v)))
    (d : Lean.Expr) (hd : st1.dom = some d) : st.dom = some d := by
  sorry

/-! ## File 2: DomForm, ShapeInputs', shapeStart_trace', machineShapeF_reach' -/

def DomForm (d : Lean.Expr) : Prop := ∃ r, machDom? 0 d = some r

theorem shapePost_domForm {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (h : shapePost ai p m st v = some sp)
    {d : Lean.Expr} (hd : st.dom = some d) : DomForm d := by
  sorry

def MidInputs' (nDecl : Nat) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)

def ShapeInputs' (nDecl : Nat) (senv : StructEnv) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
    (n : Nat) : Prop :=
  ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
    MidInputs' nDecl senv p en

theorem shapeStart_trace' (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true)
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0))
    (hform : ∀ d : Lean.Expr, st0.dom = some d → DomForm d) :
    FReachC nDecl ({} : MachRead) st0 ∧ ShapeCarry senv nDecl [] st0 := by
  sorry

theorem machineShapeF_reach' {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs' nDecl senv sm ps ci n) :
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
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) := by
  sorry

/-! ## File 3: nDeclOfCi, hbs, shapeInputs_of', shapeInputs_of_direct' -/

def nDeclOfCi (ci : Lean.ConstantInfo) : Nat :=
  match ci with
  | .defnInfo d =>
    ((mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value)).map (fun x => x.1.length)).getD 0
  | _ => 0

theorem bs_len_eq {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
    {p : ShapePre} (h : shapePre sm ps ci senv = some p) : p.bs.length = nDeclOfCi ci := by
  obtain ⟨hci, hpeel, -⟩ := shapePre_facts h
  subst hci
  simp [nDeclOfCi, hpeel]

theorem hbs_of_nDeclOfCi (sm : Bool) (ps : List (String × Nat)) (ci : Lean.ConstantInfo) (senv : StructEnv) :
    ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDeclOfCi ci :=
  fun _ h => Nat.le_of_eq (bs_len_eq h)

theorem shapeInputs_of' (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hrf : RootFloatAgrees)
    {nDecl : Nat} {senv : StructEnv} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {n : Nat}
    (hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true)
    (hpack : ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
      NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true ∧
        BvarLt L (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true)
    (hnorm : ∀ (L : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true → machNormF n senv e = some en →
      NoPh en = true ∧ BvarLt L en = true)
    (hbs : ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDecl) :
    ShapeInputs' nDecl senv sm ps ci n := by
  sorry

theorem shapeInputs_of_direct'
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    {ci : Lean.ConstantInfo} (hci : CiDirect env ci)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat} :
    ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n := by
  sorry

end Tools.ShippingGen5ReaderTrace
```

`#check` / `#print` の出力（そのまま）:

```
info: Scratch/Rev20Sig.lean:131:0: DomKeep : Hs → Prop
info: Scratch/Rev20Sig.lean:132:0: readF_domKeep : ∀ (senv : StructEnv) (n : Nat), DomKeep (readF senv n)
info: Scratch/Rev20Sig.lean:133:0: shapeRootLet_domKeep : ∀ (senv : StructEnv) (n : Nat),
  DomKeep (readF senv n) →
    ∀ (s : List MachVal × MachRead) (a : Name × Expr × Expr) {s' : List MachVal × MachRead},
      (shapeRootLet senv s a).run (wtab senv n) = some (some s') →
        ∀ (d : Expr), s.snd.dom = some d → s'.snd.dom = some d
info: Scratch/Rev20Sig.lean:134:0: rootLets_domKeep : ∀ (senv : StructEnv) (n : Nat),
  DomKeep (readF senv n) →
    ∀ (l : List (Name × Expr × Expr)) (env : List MachVal) (st : MachRead) {env' : List MachVal} {st' : MachRead},
      (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
        ∀ (d : Expr), st.dom = some d → st'.dom = some d
info: Scratch/Rev20Sig.lean:135:0: shapeBody_domKeep : ∀ (senv : StructEnv) (n : Nat),
  DomKeep (readF senv n) →
    ∀ (m : ShapeMid) (env : List MachVal) (st1 : MachRead) {st : MachRead} {v : Expr},
      (shapeBody m env st1).run (wtab senv n) = some (some (st, v)) → ∀ (d : Expr), st1.dom = some d → st.dom = some d
info: Scratch/Rev20Sig.lean:136:0: DomForm : Expr → Prop
info: Scratch/Rev20Sig.lean:137:0: @shapePost_domForm : ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Expr} {sp : MachineShape},
  shapePost ai p m st v = some sp → ∀ {d : Expr}, st.dom = some d → DomForm d
info: Scratch/Rev20Sig.lean:138:0: MidInputs' : Nat → StructEnv → ShapePre → Expr → Prop
info: Scratch/Rev20Sig.lean:139:0: ShapeInputs' : Nat → StructEnv → Bool → List (String × Nat) → ConstantInfo → Nat → Prop
info: Scratch/Rev20Sig.lean:140:0: shapeStart_trace' : ∀ (senv : StructEnv) (nDecl n : Nat),
  TraceGood senv nDecl (readF senv n) →
    ∀ (m : ShapeMid),
      (∀ (dom αs ie b : Expr),
          m.run? = some (dom, αs, ie, b) → NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true) →
        ∀ {st0 : MachRead},
          (shapeStart senv m).run (wtab senv n) = some (some st0) →
            (∀ (d : Expr), st0.dom = some d → DomForm d) → FReachC nDecl { } st0 ∧ ShapeCarry senv nDecl [] st0
info: Scratch/Rev20Sig.lean:141:0: @machineShapeF_reach' : ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv}
  {ai : Bool} {sp : MachineShape} {nDecl : Nat},
  TraceGood senv nDecl (readF senv n) →
    machineShapeF n sm ps ci senv ai = some (some sp) →
      ShapeInputs' nDecl senv sm ps ci n →
        ∃ p en st0 env st1 st v,
          shapePre sm ps ci senv = some p ∧
            machNormF n senv p.e = some en ∧
              (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
                (foldO (shapeRootLet senv) ([], st0) (shapeMid senv p en).rootLets).run (wtab senv n) =
                    some (some (env, st1)) ∧
                  (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
                    shapePost ai p (shapeMid senv p en) st v = some sp ∧
                      st.LenOk ∧
                        sp.insts = st.insts.toList ∧
                          sp.instOrigins = st.instOrigins.toList ∧
                            sp.layout.slots.length = st.kinds.size ∧
                              sp.layout.lets = Array.size st.lets ∧
                                FReachC nDecl { } st0 ∧
                                  FReachC nDecl st0 st1 ∧
                                    FReachC nDecl st1 st ∧
                                      TrInv senv nDecl st ∧
                                        ((shapeMid senv p en).wrap? = none →
                                          InRange nDecl st (Array.size st.lets) v ∧ NoLoose 0 v)
info: Scratch/Rev20Sig.lean:142:0: nDeclOfCi : ConstantInfo → Nat
info: Scratch/Rev20Sig.lean:143:0: @bs_len_eq : ∀ {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv} {p : ShapePre},
  shapePre sm ps ci senv = some p → p.bs.length = nDeclOfCi ci
info: Scratch/Rev20Sig.lean:144:0: hbs_of_nDeclOfCi : ∀ (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (p : ShapePre),
  shapePre sm ps ci senv = some p → p.bs.length ≤ nDeclOfCi ci
info: Scratch/Rev20Sig.lean:145:0: shapeInputs_of' : Assume.N3Extern.ZeroLitAgrees0 →
  RootFloatAgrees →
    ∀ {nDecl : Nat} {senv : StructEnv} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {n : Nat},
      (∀ (d : DefinitionVal), ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true) →
        (∀ (L : Nat) (e : Expr),
            NoPh e = true →
              BvarLt L e = true →
                NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true ∧
                  BvarLt L (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true) →
          (∀ (L : Nat) (e en : Expr),
              NoPh e = true → BvarLt L e = true → machNormF n senv e = some en → NoPh en = true ∧ BvarLt L en = true) →
            (∀ (p : ShapePre), shapePre sm ps ci senv = some p → p.bs.length ≤ nDecl) →
              ShapeInputs' nDecl senv sm ps ci n
info: Scratch/Rev20Sig.lean:146:0: shapeInputs_of_direct' : Assume.N3Extern.ZeroLitAgrees0 →
  LiftAgrees →
    Inst1Agrees →
      ∀ (env : Environment),
        Assume.EnvDeclValue.DeclValuePh env →
          ∀ {ci : ConstantInfo},
            CiDirect env ci →
              Assume.PackTupleBridge.PackTupleInputsBridge →
                Assume.NormNodePh.RawNodePh (structEnv env) →
                  Assume.NormNodePh.NormNodePh (structEnv env) →
                    ∀ {sm : Bool} {ps : List (String × Nat)} {n : Nat},
                      ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n
info: Scratch/Rev20Sig.lean:147:0: def Tools.ShippingGen5ReaderTrace.DomKeep : Hs → Prop :=
fun h =>
  ∀ (c : Call) (v : c.Res), h c = some (some v) → ∀ (d : Expr), (callSt c).dom = some d → (callOut c v).dom = some d
info: Scratch/Rev20Sig.lean:148:0: def Tools.ShippingGen5ReaderTrace.DomForm : Expr → Prop :=
fun d => ∃ r, machDom? 0 d = some r
info: Scratch/Rev20Sig.lean:149:0: def Tools.ShippingGen5ReaderTrace.MidInputs' : Nat → StructEnv → ShapePre → Expr → Prop :=
fun nDecl senv p en =>
  p.bs.length ≤ nDecl ∧
    (∀ (k : Nat) (x : Name × Expr × Expr),
        (shapeMid senv p en).rootLets[k]? = some x → NoPh x.snd.snd = true ∧ BvarLt (k + nDecl) x.snd.snd = true) ∧
      (∀ (dom αs ie b : Expr),
          (shapeMid senv p en).run? = some (dom, αs, ie, b) →
            NoPh dom = true ∧
              BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
                NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
        ((shapeMid senv p en).run? = none →
          NoPh (shapeMid senv p en).root = true ∧
            BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)
info: Scratch/Rev20Sig.lean:150:0: def Tools.ShippingGen5ReaderTrace.ShapeInputs' : Nat →
  StructEnv → Bool → List (String × Nat) → ConstantInfo → Nat → Prop :=
fun nDecl senv sm ps ci n =>
  ∀ (p : ShapePre) (en : Expr),
    shapePre sm ps ci senv = some p → machNormF n senv p.e = some en → MidInputs' nDecl senv p en
info: Scratch/Rev20Sig.lean:151:0: def Tools.ShippingGen5ReaderTrace.nDeclOfCi : ConstantInfo → Nat :=
fun ci =>
  match ci with
  | ConstantInfo.defnInfo d =>
    (Option.map (fun x => x.fst.length) (mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value))).getD 0
  | x => 0
```

## 6. 主張しないこと

`DomKeep` / `readF_domKeep` が証明できること（全腕で確認していない）、`shapeStart_trace'` / `machineShapeF_reach'` / `shapeInputs_of'` / `shapeInputs_of_direct'` の証明、`ShapeInputs'` が受理されたソースで供給されること、`hnD`（`kDOf d = nDeclOfCi ci`）、変換前の `dom` が atomic であること（D-b は要さない）、`hci` 等 rev19 の入力条件の供給、C.EN-6（C0）。mutant は使っていない。コンパイラ・共有定義・TRUSTED 境界・law は変えていない。
Elab.lean の行番号は base 6a52d257 時点の読み取りで、grep による網羅証明ではない（`st.dom` を書く 5 箇所は `RT_DOM_SURVEY` §1.2 (b) と同じ）。

## 7. reviewer への依頼

1. §1 の `DomKeep` の型と、独立の帰納にする決定、7 腕の表。
2. §2 の primed 4 定義の型（`DomForm`、`hform` の置き方、`machineShapeF_reach'` の供給の流れ）と、既存の `DomAtomic` 版を残す方針。
3. §3 の `nDeclOfCi` / `shapeInputs_of_direct'` の署名と `hnD` への付け替え、§4 の台帳（消える行 0 / 増える行 0）。
