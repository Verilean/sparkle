# M4 非 machine route の D.E-12 `hno` / `htop`: 供給調査（文書のみ）

- Issue: `sparkle-gen4-fallback-supply`（agent rt156）。base: par/fb-hno = 66d13eef。前段: `scripts/gen4/FB_RESUME_STUDY.md` §3（d2ac5d60、承認）。
- 種別: 調査。Lean のソースツリーは編集していない。scratch（Pod の scratchpad、ソースツリー外）を `kjob lake env lean` で elaborate した。`Tools.ShippingDesignWriterRun` は `kjob lake build` で 420 jobs exit 0（clean build ではない）。
- 台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。この文書は台帳の数を変えない。§5 は見込みで、受入済みではない。
- 「見つからなかった」は、読んだ範囲で供給元・経路が見つからなかったという意味で、不可能・導出不能とは言っていない。mutant は扱っていない（signature/defeq 棄却も意味的反例も無い）。**観測**（scratch で実行して見えた事実）と**証明**（Lean が通した定理）と**読解**（コードを読んだだけ）を区別して書く。
- 禁止事項に触れる提案はしない。`RefLawsM`・`ofDecl` 単射の新前提化・shim 変更は reviewer の保留どおり使っていない。

## 0. 結論（先に）

1. **`ofDecl` の単射性は新前提にならない**。既に定理がある（証明）: `Tools.ShippingModuleName.ofDecl_injective : ofDecl a = ofDecl b → a = b`（Tools/ShippingModuleName.lean:766、`encode`/`decode` の往復で証明）。`ofDecl_ne_ofMem`・`ofDecl_ne_aux` もある。scratch で再利用して公理は `propext, Classical.choice, Quot.sound` のみ（§2.1）。
2. **`htop`**: 小補題（`CircuitM.init` / `finalize` / `addClockResetIfSequential` / `finishSynth` が name と topModule を保つ）は scratch で証明まで通った（§1.2）。ただし `htop` 全体は「最終 state の `module.name` と `design.topModule` が `ofDecl declName` のまま」を要し、その部分は route ごとに状況が違う（§1.3）。**certified / mixed の transition 形と machine には既存の定理がある。legacy（と gate の transition 形でない mixed）には、circuit state を追う不変量の walk が見つからなかった**。既存の `Keeps`/`TripleC` の枠組みは world だけを追い、circuit state は全称で捨てている（§1.3）。
3. **`hno`**: 次の二点が分かった。
   - **証明**: `synthesizeHierarchical` の `design.modules.any (·.name == module.name)` の分岐は、`hno` が成り立つこと **と同値**（`hno_iff_not_any`、§2.2）。`validateDesignNames`（`checkDesign`）は両分岐で通るので、**`synthesizeHierarchical` の成功は `hno` を含意しない**。
   - **読解**: `hno` は「outermost の core run の中に、同じ宣言 `declName` の成功した入れ子 run が無い」ことと同じ。depth 上限（1024）で throw するから循環は成功しない、という論法は、`tryInlineUnfold` の catch / retry（Elab.lean 6358-6376）が入れ子の throw を飲み込めるので、**そのままでは閉じない**（反例は作れていない。§2.3）。
   - **観測**: 直接の自己再帰（`unsafe def`）は depth 上限で throw した（1 例のみ。§2.4）。
4. したがって `hno` の非 machine 分は、(a) 呼び出しグラフが declName に戻らない（acyclic）という **新しい前提**、(b) その前提を FG 側に置く、(c) `NoRawBelow` 系の machine route 用の補題は非 machine route に **流用できない**（§2.5）、のいずれかになる。(a)/(b) は台帳の前提追加で、reviewer の承認とユーザー判断の対象。`htop` の legacy 分は前提ではなく証明作業だが、outermost で memo が miss することに `RefLawsM`（保留）が要る可能性がある（§3）。**ここで止まる**（使わない）。

## 1. `htop`

### 1.1 完全な型

`Tools/ShippingDesignWriterRun.lean:119` の仮説と、その元の run:
```lean
(hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w2)
(htop : D.topModule = raw.name)
```
outermost の core run で言いたい文（これは**まだ定理ではない**。freeze 候補の型）:
```lean
theorem htop_core {declName : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w2 : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hstart : /- outermost: sparkleSynthDepth = 0 の start world（`Start`、E5 が cache/memo を空にする） -/ True)
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w2) :
    raw.name = Sparkle.IR.ModuleName.ofDecl declName ∧
      D.topModule = Sparkle.IR.ModuleName.ofDecl declName
```
（`hstart` の正確な述語名は、Tools の `Start`/`StartW` 系を freeze 時に写す。ここでは「outermost である」ことの印。）これから `htop : D.topModule = raw.name` は連言の二成分の合成で出る。

### 1.2 scratch で証明した小補題（証明）

```lean
theorem init_name_top (s : String) :
    (CircuitM.init s).module.name = s ∧ (CircuitM.init s).design.topModule = s := ⟨rfl, rfl⟩
theorem finalize_name (m : Sparkle.IR.AST.Module) : m.finalize.name = m.name := rfl
theorem addClockReset_name (m : Sparkle.IR.AST.Module) :
    (addClockResetIfSequential m).name = m.name
theorem finishSynth_name_top {declName : Name} {st : CircuitState} {M : Sparkle.IR.AST.Module} {D : Design}
    (h : MReturns (finishSynth declName [] false st) (M, D)) :
    M.name = st.module.name ∧ D.topModule = st.design.topModule
theorem htop_of_finalState {declName : Name} {st : CircuitState} {M : Sparkle.IR.AST.Module} {D : Design}
    (h : MReturns (finishSynth declName [] false st) (M, D))
    (hn : st.module.name = Sparkle.IR.ModuleName.ofDecl declName)
    (ht : st.design.topModule = Sparkle.IR.ModuleName.ofDecl declName) :
    D.topModule = M.name
```
`#print axioms htop_of_finalState`: `[propext, Classical.choice, Quot.sound]`。`finishSynth_name_top` は既存の `finishSynth_returns`（Tools/ShippingEntrySoundness.lean:521）を使う。証明は §6 に全文。これで残るのは `hn` と `ht`、すなわち **`finishSynth` に渡る最終 state の name と topModule**。

### 1.3 route ごとの `hn`/`ht`（最終 state）

| route | `hn`/`ht` の供給元 | 状態 |
|---|---|---|
| certified（`synthesizeCertified`） | `synthesizeCertified_returnsM`（Tools/ShippingFirstGateChild.lean:114）が `bindMixedCertifiedInputs …` の run を `CircuitM.init (ofDecl declName)` から `st` まで返す。`transition_closed`（Tools/ShippingTransitionClosed.lean:35-56）が **transition 形（`PositiveBinders`、`Term` の `quote` 形の body）** に対して `st.design = (CircuitM.init (ofDecl declName)).design ∧ m.name = ofDecl declName` を出す | **transition 形のみ供給あり**（既存定理）。任意の certified body では見つからなかった |
| mixed（`synthesizeMixedCertified`） | 同上（`mixedHarness_runs`、ShippingGateParentRuns.lean:255）。gate cone 形は `DOk G N`（ShippingGateDesignWalk.lean:89 の `name : s.module.name = N`、`desFinal_of_run`）| **gate cone / transition 形のみ**。それ以外の mixed body では見つからなかった |
| machine（closeInsts、`synthesizeMachineCertified`） | `closeMachine … .name = ofDecl declName`（Tools/ShippingCacheCoherentCert.lean:425, 575; Tools/ShippingCacheCoherentData.lean:41）。design 側は `Machine.designWith`/`closeInsts` | machine 側の既存定理（台帳 D.D-7 の guard 付き分）。この調査の対象外 |
| legacy（`openRecordInputs` → `bindInputsLegacy … emitLeaves` → `finishSynth`） | **見つからなかった** | 下記 |

**legacy で見つからなかった理由（読解）**。`CompilerM := ReaderT CompilerState (StateT CircuitState MetaM)`（Elab.lean:94）で、legacy の `emitLeaves`/`translateExprToWire` は `CircuitState` を状態として回す。既存の walk の述語は world だけを追う: `TripleC`（Tools/ShippingChildHarness.lean:37）は `∀ ctx st, Triple … P (c ctx st) …` と **circuit state `st` を全称で捨て**、`Keeps`/`KeepsC`（Tools/ShippingChildInv.lean:315, 601）も `I : Void IO.RealWorld → Prop` だけである。`@[keeps]` 補題は 7 ファイルに 81 本あるが、どれも `module.name` や `design.topModule` を言わない。`module.name` を書き換えうる箇所は Elab.lean を読んだ範囲では `Module.addWire`/`addInput` 等と `{ cs with module := cs.module.addWire p }`（6773）で、**name を触る箇所は見つからなかった**（読解、定理ではない）。定理にするには、circuit state を言う新しい triple（`TripleCS` 相当）で legacy translator の handler 全体を歩き直す必要がある。world 側の同じ範囲の walk は ShippingChildLegacy*/ShippingChildTranslate* で約 1874 行ある。**この調査はその規模の作業の見積もりまでで、実装していない**。

加えて、outermost で memo が **miss** であること（`sparkleSubModuleCache` が空）は、`outer_miss`（Tools/ShippingLegacySemMemoWalk.lean:495）で定理になっているが `RefLawsM` が前提（FB_RESUME_STUDY §3.2）。memo hit だと `return cached` で cached 側の name を使うので、`htop` の legacy 分は hit が起きないことか、cache entry が `ofDecl key` の name を持つ不変量（`Fits` 系、ShippingCacheCoherent*）を要する。**RefLawsM が要る場合はここで止める**。

## 2. `hno`

### 2.1 (i) `ofDecl` の単射性（証明）

`ofDecl n = encode (.decl n)`（Sparkle/IR/ModuleName.lean:259）。`decode (encode k) = some k`（`decode_encode`）から `encode_injective`、そこから
```lean
theorem Tools.ShippingModuleName.ofDecl_injective {a b : Name} (h : ofDecl a = ofDecl b) : a = b
```
（Tools/ShippingModuleName.lean:766）。任意の `Lean.Name`（匿名、数値成分、任意の文字）で成り立つ。scratch で `Tools.ShippingModuleName.ofDecl_injective h` をそのまま使えて、公理は `[propext, Classical.choice, Quot.sound]`。**新前提は要らない**。`ofDecl_ne_ofMem`（`SparkleMem_…` の名前との非衝突）、`ofDecl_ne_aux` も既存。
注: 既存の probe `Tests/Compiler/CacheCoherenceProbe.lean` は `Name.toString` の非単射を扱うが、`ofDecl` は `encode` を経由し `toString` に依らない。

したがって、`D.modules` の module が `ofDecl declName` の名前を持つのは、その module が key `.decl declName` で作られたとき、すなわち **declName 自身の synthesis の結果がどこかに入った**ときに限る（module の名前の出自 `IsMem a ∨ IsTop …` を追う既存の不変量が ShippingCacheCoherentRun/Cert にあるが、非 machine の legacy 分に使えるかは確認していない）。

### 2.2 hierarchical の分岐と `hno` の同値（証明）

`synthesizeHierarchical`（Elab.lean:9124）は `design' := if design.modules.any (·.name == module.name) then design else design.addModule module` の後 `validateDesignNames`（`checkDesign`）を通す。`design` は `synthesizeCombinationalWith` の後処理で、`top f` は `x.name == m.name` の module にだけ `f`（`dropZeroWidthModule`/`mergeChecked`）を当てる。`f` は name を保つ（`dropZeroWidth_name`、`mergeChecked_name`、既存定理）。scratch で証明した:
```lean
theorem hno_iff_not_any {D : Design} {m : Sparkle.IR.AST.Module}
    {f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module} (hf : ∀ x, (f x).name = x.name) :
    (∀ x ∈ D.modules, x.name ≠ m.name) ↔
    ¬ ((D.modules.map fun x => if x.name == m.name then f x else x).any (·.name == m.name) = true)
```
公理 `[propext, Quot.sound]`。つまり **`hno` ⇔ hierarchical が `addModule` 側の分岐に入る**。`hno` が偽のとき `any` は真で、`design' = design`（親の post-processed module `b` は足されず、同名の子 module が親の定義の位置に残る）。このとき `checkDesign` は通りうる（`design.modules` 自体が Nodup なら）ので、**成功した `synthesizeHierarchical` から `hno` は出ない**。`writer_prints_endpoint_artifact` が `hno` を仮説に持つのは正しい（偽だと印字される artifact が `D.modules ++ [checkedOptimize b]` と違う）。

### 2.3 (ii) acyclicity の道筋と、そのままでは閉じない点（読解）

- outermost の core run の入口で cache/memo は空（E5）。入れ子の run が `declName` 自身に戻る（`P → … → P`）ときだけ `hno` が破れる（§2.1）。
- 子の synthesis に入る場所: `handleDefinitionUnfold`（Elab.lean 6568-6603）。`@[hardware_module]` 付きは `try synthesizeCombinational name catch _ => throwError`（**再 throw**。ここで失敗は伝わる）。付いていない定義は `tryInlineUnfold` を先に試し、失敗したら `synthesizeCombinational name`（失敗は再 throw）。machine/gate の route は `synthesizeChild`（`sparkleChildCache` 経由）。
- 循環が成功しない論法: 入れ子 run が再び `P` に入るたびに `sparkleSynthDepth` が増え、1024（Elab.lean:970）で throw（Elab.lean 5465-5466）。throw が最上位まで伝われば循環は成功しない。
- **閉じない点**: `tryInlineUnfold`（6347-6380）は `translateExprToWire eReduced` の失敗を `catch ex1`/`catch ex2` で飲み込み、transparency を変えて retry する。展開した body の中に `@[hardware_module]` の `P` 呼び出しがあり、その入れ子 run が throw しても、retry 側が `P` を呼ばずに成功すれば、その階層の run は成功する。すると深い階層から順に、`P` の run が成功 → その外側の最初の試行は成功した子 `P` を持つ → … と成功が上へ伝わり、outermost の design に `ofDecl P` の module が入る可能性がある。**この機構を満たす宣言は作れていない**（Lean の再帰定義は kernel 値に自己参照を持たない。自己参照が残るのは `unsafe`、smart unfolding、`implemented_by` 等。§2.4 の probe は retry 側を持たない）。したがって「`hno` は偽」とも「depth 上限だけで真」とも言えない。**depth 上限だけでは証明にならない**、が確からしい結論。
- 閉じるために要るもの（候補）: (a) 宣言 `declName` から synthesizeCombinational で到達する宣言の列が `declName` に戻らない、という前提（Lean の kernel 環境の定義順に由来するが、`Environment` は不透明で Lean の中では定理にならない。TRUSTED に近い）、(b) 失敗が catch される箇所の網羅（`tryInlineUnfold` 以外が無いことの確認）と、retry が `P` を再び呼ぶことの排除。どちらも現行の台帳に無い。

### 2.4 (iii) 観測（scratch probe）

- `ModuleNameCheck.check [mk "P", mk "P"] = true`（同じ raw 名の重複を許す、`namesOf … eraseDups`）。`checkDesign {topModule := "P", modules := [mk "P"]} = true`、`modules := [mk "P", mk "P"]` は `false`（Nodup を要求）。観測。study §3.3 の読みの確認。つまり `finishSynth` の `check` は重複を許し、`checkDesign` は `design.modules` 内の重複だけを拒否する。
- 自己再帰の宣言 `@[hardware_module] unsafe def selfP {dom} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := selfP x + x` に `synthesizeCombinational ``selfP` を当てると **`THROW: hardware modules nested deeper than the synthesis depth limit`**（観測、1 例。scratch は §6）。循環が成功しなかった例で、retry 側を持つ宣言は試していない。この観測は `hno` の証拠ではない。
- `Machine.designWith` の skip（`acc.any (·.name == c.name)`）と `handleDefinitionUnfold` の `existing.contains`（6620-6630）は、同名の module を重複して足さないだけで、子の design が親と同名の module を持つことと `hno` の破れは同じ事象である（新しい経路は見つからなかった）。

### 2.5 既存の `NoRawBelow`（74343ad8）の流用可否

`NoRawBelow D rn n mc`（Tools/ShippingGen5DCEntryR.lean:14）は「`mc` から `n` 段下の module の **instance 文**が `rn` を指さない」で、`Machine.closeInsts` の検査 `noInstOfB`（Machine.lean:423）から出る（`noRawBelow_of_closeInsts`/`noRawBelow_of_coreRun`、ShippingGen5DCEntryS/U）。非 machine route には `closeInsts` が無いので、その前件の供給元が無い。また `NoRawBelow` は instance 文の話で、`hno`（`D.modules` の name）とは別の文。**流用できる経路は見つからなかった**。

## 3. 必要な前提（台帳 ID か新前提候補）

- `ofDecl` 単射: 前提不要（既存定理、§2.1）。
- `htop`: certified/mixed の transition 形・machine は既存定理。legacy と任意 body の mixed は**証明作業**（新前提ではない）だが、circuit state を追う新しい triple の導入で大きい。outermost の memo miss は `RefLawsM`（**保留中なので使わず、ここで止める**）か、cache 不変量が要る。
- `hno`（非 machine）: 新前提候補（完全な型）。**使わない・台帳に入れない・承認待ち**:
```lean
-- 候補 A（hno そのもの。outermost の core run の結果についての前提）
(hnoA : ∀ x ∈ D.modules, x.name ≠ Sparkle.IR.ModuleName.ofDecl declName)
-- 候補 B（FG 側の言い方: declName が自分の synthesis の入れ子に現れない。run の木の形式化が既存に無い）
-- NoSelfReentry declName := ¬ ∃ (入れ子の成功 run of synthesizeCombinationalCore declName) ...
```
  A は E-12 の文をそのまま前提にするだけで、実質は前提の追加（FG 行の増加）。B は run の木を言う述語が既存に無く、定義から要る。

## 4. 選択肢（reviewer / ユーザー判断が要る点。ここでは決めない）

1. `hno` の非 machine 分を FG の前提（新しい行）にする（候補 A/B）。影響: FG +1（条件付き）。可逆。判断しない場合: D.E-12 の非 machine 分は未供給のまま、M4 は完了を名乗れない。
2. retry 側が `P` を呼ばないこと等、`tryInlineUnfold` の挙動を run から出す補題を作り、depth 上限と合わせて acyclicity を証明する。影響: 新前提なしだが、translator の catch 全体の walk が要り大きい。reviewer が範囲を決める。
3. `htop` の legacy 分: circuit state を追う walk（約 1874 行規模の見積もり）。`RefLawsM` が要るかは §1.3 の memo miss の扱い次第。

## 5. 台帳への見込み（R0 行単位）

| 行 | 現状 | 見込み | 条件 |
|---|---|---|---|
| D.E-12 非 machine 分（`htop`） | M4 の義務（現在行ではない） | 0（今回）。証明できれば義務の消化で、FG 行の増減は reviewer が決める | §1.3 の walk と memo miss の扱い。`RefLawsM` は使わない |
| D.E-12 非 machine 分（`hno`） | M4 の義務 | 前提として入れるなら **FG +1（条件付き、未受理）**。証明で消すなら 0 | §2.3 の (a)/(b)。行の扱い（現在行にするか義務のままか）は reviewer に問う |
| 新しい仮定 | — | この調査が増やす数 0 | 候補 A/B は承認まで行にしない |

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付き台帳: `hno` を前提にした場合 FG +1（未受理）。

## 6. scratch（elaborate 済みの全文）

```lean
import Tools.ShippingDesignWriterRun
import Tools.ShippingModuleName
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Tools.ShippingEntrySoundness

theorem init_name_top (s : String) :
    (CircuitM.init s).module.name = s ∧ (CircuitM.init s).design.topModule = s := ⟨rfl, rfl⟩

theorem finalize_name (m : Sparkle.IR.AST.Module) : m.finalize.name = m.name := rfl

theorem addClockReset_name (m : Sparkle.IR.AST.Module) :
    (addClockResetIfSequential m).name = m.name := by
  unfold addClockResetIfSequential
  dsimp only
  split
  · split <;> split <;> rfl
  · rfl

theorem finishSynth_name_top {declName : Name} {st : CircuitState}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : MReturns (finishSynth declName [] false st) (M, D)) :
    M.name = st.module.name ∧ D.topModule = st.design.topModule := by
  obtain ⟨hM, hD, -⟩ := finishSynth_returns h
  refine ⟨?_, by rw [hD]⟩
  rw [hM, finalize_name, addClockReset_name]

/-- the reduction: htop follows from the final state's name/top facts. -/
theorem htop_of_finalState {declName : Name} {st : CircuitState}
    {M : Sparkle.IR.AST.Module} {D : Design}
    (h : MReturns (finishSynth declName [] false st) (M, D))
    (hn : st.module.name = Sparkle.IR.ModuleName.ofDecl declName)
    (ht : st.design.topModule = Sparkle.IR.ModuleName.ofDecl declName) :
    D.topModule = M.name := by
  obtain ⟨h1, h2⟩ := finishSynth_name_top h
  rw [h1, h2, hn, ht]

#print axioms htop_of_finalState

/-! ofDecl injectivity (already in the tree) -/
theorem ofDecl_inj' {a b : Name} (h : Sparkle.IR.ModuleName.ofDecl a = Sparkle.IR.ModuleName.ofDecl b) : a = b :=
  Tools.ShippingModuleName.ofDecl_injective h
#print axioms ofDecl_inj'
#print axioms Tools.ShippingModuleName.ofDecl_ne_aux
#check @Tools.ShippingModuleName.ofDecl_ne_ofMem

/-! hno <-> hierarchical's addModule branch -/
theorem hno_iff_not_any {D : Design} {m : Sparkle.IR.AST.Module}
    {f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module}
    (hf : ∀ x, (f x).name = x.name) :
    (∀ x ∈ D.modules, x.name ≠ m.name) ↔
    ¬ ((D.modules.map fun x => if x.name == m.name then f x else x).any (·.name == m.name) = true) := by
  have key : ∀ x : Sparkle.IR.AST.Module, (if x.name == m.name then f x else x).name = x.name := by
    intro x; split
    · exact hf x
    · rfl
  constructor
  · intro h hany
    obtain ⟨y, hy, hyn⟩ := List.any_eq_true.mp hany
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [key] at hyn
    exact h x hx (by simpa using hyn)
  · intro h x hx hxe
    apply h
    refine List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    rw [key]; simpa using hxe

#print axioms hno_iff_not_any

/-! ModuleNameCheck accepts a repeated raw name (probe) -/
def mk (n : String) : Sparkle.IR.AST.Module := Sparkle.IR.AST.Module.empty n
#eval Sparkle.IR.ModuleNameCheck.check [mk "P", mk "P"]
#eval Sparkle.IR.ModuleNameCheck.checkDesign { topModule := "P", modules := [mk "P"] }
#eval Sparkle.IR.ModuleNameCheck.checkDesign { topModule := "P", modules := [mk "P", mk "P"] }
```

自己再帰 probe（観測 1 例）:
```lean
import Sparkle
import Sparkle.Compiler.Elab
open Sparkle.Core.Signal Sparkle.Core.Domain

-- An unsafe self-recursive combinational declaration (kernel does not check unsafe)
@[hardware_module]
unsafe def selfP {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  selfP x + x

open Lean Elab Command Sparkle.Compiler.Elab in
#eval show CommandElabM Unit from do
  let r ← liftTermElabM (do
    try
      let (m, d) ← synthesizeCombinational ``selfP
      pure s!"OK top={m.name} mods={d.modules.map (·.name)}"
    catch e => pure s!"THROW: {← e.toMessageData.toString}")
  logInfo r
```

## 7. 限界

- Lean のソースは編集していない。`kjob lake build Tools.ShippingDesignWriterRun`（420 jobs、exit 0）と scratch の elaborate のみ。clean build ではない。
- §1.3 の legacy の読解、§2.3 の機構は読解で、定理ではない。反例が作れなかったことは成立の証拠ではない。
- `hno`/`htop` を route ごとに全て覆う定理は、この調査では作っていない。
- 行番号は 66d13eef の Elab.lean に対する値。
