# RT 最終定理 freeze: TraceGood の最終定理への条件付き接続（`readerTrace_final`）

Issue `sparkle-gen5-dg-readertrace`（agent rt140、文書のみ）。base: `par/rt-u2-int3` 6699a019（U2 + inline-compose cd0b66ff + pass_ph 16669552 を含む。すべて reviewer 承認済み・exact-head build 済み）。根拠: `par/ledger-replan:scripts/gen2/LEDGER_SHORTEN_PLAN2.md`（rev3.1 3e90ef74）§4 推奨 2・§2.1.1。
**台帳: FG 93 / T1 55（今回 FG -0 +0 / T1 -0 +0）。** この文書は何も登録・除去しない。条件付き台帳 FG 95 / T1 57 は見込みで、最終計上は reviewer / ユーザー判断。
Lean は書いていない。scratch（リポジトリ外）で型を elaborate しただけ。コンパイラ・共有定義・TRUSTED 境界・law・FG 範囲・`GenWF` は変えない。mutant は signature / defeq での棄却であって意味的反例ではない。

## 0. 結論

1. 最終定理 `Tools.ShippingGen5ReaderTraceFinal.readerTrace_final`（新規ファイル `Tools/ShippingGen5ReaderTraceFinal.lean`）の完全な型を §2 に固定する。
2. 部品 `readF_traceGood_of_premises`（U1）、`u2_core'` と同じ構成（`machineShapeF_state_side` / `reach'_of_witness` / `dims_of_dataOfAt` / `kDOf_eq_nDeclOfCi`）、`shapeInputs_of_direct'` / `shapeInputs_of_inline'` から、**scratch で sorry なしに elaborate できた**（§3）。`#print axioms` は `propext, Classical.choice, Quot.sound` のみ。型が合わない部品はなかった。
3. 仮説は計画 §4 推奨 2 の集合に、**既に台帳にある行**（§1 の上 4 グループ）を加えたものになる。新しい台帳前提は増えない（§1）。

## 1. 仮説と台帳 ID

| 仮説（binder） | 型 | 台帳 | 今回の差分 |
|---|---|---|---|
| `hv` | `Tools.Assume.EnvDeclValue.DeclValuePh env` | FG N1-a（U2 の登録。条件付き +1） | 条件付き +1 |
| `hbr` | `Tools.Assume.PackTupleBridge.PackTupleInputsBridge` | FG N2-b（条件付き +1） | 条件付き +1 |
| `hraw` | `Tools.Assume.NormNodePh.RawNodePh (structEnv env)` | FG N3-b（条件付き +1） | 条件付き +1 |
| `hnode` | `Tools.Assume.NormNodePh.NormNodePh (structEnv env)` | FG N3-b（条件付き +1） | 条件付き +1 |
| `hrr` | `Tools.PassPh.RecRulePhU env` | FG `RecRulePhU`（独立の新条件。条件付き +1。数え方は reviewer 判断） | 条件付き +1 |
| `hbt` | `Tools.PassPh.BetaNonTargetAgrees` | T1（条件付き +1） | 条件付き +1 |
| `hEq` | `Tools.Assume.ExprEqvGL.ExprEqvLaws` | T1（条件付き +1。3 条項を 1 行に束ねる案 A） | 条件付き +1 |
| `hh` | `Tools.Assume.AbbrevExtern.HeadBetaAgreesL` | T1L-74 の置き換え（reviewer 承認済み案 i） | ±0 |
| `hfb` | `FuelBridge` | FG C.CV-4（既存の TRUST 行） | 0 |
| `hE` | `Tools.Assume.ExprEqv.EqvAtom` | T1L-72（既存） | 0 |
| `hr` | `Tools.Assume.AbbrevExtern.ReplaceAgrees` | T1L-73（既存） | 0 |
| `hla` | `LiftAgrees` | T1L-50（既存） | 0 |
| `hi1` | `Inst1Agrees` | T1L-51（既存） | 0 |
| `hK` | `EnvTypesFVarFree env` | T1L-53（既存） | 0 |
| `hC` | `Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)` | FG（EnvSigTy で登録済みの行。U2 freeze §1.3 が「FG 登録済み」と記録） | 0 |
| `hD` | `Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env)` | FG（同上） | 0 |

注意点（reviewer 確認）:
* 計画 §4 推奨 2 の仮定集合には `hE hla hi1 hK hC hD hr` が明記されていない。`u2_compose'` の型にこれらが現れるので書き足した。**いずれも既存行で、新しい前提ではない**。FG 側 `hC` / `hD` が 93 に入っているかは、この調査では台帳 §12.x の行番号まで突き合わせていない（U2 freeze §1.3 の記述に依る）。
* `u2_compose'` は `hz : ZeroLitAgrees0`（T1L-54）と `hr : ReplaceAgrees` の両方を取る。最終定理は `hz` を取らず、`zeroLitAgrees0_of_replace hr`（AbbrevS1）で導く。**これで T1L-54 を台帳から除くとは書かない**（T1 の −1 は別判断。この文書では 0 とする）。
* `PassPh` は仮説にない（pass_ph で証明済み）。`ReplaceAgrees` と `ZeroLitAgrees0` の二重計上はない。
* `hd` / `h` / `hEd` / `hci` / `hbranch` は台帳前提ではなく、対象 `E` の仮定（`entryConst` が原構成かインライン後か）。
* 台帳の合計（plan §2.1.1 の表と一致）: FG +5（U2 の 4 + `RecRulePhU`）−3（C.RT-2 / C.CV-2 / C.CV-3 は U2 freeze の条件付き除去。**この定理だけでは除去しない**）= 条件付き +2 → 95。T1 +2 → 57。受入済みは FG 93 / T1 55 のまま。感度（RT-2 が `ShapeInputs'` で尽きるか、`RecRulePhU` の数え方、`ExprEqvLaws` の束ね方）は plan §2.1.1 と同じで、reviewer 判断。

## 2. 最終定理の完全な型（凍結）

新規ファイル `Tools/ShippingGen5ReaderTraceFinal.lean`（`import Tools.ShippingGen5ReaderTraceU2Compose` と `Tools.ShippingGen5ReaderTraceAbbrevS1`）。名前空間 `Tools.ShippingGen5ReaderTraceFinal`、`set_option autoImplicit false`。open は
`Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel Tools.ShippingGen5Cover3 Tools.ShippingGen5GDCover1 Tools.ShippingGen5Cover3Canon Tools.ShippingMachineAuto Tools.ShippingGen5Sem Tools.ShippingGen5ReaderTraceU2 Tools.ShippingGen5Cover6`。

```lean
theorem readerTrace_final
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hfb : FuelBridge)
    {ci0 E : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    (∀ n : Nat, TraceGood (structEnv env) (nDeclOfCi E) (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) ({} : MachRead) st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧
      ShapeAgree d st ∧ FullInv (kDOf d) st ∧ LetsNoLoose st
```

結論の読み方（Issue の完了条件との対応）:
* 第 1 連言: `TraceGood nDecl (readF senv n)`（`nDecl = nDeclOfCi E`、全 fuel `n`）。`TraceGood` は `TracePost` を含み、そこに「readF の各 call の入力状態から出力状態へ `FReachC`」が入る。
* 第 2 連言の `FReachC` 3 本と `TrInv`: U-E3b `machineShapeF_reach'` の到達部分（`reach'_of_witness` 経由）。
* `FullInv (kDOf d) st` / `LetsNoLoose st`: R-in / R-nl（consumer `rowC_of_reader_canon` の入力）。`ShapeAgree d st`: R-dom 側の `d` との一致。
* `StateSideWitness`: 状態が `machineShapeF` の実行そのもの（`stateSide_functional` で一意）。

## 3. scratch での elaborate 結果

scratch ファイル（リポジトリ外、`scratchpad/Final.lean`）で、上の型の定理を次の証明で `kjob lake env lean` により elaborate した。exit 0、`sorry` / `axiom` / `native_decide` なし、`#print axioms` は標準 3 つのみ。証明の骨子（実装でもこの形を使う）:
1. `hz := zeroLitAgrees0_of_replace hr`。
2. `hIn : ∀ n, ShapeInputs' (nDeclOfCi E) (structEnv env) false [] E n`: `hbranch` で場合分けし、直接枝は `shapeInputs_of_direct' hz hla hi1 env hv hci hbr hraw hnode`、インライン枝は `hci` から `⟨c, hc⟩` を取り `shapeInputs_of_inline' hz hla hi1 env hv hrr hr hh hbt hEq hc rfl hbr hraw hnode`。
3. `hT := readF_traceGood_of_premises env hK hC hla (rootFloatAgrees hla) hi1 hD (nDeclOfCi E)`。
4. `hfb` から `n`、`machineShapeF_state_side` から witness `w`、`reach'_of_witness hE (hT n) hn (hIn n) w` から `R0 R1 R2 Tr`、`dims_of_dataOfAt` と `kDOf_eq_nDeclOfCi`（`hEd` を subst）で `ShapeAgree` / `FullInv`、`Tr.2.2.2.2.2.1` で `LetsNoLoose`。

型が合わなかった部品: なし。ただし scratch は `kjob lake env lean` の 1 ファイル elaborate で、`lake build` 全体や clean build ではない。

## 4. 実装の単位（freeze 承認後）

1. `Tools/ShippingGen5ReaderTraceFinal.lean` に §2 の定理を §3 の証明で置く（既存ファイルは編集しない）。lakefile.lean に `lean_lib` を 1 つ追加（`Tests/Gen5/ReaderTraceFinalCheck.lean` 用にも 1 つ）。
2. 実装コミットを出したら、coder が clean issue-linked build を実行してから review にする（この job では実装しない）。

## 5. 後続の Check の計画（`Tests/Gen5/ReaderTraceFinalCheck.lean`、U2Check と同じ形）

* **BINDERS**: `readerTrace_final` の binder を**完全修飾名**で照合する。§1 の表の 16 仮説の型が、独立に書いた expected type と一致すること（binder の名前・順序・型）。仮定の集合が表と過不足なく一致し、`PassPh` と `ZeroLitAgrees0` が現れないこと、`sorryAx` を含む仮説がないこと。
* **TYPE**: 結論の型を独立に書いた expected type と `isDefEq`（reducible でない通常の defeq）で照合する。条件 def の展開による受理は、その旨を Check の出力に書く。
* **CLOSURE**: 定理の閉包に `sorryAx` / 禁止定数（`Lean.ofReduceBool`、`native_decide` 由来、新 `axiom`）がないこと。負の対照（禁止定数を含む定理を拒否できること）を付ける。
* **AXIOMS**: 標準 3 つ（`propext, Classical.choice, Quot.sound`）のみ。
* **MUTANT**: 仮説を 1 つ落とした型、結論の連言を 1 つ落とした型、`nDeclOfCi E` を別の `nDecl` にした型が expected type と**不一致**になること。**signature / defeq での棄却であって、意味的反例ではない**。
* **POSITIVE**: 仮説を `sorry` でなく variable として受ける形で、`u2_compose'` / `readF_traceGood_of_premises` から型が組めること（定理自体の elaborate）。
* build は `kjob lake build Tools.ShippingGen5ReaderTraceFinal Tests.Gen5.ReaderTraceFinalCheck` を 1 つずつ。

## 6. 台帳の扱い

* 受入済み: **FG 93 / T1 55 のまま**。この定理を build しても、仮定は登録されず、行は消えない。
* 条件付き: **FG 95 / T1 57**（§1 の合計）。最終計上（受理するか）は reviewer / ユーザー判断。計上しない場合の扱い（条件付きのまま残す／置き換える証明を探す）も同じ判断。
* この接続自体は行を消さない。C.CV-5 / C.RK-8 など、接続で消える行は、この調査では供給元・経路が見つからなかったので見込みに入れない。
* 新しい TRUSTED / law / compiler 境界の文はない。仮説は定理の仮説のまま。

## 7. 止める条件

* 実装中に、新しい台帳前提が必要とわかったとき（reviewer の番、停止して coder に報告）。
* Check の BINDERS が §1 の表と合わないとき。

## 付録: elaborate した scratch の全文

```lean
import Tools.ShippingGen5ReaderTraceU2Compose
import Tools.ShippingGen5ReaderTraceAbbrevS1
set_option autoImplicit false
namespace Tools.ShippingGen5ReaderTraceFinal
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel
open Tools.ShippingGen5Cover3 Tools.ShippingGen5GDCover1 Tools.ShippingGen5Cover3Canon Tools.ShippingMachineAuto Tools.ShippingGen5Sem
open Tools.ShippingGen5ReaderTraceU2 Tools.ShippingGen5Cover6

theorem readerTrace_final
    (hE : Tools.Assume.ExprEqv.EqvAtom) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (hr : Tools.Assume.AbbrevExtern.ReplaceAgrees) (hh : Tools.Assume.AbbrevExtern.HeadBetaAgreesL)
    (hbt : Tools.PassPh.BetaNonTargetAgrees) (hEq : Tools.Assume.ExprEqvGL.ExprEqvLaws)
    (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hD : Tools.Assume.EnvInstS.InstSFieldsDet (structEnv env))
    (hv : Tools.Assume.EnvDeclValue.DeclValuePh env) (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env)) (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    (hrr : Tools.PassPh.RecRulePhU env)
    (hfb : FuelBridge)
    {ci0 E : ConstantInfo} (hci : Tools.ShippingGen5ReaderTrace.CiDirect env ci0)
    (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E (structEnv env) sp = some d) :
    (∀ n : Nat, TraceGood (structEnv env) (nDeclOfCi E) (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) ({} : MachRead) st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧
      ShapeAgree d st ∧ FullInv (kDOf d) st ∧ LetsNoLoose st := by
  have hz := Tools.ShippingGen5ReaderTraceAbbrevS1.zeroLitAgrees0_of_replace hr
  have hIn : ∀ n : Nat, ShapeInputs' (nDeclOfCi E) (structEnv env) false [] E n := by
    rcases hbranch with rfl | rfl
    · exact fun n => shapeInputs_of_direct' hz hla hi1 env hv hci hbr hraw hnode
    · obtain ⟨c, hc⟩ := hci
      exact fun n => Tools.ShippingGen5ReaderTrace.shapeInputs_of_inline' hz hla hi1 env hv hrr hr hh hbt hEq hc rfl hbr hraw hnode
  have hT := readF_traceGood_of_premises env hK hC hla (Tools.PartialTotal.Agree.rootFloatAgrees hla) hi1 hD (nDeclOfCi E)
  refine ⟨hT, ?_⟩
  obtain ⟨n, hn⟩ := hfb E (structEnv env) sp h
  obtain ⟨p, en, st0, env1, st1, st, v, w⟩ := Tools.ShippingGen5Cover5.machineShapeF_state_side hn
  obtain ⟨R0, R1, R2, Tr, -⟩ := reach'_of_witness hE (hT n) hn (hIn n) w
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11⟩ := w
  obtain ⟨hsp, hss', hls, hn'⟩ := dims_of_dataOfAt hd
  have hkd' : kDOf d = nDeclOfCi E := by
    subst hEd
    exact kDOf_eq_nDeclOfCi lvl hd
  refine ⟨n, p, en, st0, env1, st1, st, v, ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11⟩, R0, R1, R2, Tr,
    Tools.ShippingGen5Cover5.shapeAgree_of_sides ⟨hw8, hw9, hw10, hw11⟩ hsp hss' hls hn', ?_, Tr.2.2.2.2.2.1⟩
  rw [hkd']
  exact Tr.1

#print axioms readerTrace_final
end Tools.ShippingGen5ReaderTraceFinal
```
