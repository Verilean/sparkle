# DG-READERTRACE freeze rev16 — N1-a `DeclValuePh` / N2-b `PackTupleInputsBridge` / N3-b `RawNodePh`・`NormNodePh` の完全型と重複照合（文書のみ、review に出す）

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt20` be72e9ca（U-R12c 179cbe7a、rev15 883153e9）。reviewer は rev15 を承認し、N1-a / N2-b / N3-b / N4-a を採用の**方向**として選び、`DomAtomic` は D-b 調査を先行とした（`DG_DOMATOMIC_SURVEY.md`、別 md）。この rev16 はその方向に沿った**完全型 freeze**で、台帳への実際の追加は**この文書が承認されたとき**に別コミットで登録する。
**この rev16 は文書だけ。Lean は書かない。** 用語: 「見つからなかった」は「この調査で辿った経路では見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant は signature / defeq での棄却であって意味的反例ではない。条件付きの結果は中間結果。

**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。** この文書は台帳を 1 行も変えない。§7 の増減は、承認後に登録した時点の**見込み**で、数えていない。

review に出す理由（共通ルール 14）: 台帳前提の追加（N1・N2・N3）を提案するため。

## 0. 読んだもの

`DG_READERTRACE_FREEZE_REV15.md`（全文）、`git show par/fg-ledger-sync:scripts/gen2/PREMISE_LEDGER.md`（44889946、§8.2 の行 C.CV-* / C.RT-*、§12、§12.1）、`git show par/t1-ledger-sync:scripts/gen3/PREMISE_LEDGER.md`（5e915142、§3 の T1L-30〜59、§12）、`Tools/Assume/{N3Extern,EnvSigTy,EnvInstS}.lean`、`Tools/ShippingLetsSigTy.lean`（`EnvTypesFVarFree`）、`Tools/ShippingLetsExternSpec.lean`（`LiftAgrees` / `Inst1Agrees` / `RootFloatAgrees`）、`Tools/ShippingGen5ReaderTrace{Let,Inst1,Dispatch,Shape,ShapeIn}.lean`、`Sparkle/Compiler/{MachTupleIn,MachRawSurface}.lean`、`Sparkle/Compiler/Elab.lean`（`machineShape?` 5072〜、`machNormNode` 4927）、`Tools/ShippingReaderFuelDefs.lean`（`normStep` / `machNormF`）、`Tools/ShippingReaderFuelShape.lean`（`shapePre`）、`Tools/Prototype/{NormRangeLetOk,RawNodeRangeLetOk}.lean`、`git show 7b12301e:scripts/gen3/PARTIAL_SURVEY_A.md`。`sparkle-gen5-dg-env` の Issue 本文（`managerctl show`）。DG-ENV の freeze 文書そのものは、この worktree の `scripts/gen5/` に無かったため**読んでいない**（C0 の定義は FG 台帳 C.EN-6 の行と `EnvSigTy.lean` / `EnvInstS.lean` のヘッダで代用した）。

## 1. 行 ID / 型の同期（現行台帳との照合）

現行値の出典: FG 103 = `par/fg-ledger-sync` 44889946 §12.1、T1 54 = `par/t1-ledger-sync` 5e915142 §12（どちらも `git rev-parse` で SHA を確認した）。rev15 §0 が「再照合していない」とした点を、読める範囲で照合した結果:

| 名前 | 現行台帳での扱い（読んだ箇所） | この base の Lean | rev15 から変わる点 |
|---|---|---|---|
| `LiftAgrees` | T1L-50。T1 §12「Not changed」 | `LetsExternSpec:115`: `∀ e, LetOk 0 e = true → e.liftLooseBVars 0 1 = liftSpec e 0 1 ∧ e.liftLooseBVars 1 1 = liftSpec e 1 1` | なし。**(1,1) はこの行が持つ**（`LiftAgrees0` は start=0 のみ） |
| `Inst1Agrees` | T1L-51。「Not changed」 | `LetsExternSpec:121`: `∀ b a, b.instantiate1 a = inst1Spec b a 0` | なし |
| `RootFloatAgrees` | T1L-52。T1 §12 で**削除済み**（partial-total、965fe51b、`par/ptot-m4`）。**この base には入っていない** | `LetsExternSpec:237` が仮定のまま。`shapeMid_ph` / `machineShapeF_reach_of_premises` が引数に取る | 台帳の T1 54 は既に除いた値。この base ではまだ仮説。ptot-m4 の統合後に仮説は定理になる（この rev16 の範囲外、新しい行は出ない） |
| `EnvTypesFVarFree` | T1L-53。「Not changed」 | `LetsSigTy:63`: `∀ n ci, env.find? n = some ci → NoFv ci.type = true` | なし |
| `ZeroLitAgrees0` | **T1L-54 は `ZeroLitAgrees` から `ZeroLitAgrees0` へ置換（net 0、ad5f7704）**。T1 §12 の表 | `Assume/N3Extern.lean`（ヘッダ表も T1L-54） | rev15 §3.4 の「どちらの文か未照合」は、**§12 の記録で `ZeroLitAgrees0` と読める**。ただし §3 の表の本文は旧文のまま（§12 は表を書き換えない方針） |
| `LiftAgrees0` / `LowerAgreesEq` | T1L-55 / T1L-56 を置換（net 0、同上） | `Assume/N3Extern.lean` | なし |
| `BetaRange` | T1L-57。「Not changed」。型は `LetOk 0 f → LetOk 0 a → LetOk 0 (f.beta #[a])` | `Prototype/RawNodeRangeLetOk:53` | なし。`LetOk` の文で、`NoPh ∧ BvarLt` は含まない（§4.4） |
| `LiftScalarCorr` / `BoolMapCorr` | T1L-58 / T1L-59。T1 §12 で**削除済み**（ptot-m4）。この base には入っていない | `Prototype/LiftScalarModelLetOk:350` / `BoolMapModelLetOk:100` | N3-c の前提（rev15 §3.3）。この rev16 では使わない |
| `hkD`（T1L-30） | `mixedGatePeel (packTupleInputs dP.value) = some (bs, e) → p.kD = bs.length` | — | N2 の本番 `packTupleInputs` を含むが、範囲の保存ではない（§3.4） |
| `OSH`（T1L-43）= C.CV-4 `ShapeFuelBridge` | FG は `h_C_CV4` として型付き（TY-O）、T1 と共有 | — | `machineShape?` と `machineShapeF n` の一致。`packTupleInputs` の twin は含まない（§3.4） |
| `SigTyClosed` / `InstSFieldsDet` | FG §12.1 で各 +1。**行 ID は割り当てられていない**（名前だけ）。「DG-ENV と同じ置き場所、一度だけ数える」 | `Assume/EnvSigTy.lean` / `Assume/EnvInstS.lean` | なし |
| C.RT-1〜4 / C.CV-2/3 | FG §8.2: C.RT-2 = `hpre : TracePre …`（担当欄 REV7: `ShapeInputs`）、C.CV-2 = `LetsNoLoose st`、C.CV-3 = `FullInv`/`FReachC` | — | §7: **この rev16 では 1 行も減算しない** |

**新しい行の ID は割り当てない。** FG 台帳は §8.2 の表形式で、`SigTyClosed` の前例（名前だけを §12.1 に足し、ID を付けなかった）に倣い、登録時に reviewer が付番する。本文中の「N1」「N2」…は**この文書内の呼び名**で、台帳の行 ID ではない。

## 2. N1-a `DeclValuePh`（宣言の値の範囲）

### 2.1 完全型

```lean
-- 新規ファイル Tools/Assume/EnvDeclValue.lean（Assume/ 流儀: 文だけ、定理なし）
namespace Tools.Assume.EnvDeclValue
open Lean Tools.ShippingGen5ReaderTrace

/-- Every definition of `env` has a value with no placeholder fvar and no loose bound variable. -/
def DeclValuePh (env : Lean.Environment) : Prop :=
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal),
    env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true

end Tools.Assume.EnvDeclValue
```

* domain: `env` の全 `defnInfo`。`NoPh`（`ShippingGen5ReaderTrace.lean:22`）は 4 つの placeholder タグ（`_machIn` / `_machInst` / `_machSlot` / `_machLet`）の fvar の不在、`BvarLt 0`（同 :33）は loose bvar の不在（閉じている）。
* `NoFv`（任意の fvar の不在、`EnvTypesFVarFree` が使う）の形にはしない。`NoPh` は `NoFv` より弱い文で、必要なのは `NoPh` だけだから（弱い仮定を優先）。
* 根拠（読んだ範囲）: Lean の kernel は fvar・loose bvar を含む宣言を受理しない（`EnvTypesFVarFree` のコメントと同じ種類の事実）。`Environment` はこの開発でモデル化されていない。**この調査では、値についてのこの文の供給元・経路は見つからなかった。**

### 2.2 使い方（`ci` と `env` のつなぎ）

`ShapeInputs` は `ci : ConstantInfo` を**自由変数**として取り、`env` との関係を持たない（`Shape.lean:33`、`machineShapeF_reach` は `ci` と `structEnv env` をつなぐ仮説を持たない）。`DeclValuePh env` から `hdecl`（`ci = .defnInfo d → NoPh d.value ∧ BvarLt 0 d.value`）を作るには、**`ci` が `env` の定数であること `hmem : ∃ c, env.find? c = some ci`** が要る。この `hmem` は**台帳の行にしない入力の仮説**として `shapeInputs_of` の引数にする（`ShapeInputs` と同じ扱い）。`hmem` の供給元（`machineShape? env … (← getConstInfo declName)` の `ci` が `env.find?` の結果であること）は、本番の呼び出し側（`Elab.lean`）の読みでは `getConstInfo` が `env` から引くので成り立つ見込みだが、**このリポジトリの定理としては繋がっていない**（この調査では経路が見つからなかった）。§8 に残りとして書く。

### 2.3 重複照合

| 既存の条件 | 文 | N1 との関係 |
|---|---|---|
| `EnvTypesFVarFree env`（T1L-53） | 全定数の**型**に fvar なし（`NoFv ci.type`） | 対象が違う（型 vs 値）。`BvarLt 0`（閉じている）も含まない。値は型から出ない。**重複しない** |
| `SigTyClosed senv`（FG §12.1、EnvSigTy） | `senv.instS` の**型** `ty` に loose bvar なし | 対象が違う（`instS` 表の型 vs `defnInfo.value`）。`BvarLt 0` の形は同じ種類だが別の対象。**重複しない** |
| `InstSFieldsDet senv`（FG §12.1、EnvInstS） | 同じ `instS` 署名の args 間で field 数一致 | 無関係 |
| DG-ENV の C0（C.EN-6 `hall`） | 全 world の `ReadsAt`、環境が run 間で同一 | N1 は**単一の `env` についての静的な文**。C0 の「同一の `env₀`」を使えば、N1 は `env₀` についての 1 本で足りる（`EnvSigTy` / `EnvInstS` と同じ置き場所の候補）。C0 そのものとは別の文 |
| C.RK-8 / C.DO-1〜3 | reader 完全性、`dataOfAt = some d` | 無関係 |

結論: **既存の名前付き条件や行に含まれない新規の文**（reviewer 結論 (b)）。DG-ENV の環境条件の族（`EnvTypesFVarFree` / `SigTyClosed` / `InstSFieldsDet`）の隣に置き、DG-ENV の Issue が再開したときに同じ置き場所で一度だけ数える。この rev16 では DG-ENV の Issue を変えない。

可逆性: 台帳の行の追加は可逆（削除すれば元に戻る）。登録前なら何も変わらない。

## 3. N2-b `PackTupleInputsBridge`（燃料 twin と、本番との一致条件）

### 3.1 完全型

```lean
-- 新規ファイル Tools/ShippingGen5ReaderTracePack.lean（twin と証明。Assume/ ではない）
namespace Tools.ShippingGen5ReaderTracePack
open Lean Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTrace

/-- 先頭の `lam` の個数（燃料）。 -/
def lamDepth : Lean.Expr → Nat
  | .lam _ _ b _ => lamDepth b + 1
  | _ => 0

/-- `packTupleInputs`（`MachTupleIn.lean:79`）の本体と同じ 2 腕を燃料 `k` で回す全域 twin。
`liftLooseBVars` / `instantiate1` は本番と同じ extern を呼ぶ（spec には置き換えない）。 -/
def packTupleInputsF : Nat → Lean.Expr → Lean.Expr
  | k + 1, .lam nm ty b bi =>
    match tupleInput? ty with
    | some (dom, ws) =>
      let n := ws.foldl (· + ·) 0
      let ty' := mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (mkApp (.const ``BitVec []) (natE n))
      let b' := (b.liftLooseBVars 1 1).instantiate1 (unpackE (dom.liftLooseBVars 0 1) ws (.bvar 0))
      .lam nm ty' (packTupleInputsF k b') bi
    | none => .lam nm ty (packTupleInputsF k b) bi
  | _, e => e
```

```lean
-- 新規ファイル Tools/Assume/PackTupleBridge.lean（文だけ）
/-- **本番 = twin の一致。domain は `shapePre` に渡る宣言値の範囲（N1 の下で `NoPh e ∧ BvarLt 0 e`）に限る。** -/
def PackTupleInputsBridge : Prop :=
  ∀ e : Lean.Expr, NoPh e = true → BvarLt 0 e = true →
    Sparkle.Compiler.MachTupleIn.packTupleInputs e = Tools.ShippingGen5ReaderTracePack.packTupleInputsF (Tools.ShippingGen5ReaderTracePack.lamDepth e) e
```

* reviewer 指摘への対応: `∀ e` ではなく `NoPh e ∧ BvarLt 0 e` に限る。`shapePre` の唯一の呼び出しは `packTupleInputs d.value` で、N1 の下で `d.value` がこの domain に入る。
* 本体の再帰は `lam` の下で `L + 1` の式に対して呼ばれるが、**一致の文はトップレベルの 1 回だけ**（再帰の中の式についての別の仮定はない）。
* `packTupleInputs` は `partial def` で、論理の中に本体が無い（等式補題が無い）。したがって一致は証明できず、名前付き条件にする。`Tools/` にも各 branch にも、この関数のモデル（spec）は**見つからなかった**（調査 A 7b12301e）。
* 一致が成り立つ根拠の読み（**証明ではない**）: 燃料 `lamDepth e` が過不足ないのは、`b'` の先頭 `lam` の個数が `b` と等しいこと（`lift` / `instantiate1` が `lam` を保つ）による。調査 A はこの twin と本番の一致を 5000 件のランダム宣言（3346 件が実際に書き換わる）で**検査**した（検査であって証明ではない）。

### 3.2 twin の範囲保存（新しい前提なし、証明）

```lean
theorem packTupleInputsF_ph (hla : LiftAgrees) (hi1 : Inst1Agrees) :
    ∀ (k L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
      NoPh (packTupleInputsF k e) = true ∧ BvarLt L (packTupleInputsF k e) = true
```

証明の計画: `k` についての帰納。`lam` 腕で `b : L+1`。`b.liftLooseBVars 1 1`: `lift11_ph hla`（既存、`Let.lean:23`）で `L+2`。`dom.liftLooseBVars 0 1`: `lift01_ph hla`（既存）で `L+1`。`unpackE … (.bvar 0)` は `dom'`・`bvar 0`（`0 < L+1`）・閉じた構築子（`natE`、`BitVec`、`Signal.map` 等の `const` と `lam (bvar 0)`）だけで作られるので `NoPh ∧ BvarLt (L+1)`。`instantiate1`: `inst1Ph_of_agrees hi1`（既存、`Inst1.lean:94`）を `m = m' = L+1` で。結果は `L+1` で、再帰呼びの入力。`ty'` は `dom`（`tupleInput?` が `ty` の部分式として返す）と閉じた構築子。`unpackE` / `tupleInput?` の補題（`NoPh ∧ BvarLt` の閉包）は**新規の構造補題**。使う仮定は `LiftAgrees`（T1L-50）と `Inst1Agrees`（T1L-51）で、**どちらも既存の行**。`LiftAgrees0` では足りない（(1,1) の lift が要る）ので、`LiftAgrees` を使い続ける。**台帳の行は増えない。**

### 3.3 `shapePre` での使い方

`DeclValuePh` + `hmem`（§2）で `NoPh d.value ∧ BvarLt 0 d.value`。`PackTupleInputsBridge` で `packTupleInputs d.value = packTupleInputsF (lamDepth d.value) d.value`。`packTupleInputsF_ph` で `NoPh ∧ BvarLt 0`。これを `mixedGatePeel_ph`（U-R12c、既存）に渡して `NoPh p.e ∧ BvarLt p.bs.length p.e`。rev15 §1 の `hpack : ∀ L e, NoPh e → BvarLt L e → …`（全 `e`・全 `L`）は、**この 1 インスタンス（`L = 0`、`e = d.value`）に置き換わる**（reviewer 指摘の「広すぎ」を解消）。

### 3.4 重複照合

| 既存の条件 | 文 | N2 との関係 |
|---|---|---|
| C.CV-4 `ShapeFuelBridge` / T1L-43 `OSH` | `machineShape?` と `machineShapeF n` の一致 | `machineShapeF` の中の `shapePre` は**本番の `packTupleInputs` を直接呼ぶ**（`ShippingReaderFuelShape.lean:111`）。C.CV-4 は shape 全体の一致で、`packTupleInputs` の twin を含まない（読んだ範囲）。N2 の文は `packTupleInputs` 単体の twin との一致で、**別の文** |
| T1L-30 `hkD` | `mixedGatePeel (packTupleInputs dP.value) = some (bs, e) → p.kD = bs.length` | `packTupleInputs` を使うが、`kD` と `bs.length` の等式。範囲の保存も twin との一致も含まない。**重複しない** |
| T1L-50 `LiftAgrees` / T1L-51 `Inst1Agrees` | extern `liftLooseBVars` / `instantiate1` の spec 一致 | twin の範囲保存の**前提として使う**（新しい行にならない）。bridge 自体は含まない |
| T1L-55 `LiftAgrees0` | `liftLooseBVars` の start=0 の一致 | (1,1) を含まないので足りない |
| 調査 A（`PARTIAL_SURVEY_A.md`）の「モデルとの一致定理」 | `packTupleInputsS`（spec 版）への一致の提案 | **台帳には入っていない**（調査のみ、実装なし）。N2-b の bridge は spec 版ではなく、extern を呼ぶ twin との一致なので、`LiftAgrees(1,1)` の拡張を要さない |
| DG-ENV | 環境の同一性 | 無関係（共有しない） |

結論: **既存の条件に含まれない新規の文**（reviewer 結論 (b)）。N2-c（コンパイラの `packTupleInputs` を全域化して一致を定義にする）は**ユーザー判断が要る**ので採らない（共通ルール 5）。

可逆性: 行の追加は可逆。N2-c が将来選ばれたら、この bridge は定義そのものになり消える。

## 4. N3-b `RawNodePh` / `NormNodePh`

### 4.1 `machNormF` の呼び出し側の事実（読んだ範囲）

`normStep`（`ShippingReaderFuelDefs.lean:655`〜）の `.app f a` 腕:
* `ashrView?` が一致して `canonicalNatLitValue? nE = some n`、`n ≠ 0` のとき: `x'`・`y'` を再帰で正規化して `ashrE inlNatLit (machSigBin …) dom n x' y'`。
* それ以外で `rawNode senv.prodMatch e = some e'`（`e = .app f a`）のとき: `FM.call e'`（再帰）。
* それ以外: `f`・`a` を再帰で正規化して `FM.pure (machNormNode senv (.app f' a'))`。

`machNormNode` の入力は常に `.app f' a'` で、`f'`・`a'` は正規化後の式（再帰の結果）。`rawNode` の入力は常に `.app f a`（元の式）。これが下の型の domain の根拠。

### 4.2 完全型

```lean
-- 新規ファイル Tools/Assume/NormNodePh.lean（文だけ）
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5ReaderTrace

/-- `rawNode` が `.app f a` に返す書き換え結果の範囲。 -/
def RawNodePh (senv : StructEnv) : Prop :=
  ∀ (L : Nat) (f a e' : Lean.Expr),
    NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch (.app f a) = some e' →
    NoPh e' = true ∧ BvarLt L e' = true

/-- `machNormNode` が `.app f a` に返す式の範囲。 -/
def NormNodePh (senv : StructEnv) : Prop :=
  ∀ (L : Nat) (f a : Lean.Expr),
    NoPh f = true → NoPh a = true → BvarLt L f = true → BvarLt L a = true →
    NoPh (machNormNode senv (.app f a)) = true ∧ BvarLt L (machNormNode senv (.app f a)) = true
```

* domain: 全 `L`（束縛変数の上限は全称）、`f` と `a` が `NoPh ∧ BvarLt L`。`.app f a` 以外の `e` は含めない（呼び出し側が `.app` だけ）。
* 構造部分の補題（**新しい前提なし**、証明）:

```lean
theorem machNormF_ph (hi1 : Inst1Agrees) (senv : StructEnv) (hraw : RawNodePh senv) (hnode : NormNodePh senv) :
    ∀ (n L : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true →
      machNormF n senv e = some en → NoPh en = true ∧ BvarLt L en = true
```

`n` についての帰納（`fuel` の展開、`Prototype/NormRangeLetOk` に `LetOk` 版の先例）。腕ごとの根拠:

| 腕 | 覆うもの | 使う仮定 |
|---|---|---|
| `ashr`（`n = 0`） | `e` 自身 | 自明 |
| `ashr`（`n ≠ 0`） | `ashrE inlNatLit (machSigBin …) dom n x' y'` は閉じた構築子 + `dom` + `x'` + `y'`（IH で `L`） | 構造補題（`ashrE` / `machSigBin` の範囲、`LetOk` 版 `machSigBin_ok` に先例、**Ph 版は新規**）。前提なし |
| `rawNode … = some e'` | `RawNodePh` | **`hraw`**（新規の名前付き条件） |
| `machNormNode (.app f' a')` | `NormNodePh` | **`hnode`**（新規の名前付き条件）。`f'`・`a'` は IH |
| `lam` | 再帰のみ（`t` は不変） | 構造 |
| `letE`（`Nat` 型 / 幅つき `!hasLooseBVars`） | `b.instantiate1 v`（`b : L+1`、`v : L`） | `inst1Ph_of_agrees hi1`（`m = m' = L`）= **既存の T1L-51** |
| `letE`（保持）・その他 | 再帰のみ / `FM.pure e` | 構造 |

### 4.3 重複照合

| 既存の条件 | 文 | RawNodePh / NormNodePh との関係 |
|---|---|---|
| T1L-55 `LiftAgrees0` / T1L-56 `LowerAgreesEq` | `liftLooseBVars 0 d`（start=0）/ `lowerLooseBVars i i` の spec 一致 | `rawNode` が使う extern の一部（`liftLooseBVars 0 n`、`lowerLooseBVars`）の**一致**。範囲の文ではない。`liftSpec_noPh` / `liftSpec_bvarLt` と合わせれば lift 部分の範囲は出る見込みだが、`rawNode` の全体には足りない（下） |
| T1L-57 `BetaRange` | `LetOk 0 f → LetOk 0 a → LetOk 0 (f.beta #[a])` | `rawNode` が `Expr.beta`（`partial def betaRev`）を使う。`BetaRange` は **`LetOk`（`_machLet` の不在）だけ**で、`BvarLt` を含まない。`NoPh` は `LetOk` より強いので `BetaRange` から出ない。**`beta` の `BvarLt` 範囲の供給元は見つからなかった** |
| 旧 `RawNodeRange` / `NormNodeRange`（`Prototype/NormRangeLetOk`） | `LetOk 0 e → LetOk 0 (rawNode …)` / `LetOk 0 (machNormNode …)` | **台帳の行ではない**（T1 §3 の表で T1L-55〜57 に置き換えられた「replaces」欄）。`LetOk` の文で別の性質 |
| T1L-58 `LiftScalarCorr` / T1L-59 `BoolMapCorr` | 本番 `machLiftScalarN` / `machBoolMap` とモデルの一致 | T1 §12 で**削除済み**（ptot-m4）。この base ではまだ partial で、**`NormNodePh` を導く道に使えない**（統合後は N3-c の経路、rev15 §3.3） |
| C.CV-4 / T1L-43 | `machineShape?` と `machineShapeF` の一致 | `machNormF` は twin 側の関数で、N3 は twin の出力の範囲。本番との一致は C.CV-4 の側。**別の文** |
| `SigTyClosed` / `InstSFieldsDet`（DG-ENV 隣接） | `senv.instS` の型 / field 数 | `NormNodePh` が使う `senv.proj / inst / instS` の性質に**隣接するが、文は別**。`senv` は固定された `StructEnv` で、環境の同一性ではなく reader の振る舞い。DG-ENV と共有しない |

結論: `RawNodePh` と `NormNodePh` は**既存の条件に含まれない新規の文**（reviewer 結論 (b)）。`rawNode` 内の `beta` に当たる部分は、既存の `BetaRange` が `LetOk` だけなので、`BvarLt` を足した文として `RawNodePh` に含まれる。分解はこれ以上しない（`machLiftScalarN` / `machBoolMap` ごとの分解は N3-c、ptot-m4 の統合後。rev15 §3.3）。

可逆性: 行の追加は可逆。N3-c が将来実現したら `NormNodePh` を定理に置き換えられる（その単位で別 freeze）。

## 5. N4-a `ZeroLitAgrees0` の domain 照合

結論: **足りる。新しい前提は要らない。**

* 本番の呼び出しは `Elab.lean:5089` の 1 箇所: `zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat (machNorm senv e))`。`zeroLit` の第 1・2 引数は `inlNatLit` と `canonicalNatLitValue?` に固定されている。`ZeroLitAgrees0`（`N3Extern.lean:72`）の文も同じ 2 引数に固定なので、**文の関数が呼び出しと一致する**。
* `ZeroLitAgrees0 : ∀ e, LetOk 0 e = true → zeroLit inlNatLit canonicalNatLitValue? e = e.replaceNoCache zeroLitF`。呼び出しの入力は `inlFoldNat en`（twin 側。`shapeMid`）。`inlFoldNat_ph`（U-R12c）で `NoPh ∧ BvarLt L`、`noPh_letOk`（`ShippingGen5ReaderTrace.lean:95`）で `LetOk 0` に入る（`NoPh` は `_machLet` タグも除く）。
* `zeroLitF` が返す式（`BitVec.ofNat (inlNatLit n) (inlNatLit 0)`）は閉じていて placeholder を含まないので、`replaceNoCache_ph` が構造で閉じる。**実装済み**（`zeroLit_ph`、U-R12c 179cbe7a）。
* 他の `zeroLit` の呼び出し（`ShippingReaderFuelShape.lean:134`、`ShippingGen3ArgSupply2.lean:211`）は同じ形の twin 側・別 Issue 側で、この rev16 の範囲外。
* FG ±0 / T1 ±0。T1L-54 の文は T1 §12 の置換の後の `ZeroLitAgrees0`（§1）。

## 6. `shapeInputs_of` の新しい署名（実装時、承認後）

rev15 §1 の `hdecl` / `hpack` / `hnorm` の 3 仮説（全称・広い）を、次で置き換える:

```lean
theorem shapeInputs_of (hz : ZeroLitAgrees0) (hrf : RootFloatAgrees) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : DeclValuePh env) (hmem : ∃ c, env.find? c = some ci)
    (hbr : PackTupleInputsBridge) (hraw : RawNodePh (structEnv env)) (hnode : NormNodePh (structEnv env))
    (hdom : …DomAtomic の節。D-b の結果が出るまで現行のまま…) (hbs : ∀ p, shapePre sm ps ci (structEnv env) = some p → p.bs.length ≤ nDecl) :
    ShapeInputs nDecl (structEnv env) sm ps ci n
```

* `hmem` は台帳の行にしない入力の仮説（§2.2）。`hbs` と `hdom` は rev15 の通りで、この rev16 では変えない（`hbs` は dg-dataof の `nDecl = kDOf d` の同定 + T1L-30 に付け替え見込み、`hdom` は D-b の結果待ち）。
* 型は**未 elaborate**。elaborate 時に直した差があれば rev17 の冒頭に表で書く（黙って直さない）。
* 負の対照（Check の mutant 案）: 各 `def` の `NoPh` / `BvarLt L` の `L` を落とす、`PackTupleInputsBridge` の domain の `BvarLt 0` を落とす、`NormNodePh` の `L` を `L + 1` にする。**signature / defeq での棄却であって意味的反例ではない。**

## 7. FG / T1 の差分（すべて見込み。数えていない。登録は承認後）

| 変更 | FG | T1 | 内容 |
|---|---|---|---|
| 追加 N1-a | +1 | ±0 | `DeclValuePh`（§2）。DG-ENV の環境条件の隣、一度だけ数える |
| 追加 N2-b | +1 | ±0 | `PackTupleInputsBridge`（§3、domain は `NoPh e ∧ BvarLt 0 e`） |
| 追加 N3-b | +2 | ±0 | `RawNodePh`、`NormNodePh`（§4） |
| N4-a | ±0 | ±0 | `ZeroLitAgrees0`（T1L-54、既存） |
| `DomAtomic` | ±0 | ±0 | D-b の結果が出るまで追加しない（`DG_DOMATOMIC_SURVEY.md`）。D-a は足さない |
| 消える行 | **0** | ±0 | 下 |

**候補の合計: FG +4（承認・登録した場合）/ T1 ±0。減算は 0。** 現時点（この文書）の台帳は FG 103 / T1 54 のまま。

**消える行について（reviewer 指摘の「C.RT-2 など」）。** C.RT-2（`hpre : TracePre senv nDecl (Call.…)`）は、N1〜N3 を登録しても**消えない**:
* `ShapeInputs` が残る未供給の成分は `hbs`（`p.bs.length ≤ nDecl`）と `hdom`（`DomAtomic`、D-b 待ち）で、N1〜N3 だけでは `ShapeInputs` 全体は供給されない。
* C.RT-2 の文は `Call.…` の全ての呼び出しの `TracePre` で、`ShapeInputs`（`shapeStart` の入力）はその一部の供給にすぎない。C.RT-2 が `ShapeInputs` で尽きるかは、台帳の担当欄（REV7）の読みで、**reviewer の判断**。
* したがって C.RT-2 / C.CV-2 / C.CV-3 の減算は、`hbs`・`hdom` が供給され、かつ reviewer が C.RT-2 の範囲を確認した後の別単位。この rev16 は数えない。

**正直な収支:** この単位は FG を +4 に向けて増やし、同じ単位では 1 行も減らさない（reviewer 結論 (a): 純減 0 の単位は証明 bridge に限る。この rev16 は前提を足す単位）。得るものは、`ShapeInputs` の 3 成分（`d.value`、`packTupleInputs`、`machNormF`）の供給が、広い全称の仮説から狭い名前付き条件 4 本に分解されること。**採らない場合**（先送り）は、`ShapeInputs` が U-R12b の仮定のまま残り、台帳は変わらない（可逆、後から採用できる）。

## 8. 残り（この rev16 の範囲外）

* `hbs`（`p.bs.length ≤ nDecl`）、`hmem`（`ci` と `env` のつなぎ）、`hdom`（D-b 調査の結果待ち）、C.CV-2/3。
* U-R12c の clean build（coder、rtv-be72e9ca 実行中）。Lean の実装は、この rev16 の承認と clean build の後。
* 実装時の新規ファイル: `Tools/Assume/EnvDeclValue.lean`、`Tools/Assume/PackTupleBridge.lean`、`Tools/Assume/NormNodePh.lean`、`Tools/ShippingGen5ReaderTracePack.lean`、`Tools/ShippingGen5ReaderTraceNormPh.lean`、対応する Check、`lakefile.lean` の `lean_lib`（追加のみ）。共有定義・コンパイラ・T1Hyp 系は編集しない。

## 9. 主張しないこと

N1・N2・N3 の文が受理されたソースで成り立つこと、`ShapeInputs` が供給されること、C.RT-2 等の減算、台帳の増減（§7 は見込み）。`hmem`・`hbs`・`hdom` の供給。`LiftAgrees` / `Inst1Agrees` / `RootFloatAgrees` / `ZeroLitAgrees0` が成り立つこと。C-QWIT、`d'.ok`、実 run、FG。コンパイラ・共有定義・TRUSTED 境界・law は変えていない（N2-c は採らない）。`GenWF` は強化しない。DG-ENV の freeze 文書は読んでいない（§0）。

## 10. reviewer への依頼

1. §2・§3・§4 の完全型（特に N2-b の domain `NoPh e ∧ BvarLt 0 e`、N3-b の `.app f a` 限定の domain）の承認。
2. §1 の ID / 型の同期（T1L-54 = `ZeroLitAgrees0`、`SigTyClosed` / `InstSFieldsDet` に行 ID なし、新しい行は登録時に付番）の確認。
3. §2.3・§3.4・§4.3 の重複照合の確認。特に `RawNodePh` が `BetaRange`（T1L-57）で覆われないという読み。
4. §7 の見込み（FG +4、減算 0）を承認して登録してよいか。登録は承認後に別コミット（文書のみ）で行う。
5. `hmem`（`ci` ∈ `env`）を台帳の行にしない入力の仮説として扱ってよいか（§2.2）。
