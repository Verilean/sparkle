# DG-READERTRACE freeze rev15 — U-R12c の実装記録と `ShapeInputs` の供給（N1〜N4 の採用 / 分解 / 先送り案）（文書のみ、review に出す）

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt19` 0dee3721（U-R12a/b、reviewer 承認）。この Issue の続きは `DG_READERTRACE_FREEZE_REV14.md`（§5 の N1〜N4 は「候補であって採用ではない」、§9 末尾「次の rev で選ぶ」）。
**この rev15 は文書だけ。** §1 に書く Lean（U-R12c）は別コミット 179cbe7a（新規ファイル 2 つ + `lakefile.lean` の `lean_lib` 2 件、新しい前提なし）。§2 以降の案は**提案であって採用ではなく、台帳の件数には数えない**。
用語: 「見つからなかった / 未供給」は「この調査で辿った経路では供給元・経路が見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant（Check）は signature / defeq での棄却であって意味的反例ではない。条件付きの結果は中間結果。

**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。この rev15 は台帳を 1 行も変えない。** 下の「候補の増減」は選択ごとの**見込み**で、数えていない（共通ルール 13: 数えていないものは「未計数」）。

review に出す理由（共通ルール 14）: §3 の N1〜N4 と `DomAtomic` の案に、台帳前提の追加・変更・付け替えの案が含まれる。

## 0. 読んだもの

`DG_READERTRACE_FREEZE_REV14.md`（全文）、`Tools/ShippingGen5ReaderTraceShape.lean`（`MidInputs / ShapeInputs / DomAtomic / shapeStart_trace / machineShapeF_reach`）、`Sparkle/Compiler/Elab.lean`（`mixedGatePeel / inlFoldNat / machLoopAsLet / machRootLets / machRoot / machRunApp? / machDom?`）、`Sparkle/Compiler/MachTupleIn.lean`（`packTupleInputs`）、`Sparkle/Compiler/MachRawSurface.lean`（`zeroLit / rootFloat`）、`Tools/ShippingReaderFuelDefs.lean`（`normStep / machNormF`）、`Tools/Assume/N3Extern.lean`（`LiftAgrees0 / LowerAgreesEq / ZeroLitAgrees0`）、`Tools/Prototype/{PreprocLetOk,NormRangeLetOk}.lean`、`Tools/ShippingGen5ReaderTrace{Let,Inst1,Extract,Reg}.lean`（`lift01_ph / lift11_ph / rootFloat_ph / Inst1Ph / inst1Ph_of_agrees / machRunApp?_ph / phArgs_getAppArgs`）、`git show 7b12301e:scripts/gen3/PARTIAL_SURVEY_A.md`（調査 A）、`git show kjob/fg-ledger-int:scripts/gen2/PREMISE_LEDGER.md`（FG 側の行 C.CV-* / C.RT-* / C.RK-8 / C.DO-2/3）、`git show kjob/t1-ledger-int:scripts/gen3/PREMISE_LEDGER.md`（T1L-30 / 50〜59）。`par/ptot-m4` 965fe51b は `git show par/ptot-m4:Tools/PartialTotal/Agree.lean` の定理名だけ読んだ（この base には入っていない）。
**ID の注意。** 上の 2 つの台帳 branch は現在値（FG 103 / T1 54）より古い snapshot（FG 側に 110、T1 側に 62 の記述がある）で、**行番号が現在の台帳と一致するかは再照合していない**。たとえば `N3Extern.lean` のヘッダは A3 `ZeroLitAgrees0` を T1L-54 と書くが、snapshot の T1L-54 は `Prototype/PreprocLetOk:143` の `ZeroLitAgrees` である。以下の「既存 ID との照合」は、読んだ範囲の文と型の比較であり、現在の台帳との突き合わせは reviewer に残る。

## 1. U-R12c の実装記録（新しい前提なし）

Lean コミット 179cbe7a: `Tools/ShippingGen5ReaderTraceShapeIn.lean`、`Tests/Gen5/ReaderTraceShapeInCheck.lean`、`lakefile.lean`（`lean_lib` 2 件）。共有定義・既存ファイルは編集していない。Pod build は §6。

rev14 §2.3 からの型の差（未 elaborate の型を elaborate 時に直したもの。黙って直さない）:

| rev14 §2.3 | 実装 | 理由 |
|---|---|---|
| `machRoot_ph`: `r := machRoot projs e []` の三連言 | `machRoot_ph (projs) : ∀ e acc, NoPh e → BvarLt (L + acc.length) e → LetsPh L acc.reverse → RootPhOut L (machRoot projs e acc)`（`LetsPh L l := ∀ k x, l[k]? = some x → NoPh x.2.2 ∧ BvarLt (k + L) x.2.2`、`RootPhOut` は三連言の `def`） | `machRoot` は `acc` 付きの再帰なので帰納法の形に一般化。`acc = []` で rev14 の型になる |
| `machRoot_ph` の `wrap?` 腕は `shapeMid_ph` 側 | `MidPh L m`（`def`: `LetsPh`、run 節、root 節）と `shapeMid_ph` | rev14 と同じ切り分け。`wrap?` の run は `root.getAppArgs.back?`（`phArgs_getAppArgs` 経由） |
| `shapeInputs_of`: §5 の名前付き条件を仮定に取る | 5 つの仮説を**定理の引数**として取る（下） | 台帳の行にしない（rev14 §1 と同じ扱い） |
| `zeroLit` の扱いは未記載 | `zeroLit_ph (hz : ZeroLitAgrees0)`（`Tools/Assume/N3Extern.lean` の既存の仮定。`replaceNoCache` の Ph 保存は新規の構造補題） | N4 の照合（§3.4） |
| `rootFloat_ph` を使う | `shapeMid_ph (hz : ZeroLitAgrees0) (hrf : RootFloatAgrees)` | `rootFloat_ph`（Let、既存）の仮定 |

`shapeInputs_of (hz : ZeroLitAgrees0) (hrf : RootFloatAgrees) (hdecl) (hpack) (hnorm) (hdom) (hbs) : ShapeInputs nDecl senv sm ps ci n` の仮説の型（完全な型は §3 の各案に再掲）:
* `hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true`（N1 の内容）
* `hpack : ∀ L e, NoPh e → BvarLt L e → NoPh (packTupleInputs e) ∧ BvarLt L (packTupleInputs e)`（N2）
* `hnorm : ∀ L e en, NoPh e → BvarLt L e → machNormF n senv e = some en → NoPh en ∧ BvarLt L en`（N3）
* `hdom : ∀ p en, shapePre … = some p → machNormF n senv p.e = some en → ∀ dom αs ie b, (shapeMid senv p en).run? = some (dom, αs, ie, b) → (∃ j, dom = .bvar j) ∨ (∃ c ls, dom = .const c ls)`（`DomAtomic`）
* `hbs : ∀ p, shapePre sm ps ci senv = some p → p.bs.length ≤ nDecl`

構造補題（前提なし）: `inlNatSum?_ph`、`inlFoldNat_ph`、`replaceNoCache_ph`、`machLoopAsLet_ph`、`mixedGatePeel_ph`、`machRootLets_len`、`machRootLets_ph`、`machRoot_ph_base`、`machRoot_ph`、`letsPh_snoc`。条件付き（既存の名前付き仮定のみ）: `zeroLit_ph`（`ZeroLitAgrees0`）、`shapeMid_ph`（+ `RootFloatAgrees`）。
**`MidInputs` の 4 節のうち、構造から出ないもの**は `p.bs.length ≤ nDecl` と `DomAtomic dom` の 2 つ（`shapeMid_ph` はこの 2 つを出さない）。残りの 3 節（rootLets、run の `NoPh/BvarLt`、root）は `en` の `NoPh ∧ BvarLt p.bs.length` から出る。つまり**供給の残りは「`en` の範囲」（N1〜N3）、`DomAtomic`、`p.bs.length ≤ nDecl` の 3 点**。

主張しないこと: 上の仮説のどれも受理されたソースで成り立つこと。C-QWIT、`d'.ok`、実 run、FG。

## 2. `ShapeInputs` の各成分の供給元の表

`MidInputs nDecl senv p en` の各成分について、**何から供給するか**（4 区分: 実 run の事実 / 既存の名前付き条件 / rev14 §5 の候補 N1〜N4 / 未供給）。`ShapeInputs` は `shapePre sm ps ci senv = some p` と `machNormF n senv p.e = some en` を前提に取る（この 2 つは `machineShapeF … = some (some sp)` から出る実 run の事実で、U-R12b の `machineShapeF_state_side` が与える）。

| `MidInputs` の成分 | 何が要るか | 供給元（読んだ範囲） | 区分 |
|---|---|---|---|
| (前提) `shapePre … = some p`、`machNormF n senv p.e = some en` | `ShapeInputs` の前件 | `machineShapeF = some (some sp)`（U-R12b の仮定）。`shapePre_facts`（R5）が `ci = .defnInfo p.d` と `mixedGatePeel (packTupleInputs p.d.value) = some (p.bs, p.e)` を出す | 実 run の事実 |
| `d.value` の `NoPh ∧ BvarLt 0` | 宣言の値は閉じていて placeholder の fvar を含まない | **N1**（§3.1）。`EnvTypesFVarFree`（型の fvar 不在）は値を覆わない。`SigTyClosed` は `instS` の型のみ | 候補 N1 |
| `packTupleInputs` の出力の `NoPh ∧ BvarLt L` | `shapePre` の `packTupleInputs`（partial） | **N2**（§3.2）。内部で使う `liftLooseBVars`（start=1）と `instantiate1` は `LiftAgrees`（T1L-50）・`Inst1Agrees`（T1L-51）の側（`lift11_ph` / `inst1Ph_of_agrees` が既存） | 候補 N2（+ 既存条件 T1L-50/51） |
| `mixedGatePeel` の出力 | `NoPh p.e ∧ BvarLt p.bs.length p.e` | `mixedGatePeel_ph`（§1、前提なし） | 構造補題（実装済み） |
| `machNormF` の出力 `en` の `NoPh ∧ BvarLt p.bs.length` | `normStep` の全 arm | **N3**（§3.3）。`instantiate1` の 2 arm は `Inst1Agrees`（T1L-51）で覆われる見込み。`ashr` / `lam` / `letE`（保持）は構造。`rawNode` と `machNormNode`（`machLiftScalarN` / `machBoolMap`）は `LetOk` 版の分解が `Tools/Prototype/` にあるが型が違う | 候補 N3（+ 既存 T1L-51） |
| `inlFoldNat` / `machLoopAsLet` / `machRoot` / `machRunApp?` | 範囲の保存 | `inlFoldNat_ph`、`machLoopAsLet_ph`、`machRoot_ph`（§1、前提なし） | 構造補題（実装済み） |
| `zeroLit` | 範囲の保存 | **N4**（§3.4）。`ZeroLitAgrees0`（`N3Extern.lean`）で足りる。`zeroLit_ph` を実装済み | 既存の名前付き条件 |
| `rootFloat` | 範囲の保存 | `RootFloatAgrees`（T1L-52）→ `rootFloat_ph`（既存） | 既存の名前付き条件 |
| `DomAtomic dom`（run 節） | `shapeStart_trace` が `dom` の変換状態 `stc = {}` を示すのに使う | **供給元が見つからなかった**（§4） | 未供給 |
| `p.bs.length ≤ nDecl` | `j - d - |env| < nDecl` の算術 | `nDecl` は `kDOf d` に同定される（行 6b、`sparkle-gen5-dg-dataof` の担当）。T1L-30 `hkD`（`mixedGatePeel (packTupleInputs dP.value) = some (bs, e) → p.kD = bs.length`）と `nDecl = p.kD` の同定があれば等号で足りる見込み。**同定が本 base では未供給** | 未供給（既存条件 T1L-30 + dg-dataof の同定に付け替え見込み） |
| `hT : TraceGood senv nDecl (readF senv n)` | readF の trace | `readF_traceGood_of_premises`（Dispatch）が 6 つの既存の名前付き仮説（`LiftAgrees`、`RootFloatAgrees`、`Inst1Agrees`、`EnvTypesFVarFree`、`SigTyClosed`、`InstSFieldsDet`）の下で出す | 既存の名前付き条件 |

`ShapeInputs` 以外の未解消（reviewer の指摘）: C.CV-2（`LetsNoLoose st`）/ C.CV-3（`FullInv`/`FReachC`）は、U-R12b の結論が同じ witness で出すが、**`ShapeInputs` が供給されるまで数えない**（rev14 §6 の条件のまま）。

## 3. N1〜N4 の案

共通: 各案に完全な型、domain、既存 ID との照合、FG / T1 の差分、DG-ENV と共有するか、を書く。台帳の ID は snapshot の行（§0 の注意）。「増減」はすべて**見込みで未計数**。

### 3.1 N1 `DeclValuePh`（宣言の値の範囲）

**型（案）。**
```lean
def DeclValuePh (env : Lean.Environment) : Prop :=
  ∀ (n : Name) (d : DefinitionVal), env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true
```
domain: `env` 内の全 `defnInfo`（`NoPh` は 4 つの placeholder tag の fvar の不在、`BvarLt 0` は loose bvar の不在 = 閉じている）。`shapeInputs_of` の `hdecl` は、`ci = env.find? c` の特定の `ci` についてのこの条件の 1 インスタンス（`ci` が `ShapeInputs` の引数なので、全称版から取り出せる）。
**内容の根拠（読んだ範囲）。** kernel の `addDecl` は fvar を含む宣言と loose bvar を持つ宣言を受理しない。`EnvTypesFVarFree`（`LetsSigTy:63`）は同じ種類の「kernel の事実」を**型について**述べる既存の前提で、コメントに「Lean's `addDecl` rejects free variables; `Environment` is not modelled」と書いてある。値版（と閉包性）は、この調査では見つからなかった。

| 案 | 内容 | FG / T1 | 影響 |
|---|---|---|---|
| **採用案 N1-a（推奨）** | `DeclValuePh` を FG の新しい名前付き条件として台帳に足す（DG-ENV の環境条件の族。`EnvTypesFVarFree` の隣） | FG +1 見込み（未計数）/ T1 ±0 | 型が小さく、kernel の事実で、`EnvTypesFVarFree` と同じ性格。既存行と**同一の型・domain ではない**ので、reviewer 結論 (b) により新規として数える |
| 分解案 N1-b | `EnvTypesFVarFree` を「型と値の両方」に強化（`NoFv ci.type ∧ NoFv ci.value`）し、閉包性（`BvarLt 0`）を別条件にする | FG ±0〜+1 / T1 ±0 | **既存行の文の強化**（reviewer 結論 (b) で強化は新規扱い）。T1L-53 と FG の共有行を同時に変えるので影響が広い。得るものは数の見かけだけ（強化は +1 と同じ重さ） |
| 先送り案 N1-c | `ShapeInputs` を仮定のまま | ±0 | FG 受理側で `ShapeInputs` が残る（C.RT-2 は付け替わるだけで消えない） |

DG-ENV との共有: **共有できる見込み**（`sparkle-gen5-dg-env` の環境条件。現在 TODO で、台帳待ちの一時停止）。共有するかは N1-a の行が DG-ENV の C0 とは別の文であること（C0 は run 間で環境が同一という文）を reviewer が確認する。この rev15 では DG-ENV の Issue は変えない。
可逆性: 台帳の行の追加は可逆（削除すれば元に戻る）。Lean 側は `hdecl` が引数のままなので、行を置かなくても U-R12c は壊れない。

### 3.2 N2 `PackTupleInputsPh`（`packTupleInputs`、partial def）

**型（案）。**
```lean
def PackTupleInputsPh : Prop :=
  ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
    NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true ∧
    BvarLt L (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true
```
domain: 全 `Lean.Expr`（`NoPh ∧ BvarLt L` を満たすもの）。`partial def` なので logic の中に本体が見えない。
**読み取り。** 本体は先頭の `lam` を剥がしながら、タプル型の束縛を `Signal dom (BitVec n)` に置き換え、本体を `(b.liftLooseBVars 1 1).instantiate1 (unpackE (dom.liftLooseBVars 0 1) ws (.bvar 0))` に取り替える。`unpackE` は閉じた構築子（`natE`）と `dom` / `bvar 0` だけで作られる。したがって `LiftAgrees`（T1L-50、(1,1) を含む）と `Inst1Agrees`（T1L-51）の下では、全域化された twin について `lift11_ph` と `inst1Ph_of_agrees`（`m = m' = L + 1`）で Ph の保存が出る見込み（**未証明**）。調査 A（7b12301e）: 燃料 `lamDepth e`（先頭 `lam` の個数）の燃料版は停止し、5000 件のランダム宣言（3346 件が実際に書き換わる）で元の partial と一致（**検査であって証明ではない**）。**モデル（spec）は Tools/ にも各 branch にも見つからなかった。**

| 案 | 内容 | FG / T1 | 影響・コスト |
|---|---|---|---|
| 採用案 N2-a | `PackTupleInputsPh` を FG の名前付き条件として直接足す | FG +1 見込み / T1 ±0 | 証明が要らず小さいが、ユーザー方針（`partial def` は振る舞いのモデル + 本番との一致を前提）に反する。「partial の出力が範囲を保つ」という振る舞いの文を、モデルなしに前提にする |
| **分解案 N2-b（推奨）** | `Tools/` の新規ファイルに燃料 twin `packTupleInputsF`（`lamDepth` 燃料、本体は `packTupleInputs` と同じ 2 腕）を置く。(i) twin の Ph 保存を `LiftAgrees`（T1L-50）+ `Inst1Agrees`（T1L-51）から**証明**（新しい前提なし）。(ii) 本番との一致 `∀ e, packTupleInputs e = packTupleInputsF (lamDepth e) e` を**名前付き条件**として FG に足す（C.CV-4 `ShapeFuelBridge` / 調査 A の「モデルとの一致定理」と同じ型の前提） | FG +1 見込み（一致の 1 本）/ T1 ±0 | 前提の文が「本番 = 計算可能 twin」の一致で、`Ph` の文より狭くレビューしやすい。証明量は中程度（`lamDepth` の保存、`unpackE` の Ph）。**ただし (1,1) の lift が要る**（調査 A §2.2）: 今の `LiftAgrees0`（`N3Extern`、start=0 のみ）では足りず、T1L-50 `LiftAgrees` を使い続けるか、A1 の範囲を広げるかの確認が要る（この調査では決めない） |
| 分解案 N2-c（ユーザー判断が要る） | コンパイラ側 `Sparkle/Compiler/MachTupleIn.lean` の `packTupleInputs` を燃料版に置換（調査 A §6 の diff）。一致は定義そのものになり前提が 0 | FG ±0（N2 の前提が消える）/ T1 ±0 | **コンパイラ（本番）定義の編集**で、共通ルール 5 により、ユーザーの承認なしにはできない。調査 A §5.2 は「実装は勧めない」と判断していた（T1L-30 を減らさないため）が、その理由は N2 が ShapeInputs の供給に要るという事実を数えていなかった。**判断資料は別 md が要る**（この rev15 では出さない。reviewer が N2-c を選ぶなら次の単位で出す） |
| 先送り案 N2-d | `ShapeInputs` を仮定のまま | ±0 | FG 受理側で `ShapeInputs` が残る |

DG-ENV と共有するか: **しない**（`packTupleInputs` は環境ではなく宣言の値の書き換えで、DG-READKINDS / reader-bridge 側の性格。`ShapeFuelBridge`（C.CV-4）の隣）。
照合: C.CV-4 / T1L-43（`ShapeFuelBridge`）は `machineShapeF n` と本番 `machineShape?` の一致で、`packTupleInputs` の twin は含まない（読んだ範囲）。T1L-30 `hkD` は `packTupleInputs` を使うが `kD = bs.length` の文で、範囲の保存は含まない。

### 3.3 N3 `NormFPh`（`machNormF` の出力の範囲）

**型（案）。**
```lean
def NormFPh (senv : StructEnv) : Prop :=
  ∀ (L n : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true →
    machNormF n senv e = some en → NoPh en = true ∧ BvarLt L en = true
```
domain: 全燃料 `n`、全 `L`（束縛変数の上限は全称。reviewer 指摘 2026-11-02 の明記）。`machNormF`（`ShippingReaderFuelDefs.lean:681`）= `fuel (normStep senv) n e`。
**`normStep` の arm と覆う条件（読んだ範囲）。**
| arm | 呼ぶもの | 覆うもの |
|---|---|---|
| `ashr`（`ashrView?`） | `ashrE inlNatLit …`、`machSigBin`（構築子の積み） | 構造補題（前提なし、`LetOk` 版は `NormRangeLetOk` に `ashrE_ok`）。**Ph 版は未実装** |
| `rawNode senv.prodMatch e = some e'` | `liftLooseBVars 0 n`、`beta`、`peel` | `RawNodePh senv`（新規）。T1 snapshot の T1L-55〜57（`LiftLooseRange / LowerLooseRange / BetaRange`）は `LetOk` 型で別の文 |
| `machNormNode senv (.app f' a')`（約 40 arm） | `machNormPure/Ap/ApLift/Map`、`machLiftScalarN`、`machBoolMap`（後 2 つは partial） | `NormNodePh senv`（新規）。T1 snapshot の T1L-58/59（`LiftScalarCorr / BoolMapCorr`）は**モデルとの一致**で、`par/ptot-m4` 965fe51b が全域化 + 一致定理を受理済み（**この base には入っていない**） |
| `lam` | 再帰のみ | 構造 |
| `letE`（`Nat` 型 / 幅つき `!hasLooseBVars`） | `b.instantiate1 v` | `Inst1Agrees`（T1L-51）+ `inst1Ph_of_agrees`（既存）。`m = m' = L`（`b : L + 1`、`v : L`） |
| `letE`（保持） | 再帰のみ | 構造 |
| その他 | `FM.pure e` | 自明 |

| 案 | 内容 | FG / T1 | 影響・コスト |
|---|---|---|---|
| 採用案 N3-a | `NormFPh senv` を 1 本の名前付き条件として FG に足す | FG +1 見込み / T1 ±0 | 最小の変更。ただし 1 本で `machNormNode` の約 40 arm と partial 2 本の振る舞いを丸ごと前提にする（広い）。reviewer 結論 (b): 既存 ID と型・domain で照合できないので新規として数える |
| **分解案 N3-b（推奨）** | `NormFPh` を、(i) 構造 arm（`ashr`/`lam`/`letE`/`pure`）と `instantiate1` arm を**証明**（新しい前提は `Inst1Agrees` T1L-51 のみ = 既存）、(ii) `rawNode` と `machNormNode` を 2 本の名前付き条件 `RawNodePh senv`、`NormNodePh senv`（型は `NormRangeLetOk` の `RawNodeRange` / `NormNodeRange` の `LetOk 0` を `NoPh ∧ BvarLt L` に置いたもの）に分ける | FG +2 見込み（`RawNodePh`、`NormNodePh`）/ T1 ±0 | 各々が 1 つの呼び（`rawNode`、`machNormNode`）を覆うので狭い。(i) の証明は fuel 帰納法（`tabOk_fuel` 型、`NormRangeLetOk` に `LetOk` 版の先例）で中程度。(ii) の 2 本は**さらに分解できる可能性**（下の N3-c） |
| 分解案 N3-c（調査が要る） | `NormNodePh` を `machLiftScalarN` / `machBoolMap` の呼びに分ける。par/ptot-m4 を統合した後で、両者の全域版と一致定理（`liftScalarCorr`、`boolMapCorr` が既存のモデル上で証明済み）から Ph 保存を**証明**する（モデル上の Ph 版の補題が新規）。`machNormNode` の約 40 arm は構造補題 | FG ±0〜+1 見込み / T1 は ptot-m4 の統合後の台帳で別途 | par/ptot-m4 の統合（このIssueの範囲外）と、モデル `LiftScalarModelLetOk / BoolMapModelLetOk` の Ph 版の再証明が前提。**この調査では、統合後に何行が消えるかを数えていない**。N3-b と二者択一ではなく、N3-b の `NormNodePh` を後で N3-c に置き換える経路 |
| 先送り案 N3-d | `ShapeInputs` を仮定のまま | ±0 | FG 受理側で `ShapeInputs` が残る |

DG-ENV と共有するか: **しない**（`senv` は固定された `StructEnv` で、環境の同一性ではなく reader の振る舞い）。ただし `NormNodePh` が使う `senv.proj / inst / instS` の性質は DG-ENV の `SigTyClosed / InstSFieldsDet` に隣接する（`senv` の中身についての仮定は `readF_traceGood_of_premises` が既に取っている）。
照合: `Inst1Agrees`（T1L-51）= `instantiate1`、`LiftAgrees`（T1L-50）= `liftLooseBVars` の (0,1) / (1,1)。`rawNode` の `liftLooseBVars 0 n`（任意の `n`）は T1L-50 の (0,1) では覆われない（`LiftRange` の注記、`NormRangeLetOk` ヘッダ）。`LiftAgrees0`（`N3Extern`）は任意の `d` を含む start=0 の一致（`rawNode` の `liftLooseBVars 0 n` に使える可能性があるが、`LiftAgrees0` の domain は `LetOk 0` で、`NoPh` から `noPh_letOk` で渡せる）。**`rawNode` が `lowerLooseBVars` と `beta` を使う部分は `LowerAgreesEq`（i = i のみ）で足りるかを照合していない。**

### 3.4 N4 `zeroLit`（`Expr.replace`）

**結論（照合済み）: 既存の名前付き条件 `ZeroLitAgrees0` で足り、新しい前提は要らない。** 型 `∀ e, LetOk 0 e = true → zeroLit inlNatLit canonicalNatLitValue? e = e.replaceNoCache zeroLitF`（`Tools/Assume/N3Extern.lean`）。`zeroLit` の入力は `inlFoldNat en` で、`inlFoldNat_ph` により `NoPh ∧ BvarLt` を満たすので、`noPh_letOk` で `LetOk 0` の domain に入る。`zeroLitF` が返す式（`BitVec.ofNat (inlNatLit n) (inlNatLit 0)`）は閉じていて fvar を含まないので `replaceNoCache_ph` は構造で閉じる。**実装済み**（`zeroLit_ph`、§1）。
| 案 | 内容 | FG / T1 |
|---|---|---|
| **採用案 N4-a（推奨、実装済み）** | 既存の `ZeroLitAgrees0` を使う | FG ±0 / T1 ±0 |
照合の残り: snapshot の T1L-54 は `Prototype/PreprocLetOk:143` の `ZeroLitAgrees`（`∀ e`、`LetOk 0` の domain 制限なし）で、`N3Extern` の `ZeroLitAgrees0` は `LetOk 0` に制限した文（弱い仮定）。現在の台帳の T1L-54 がどちらの文かは**再照合していない**。`ZeroLitAgrees0` を使う限り、台帳の行がどちらでも（より強い `ZeroLitAgrees` でも）足りる。
DG-ENV と共有するか: しない。

## 4. `DomAtomic dom` の供給

`MidInputs` の run 節の `DomAtomic dom`（bvar または const）は構造からは出ない（§1）。**この調査では、受理されたソースで run の `dom` が bvar / const であることの供給元は見つからなかった。** 成功した `machineShapeF` の事実から導けるかを読んだ範囲:
* `shapePost` は `domE ← st.dom <|> machTypeDom? p.d.type` に `machDom? (kI + n + k) domE` を要する。`machDom?`（`Elab.lean:4269`）は `domE` が `fvar _machIn i` か `const defaultDomain` のときだけ `some`。つまり成功した run では最終状態の `st.dom` は**変換後の** `_machIn i` または `defaultDomain`（読んだ範囲）。
* だが `shapeStart_trace` が要るのは**変換前**の `dom` が atomic（`convBvar` の `stc = {}` を示すため）ということで、変換後が atomic でも変換前が atomic とは限らない（`conv` は let を束縛したあと `_machIn` を返し得る）。
* 別の道（**未調査、証明していない**）: `shapeStart_trace` の `DomPh` が要るのは `InRange nDecl st0 0 dom'` だけで、`dom'` が `_machIn i` / `defaultDomain` のときこれは `i < nDecl`（`PhInRange`）または自明で、`stc` に依存しない可能性がある。そのためには、**最終状態の `st.dom` が `st0.dom` と同じ**（`dom := some …` の書き込みが `Elab.lean:3716 / 3933 / 4068 / 4107 / 4235` の複数箇所にある）ことを `FReachC` か別の不変条件で示す必要がある。これは `DomAtomic` を `MidInputs` から外す（rev14 §10 の案 B と同種の、`ShapeInputs` を弱める変更）ことになり、型が変わる。

| 案 | 内容 | FG / T1 | 影響 |
|---|---|---|---|
| 採用案 D-a | `DomAtomicIn`（`hdom` の全称版、受理されたソースで run の `dom` は bvar / const）を FG の名前付き条件として足す | FG +1 見込み / T1 ±0 | 受理されたソースでの成立は未確認。rev14 §10 案 A の帰結（`ShapeInputs` が強い） |
| 分解案 D-b（調査が要る） | 上の「別の道」を調べ、`MidInputs` から `DomAtomic` を外し、`shapeStart_trace` を `dom'` の範囲の事実に置き換える | FG ±0（前提が減る）/ T1 ±0 | `shapeStart_trace` と `MidInputs` の型の変更（承認済みの型の変更なので別 freeze）。成功した run の事実だけを使うので新しい前提はない見込み。**証明できるかは未確認** |
| 先送り案 D-c | `ShapeInputs` を仮定のまま | ±0 | `DomAtomic` が仮定のまま |

推奨: **D-b を先に調べる**（前提を増やさない道が先）。D-b がだめだったときに D-a。この rev15 では型を変えない。

## 5. 推奨の組合せと、台帳の見込み（未計数）

| 項目 | 推奨案 | 見込み（FG / T1） | 状態 |
|---|---|---|---|
| N1 | N1-a（`DeclValuePh` を新規 FG 条件） | +1 / ±0 | 提案 |
| N2 | N2-b（燃料 twin + 一致の名前付き条件） | +1 / ±0 | 提案。(1,1) の lift の確認が前提 |
| N3 | N3-b（`RawNodePh` + `NormNodePh`、arm の残りは証明） | +2 / ±0 | 提案。将来 N3-c で減る可能性 |
| N4 | N4-a（既存 `ZeroLitAgrees0`） | ±0 / ±0 | 実装済み |
| `DomAtomic` | D-b を先に調査、だめなら D-a | ±0〜+1 / ±0 | 未調査 |
| `p.bs.length ≤ nDecl` | dg-dataof の `nDecl = kDOf d` の同定 + T1L-30 | ±0 / ±0（付け替え見込み） | 本 Issue の外 |
| 消える候補 | C.RT-2（`ShapeInputs` の行）。C.CV-2 / C.CV-3 は rev14 §6 の条件が揃ったとき | −1〜−3 見込み（**数えない**） | rev14 §6 のまま |

**候補を合計した台帳の見込み: FG +4〜+5（足す行）に対し −1〜−3（消える候補）。純減ではない見込みで、全体は未計数。** reviewer 結論 (a): 純減 0 の単位は証明 bridge に限る。この提案は**前提を足す単位**（N1・N2・N3・D）と**証明の単位**（U-R12c 実装済み、N2-b / N3-b の証明部分）に分けて出す。**足す行はそれぞれ別に承認を求める**（束にして 1 回で全承認を求めない選択もできる: reviewer が N1〜N3 のうち採用するものだけを選ぶ）。
**先送り（全案を選ばない）の場合の影響:** U-R12a/b/c は進んだまま、`ShapeInputs` が U-R12b の仮定として残る。FG 受理側で `ShapeInputs`（`DomAtomic` を含む）が 1 つの未供給の義務として残り、C.RT-2 は `ShapeInputs` に付け替わるだけで消えない。後から N1〜N3 を採用することは可逆（台帳の行を足すだけ）。

## 6. 実行した検証（U-R12c、Lean コミット 179cbe7a）

`kjob lake build` を 1 つずつ実行（Pod 内、ログはソースツリー外）: `Tools.ShippingGen5ReaderTraceShapeIn` exit 0 / `Tests.Gen5.ReaderTraceShapeInCheck` exit 0。Check の COUNTS: TYPE 9 宣言（`LetsPh`、`MidPh`、`inlFoldNat_ph`、`machLoopAsLet_ph`、`mixedGatePeel_ph`、`zeroLit_ph`、`machRoot_ph`、`shapeMid_ph`、`shapeInputs_of`。`LetsPh` は構文一致、`MidPh` / `machRoot_ph` / `shapeMid_ph` / `shapeInputs_of`（`hdom` の binder）は `isDefEq` で受理（Check のログに明記））、MUTANT 5（`inlFoldNat_ph` の出力を `L + 1`、`mixedGatePeel_ph` の `bs.length` を落とす、`machRoot_ph` の `k + L` を `L`、`MidPh` の run 節の `+ 1` を落とす、`shapeInputs_of` の `hdom` を落とす。**signature / defeq での棄却であって意味的反例ではない**）、AXIOMS 9（標準の 3 つのみ）、CLOSURE OK 4845 constants from 9 roots（unknown 0、sorryAx なし。Check 内の sorry 警告は in-memory の負の対照）。Tools 側に sorry / axiom / native_decide なし。**clean build は coder。**

## 7. 主張しないこと

`ShapeInputs`（`DomAtomic` を含む）が受理されたソースで成り立つこと、N1〜N4 の真偽、`hT` の 6 つの名前付き仮説の真偽、`ZeroLitAgrees0` / `RootFloatAgrees` / `LiftAgrees` / `Inst1Agrees` が成り立つこと。台帳の行が増える・消えること（§5 は見込み）。C-QWIT、`d'.ok`（G9）、`dom'` の一致（G5）、行 6b・`nDecl = kDOf d`、`hbr`（C.CV-4）、実 run と FG。コンパイラ・共有定義・TRUSTED 境界・law は変えていない（N2-c はユーザー判断が要る案で、採用していない）。`GenWF` は強化しない。

## 8. reviewer への依頼

1. §1 の U-R12c（実装済み、rev14 §2.3 の型からの差を含む）の確認。Lean のレビューは coder の clean build の後。
2. §3・§4 の各案について、**項目ごとに**採用 / 分解 / 先送りを選ぶ（推奨は §5）。N2-c（コンパイラの置換）を選ぶ場合は、次の単位でユーザー判断資料を出す。
3. N1〜N3 と `DomAtomic` を台帳に足す場合の行の文は §3・§4 の型のとおりで、足す前に DG-ENV / reader-bridge との重複（§3 の共有欄）を現在の台帳で確認する。
