# DG-READERTRACE freeze rev5 — 残りの arm の単位列、range 条件の支払い表、L1 の見直し、最初の Lean 単位 U-R4a

Issue `sparkle-gen5-dg-readertrace`（再開）。Base: `kjob/rt11` = `par/rt-n3` 585aad02（`kjob/g5rt-r10` 6e6c880f = U-R3b 承認済みを含み、N3 の `Tools/Assume/N3Extern.lean` / `Tools/ShippingN3ExternAgree.lean` / `Tests/Gen3/N3AgreeCheck` を取り込み済み）。
`DG_READERTRACE_FREEZE.md`（rev0）…`..._REV4.md` の続き。**文書のみ。このコミットでは Lean を書かず elaborate もしていない。** 以下の Lean は読んだファイルに合わせた未 elaborate の提案で、後で見つかった elaboration 誤りは rev の addendum で直す（黙って直さない）。
用語: 「見つからなかった / 未供給」は「この調査で辿った経路では供給元・経路が見つからなかった」の意味で、不可能・導出不能の主張ではない。mutant は signature / defeq での棄却であって意味的反例ではない。条件付きの結果は中間結果。単位の承認は `TraceGood senv nDecl (readF senv n)` 全体の成立の承認ではない。
ユーザー方針（2026-11-01、manager 経由）: `partial def` は振る舞いから書いたモデル（`readF` / `machineShapeF` / `machNormF`）で証明し、本番との一致は前提（C.CV-4）として持つ。純減 0 の単位でも道筋の途中なら着手してよい。新しい law / TRUSTED は freeze → reviewer。

**この rev5 が台帳に与える差分: なし**（FG 102 / T1 54、今回 FG -0 +0 / T1 -0 +0）。§2 に「新しい等式仮定案 / 新しい名前付き条件」が 2 件出てくるが、**提案であって採用ではない**。どちらも最初に必要になる単位（U-R4e / U-R8）の直前に、流れごとに束ねた 1 回の freeze として reviewer に出し、承認まで Lean に置かない。それより前の単位 U-R4a〜U-R4d は前提を増やさない（§1）。

## 0. 読んだもの

`convStep … loopRootStep`、`step`、`readF`（`ShippingReaderFuelDefs.lean` 262–600）、`TracePre/TracePost/TraceGood/PhPre/PhPost/CtlPh/TrInv`（`…ReaderTraceCtl.lean`）、`conv_basic_trace` / `readF_traceGood_of_step`（`…ReaderTraceArms.lean`）、`chain_basic_trace`（`…ReaderTraceChain.lean`）、`RootFloatRange … BundleIotaRange` と `pureFacts_of`（`ShippingLetsReaderInvMain.lean` 53–95）、`LiftAgrees` / `Inst1Agrees` / `RootFloatAgrees`（`ShippingLetsExternSpec.lean`）、`LiftAgrees0 / LowerAgreesEq / ZeroLitAgrees0` と `r1/r2/r3`（`Tools/Assume/N3Extern.lean`、`ShippingN3ExternAgree.lean`）、`bundleIota`（`MachRawSurface.lean` 162–）、`git show par/ptot-m4:Tools/PartialTotal/Agree.lean`（`rootFloatAgrees (hl : LiftAgrees) : RootFloatAgrees`、この base には無い）、`git show b68e83bd:scripts/gen5/GENDATA_COVER_SURVEY.md` §3.4 / §6.2、`git show bb665fa2:scripts/gen3/N3_EXTERN_MIN.md`（N3 設計 rev2）。

**読み取りで分かった 4 点（elaborate はしていない）。**
1. `readF` の 7 本体が呼ぶ extern / partial は、`grep` と目視で、`rootFloat`（partial）、`Expr.liftLooseBVars`（`(0,1)` と `(1,1)` の 2 組だけ。letE の `ty.liftLooseBVars 0 1` と `b.liftLooseBVars 1 1`）、`Expr.instantiate1`（`instRes`）、`bundleIota`（total 関数）だった（`Elab.lean` 3480–4300 の範囲）。`lowerLooseBVars` と `zeroLit` は reader 本体から呼ばれていない。
2. したがって N3 の等式仮定のうち reader の trace に効くのは `LiftAgrees0`（`s = 0`）の `(0,1)` 側だけで、`(1,1)` 側は N3 の範囲外。`(0,1)` と `(1,1)` の両方を持つ**既存の** T1L-50 `LiftAgrees` がすでにある（N3 設計 §3.4.4 の注: `LiftAgrees0` で T1L-50 を置き換えることは成立しない）。**r2 `LowerAgreesEq → LowerLooseRangeEq` と r3 `ZeroLitAgrees0 → ZeroLitRange0` は readF の range 条件を 1 つも払わない**（この調査では reader 側の使用箇所が見つからなかった）。r1 も `LiftRange` の `(1,1)` 半分は払えない。
3. 既存の `Range` 述語は `LetOk`（`_machLet` 不在）の保存、`TraceGood` が要るのは **`NoPh` / `BvarLt` / `InRange` / `NoLoose` の保存**で、型が違う。lift 等の呼び出し先は入力 `ty / b / v / args` で、これらは `PhPre` から `NoPh`（⇒ `LetOk n`）。等式 `liftLooseBVars = liftSpec` が構造再帰の `liftSpec` に帰着するので、`NoPh` / `BvarLt` の保存は `liftSpec` 上の**構造的補題**（in-Lean で証明する、前提を増やさない）になる。
4. `BundleIotaRange` は既に証明済み（`Tools/ShippingBundleIotaRange.lean` `bundleIotaRange`）。`ShippingLetsReaderInvMain.lean` のコメント「NOT PROVED」は古い。`bundleIota` の結果は入力の部分項そのもの（`a` / `b`）か、その部分項から `bundle2` を組み直した式なので、`NoPh` / `BvarLt` の保存も構造的補題で閉じる見込み（読み取り。未 elaborate）。

## 1. 残りの arm と単位の列

記法: 「arm 補題」は `conv_basic_trace`（rev3）/ `chain_basic_trace`（rev4）と同じ形で、`hT : TraceGood senv nDecl (readF senv n)`（燃料 `n` の表）と `hpre : TracePre …` と成功 run `hv` から `FReachC … ∧ PhPost …` を出す（`Post` は `readF_good` から別に取る＝rev3 の reduction）。dispatch は最後の単位 U-R11 で束ねる。各 arm 補題は `convStep` の match の判別式を**仮説**として取り、「その arm に入る」ことを仮定して結論する（末尾の組み立てで全判別式を場合分けする）。

| 単位 | 内容 | 使う既存補題 | 新しい前提（台帳 ID） | 台帳の差分 |
|---|---|---|---|---|
| **U-R4a**（最初の Lean 単位、§4） | `convStep` `app` の葉 3 arm: 登録済み bare register（`bareRegs.find?` が当たる）、`machLoopRead?`、`machReadV`。結果は `machSlot i`、状態不変 | `inRange_machSlot`、`noLoose_fvar`、`FReachC.refl`、`CtlPh` の `bareRegs` 節（`hTr.2.2.1`）、各 arm の `i < kinds.size` ガード（コード自身） | なし | FG -0 +0 / T1 -0 +0 |
| **U-R4b** | `app` の新しい bare register（`regView?` が当たり `find?` が外れる）。`cConv dom`、`domGuard`、状態に `kinds/inits/names/dom/bareRegs` を push、`cConv x`、`ws` を push。`FReachC` の register 作成と `TrInv` の再構成 | `reachC_ws`、`reachC_slots`、`envPh_mono`、`reachC_sizes_mono`、`inRange_mono`、`noPh_letOk`、`machSlotKind?` / `machInit?` の結果は `optK` で使うだけ | なし | -0 +0 |
| **U-R4c**（構造的補題群） | `liftSpec` の `NoPh` / `BvarLt` 保存（`(0,1)` と `(1,1)`、`LetOk` 入力）、`bundleIota ∘ machProjIota` の `NoPh` / `BvarLt` / `InRange` / `NoLoose` 保存、`rootFloatS` の同様の保存。**これらは仮定ではなく補題**（等式仮定からの接続は §2 の表と各 arm 単位） | `liftSpec`、`rootFloatS`（ExternSpec / ReaderInv）、`projIota_ok`、`bundleIotaRange` の証明方針 | なし | -0 +0 |
| **U-R4d** | `app` の一般分岐（`cConv f`、`cConv a`、`bundleIota (machProjIota senv.proj (.app f' a'))`）。2 回の `cConv` 連鎖は `conv_basic_trace` の `lam` と同じ形 | U-R4c、`reachC_trans`、`inRange_mono`、`inRange_app`、`noLoose_app` | なし | -0 +0 |
| **U-R4e** | 抽出子の Ph 版（旧 "U-R2"）: `machRunApp?`、`machInstCall?`（`machInstCall?_spec` は Ctl にある）、`machInstCallS?`（同）、`memCall?` の結果成分が `NoPh` ∧ `BvarLt (env.length+nDecl)`（呼び出し spine の引数＝部分項）。`machInstCallS?` は `senv.instS c = some (kinds, ty)` の `ty` が要るため **`SigTyPh senv`**（下の §2 表、環境条件） | `machInstCall?_spec`、`machInstCallS?_spec`、spine 補題 | **`SigTyPh senv`（名前付き条件、提案。未提出）** | 採用されれば T1/FG のどちらに数えるかは reviewer 判断（DG-ENV 側と見る案）: +1 |
| **U-R5a** | `convStep` `letE`: `d ≠ 0` で失敗、`rootFloat` が `letE` を返す分岐（float。`ty.liftLooseBVars 0 1`、`b.liftLooseBVars 1 1` で組み直した `letE` を再帰）、`Signal.loop` 分岐（`cLoopRoot`）、`machTailV`（`.regs`）、`machHandleV`（`.handle`）、既定（`cConv v`、`machBindLet`、`.val x`）。`bindLet_reach`（Trace にある） | U-R4c の rootFloat / lift 補題、`bindLet_reach`、`envPh_cons_val`、`NoLoose` 輸送 | `RootFloatAgrees`（既存 T1L-52。この base では名前付き仮説）、`LiftAgrees`（既存 T1L-50） | -0 +0（新規なし） |
| **U-R5b** | `chainStep` `letE`（5a と同形で `cChain`） | 5a の複製的補題 | 同上 | -0 +0 |
| **U-R6** | `nestedStep`: `cConv dom`、`findSomeO` の共有探索（`nestedProbe`）、`machReserve` の reach、`cChain`、`ws ++`、`nested` を push | `machReserve` の reach 補題は**この調査では既存名が見つからなかった**（新規の可能性。その場合この単位で証明） | なし（`machReserve` の補題が新規前提を要さない場合） | -0 +0（未確認） |
| **U-R7** | `instStep`（`instArg` の `foldO`、`machLetIndex`、`insts` の push / dedup） | `letIndex_reach`（Ctl）、`foldO` 帰納（`foldO_js_length`、`mapM_length_some` 相当は**新規**かもしれない） | なし | -0 +0 |
| **U-R8** | `instSStep`（`instRes` が `instantiate1` を使う。`machOuts?`、`foldO` 2 本、`GroupsPh` の再構成） | U-R4e、`instRes` の `NoPh/BvarLt` 保存（等式仮定が要る、§2 の A4 案） | **A4: 新しい等式仮定案（`Inst1Range` T1L-51 の付け替え）**、`SigTyPh`、`InstSFieldsDet`（`GroupsPh` 用、この調査では未確認） | 付け替え 1（採用なら ±0）、`InstSFieldsDet` は未計数 |
| **U-R9** | `loopBodyStep`: `letE` arm（`bindLetAlias` / `bindLetNamed`）と末尾 `foldO loopNext`。`bindLetAlias_reach` は**この調査では既存補題が見つからなかった** | `bindLetNamed_reach`（Ctl）、`bindLetAlias_reach`（新規） | なし | -0 +0 |
| **U-R10** | `loopRootStep`（`loopView?`、`machLoopRegs`、`loopRegBad/Kind/Init`、`loopProbe`、`loops` 等の push、`loopBodyStep` 呼び出し） | U-R9、`fullInv_reachC` 系 | なし | -0 +0 |
| **U-R11** | dispatch 組み立て: `hstep`（`readF_traceGood_of_step` の仮説）を 7 本体から。`TraceGood senv nDecl (readF senv n)`（任意 `n`）。**この時点で F : PureFacts senv が必要**（§2 の支払い表の結果を `pureFacts_of` に渡す）。結論は名前付き仮説（`LiftAgrees`、`RootFloatAgrees`、`Inst1`（現行 `Inst1Range` または A4）、`SigTyRange`、`SigTyPh`）に条件付き | U-R4a〜U-R10、`readF_traceGood_of_step`、`pureFacts_of`、`liftRange_of_agrees`、`rootFloatRange_of_agrees`、`bundleIotaRange` | 上の名前付き仮説（新規は A4 と `SigTyPh` の 2 件のみ） | 単位としては -0 +0 |
| **U-R12** | `machineShapeF_reach`（U-E3b）、`ShapeInputs`、R-in / R-nl / R-dom の readF 呼び出し側、C-QWIT（`TraceGood` から quote）への接続。**未調査**（`machineShapeF` / `shapeStart/RootLet/Body` を読んでいない） | — | 未確認 | 未計数 |

U-R4a〜U-R10 は互いに独立（U-R4b 以降は U-R4a の `exprPh_slot` を共用できる）で、順序は上から。U-R4e / U-R8 の前に §2 の提案を reviewer に出す。

## 2. range 条件ごとの支払い表（N3 の bridge で払えるか / 新しい等式仮定案 / 残る）

`PureFacts senv`（`pureFacts_of`）の入力と、trace 側で別に要る Ph 版（§0 の 3 点目）。

| 条件 | 定義（場所） | N3 の bridge で払えるか | 払い方 / 案 | 状態 |
|---|---|---|---|---|
| `LiftRange`（`(0,1)` と `(1,1)`） | `ShippingLetsReaderInvMain.lean:57` | **半分だけ**: r1 `LiftAgrees0 → LiftLooseRange0`（`s = 0`）は `(0,1)` 側（任意 `d`）を払う。`(1,1)` 側は払えない | 既存の `LiftAgrees`（T1L-50）から `liftRange_of_agrees`（証明済み）。新しい仮定は要らない | **既存 T1L-50 で払う**（N3 の r1 は不要） |
| lift の Ph 版（`NoPh` / `BvarLt` 保存） | 新規 U-R4c の補題 | 同上（等式は `liftSpec`、構造的補題で閉じる見込み） | in-Lean の補題。`LiftAgrees`（T1L-50）に条件付き | 前提を増やさない |
| `RootFloatRange` | `…InvMain.lean:53` | いいえ（`rootFloat` は partial） | `RootFloatAgrees`（既存 T1L-52、`ExternSpec.lean:237`）から `rootFloatRange_of_agrees`。par/ptot-m4（965fe51b）は `rootFloatAgrees (hl : LiftAgrees) : RootFloatAgrees` を与えるが、この base には**入っていない**（`rootFloat` を total にしたコンパイラ編集を含む）。統合までは `RootFloatAgrees` を**名前付き仮説**に残す | **残る（既存 T1L-52）**。統合後は T1L-50 のみ |
| rootFloat の Ph 版 | U-R5 の補題 | 同上 | `RootFloatAgrees` ⇒ `rootFloatS`（構造再帰）の `NoPh` / `BvarLt` 保存 | 前提を増やさない |
| `Inst1Range` | `…InvMain.lean:62`（T1L-51） | いいえ（N3 の対象外。`instantiate1` の等式は N3 設計で「別判断」） | 現行は T1L-51 のまま（`PureFacts.inst1` はこれを取る）。**Ph 版（`instRes` の結果の `NoPh` / `BvarLt`）は `LetOk` 範囲では出ない**。案 **A4**（提案、未提出）: `Inst1Agrees` と同じ形の等式を必要 domain に限る — `∀ n b a, LetOk n b = true → LetOk n a = true → b.instantiate1 a = inst1Spec b a 0`。`Inst1Range` は `inst1Spec_ok`（既存）で補題に、Ph 版も補題になる。`instantiate1` の C++ 側（`instantiate.cpp:44-53`）は N3 設計 §1.2 で `inst1Spec` と構造一致を読み取り済み（形式証明ではない） | **A4 を reviewer に出す（U-R8 の前）**。T1L-51 の付け替え（range → 等式。T1 ±0 の案）。reviewer が採らなければ `Inst1Range` と名前付き条件 `Inst1Ph`（+1）のまま |
| `BundleIotaRange` | `…InvMain.lean:72` | — | **証明済み**（`Tools/ShippingBundleIotaRange.lean` `bundleIotaRange`）。Ph 版は U-R4c の補題 | 払われている |
| `SigTyRange senv` | `…InvMain.lean:67` | — | 環境条件（DG-ENV）。`sigTyRange_structEnv env (hK : EnvTypesFVarFree env)` が既存（LC4b）。**Ph 版 `SigTyPh senv := ∀ c kinds ty, senv.instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true`** は `EnvTypesFVarFree`（fvar 不在）だけでは出ない（`BvarLt 0` は型が閉じていることで、kernel の `addDecl` 事実）。名前付き環境条件の提案（未提出）。DG-ENV の `EnvTypesFVarFree` に「閉じている」を足す案もあるが、それは既存前提の文の変更なので reviewer 判断 | **残る / 名前付き条件**（DG-ENV 側）。提案 `SigTyPh`（+1） |
| r2 `LowerLooseRangeEq` / r3 `ZeroLitRange0` | `ShippingN3ExternAgree.lean` | — | readF は `lowerLooseBVars` / `zeroLit` を呼ばない（§0 の 1 点目）。この trace では使わない | 払う対象なし |

**まとめ**: N3 の bridge（r1/r2/r3）は、この道筋の range 条件を**直接は払わない**（r1 は `(0,1)` 半分、r2/r3 は対象外）。払うのは既存の T1L-50 `LiftAgrees`（lift）と T1L-52 `RootFloatAgrees`（rootFloat。統合後は T1L-50 に帰着）、証明済みの `bundleIotaRange`。新しいのは、(a) `Inst1Range` を等式 A4 に付け替える案（trace が要る Ph 版を出すため）、(b) 名前付き環境条件 `SigTyPh`。どちらも reviewer 提出前で、Lean に置かない。

## 3. GENDATA_COVER_SURVEY §6.2 の L1 の純差分（N3 後の値で見直し）

N3 前の見積（b68e83bd §6.2）: 減る行 C.CV-2（`LetsNoLoose`）、C.CV-3（`FullInv` / `FReachC`）の 2。増える行は操作ごとの対応前提 5（`RootFloatPh`、`LiftPh`、`Inst1Ph`、`BundleIotaPh`、`SigTyPh`）。純差分 -3。

N3 後（この rev5 の読み取りによる見積。台帳そのものを再計数してはいない）:
* 減る行: C.CV-2、C.CV-3 の 2（`TraceGood` が `TrInv`、すなわち `LetsNoLoose` と `FullInv`/`FReachC` を供給する、という前提。U-R12 まで繋がって初めて成立。`hnl` の `Expr.hasLooseBVars` extern 側は `NoLoose` の帰納に置き換わり、reader の外の `LetsNoLoose` 供給が別に残るかは**未確認**）。
* 増える行: `RootFloatPh` → 新規なし（既存 T1L-52 に帰着、統合後は T1L-50）、`LiftPh` → 新規なし（既存 T1L-50 に帰着、構造的補題）、`BundleIotaPh` → 新規なし（`bundleIotaRange` が証明済み、構造的補題）、`Inst1Ph` → **A4 採用なら T1L-51 の付け替えで ±0、不採用なら +1**、`SigTyPh` → **+1**（環境条件）。
* 純差分（見込み）: A4 採用で 2 − 1 = **+1**、A4 不採用で 2 − 2 = **0**。N3 前の -3 から改善した主因は、Ph 版の `RootFloat/Lift/BundleIota` が**新しい前提でなく既存前提 + 構造的補題**に落ちる点（N3 前の見積は各々を 1 行と数えていた）。
* 未確認で数字が動き得る点: (1) `InstSFieldsDet`（U-R8、`GroupsPh` 用）が新しい前提を要するか。(2) `machReserve` / `bindLetAlias` の reach 補題が前提なしで証明できるか。(3) C.CV-2 と C.CV-3 が 2 行として別個に消えるか（U-R12 を調べていない）。(4) DG-ENV 側に `SigTyPh` を吸収できるか。(5) ptot-m4 を統合するとき T1L-52 が消えること（これは ptot 側の台帳）。
* 台帳: FG 102 / T1 54（今回 FG -0 +0 / T1 -0 +0）。上は見込みで、台帳の数は変えていない。

## 4. 最初の Lean 単位 U-R4a の完全な型（新規 `Tools/ShippingGen5ReaderTraceApp.lean`、namespace `Tools.ShippingGen5ReaderTrace`）

Imports: `Tools.ShippingGen5ReaderTraceChain`。`set_option autoImplicit false`。Opens: `Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv`。`lakefile.lean`: `lean_lib` をファイルと Check にそれぞれ 1 つ追加（追加のみ）。既存の Lean ファイル（共有定義、`Elab*.lean`、`ShippingGen5Cover*`、`ShippingReaderFuelDefs`、`ShippingLetsReaderInv*`、`Tools/Assume/*`、`T1Hyp*`）は編集しない。

```lean
theorem exprPh_slot {senv : StructEnv} {nDecl : Nat} {st : MachRead} {d i : Nat}
    (hTr : TrInv senv nDecl st) (hi : i < st.kinds.size) :
    FReachC nDecl st st ∧ ExprPh senv nDecl d (machSlot i, st)

theorem conv_app_bareFound_trace (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (dom α init x : Lean.Expr)
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x))
    (hgate : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false)
    (e0 : Lean.Expr) (k : Nat)
    (hfind : st.bareRegs.find? (·.1 == Lean.Expr.app f a) = some (e0, k))
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

theorem conv_app_loopRead_trace (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (i : Nat) (hl : machLoopRead? env d (.app f a) = some i)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v

theorem conv_app_readV_trace (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (hrun : machRunApp? (.app f a) = none)
    (hic : machInstCall? senv (.app f a) = none)
    (hics : machInstCallS? senv (.app f a) = none)
    (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none)
    (i : Nat) (hr : machReadV env d (.app f a) = some i)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
```
* `exprPh_slot` の証明概略: `FReachC.refl st`、`TrInv` はそのまま、`inRange_machSlot hi`、`NoLoose d (machSlot i)` は `noLoose_fvar`（`machSlot i` は `.fvar` なので `fun _ h => h.elim`）。
* `conv_app_bareFound_trace`: `hgate` で最初の `if` を落とし、`hfind` で `st.bareRegs.find? … = some (_, k)` の arm に入る。`simp [convStep, hreg, hgate, hfind, okO, run_pure]` で `v = (machSlot k, st)`。`k < st.kinds.size` は `hpre.2.1.2.2.1`（`TrInv` の `CtlPh` の `bareRegs` 節）に `Array.find?` のメンバシップ補題を当てる。`exprPh_slot` で閉じる。
* `conv_app_loopRead_trace` / `conv_app_readV_trace`: arm は `FM.pure (if i < st.kinds.size then some (machSlot i, st) else none)`。`hv` が `some (some v)` なので `i < st.kinds.size`（`split_ifs` で偽側は `some none ≠ some (some v)`）、`exprPh_slot`。`hpre` は `TrInv` だけを使う。
* どの補題も `hT` / `hstep` / `PureFacts` / extern 事実を取らない。`n` は `hv` の燃料で、結論に現れない（`readF` の表を渡すだけ）。
* 「match の判別式が当たらない arm」は別補題で扱う（U-R4b 以降、U-R11 の組み立て）。

### Check（新規 `Tests/Gen5/ReaderTraceAppCheck.lean`。`ReaderTraceChainCheck` / REV4 §3 と同じ要件）
* **TYPE**: §4 の 4 定理それぞれを `checkExpected`（`Tests/Gen3/ExpectedType.lean`）で、own spelling の独立な `Exp…` と比べる。1 宣言 = 1 件。
* **MUTANT**（well-typed な単一変更のみ。signature / defeq での棄却で、意味的反例ではない。数は測定値を書く）: `exprPh_slot` の `hi` 無し、結論から `FReachC` / `ExprPh` を落とす、`st` ↦ `{ st with … }` の別状態、`d` ↦ `d+1`; `bareFound` の `hgate` を `= true`、`hfind` を `none`、`hreg` を落とす; `loopRead` の `hreg` を `some`; `readV` の判別式 1 つを落とす、`hr` を `machLoopRead?` に取り替える; 各定理で結論の `PhPost` を落とす。型が通らない変更は数えない。
* **AXIOMS**: `collectAxioms` が `propext / Classical.choice / Quot.sound` のみ。
* **CLOSURE**: 全 4 宣言を root にした value-closure walk、`seen` に全部入ることを assert。禁止 root（`sorryAx / ofReduceBool / trustCompiler`）の自己ヒット対照、未知 root / helper の対照と clean 対照、`withoutModifyingEnv` 内の負例。意図した `sorry` 負例だけが `sorry` で、その数をヘッダーに観測値で書く。
* ソースに `sorry` / `axiom` / `native_decide` なし。
* ビルド: `kjob lake build Tools.ShippingGen5ReaderTraceApp`、次に `Tests.Gen5.ReaderTraceAppCheck`、1 つずつ。ログはソースツリーの外。成功 SHA はヘッダーにコメントだけのコミットで反映。Lean コミット後は Issue を `doing` のままにして「clean build は coder」と note に書く。

## 5. この rev5 が主張しないこと

* `TraceGood senv nDecl (readF senv n)` の成立、`hstep` の全 arm、`ShapeInputs`、R-in / R-nl / R-dom の readF 呼び出し側、実 run / FG。
* §2 の A4 / `SigTyPh` が正しい（真である）こと。A4 の C++ 側は N3 設計の読み取りであって形式証明ではなく、既知の限界（`unsigned` 切り捨て、実行バイナリがその source から作られていること）も N3 と同じ。
* U-R4a〜U-R12 の型が elaborate すること（U-R4a の型も未 elaborate。通らない箇所は addendum で直す）。
* 台帳の数の変更。FG 102 / T1 54（今回 FG -0 +0 / T1 -0 +0）のまま。
* 新しい law / TRUSTED 境界 / コンパイラ・共有定義の変更 / FG の縮小 / `GenWF` の強化はこの rev5 に含まれない。ユーザー判断が要る点は見つかっていない（`decision` なし）。
