# 前提台帳 B_M4（gate-supply / fallback-supply / parametric-supply / fg-assembly / routes）

凡例: 「Defs」=`Tools/ShippingGen2Defs.lean` 、「d0ddc50b」= 作業 worktree の HEAD。`Defs`・`ShippingInlineSoundness.lean`・`ShippingChildCacheA.lean` は gate の 59b68658 と d0ddc50b でバイト同一（md5 一致を確認）。fallback の 4519e2fb の Defs は S1 取込み版（`InstClosed` と `ShipsRes` の第3連言、`TopShips` の rst/clk 条件が d0ddc50b と異なる）。分類語: TRUSTED境界 / 入力条件 / 未供給の義務。mutant の棄却は signature/defeq 棄却であり意味的反例ではない（各 Check の記述どおり）。`ReflectsAll` は GENERAL_SPEC §1.1 の schema 名で、Lean 定義はこの調査では見つからなかった。

## 0. Issue ごとの最新 approved note（履歴 $S/h/*.json）

| Issue | 最新 approved の対象SHA（branch） | 検証 | 残り（原文要旨） | 後続 note |
|---|---|---|---|---|
| sparkle-gen4-routes | par/gen4-gate `1fdbc18d..eb23ed1b`、build 対象 aacd07ec（seq 2379 scoped approved）、census は par/gen2-spec 35e6d4a7（seq 2352）。seq 2383 done | g4gl-aacd07ec exit0 720 jobs、`gate_combChildRunN` `gate_childFn_roundTrip`、pick instance | EntryDefines と RealChildA は明示の未供給前提のまま（run 存在なし）。`o.lo/o.width=0` は再利用不可。route 別 T1Hyp / Pkg / ShipsRes / cache 接続は未完。G-ONEOUT CallDec probe は sparkle-gen4-oneout-probe へ移管 | done（seq 2383） |
| sparkle-gen4-gate-supply | kjob/g4gate-g3c `59b68658`（seq 4578 approved：U-G3 FirstLeaf）。それ以前: 103f5ae9（seq 4289, U-G2/U-G2a 監査修正）、d88f3a6d（seq 3500, U-G2 freeze）、ee4ad704→601bbecb（U-G1） | g3cv-59b68658 exit0 767 jobs、TYPE10 MUTANT9 AX8 標準 | entry/RealChildA/Q/正幅は前提。route1 全 coverage・run 存在・Top・instance parent・M4/FG は未完 | seq 4644 approved は U-G7a の freeze（文書のみ）。seq 5008 doing: kjob/g4gate-g5 `1e141f26`（Lean 76a8d731）で T1+InstCore は incremental build exit0（clean ではない）、T2 `instParent_childShipsI` は凍結文が `Design` の2 field のため elaborate 不能で停止、reviewer 判断待ち。Issue state は managerctl で `decision` |
| sparkle-gen4-fallback-supply | kjob/g4fb-fb25 `4519e2fb`（seq 5529 approved：FB-22） | fb25v-4519e2fb exit0 814 jobs、TYPE3 MUTANT14 AX3 標準 sorry0 | EntryDefines/WF/hS の供給、instance・非fragment、T-LEG/T-MEMO/K4/M4/FG 未供給 | seq 5568 todo: 「前提台帳で選ばれた時に再開」、header 同期（fb25v）未 |
| sparkle-gen4-parametric-supply | kjob/g4par-r21 `0ebbddc0`（seq 5339 approved：F2 specExprM）。以降 unit6 freeze 99f322ce は approved（seq 5358）、unit6 F3 の承認 SHA = 50d22e3b（kjob/g4par-r23）、承認イベント = seq 5604。Lean 本体と clean build の根拠 = 261a2b3c（par23v-261a2b3c exit 0, 708 jobs, dirty=false）/ seq 5599（これは承認ではなく review 提出。seq 5601 で NOT BUILT コメントの差し戻し）。50d22e3b との差は Tools/Check 先頭コメント 2 行のみ | par21w exit0 230 jobs | B1-B4・production specializeExpr 対応・T/FG 未供給 | seq 5604 approved 後、台帳待ちで一時停止（seq 5614 時点の最新記録）。残り B1-B3/T/FG |
| sparkle-gen4-fg-assembly | なし。履歴は created（seq 2627）と dependencies（seq 2639）のみ。branch もこの調査では見つからなかった。`managerctl show`: state=todo、依存 sparkle-gen3-t1-assembly(doing) / gate-supply(decision) / fallback-supply(todo) / parametric-supply(doing) | — | — | — |

## 1. sparkle-gen4-routes（census ＋ 限定 gate leaf producer）

残っている仮説（binder）は、`gate_combChildRunN` / `gate_childFn_roundTrip`（par/gen4-gate aacd07ec、同一文が kjob/g4gate-g3c 59b68658 の `Tools/ShippingGen4GateLeaf.lean:221, :350` に移送済み）の `entry` `old` `peel` `he` `hb` `hv` `h : RealChildA`。これらは §2 の G-1〜G-7 と同一の前提なので、そちらに書く。census（ROUTE_CENSUS.md rev2）は文書で、Lean の前提を追加していない。

census / done note が明示している未供給（前提ではなく義務）: route-indexed T1Hyp（`T1Hyp.defines/closed` が gate 子を除外、amendment 未適用）、`Pkg`/`ShipsRes`/cache 接続、G-ONEOUT の CallDec 名（`instFields.getD k ""` と callee 出力名 `out` の不一致、probe は sparkle-gen4-oneout-probe でこの調査では結果を読んでいない）。

## 2. sparkle-gen4-gate-supply（kjob/g4gate-g3c 59b68658、承認済み範囲）

承認済み主要定理（すべて `Tools/` 下、59b68658）: `gateLeaf_childShips`（ShippingGen4GateIface.lean:74）、`gateLeaf_shipsResI`（:85）、`gateLeaf_shipsResI_of_real`（:90）、`gateLeaf_outTy`（ShippingGen4GateOutTy.lean）、`gateLeaf_childPortWidthsI`（ShippingGen4GatePortW.lean）、`gate_combChildRunN`/`gate_childFn_roundTrip`（ShippingGen4GateLeaf.lean:221/:350）、`combChildRunN_of_fnR`（ShippingGen4FirstLeaf.lean:55）、`firstLeaf_childShips`（:157）、`firstLeaf_shipsResI`（:172）、`firstLeaf_shipsResI_of_real`（:177）、`firstLeaf_childPortWidthsI`（:183）。U-G1 の `ChildIface`/`ChildShipsI`/`ShipsResI`（ShippingGen4Iface.lean）は前提を持たない定義と同値補題。

### G-1 前提: `entry`（gate 版）
- **Lean名（binder名）**: `entry`
- **完全な型**: `EntryDefines mctx mref cctx cref g.decl g.value`（`gate_combChildRunN`/`gate_childFn_roundTrip` では `EntryDefines mctx mref cctx cref c value`）。`EntryDefines` の定義（d0ddc50b `Tools/ShippingInlineSoundness.lean:48`）:
```lean
def EntryDefines (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (v : Lean.Expr) : Prop :=
  ∀ w1 ci w2 w5 envR w6,
    RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    ∃ d : DefinitionVal,
      entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR) = .defnInfo d ∧
        d.value = v
```
- **仮定している定理名と branch@SHA**: `gateLeaf_childShips`、`gateLeaf_shipsResI_of_real`、`gateLeaf_outTy`、`gateLeaf_childPortWidthsI`、`gate_combChildRunN`、`gate_childFn_roundTrip`（kjob/g4gate-g3c@59b68658；`gate_*` の元は par/gen4-gate@aacd07ec/eb23ed1b）。
- **FG/T1 のどこに効くか**: GENERAL_SPEC §1.1 の `ReflectsAll`（gate route の宣言ごとの反射）。`T1Hyp.defines`（G3-SHAPE）の gate 版に相当する位置だが、gate 用のフィールドは `T1Hyp` に無い（census seq 2342「T1Hyp.defines/closed exclude gate children」）。
- **別名・別Issue**: first-gate では `EntryDefines … (quoteDecl f.dn f.names f.n f.fe)`（G-8、FirstLeaf 版）。fallback FB-21/FB-22 に同名 `entry`（F-6）。GateDefines（`Tools/ShippingGateDefines.lean:72`、WRITTEN NOT BUILT）は同種の反射 Prop で、U-G7 の前提調査対象（freeze Q1: 「supplier 未発見と新TRUSTEDの必要性を区別。採用は別決定」）。
- **支払い予定のIssue**: 未割当。
- **実runから払えそうか**: 不明。履歴（seq 2379, 3500, 4376, 4578）は「entry は仮説。どのテストも供給していない」。`EntryDefines.of_env`（ShippingInlineSoundness.lean 内）が `EnvDefines` と gate 受理から作る補題として存在するが、gate 版の供給 theorem はこの調査では見つからなかった。
- **分類**: 未供給の義務（反射 premise）。

### G-2 前提: `h : RealChildA`
- **Lean名**: `h`（`hchild` ではなく run 証拠）
- **完全な型**: `RealChildA O g.decl y`。定義（d0ddc50b `Tools/ShippingChildCacheA.lean:105`）:
```lean
inductive RealChildA (O : RefLawsAOps Fresh mref cref) : Name → Res → Prop
  | run {c : Name} {r : Res} (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld)
      (adm : AdmCtx O.quiet mctx cctx)
      (cache : ∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r')
      (synth : sv w = some synthesizeChild)
      (quiet : O.quiet w)
      (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w') : RealChildA O c r
```
- **仮定している定理名**: G-1 と同じ全定理＋`firstLeaf_*`（59b68658）。
- **効く場所**: `ShipsRes L P c r` の第1連言（Defs:135）。run そのもの（Start/IHAt が与える「過去の実 run」）で、FG の ∀ binder `w b D w'` と run 仮定 `RunsTo (synthesizeCombinational declName) …` 側。
- **別名**: fallback では `hr : RunsTo (synthesizeCombinational declName) …`（F-5）として現れる。
- **支払い予定**: T1 側 IH（`IHAt`/`ShipsRes`）の領域。T1 台帳を参照。
- **実runから払えそうか**: はい（`IHAt` の定義上 `RealChildA` は成功 run から作られる; Defs:166-170）。run の存在そのものは前提（census: 「no run existence claim」seq 2379）。
- **分類**: 入力条件。

### G-3 前提: `GateLeaf.old`
- **Lean名**: `g.old`（`gate_combChildRunN` では `old`）
- **完全な型**: `∀ d : Lean.DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none`（ShippingGen4GateIface.lean 構造体 `GateLeaf` のフィールド、:30 以降）
- **仮定している定理名**: G-1 の gate 系全定理（kjob/g4gate-g3c@59b68658）。first-gate 系（`firstLeaf_*`）は `old` を持たない（U-G3）。
- **効く場所**: `ReflectsAll`（gate route）の「旧 first gate が受理しない」部分。
- **別名**: route 1 では偽（first-gate 宣言では `old` が成り立たない: GATE_SUPPLY_FREEZE §0.1, rev1 R3）。
- **支払い予定**: 未割当。
- **実runから払えそうか**: 不明。`GateDefines` の `certifiedShape? false [] (.defnInfo dv) = none` 連言が同内容（`Tools/ShippingGateDefines.lean:72`）。供給 theorem はこの調査では見つからなかった。
- **分類**: 未供給の義務（反射）。

### G-4 前提: `GateLeaf.peel`
- **完全な型**: `mixedGatePeel value = some (bs, quote domE (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e)`（同 `GateLeaf` フィールド; `gate_combChildRunN` では `Tools.ShippingUnifiedSource.quote dom …`）
- **仮定している定理**: G-1 と同じ gate 系。**効く場所**: `ReflectsAll`（gate route）。**別名**: `GateDefines` の `mixedCertifiedShape? … = some (bs, body)`。**支払い予定**: 未割当。**実runから払えそうか**: 不明（供給元はこの調査では見つからなかった）。**分類**: 未供給の義務（反射）。

### G-5 前提: `GateLeaf.he`
- **完全な型**: `e.WF kb kv vw`。**仮定している定理**: G-1 の gate 系。**効く場所**: `ReflectsAll`。**支払い予定**: 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務。

### G-6 前提: `GateLeaf.hb` / `GateLeaf.hv`（2フィールド）
- **完全な型**: `hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool)`、`hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))`。
- **仮定している定理**: G-1 の gate 系。**効く場所**: `ReflectsAll`。**支払い予定**: 未割当。**実runから払えそうか**: 不明。ただし pick の個別インスタンスでは `old/peel/he/hb/hv` が供給済み（Tests/Gen4/GateLeafInstance.lean, aacd07ec; seq 2377）。ここでの「供給」は1宣言 pick のみで一般 ∀ 宣言ではない。**分類**: 未供給の義務。

### G-7 前提: `hw1 : g.srt.width ≠ 1`
- **Lean名**: `hw1`（`gateLeaf_outTy`、ShippingGen4GateOutTy.lean）。**完全な型**: `g.srt.width ≠ 1`。
- **効く場所**: 出力型 `out : bitVector w` の確定（`ChildIface.outsC` の型）。width 1 の供給元はファイル header に「Width 1: no supplier found in this survey (OPEN)」。
- **支払い予定**: 未割当（seq 3500「幅1は未供給義務として調査継続」）。**実runから払えそうか**: 幅≠1 側は `gate_full_outputs`（`Tools.ShippingGateKid.gate_full_outputs`）で供給。幅1は不明。**分類**: 未供給の義務。

### G-8 前提: `FirstLeaf` のデータ＋`entry`（first-gate 版）
- **Lean名**: `f.hwf`, `f.hn`, `entry`
- **完全な型**: `hwf : fe.WF names.length n`、`hn : 0 < n`（`structure FirstLeaf`、ShippingGen4FirstLeaf.lean:37）、`entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe)`。`FExpr.WF`（4519e2fb `Tools/ShippingEntrySoundness.lean:1161`）: `| .inp j => j < k | .lit v => v < 2 ^ n | .bin _ a b => a.WF k n ∧ b.WF k n`。
- **仮定している定理**: `firstLeaf_childShips` `firstLeaf_shipsResI_of_real` `firstLeaf_childPortWidthsI`（kjob/g4gate-g3c@59b68658）。
- **効く場所**: `ReflectsAll`（gate route / first gate）。**別名**: fallback FB-21/22 の `hwf` `hn` `entry`（F-6/F-7）。
- **支払い予定**: 未割当。**実runから払えそうか**: 不明（freeze/履歴は「entry/RealChildA/Q/正幅は前提」seq 4578）。**分類**: 未供給の義務。

### G-9 前提: `Q`（route table）と `hQ`
- **Lean名**: `Q`, `hQ`
- **完全な型**: `Q : IfaceMap ι`（`abbrev IfaceMap (ι : Type) := Name → Option (ChildIface ι)`、ShippingGen4Iface.lean）、`hQ : Q g.decl = some (g.ifaceOf ty)`（`gateLeaf_shipsResI`）／`Q f.decl = some f.ifaceOf`（`firstLeaf_shipsResI`）／`hQ : ∀ ty : HWType, y.1.outputs = [{ name := "out", ty := ty }] → Q g.decl = some (g.ifaceOf ty)`（`gateLeaf_shipsResI_of_real`）。
- **効く場所**: FG の `Pk declName = some p`／`T1Hyp.pkg`（G3-GEN）の route-agnostic 版（`ShipsResI` の `Q c = some I`）。
- **別名**: `Pkgs`／`Pkgs.iface`（`shipsResI_iface` で `ShipsRes` と同値）。
- **支払い予定**: 未割当（theorem 内コメントは「Q の supplier は route table の assembler」。assembler の Issue は sparkle-gen4-fg-assembly だが、その Issue の履歴にはこの記述は無い）。
- **実runから払えそうか**: 不明。**分類**: 入力条件（これを組み立てる側が未供給）。

### G-10 U-G7a（instance 付き gate 親）— 未承認
kjob/g4gate-g5 `1e141f26`（Lean 76a8d731）。承認されたのは freeze rev1（9bd402a2, seq 4644）のみで、Lean 実装は reviewer 未 review。`instParent_combChildRunN`（ShippingGen4InstParent.lean:234）の binder: `hcore : InstCore m c bsP sel wOut`（7 field の Prop 構造体）、`hcallee : ∀ dsn, (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) → moduleByName dsn.modules c.name = some c → CombChildRunN (childMap dsn.modules) dsn k c bsC [GateLeaf.outField (.bitVector wOut)] SC`、`hsel : ∀ vals T, (∀ τ<T, InRange (vals τ) (bsP.filter fun b => b.2 != .domain)) → ∀ τ<T, InRange (selArgs sel vals τ) (bsC.filter fun b => b.2 != .domain)`。履歴残り: 「leaf noClk の供給元は未確認」「entry/RealChildA/Q、n>0 未供給」「Q1: supplier 未発見と新TRUSTED必要性は別」。支払い予定: 未割当。分類: 未供給の義務。承認前のため FG への対応は記録しない。

## 3. sparkle-gen4-fallback-supply（kjob/g4fb-fb25 4519e2fb）

承認済みの主要定理（4519e2fb, `Tools/ShippingGen4Fb*.lean`）: 保持系 `tFin_stop`（FbFin.lean:22）、`a4_inv_tail_fin`（:35）、`tFin0_of_r4RunInvT`/`a4_inv_tail_fin0`（FbFin0）、`a4_machine_or_R4Run`（FbR4.lean:104）、`a4_inv_machine_or_R4RunInv`（FbInv.lean:242）、`a4_inv_side_or_tail`/`a4_inv_tail_fin0_both`（FbMachInv）、`legacyTail_keepsInv`（FbTailInv.lean:82）、`legacyTail_hit_or_miss`/`r4RunInvT_tail_hit_or_miss`（FbSplit）、`machineAttempt_keepsInv` `core_reads_link4Inv`（FbInv）；後処理系 `synthesizeCombinational_ppRel`/`_lookup`（FbPPRun）、`ppRel_*`（FbPP, FbPPLookup）、`childRunN_dz_instFree`/`_postReady`（FbDzRun）、`postReady_instFree`/`synthesizeCombinational_fragment_dz`（FbFrag）、`runModule_assigns_exists`/`combChildRunN_of_childFnR`/`synthesizeCombinational_fragment_childRunN`（FbFragRun.lean）。

### F-1 前提: `hC : ChildKeepsInv L P Reach (D + 1)`（D=0 の Fin0 系は `ChildKeepsInv L P Reach 1`）
- **完全な型**: d0ddc50b Defs:182 `def ChildKeepsInv … : Prop := Tools.ShippingChildFrontCP.ChildSynthA L.O (InvAt L P Reach D)`、`ChildSynthA`（`Tools/ShippingChildFrontCP.lean:240`）: `∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ c, Keeps mctx mref cctx cref I (synthesizeChild c)`。`Keeps`（`Tools/ShippingChildInv.lean:315`）: `∀ w, I w → I (endW mctx mref cctx cref m w) ∧ ErrOk mctx mref cctx cref m w`。
- **仮定している定理**: `tFin_stop` `a4_inv_tail_fin` `a4_inv_tail_fin0` `a4_inv_machine_or_R4RunInv` `a4_inv_side_or_tail` `a4_inv_tail_fin0_both` `a4_inv_tail_machine_or_R4RunInvT` `legacyTail_keepsInv` `machineAttempt_keepsInv`（kjob/g4fb-fb25@4519e2fb）。
- **効く場所**: 帰納法の IH（M3/T1 側）。T1 台帳を参照。
- **分類**: T1 台帳を参照（`KeepChildStmt`、Defs:192 が供給文）。

### F-2 前提: `hI : InvAt L P Reach D w`、`hA : AdmCtx L.O.quiet mctx cctx`、`entry : MachineDefines …`（machine 側）
- 上記 F-1 の定理群が共通に取る。`InvAt` は Defs:158、`AdmCtx` は `Tools/ShippingChildInvA.lean:77`、`MachineDefines` は `Tools/ShippingMachineEntry.lean:2345`（`T1Hyp.defines` が与える形）。**T1 台帳を参照**。

### F-3 前提: `L : Laws`（`legacyTail_keepsInv` 等）
- `legacyTail_keeps_generic`（FbTailInv.lean:42）は個別に `hS : StableA O.quiet I`, `TLam : LamTelescopeLawA O.quiet mref cref`, `TF : ForallTelescopeLawA O.quiet`, `htr : RecA O I translate` を binder に持つ。`legacyTail_keepsInv`（:82）は `L.T`（`Laws.T : RefLawsATele O.quiet mref cref`）から供給する形。`Laws` は FG の ∀ binder 自体。T1 台帳を参照。

### F-4 前提: `hS`（FB-22）— package の `S` と `firstFn` の対応
- **Lean名**: `hS`
- **完全な型**（`synthesizeCombinational_fragment_childRunN`、Tools/ShippingGen4FbFragRun.lean）:
```lean
(hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j))
```
`combChildRunN_of_childFnR` では同形で `F` を使う: `hS : ∀ vals f, (S vals)[0]? = some f → ∀ j, InRange (vals j) (bsC.filter fun b => b.2 != .domain) → f j = F (vals j)`。
- **仮定している定理**: `synthesizeCombinational_fragment_childRunN`、`combChildRunN_of_childFnR`（kjob/g4fb-fb25@4519e2fb）。
- **効く場所**: `ChildShips q n mc Dc` の `q.S`（Defs:87）と実モジュールの関数の一致。FG では `Pk declName = some p` の source package `S` に対応（`T1Hyp.pkg`/`CallDec` 経由）。
- **別名・同じ前提**: gate の `gateS`（`ShippingGen4GateLeaf.lean:189`）は同じ役割を定義側で持つ（`ChildIface.S := fun _ => gateS …`）ので、gate 側にはこの `hS` 型の仮説が現れない。
- **支払い予定**: 未割当（seq 5568: 「前提台帳で支払い先に割り当てられたとき再開」）。
- **実runから払えそうか**: 不明（履歴 seq 5529「S の hS 対応は未供給」）。
- **分類**: 未供給の義務。

### F-5 前提: run `hr` / `h`
- `synthesizeCombinational_ppRel`/`_lookup`、`synthesizeCombinational_fragment_childRunN`（`hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (b, design) w'`）、`synthesizeCombinational_fragment_dz`（`h`）、`core_reads_link4Inv` ほか `hr : RunsTo (synthesizeCombinationalCore declName [] false) …`。FG の run 仮定そのもの。分類: 入力条件。

### F-6 前提: `entry`（first-gate fragment）
- **完全な型**: `Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName (Tools.ShippingEntrySoundness.quoteDecl dn names n fe)`（EntryDefines の全文は G-1）。
- **仮定している定理**: `synthesizeCombinational_fragment_dz`（FbFrag.lean）、`synthesizeCombinational_fragment_childRunN`（FbFragRun.lean）（kjob/g4fb-fb25@4519e2fb）。
- **別名**: gate の G-8 の `entry`（同型）。**支払い予定**: 未割当。**実runから払えそうか**: 不明（seq 5174, 5529「EntryDefines/WF は前提」）。**分類**: 未供給の義務。

### F-7 前提: `hwf : fe.WF names.length n`、`hn : 0 < n`
- 型は G-8 と同じ。**仮定している定理**: F-6 と同じ2定理。**別名**: gate G-8 の `f.hwf` `f.hn`。**支払い予定**: 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務。

### F-8 前提: 実 run が走った core モジュールの `ChildRunN`（clean-up 輸送の入力）
- `childRunN_dz_instFree`（FbDzRun.lean:17）の `h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S`（＋ `hbody hin hout hwe : out.body = raw.body ∧ …`、`hf : instFree raw.body`）、`childRunN_dz_postReady`（:75）の `h` と `hpr : PostReady raw k`、`hk : 0 < k`、`synthesizeCombinational_fragment_dz` の結論内含意の前提 `0 < n → M' = dropZeroWidthModule M → … → ChildRunN … M … → ChildRunN … M' …`。`PostReady` は 4519e2fb `Tools/ShippingEntrySoundness.lean:636`。
- 履歴: 「core M の ChildRunN は明示前提」（seq 5231）。first-gate fragment では FB-22 が `ChildRunN … b` を直接生成（F-4 の条件付き）。fragment 以外の core `ChildRunN` の供給元はこの調査では見つからなかった。
- **支払い予定**: 未割当。**分類**: 未供給の義務。

### F-9 前提ではなく履歴が未供給と書いたもの（theorem は存在しない）
instance あり body、非 fragment の `mergeChecked`、T-LEG、T-MEMO、K4、depth0 T-FIN の A4MachineSideA 側（FB-11 後に FB-13 で同一 witness 版）、memo law。各 theorem はこの調査では見つからなかった。

## 4. sparkle-gen4-parametric-supply（kjob/g4par-r21 0ebbddc0 ＋ 承認済み unit6 F3 50d22e3b）

承認済み: I1/I2/I3a/I3b/I5a（`Tools/ShippingGen4ParamEntry.lean`, 8acc71dd）、I3c/I4-struct/interface 定義（`ParamKeeps.lean`/`ParamIface.lean`, 41ad0be7, seq 3620 scoped approved）、Layer A 純粋モデル（0d932e22）、ParamBridgeShape C1-C3（2f421f4f）、Compose D1（40bc5ec0）、Width E1（d7892ef6）、SpecType F1（10e7df1e）、SpecExpr F2（0ebbddc0）。unit6 F3 `ParamBridgeLegal`: freeze 99f322ce は seq 5358 で approved。実装の承認 SHA = 50d22e3b、承認イベント = seq 5604。Lean 本文と clean build の根拠 = 261a2b3c / seq 5599（par23v-261a2b3c exit 0, 708 jobs, dirty=false。seq 5599 は review 提出であり承認ではない。seq 5601 の差し戻し＝NOT BUILT コメントの同期指摘の後、コメントのみの子 SHA 50d22e3b が seq 5604 で承認された）。261a2b3c と 50d22e3b の差は Tools/Check 先頭コメント 2 行（各ファイル 1 行）のみで、Lean 本体は同一。

### P-1 前提: `AllPos θ`
- **完全な型**: `def AllPos (θ : Binding) : Prop := ∀ p ∈ θ, 0 < p.2`（0ebbddc0 `Tools/ShippingGen4ParamLayerA.lean`, 約:44）。`Binding := List (String × Nat)`。
- **仮定している定理**: `evalM_pos`（LayerA:102）, `evalM_nonneg`（:134）, `hwTypeFromDim_width_ok`（ParamBridgeWidth.lean:14）, `startLength_node_ordered`（ParamBridgeCompose.lean:26）, `specTypeM_ok`（SpecType:44）, `specTypeM_hwTypeFromDim`（:59）, `specExprM_ok`（SpecExpr:159）, `specExprM_ok_aux`（:64）（いずれも kjob/g4par-r21@0ebbddc0）。
- **効く場所**: 並列の FG（`synthesizeCombinationalWithParameters` 側 disjunct）の特殊化成功条件 `SpecSuccessAllPositive`（ParamIface.lean:106）。FG schema の ∀ binder `parameters`、`ReflectsAll`（parametric route）側。
- **別名**: `legalBinding_allPos`（unit6 F3, 承認 SHA 50d22e3b・seq 5604 / 本文・clean build 根拠 261a2b3c・seq 5599）が `LegalBinding D θ → AllPos θ`（P-8 を参照）。
- **支払い予定**: 未割当。履歴 seq 3648/5358: 「B1-B3/T/FG 未供給」。
- **実runから払えそうか**: 不明。`specializeDesign_ok_legal`（ParamIface.lean:122, 承認済み）は「成功した特殊化は `LegalBinding` を満たす」を与えるが、`LegalBinding → AllPos` は unit6 F3 の承認済み定理 `legalBinding_allPos`。したがって AllPos θ は条件付き（`LegalBinding D θ` を仮定して）導出できる。`LegalBinding` 自体を実 run から払う経路はこの調査では見つからなかった（P-8）。基準件数 146/110 は書き換えない。
- **分類**: 未供給の義務（Layer A のモデル側条件）。

### P-2 前提: `Bound θ d`、`PosDim d`、`NonNegDim s`、`SliceOK hi lo`
- **完全な型**（0ebbddc0 LayerA）:
```lean
def Bound (θ : Binding) : DimExpr → Prop
  | .literal _ => True
  | .parameter n => ∃ v, θ.lookup n = some v
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .pow a b | .min a b | .max a b => Bound θ a ∧ Bound θ b
  | .clog2 a => Bound θ a
def PosDim : DimExpr → Prop
  | .literal c => 0 < c
  | .parameter _ => True
  | .add a b | .mul a b | .pow a b | .min a b | .max a b => PosDim a ∧ PosDim b
  | .sub .. | .div .. | .mod .. | .clog2 _ => False
def NonNegDim (e : DimExpr) : Prop := e = .literal 0 ∨ PosDim e
def SliceOK (hi lo : DimExpr) : Prop :=
  ∃ s l, lo = s ∧ hi = DimExpr.mkSub (DimExpr.mkAdd s l) (.literal 1) ∧ NonNegDim s ∧ PosDim l
```
- **仮定している定理**: P-1 の定理群（`hp : PosDim d` `hb : Bound θ d` `hs : NonNegDim s` `hl : PosDim l`）、`makeSliceExpr_sliceOK`（Shape:17, `h : SliceOK hi lo`）、`sliceOK_order`（LayerA:141）。
- **効く場所**: 同 P-1。`PosDim` が `.sub/.div/.mod/.clog2` を False にするため、これらを含む宣言は条件の外（決定資料 §3.1/3.4: `W / 2` は W=1 で特殊化が `.error` を返した観察、kernel 反例ではない）。
- **支払い予定**: 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務。

### P-3 前提: `ExprOK θ e`、`TyPos t` / `TyBound θ t`
- **完全な型**: `ExprOK`（SpecExpr、mutual。`.sliceDim expression hi lo => SliceOK hi lo ∧ Bound θ hi ∧ Bound θ lo ∧ ExprOK θ expression`、`.op/.concat` は `ExprsOK θ arguments`、`.index` は両方、`.const/.ref` は True、`.slice` は `ExprOK θ expression`）、`TyPos`（`.bitVectorDim d => PosDim d`、`.array _ e => TyPos e`、`.bit/.bitVector _ => True`）、`TyBound`（`.bitVectorDim d => Bound θ d`、他同様）。
- **仮定している定理**: `specExprM_ok`（`hok : ExprOK θ e`）、`specTypeM_ok`（`hp : TyPos t` `hb : TyBound θ t`）（0ebbddc0）。
- **効く場所/支払い/払えそうか/分類**: P-2 と同じ（未割当／不明／未供給の義務）。

### P-4 前提: B1〜B4（production との橋、binder ではなくギャップ）
PARAMETRIC_BRIDGE_FREEZE.md §2-3 の表（C1-C3 は closed、B1-B4 は未供給）:
- **B1**: `∀ θ e, Sparkle.IR.Type.DimExpr.evaluate θ e = Tools.ShippingGen4ParamLayerA.evalM θ e`（`evaluate` は `partial`/opaque）。
- **B2**: `specializeType (bindings : Bindings) (context : String) : HWType → Except String HWType`（partial/opaque）の `.bitVectorDim d` 腕 = `hwTypeFromWidth <$> (evaluate d >>= requirePositive ctx)` と `specTypeM` の対応。
- **B3**: `specializeExpr (bindings : Bindings) : Expr → Except String Expr`（partial/opaque）と `specExprM` の対応（F2 のモデル `specExprM` が対象）。
- **B4**: private `requirePositive`/`validateBindings`（Specialize.lean:36,49）。unit6 で `requirePositive_eq`（`specRequirePositive context value = requirePositiveM context value`、ParamBridgeLegal.lean:44）と `LegalBinding` の mangled 名 elab（`specValidateBindings`, ParamIface.lean）は実装済み（unit6 F3 として承認済み）。`requirePositive` の実装と model `requirePositiveM` の一致（`requirePositive_eq`）はこれで閉じた。`validateBindings` 全体と `LegalBinding` の同値は主張されていない（`legal_facts` は必要条件のみ）。B1-B3 は未供給のまま。
- 履歴/文書の記述: 「この調査で経路未発見」（B1-B3）。選択肢は決定資料 D1（option 2: production の total 化、option 3: 新 TRUSTED 等式 law）で、どちらも未承認・未採用（seq 3648）。
- **FG との位置**: `ReflectsAll`（parametric route）／`ParamTopShips`（ParamIface.lean:98）の仮定「`specializeDesign … = .ok D'`」を使う側の production 橋。
- **支払い予定**: 未割当（決定資料 §5「決定が無ければ B1-B3 は未供給のまま」）。**実runから払えそうか**: 不明（「この調査で経路未発見」と書かれている）。**分類**: 未供給の義務（option 3 を採れば TRUSTED境界になるが、現時点では採用されていない）。

### P-5 前提: `T = SpecSuccessAllPositive b D`
- **完全な型**（ParamIface.lean:106）:
```lean
def SpecSuccessAllPositive (b : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ((D.addModule b).findModule (D.addModule b).topModule).isSome = true →
    ∀ θ, LegalBinding (D.addModule b) θ → SpecOk (D.addModule b) θ
```
`SpecOk D θ := ∃ D', Sparkle.IR.Specialize.specializeDesign D θ = .ok D'`、`LegalBinding D θ := specValidateBindings D.modules θ = .ok ()`。
- **仮定している定理**: なし（定義のみ。`ParamTopShips` は成功を仮説に取る）。**効く場所**: FG とは別の「成功そのもの」の目標。決定資料 §2: 「T が承認済み FG の一部かは未決定（ユーザーの判断）」。
- **観察**: `Tests/Gen4/ParamReachProbe.lean` が `pDivOut`（`W / 2`）を W=1 で特殊化して `.error`（"port 'out' specializes to zero width"）を実行時に得た（pod build の `#eval`、定理ではない、同一性の対応 (i)-(iii) は未確定）。
- **支払い予定**: 未割当（D3 の判断待ち）。**実runから払えそうか**: 不明。**分類**: 未供給の義務。

### P-6 前提: `SrcAt`、`PostTransfer raw b Dr D I`
- **完全な型**: `abbrev SrcAt := List (String × Nat) → TopIface`（コメント「A PREMISE of the same kind as G3, not a derived object」）、`def PostTransfer (raw b : Sparkle.IR.AST.Module) (Dr D : Design) (I : TopIface) : Prop := ∀ θ Dr' D', specializeDesign (Dr.addModule raw) θ = .ok Dr' → specializeDesign (D.addModule b) θ = .ok D' → ∀ n raw', Dr'.findModule raw.name = some raw' → CombTopRunN Dr' n raw' I → ∃ b', D'.findModule b.name = some b' ∧ CombTopRunN D' n b' I`（ParamIface.lean:77-119 付近、`PostTransfer` のコメント「UNSUPPLIED … never assumed」）。
- 仮定している定理: なし（定義のみ。`ParamTopShips b D src` に `src : SrcAt` が現れる）。**効く場所**: FG の `TopShips` の parametric 版／raw-post 関係（GENERAL_SPEC §1.1「b ↔ raw」）。**支払い予定**: 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務。

### P-7 前提: `RefLaws` 系（I3c, ParamKeeps.lean）
- `body_symbolic_keeps`（ParamKeeps.lean, `L : RefLaws mref cref`, `hC : ChildKeeps L D`）、`core_symbolic_keeps`（`hA0 : D = 0 → L.aux {}`, `hbody : ∀ {tenv}, D < sparkleSynthDepthLimit → ∀ b ci isInst, Keeps … (J L (D + 1)) (synthesizeFromConst …)`）、`core_symbolic_triple0`（`hA : L.aux {}`）、`core_symbolic_balance`（`hs : StartV L w` `hq : L.quiet w` `hd : L.dval w = 0`）、`core_symbolic_worlds`（`hA : L.aux {}`, `hw : Out0 L w`, `hbody`）。`ChildKeeps`（`Tools/ShippingChildInv.lean:609`）: `∀ (mctx : Meta.Context) (cctx : Core.Context) c, Keeps mctx mref cctx cref (J L D) (synthesizeChild c)`。`StartV`（:582）: `L.sval w = some synthesizeChild ∧ (L.dval w = 0 ∨ CacheInv mref cref (L.val w))`。
- **ギャップ（freeze に原文あり）**: FG の `Start L mctx cctx w`（`AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`, Defs:52）は新 `Laws`（`RefLawsAOps`）上、I3c は旧 `RefLaws` 上。freeze F1 行（PARAMETRIC_FREEZE.md 623 行付近）に「`Start` から `RefLaws` witness の `Out0` への lemma はこの調査では見つからなかった」。reviewer も seq 3620 で「I3c は RefLaws 上、I4 は構造的分解のみ」と範囲限定。
- **支払い予定**: 未割当。**実runから払えそうか**: 不明。**分類**: 未供給の義務（対応する M3 側の IH は T1 台帳を参照）。

### P-8 承認済み unit6 F3 の `LegalBinding D θ`
- `legal_facts` `legalBinding_allPos` `legalBinding_covers`（`Tools/ShippingGen4ParamBridgeLegal.lean:52, :79, :84`）の `h : LegalBinding D θ`。`ExpLegal` は `LegalBinding` の必要条件のみ（同値ではない: 重複・unknown 名・宣言重複チェックは含まない）。
- **承認状態**: unit6 F3 は承認済み。freeze 99f322ce（parametric-supply seq 5358）、承認 SHA = 50d22e3b、承認イベント = seq 5604。本文と clean build の根拠 = 261a2b3c（kjob/g4par-r23）/ seq 5599（review 提出。par23v-261a2b3c exit 0・708 jobs・dirty=false・sorry 0・標準 axioms のみ）。seq 5601 の差し戻し後、コメントのみの子 SHA 50d22e3b（261a2b3c との差は 2 ファイル先頭コメント各 1 行、Lean 本体同一で再 build 不要）が seq 5604 で承認された。以後この Issue は台帳待ちで一時停止。mutant の棄却は signature / defeq / 証明失敗によるもので、意味的反例ではない。
- **既知の前提差分（F3 本体の記録による。段 1 の基準件数 146/110 とは別に数え、基準件数は書き換えない）**:
  - `LegalBinding D θ` を前提にして、P-1 の `AllPos θ`（`legalBinding_allPos`）と、宣言 parameter の coverage（`legalBinding_covers`: `∀ m ∈ D.modules, ∀ q ∈ m.parameters, ∃ v, θ.lookup q.name = some v`）の **2 項目を条件付きで導出**できる。条件は `LegalBinding D θ` であり、無条件の解消ではない。coverage 項目に対応するのは、P-2 の `Bound θ d`（`.parameter n` の腕が `∃ v, θ.lookup n = some v`）が要求する束縛の存在で、ブロック単位で 1 対 1 に対応づけた確認はしていない。
  - `requirePositive` の実装と model の一致（`requirePositive_eq`、P-4 の B4 の一部）の **1 項目を解消**（条件なし）。
  - **追加前提 0**。
  - **`LegalBinding D θ` は入力として残る**。成功した特殊化が `LegalBinding` を満たすことは `specializeDesign_ok_legal`（ParamIface.lean:122, 承認済み）が与えるが、これを FG の実 run から受け取る経路はこの調査では見つからなかった（支払い予定は未割当）。
- **広い残余（P-4 の B1-B3、P-5 の T、FG への接続）は未供給のまま**。F3 はそのいずれも供給していない。上記 §0 と P-1 〜 P-7 の「未割当／不明」の記述はこの意味で保たれる。
- **分類**: 入力条件（`LegalBinding D θ`）。

## 5. sparkle-gen4-fg-assembly
前提の台帳なし。Issue の goal 文: 「前提はGENERAL_SPECの一様なLaws/Start/ReflectsAll境界に限定し、route別の未供給契約を隠さない」。履歴に Lean の出力はなく、依存先 `sparkle-gen3-t1-assembly`（M3、T1 台帳を参照）。

## 6. 読んだ文書・branch@SHA 一覧
- 履歴: `$S/h/sparkle-gen4-{routes,gate-supply,fallback-supply,parametric-supply,fg-assembly}.json`、`managerctl show sparkle-gen4-fg-assembly`。
- worktree HEAD d0ddc50b: `scripts/gen2/GENERAL_SPEC.md` §1.1-1.3、`Tools/ShippingGen2Defs.lean`、`Tools/ShippingInlineSoundness.lean`、`Tools/ShippingChildCacheA.lean`、`Tools/ShippingChildInvA.lean`。
- kjob/g4gate-g3c@59b68658: `Tools/ShippingGen4{Iface,GateIface,GateLeaf,GateOutTy,GatePortW,FirstLeaf}.lean`、`scripts/gen4/GATE_SUPPLY_FREEZE.md`（rev1, 全文の前半と §6/§9 の見出し）。
- kjob/g4gate-g5@1e141f26: `Tools/ShippingGen4InstParent.lean`（binder のみ、未承認）。
- kjob/g4fb-fb25@4519e2fb: `Tools/ShippingGen4Fb*.lean` 全14ファイルの定理署名、`Tools/ShippingGen4FbFragRun.lean` `FbFrag.lean` 全文、`scripts/gen4/FALLBACK_SUPPLY_FREEZE.md` の §33-34、`Tools/ShippingChildFrontCP.lean`（ChildSynthA）、`ShippingMachineEntry.lean`（MachineDefines）、`ShippingEntrySoundness.lean`（PostReady, FExpr.WF）、`ShippingFirstGateChild.lean`（ChildFnR）。
- kjob/g4par-r23@261a2b3c（0ebbddc0 を含む）: `Tools/ShippingGen4Param{Iface,Keeps,Entry,LayerA}.lean`、`ShippingGen4ParamBridge{Compose,Shape,Width,SpecType,SpecExpr,Legal}.lean`（署名中心）、`scripts/gen4/PARAMETRIC_BRIDGE_FREEZE.md`、`PARAMETRIC_SPECSUCCESS_DECISION.md`、`PARAMETRIC_FREEZE.md`（grep で §13 と F1 行）、`Tools/ShippingChildInv.lean`（ChildKeeps, StartV, J, RefLaws の冒頭）。
- par/gen4-gate の aacd07ec/eb23ed1b は git ls-tree で直接は読まず、同文が移送された g4gate-g3c 側を読んだ。

## 7. 読めなかったもの／この調査では見つからなかったもの
- sparkle-gen4-fg-assembly の Lean ファイルと branch。
- sparkle-gen4-oneout-probe（G-ONEOUT）の結果文書（routes の done note が参照）。
- `ReflectsAll` の Lean 定義、gate 用 `T1Hyp` フィールド。
- `GateDefines` を含む WRITTEN NOT BUILT ファイル群の中身、`EntryDefines`/`GateDefines` を一般 ∀ 宣言で払う theorem。
- GATE_SUPPLY_FREEZE.md §4-§9、PARAMETRIC_FREEZE.md の全文（全体を通読していない。§13 と F1 行のみ）。
- fallback の 14 ファイルは署名中心の読みで、証明本体は読んでいない（FbFragRun/FbFrag を除く）。
- gate と parametric の最新 branch に対する build 結果の独立確認（履歴 note の記述に依拠）。
