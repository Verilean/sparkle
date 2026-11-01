# RT 調査: `hdom`（DomAtomic）・`hbs`・`GetEnvFrame` / 2 回の `getEnv` の同一性の供給経路（調査のみ・文書のみ）

Issue `sparkle-rt-dom-survey`（親 `sparkle-gen5-dg-readertrace`）。base: `par/rt-direct` 046d1d56（`shapeInputs_of_direct` は reviewer 承認済みの条件付き中間 bridge）。
**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。** 数えていない候補は「未計数」。
この文書は調査である。Lean の source tree は編集していない（scratch の probe 1 つ、§2.4、コミットしない）。コンパイラ・共有定義・TRUSTED 境界・law は変えていない。mutant は使っていない。
用語: 「見つからなかった」は「この調査で辿った経路では供給元・経路が見つからなかった」の意味で、不可能・導出不能の主張ではない。条件付き・中間結果を完了とは書かない。

## 0. 読んだもの

`DG_READERTRACE_FREEZE_REV19.md`（全文、§4 の接続表）、`REV16`（全文）、`REV17`（全文）、`REV18`（全文）、`DG_DOMATOMIC_SURVEY.md`（全文）、`Tools/ShippingGen5ReaderTraceDirect.lean`（先頭〜80 行と `shapeInputs_of_direct` の署名）、`ShippingGen5ReaderTraceShape.lean`（`DomAtomic` / `MidInputs` / `ShapeInputs` / `shapeStart_trace` / `machineShapeF_reach`）、`ShippingGen5ReaderTraceShapeIn.lean:458-491`（`shapeInputs_of`）、`ShippingReaderFuelShape.lean`（`shapePre` / `shapeMid` / `shapePost` / `shapeStart` / `shapeW`）、`ShippingReaderFuelShapeR5.lean:162`（`shapePre_facts`）、`Sparkle/Compiler/Elab.lean`（`machineShape?` 5072〜、`machRunApp?` 3675、`machReserve` 3703、`machConv` 3888〜、`machDom?` 4269、`entryConst` 5272）、`Tools/ShippingShapeDecomp.lean`、`Tools/ShippingR5Check.lean`、`Tools/ShippingMachineCommand.lean:441-460`（`readMachine`）、`Tools/ShippingGen5Cover.lean:245`（`kDOf_add_len`）、`Tools/ShippingGen5Cover6.lean`（`CtrlEq` / `FReachC`）、`Tools/ShippingGen5Env.lean` / `EnvR.lean`（`ReadsAt`、E4〜E6、`MachineDefinesR`）、`Tools/ShippingEnvSnapshot.lean`（`GetEnvFrame`）、`git show par/fg-ledger-sync:scripts/gen2/PREMISE_LEDGER.md`（C.EN-6、C.RK-2、C.RT-2）、`git show par/t1-ledger-sync:scripts/gen3/PREMISE_LEDGER.md`（T1L-36）。

DG-ENV の freeze 文書（`DG_ENV_FREEZE*.md`）は、この worktree（par/rt-direct）の `scripts/gen5/` に無く、**読んでいない**。C0 の定義は Lean の `ReadsAt`（`ShippingGen5Env.lean:29`）と FG 台帳の C.EN-6 の行で代用した。`sparkle-gen5-dg-env` Issue は `todo`（一時停止、再開条件は流れ freeze か台帳での割当）。

## 1. `hdom`（DomAtomic、D-b 案）

### 1.1 `hdom` が `shapeInputs_of_direct` で何を要求するか

署名（rev19 §3）:

```
hdom : ∀ (p : ShapePre) (en : Expr),
  shapePre sm ps ci (structEnv env) = some p → machNormF n (structEnv env) p.e = some en →
  ∀ (dom αs ie b : Expr), (shapeMid (structEnv env) p en).run? = some (dom, αs, ie, b) → DomAtomic dom
```

`DomAtomic e := (∃ j, e = .bvar j) ∨ (∃ c ls, e = .const c ls)`（`Shape.lean:19`）。`dom` は `shapeStart` に渡る**変換前**の run の domain（`machRunApp?` の第 1 要素、`Elab.lean:3675`）。

### 1.2 経路

**(a) `hdom` は production の成功とは独立に述べられている。** `hdom` の前件は `shapePre = some p` と `machNormF = some en` だけで、`machineShapeF … = some (some sp)`（成功）を含まない。しかし `ShapeInputs` を使う `machineShapeF_reach`（`Shape.lean:237`）は成功の仮説 `h` を持ち、`hIn p en hp hen` は `machineShapeF_state_side h` が返す `p` / `en` にだけ適用される（`Shape.lean:255`）。つまり使われ方は**成功した run だけ**。`hdom` の現在の形（成功を前件に持たない）は、使われ方より強い。成功を前件にしない `hdom` が受理されたソースで真かは、この調査では確かめられなかった（`dom` が非 atomic で、かつ後の段で失敗するソースが存在しうるかを構成も排除もしていない。意味的な反例は作っていない）。

**(b) 成功した run では最終状態の domain が `machDom?` を通る。** `shapePost`（`ShippingReaderFuelShape.lean:165-166`）は `domE ← st.dom <|> machTypeDom? p.d.type` から `machDom? (kI + n + k) domE` を要する。`machDom?`（`Elab.lean:4269`）は `domE` が `fvar _machIn i` か `const Domain.defaultDomain ls` のときだけ `some`。`shapeStart` は run があるとき `machReserve … dom'` で `st.dom := some dom'` を設定する（`Elab.lean:3716`）。したがって、**最終状態の `st.dom` が開始時の `some dom'` のまま残ること（`DomKeep`）が言えれば、成功した run の `dom'`（変換後）は `fvar _machIn i` か `const defaultDomain` になる**。これは `DG_DOMATOMIC_SURVEY.md` §3.1〜3.3 の経路（`st.dom` を書く 5 箇所はすべて「設定済みなら同じ値のときだけ通る」: `machReserve` 3708-3710、`machConv` の bare register 腕 3927-3929、`machInstance` 4066-4067、`machInstanceS` 4105-4106、`machLoopRoot` 4215-4217）を再確認したもの。この調査は 5 箇所の存在を `Elab.lean` で読み直した（grep の網羅証明ではない）。

**(c) 変換前の `dom`（`DomAtomic` が述べる対象）と変換後の `dom'` は別。** `machConv` は `.app` の腕で `bundleIota (machProjIota …)` を適用する（`Elab.lean:3969`）ので、非 atomic な `dom`（例: 構造体の射影）が atomic な `dom'` に変換される経路があるかは、この調査では確かめていない（見つからなかったが、無いとは言わない）。`DomAtomic dom`（変換前）を成功から導く経路は見つからなかった。一方 **D-b（`DG_DOMATOMIC_SURVEY.md` §4）は変換前の `dom` の形を要さず**、変換後 `dom'` の形だけを使う。`shapeStart_trace` が `hT` から得る `InRange nDecl stc … dom'` を、`dom'` が `_machIn i`（`i < nDecl`）か const なら状態によらない `InRange nDecl {} 0 dom'` に移す（`DG_DOMATOMIC_SURVEY.md` §3.3）。

**(d) 既存の定理で使えるもの。**

| 項目 | 場所 | 使い方 |
|---|---|---|
| `shapeStart_trace` の `hdom` clause（`DomAtomic dom`） | `Shape.lean:63-68` | D-b で置き換える対象（`stc = {}` を 1 段展開で出すために使っている、`Shape.lean:79-85`） |
| `machineShapeF_state_side` | `Cover5.lean:55` | 成功から `st0 / st1 / st / v / shapePost = some sp` を取り出す。D-b の `DomKeep` の適用点 |
| `shapePost`（`machDom?` を要する） | `ReaderFuelShape.lean:165-166` | 最終状態の `st.dom` の形（`fvar _machIn` / `const`） |
| `trInv_reserved` | `Nested.lean:15` | 予約先の状態での `InRange` と `NoLoose 0` を要求。atomic な `dom'` ならこの要求が状態によらず満たされる |
| `TraceGood` / `FReachC` / `CtrlEq` | `Ctl.lean:99` / `Cover6.lean:17,22` | `CtrlEq` は `dom` を**自由**にしている（`Cover6.lean` ヘッダ: `fullInv_reachC` は `dom` について何も言わない）。**`DomKeep` を出さない** |
| `TrInv` の `DomPh`（`st.dom = some d → InRange … ∧ NoLoose 0 d`） | `ReaderTrace.lean:53` | `dom` の範囲のみ。同一性（保存）は含まない |

`DomKeep`（「`readF` の任意の呼び出しについて、入力状態の `dom = some d` なら出力状態も `dom = some d`」）を出す既存の定理は、この調査では見つからなかった。

### 1.3 新しい条件の候補（完全型）と、D-b の規模・止まる箇所

**候補 D-b-1（証明、新しい前提なし）: `DomKeep`。** 型（未 elaborate）:

```lean
/-- 成功した readF の呼び出しは、設定済みの `dom` を書き換えない。 -/
def DomKeep (senv : StructEnv) (h : Hs) : Prop :=
  ∀ (c : Call) (v : callOutTy c), h c = some (some v) →
    ∀ d, (callSt c).dom = some d → (callOut c v).dom = some d
```

（`Hs` / `Call` / `callSt` / `callOut` は `ShippingGen5ReaderTraceCtl.lean:97-100` と `ShippingReaderFuelDefs.lean:167-` の既存の名前。`TraceGood` と同じ量化の形。型の細部は freeze 時に elaborate して確かめる。）
証明は `readF` の 7 種の `Call`（`conv` / `nested` / `inst` / `instS` / `chain` / `loopBody` / `loopRoot`）の全腕について、書き込み 5 箇所では「設定済みなら同じ値のときだけ通る」検査を使い、他の腕は再帰の帰納仮定を連ねる。**規模は見積もれる範囲で**: `Tools/ShippingGen5ReaderTrace*.lean` 23 ファイル中、`TraceGood` を示す腕ごとのファイル（`Inst` 252 行 / `InstS` 319 / `Loop` 288 / `LoopRoot` 292 / `Nested` 140 / `Reg` 158 / `Chain*` 218 / `Dispatch` 114 / `App*` 330 など）と同じ腕の数を辿る。`dom` は 1 フィールドだけを追う不変条件なので `TraceGood` より証明は軽い見込みだが、**腕の数は同じ**。行数は見積もらない（数えていない）。行数の見積もりは出さない（`TraceGood` 側の腕のファイルの行数は上に挙げたが、`DomKeep` の比は推測になるため採らない）。

**候補 D-b-2（型の変更、承認が要る）: `DomAtomic dom` を外す。** `MidInputs` の run 節（`Shape.lean:26-28`）と `shapeStart_trace` の `hdom` clause から `DomAtomic dom` を外し、`machineShapeF_reach` が成功（`shapePost` の `machDom?` と `DomKeep`）から変換後 `dom'` の形を供給する。結果として `ShapeInputs` が弱くなり、`shapeInputs_of_direct` / `shapeInputs_of` の `hdom` 仮説が**消える**（署名の binder が 1 つ減る）。型の変更なので reviewer の freeze が要る。

**止まる箇所。**

1. `DomKeep` が全 7 腕で閉じるかは**未証明**。`CtrlEq` が `dom` を自由にしているため、`FReachC` を使った既存の帰納は流用できない。`TraceGood` の拡張にするか独立の帰納にするかは freeze で決める。
2. D-b-2 は `shapeStart_trace` と `MidInputs` の型を変える（承認済みの型の変更）。`ShapeIn.lean:458` の `shapeInputs_of` と Direct の `shapeInputs_of_direct` の署名にも波及する（binder が減る）。
3. 変換前 `dom` の形を成功から導く経路は見つからなかった（§1.2 (c)）。D-b はそれを要さない。

**候補 D-a（D-b が閉じなかったときだけ）。** `DG_DOMATOMIC_SURVEY.md` §5 の D-a の完全型（成功を前件に付けた形）:

```lean
def DomAtomicRun (senv : StructEnv) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (n : Nat)
    (ai : Bool) : Prop :=
  ∀ (sp : MachineShape) (p : ShapePre) (en : Lean.Expr),
    machineShapeF n sm ps ci senv ai = some (some sp) →
    shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
    ∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) → DomAtomic dom
```

FG +1 見込み（未計数）。reviewer の指示（`DG_DOMATOMIC_SURVEY.md`）どおり D-b の結果が出るまで足さない。

### 1.4 台帳への影響

| 項目 | 消える行 | 増える候補 |
|---|---|---|
| D-b を実装・受理した場合 | `shapeInputs_of_direct` の `hdom` binder が消える。**台帳の行としては元から無い**ので FG / T1 の減算は 0 | なし |
| D-b が閉じず D-a を採る場合 | 0 | FG +1（`DomAtomicRun`、未計数） |
| 今回 | 0 | 0 |

規模の見積もり: 新規 Lean = `DomKeep` の補題群 + `shapeStart_trace` / `MidInputs` の型変更（既存 3 ファイルの置き換え版を新規ファイルに置く）。腕ごとの行数は未計測。

## 2. `hbs`（`p.bs.length ≤ nDecl`）

### 2.1 経路

`p.bs` は `shapePre` の `mixedGatePeel (packTupleInputs d.value) = some (bs, e)` の `bs`（`shapePre_facts`、`ShippingReaderFuelShapeR5.lean:162-166`: `ci = .defnInfo p.d ∧ mixedGatePeel (packTupleInputs p.d.value) = some (p.bs, p.e) ∧ …`）。

`nDecl` は `shapeInputs_of_direct` では**自由な implicit 引数**（rev19 §3 `{nDecl : Nat}`）。reader の側の `nDecl` は、`ShapeAgree` / `rowC_of_reader` では `hnD : nDecl = kDOf d`（`kDOf d := d.nIn - d.shape.insts.length`、`ShippingGen5SemGen.lean:20`）と置かれる（`DG_COVER_FREEZE_REV7.md:126`: 未供給の名前付き前提）。`nDecl` を 2 つの面から読む:

1. **`ci` の宣言 binder 数として定義する面。** `generator`（`ShippingMachineCommand.lean:459-460`）は `nDecl := bsIn.length`（`bsIn` = `mixedGatePeel (packTupleInputs entryV)` の `.1`）。`shapePre` が同じ `ci` の値に対して同じ `packTupleInputs` / `mixedGatePeel` を呼ぶので、`p.bs` は**同じ関数の同じ入力の出力**。したがって `nDecl := nDeclOfCi ci`（下）と定義すれば `p.bs.length = nDecl` は `shapePre_facts` と関数の決定性から出る。`hbs` は等式（≤ は帰結）。
2. **閉じ（closing）の `nDecl` の面。** `ShapeDecomp.nDecl`（`ShippingShapeDecomp.lean:150`）は R5（`(names.zip kinds).length = sp.layout.slots.length`）の下で `sp.binders.length - sp.insts.length - sp.layout.slots.length - sp.layout.lets = bs.length` を証明する。R5 は `ShapeDecomp.r5_of_lengths`（`:143`）で `names.length = kinds.length` と `inits.length = kinds.length`（`MachRead.LenOk`、`ShippingReaderLenOk.lean:7`）から出る。`machineShapeF_reach` の結論に `st.LenOk` が含まれる（`Shape.lean:250`）。`ShippingR5Check.lean:29-40` は `hnIn : d.nIn = bs.length + d.shape.insts.length` を「generator の知識であって定理ではない」と明記している。

### 2.2 使う既存定理

| 定理 | 場所 | 用途 |
|---|---|---|
| `shapePre_facts` | `ShippingReaderFuelShapeR5.lean:162` | `p.bs` が `mixedGatePeel (packTupleInputs ci.value)` の出力であること |
| `ShapeDecomp.nDecl` | `ShippingShapeDecomp.lean:150` | 閉じの `nDecl` = `bs.length`（R5 の下） |
| `ShapeDecomp.r5_of_lengths` | `ShippingShapeDecomp.lean:143` | R5 を `LenOk` の長さから |
| `kDOf_add_len` | `ShippingGen5Cover.lean:245` | `kDOf d + insts.length = d.nIn`（`insts.length ≤ d.nIn` の下） |
| `data_hkD` | `ShippingGen2MemData.lean:37` | `n ≤ d.bsIn.length`（`n` は呼び出しの `nDecl`） |

### 2.3 新しい条件の候補（完全型）

`hbs` は新しい**前提**を要さず、`nDecl` の取り方で消せる見込み:

```lean
def nDeclOfCi (ci : Lean.ConstantInfo) : Nat :=
  match ci with
  | .defnInfo d =>
    ((mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value)).map (fun x => x.1.length)).getD 0
  | _ => 0

theorem hbs_of_nDeclOfCi (sm : Bool) (ps : List (String × Nat)) (ci : Lean.ConstantInfo) (senv : StructEnv) :
    ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDeclOfCi ci
```

（probe の結果は §2.4。）`shapeInputs_of_direct` の `{nDecl}` を `nDeclOfCi ci` に固定し、`hbs` binder を消した版は、署名の変更なので freeze が要る。

**残る義務（止まる箇所）。** `nDecl` をこう固定すると、`ShapeInputs` / `TraceGood` を `nDeclOfCi ci` で使うことになる。一方 `rowC_of_reader` 側（Cover）の `hnD : nDecl = kDOf d`（`d` = `dataOf` のデータ）は別の前提で、**`kDOf d = nDeclOfCi ci` を繋ぐ定理はこの調査では見つからなかった**（`ShapeDecomp.nDecl` は閉じの式 `sp.binders.length - …` との等式で、`d.nIn - insts.length` との接続には `d.nIn` の定義＝ `dataOf` の `nIn := nDecl + insts.length`（`ShippingR5Check.lean:29`、generator の知識）が要る）。これは `hnD` / `hnIn` の供給で、DG-DATAOF 側の義務（rev16 §6 が `hbs` を「`dg-dataof` の `nDecl = kDOf d` の同定 + T1L-30 に付け替え見込み」と書いたもの）。`hbs` 自体は消せるが、**同じ内容が `hnD` に移る**（消えたのではなく付け替え）。

### 2.4 scratch の probe

`Scratch/RtDomProbe.lean`（コミットしない、`lakefile.lean` の `lean_lib` もコミットしない）に §2.3 の `nDeclOfCi` / `bs_len_eq` / `hbs_of_nDeclOfCi` を置き、`kjob lake build Scratch.RtDomProbe` で elaborate した。結果は §5 に書く。

### 2.5 台帳への影響

| 項目 | 消える行 | 増える候補 |
|---|---|---|
| `nDecl := nDeclOfCi ci` とした場合の `hbs` | 署名の `hbs` binder（台帳の行ではない）。FG / T1 の減算 0 | 0（`hnD` / `hnIn` への付け替えは既存の義務、新しい行ではない） |
| 今回 | 0 | 0 |

規模の見積もり: `nDeclOfCi` と 2 補題で 10 行台（probe の通りなら）。署名変更の freeze 1 本（小）。

## 3. `GetEnvFrame` / 2 回の `getEnv` の同一性と DG-ENV の C0 の重なり

### 3.1 何が未解消か（rev17 §2.3 / rev18 の再掲）

`doSynth`（`Elab.lean:5578-5587`）は `getConstInfo` → `getEnv` で `userInliner env` / `structEnv env` を `entryConst` に渡し、`synthesizeFromConst`（5313-5314）は内部の別の `getEnv` の `structEnv env` で `machineShape?` を呼ぶ。rev17 の未解消の義務: (a) `GetEnvFrame` が実際の run で成り立つ、(b) 2 つの `getEnv` の環境の同一性。

### 3.2 DG-ENV の C0 との重なり: **重なる**

`ReadsAt env₀ cref w`（`ShippingGen5Env.lean:29`）は「`w` の Core 環境が `env₀` と、(1) 見つかる定数、(2) `instancePredicate`、(3) `userInliner`、(4) `structEnv` で一致する」。FG 台帳の C.EN-6（`hall` = C0 = 全 world の `ReadsAt`）は「未供給の義務」で、DG-ENV の担当（`sparkle-gen5-dg-env`、`todo`）。

* `ci_of_readsAt`（E4、`ShippingGen5Env.lean:52`）: `getConstInfo X` の run が返す `ci` について `env₀.find? X = some ci`。→ **`CiDirect env₀ ci₀` の `c` と `ci₀` を供給**（`CiDirect` は `∃ c, env.find? c = some ci`）。
* `envR_of_readsAt`（E5、`:58`）: `getEnv` の run が返す `envR` について `userInliner envR = userInliner env₀`、`structEnv envR = structEnv env₀`、`instancePredicate envR = instancePredicate env₀`。→ **`doSynth` の `getEnv` と `synthesizeFromConst` の `getEnv` の 2 つが、`structEnv` / `userInliner` について同じ `env₀` の値を返す**（`structEnv envR = structEnv env₀ = structEnv envR'`）。これが rev17 の (b) の「2 回の `getEnv` の同一性」のうち、`shapeInputs_of_direct` が実際に使う部分（`structEnv`）である。
* `machineDefines_of_readsAll`（E6、`:69`）と `machineDefinesR_of_env`（R2、`EnvR.lean:46`）は、この 2 つの補題で `machineShape? … (structEnv env₀) = some shape` を `env₀` の式として使う形に落としている（`rw [hi, hu, hs, hs']`）。**`MachineDefinesR` は `GetEnvFrame` / `ReadKeeps` / `EnvSnapshot` を使わない**（`EnvR.lean` ヘッダ: "LAW-FREE"）。

したがって、`shapeInputs_of_direct` の `env` を `env₀`（DG-ENV の `env₀`）にとれば、`hci`（`CiDirect env₀ ci`）と `structEnv env` は C0（`ReadsAt` の 4 つの conjunct、`w1` / `w5` / `w7`）で供給される。**`GetEnvFrame` は要らない**（C0 が `GetEnvFrame` の役を、per-world の `ReadsAt` として置き換える形）。

### 3.3 重ならない部分・残る義務

* C0 自体（`hall` または D2 の per-world `ReadsAt` の 3 つ）は**未供給**（FG 台帳 C.EN-6、DG-ENV の全 note で「未供給」）。DG-ENV 側で供給する案を書くとすれば、**DG-ENV の C0 が供給されたときに、`shapeInputs_of_direct` の `env := env₀`、`hci := ⟨c, ci_of_readsAt hget (h w1)⟩`、`structEnv` の置換が自動で付いてくる**、という接続の補題（新規ファイル、`ci_of_readsAt` + `envR_of_readsAt` の合成だけ。新しい前提なし）。供給元そのものを新たに見つけたわけではない。
* **`entryConst` の腕（非 inline）の保証。** `entryConst true false [] ci₀ (instancePredicate env₀) (userInliner env₀) (structEnv env₀)`（E6 / R2 の `hg1 hg2 hsh` の式の中の `ci` の位置）は `env₀` と `ci₀` だけの純関数で、どちらの腕を取るかは **run の性質ではなく `(env₀, c)` の静的な性質**（`Elab.lean:5272-` の `entryConst` が `certifiedShape?` / `mixedCertifiedShape?` / `machineShape?` の結果で決める）。`CiDirect` を満たすのは「`entryConst … ci₀ … = ci₀`」の宣言。これは E6 の `hg1 hg2 hsh`（宣言ごとの env₀-側の事実）と**同じ族の宣言ごとの事実**で、新しい runtime law ではない。ただし inline 枝（`UserInlinerPh`、S1 / S2、rev18 §3）を取る宣言は `CiDirect` を満たさず、この路では供給されない（rev18 のとおり未解消）。この調査は `entryConst` の具体的な条件の解析（どの宣言がどちらの腕か）をしていない。
* **`DeclValuePh env₀`（N1-a）** は C0 に含まれない（rev16 §2.3: 「単一の `env` についての静的な文」。DG-ENV の `EnvTypesFVarFree` / `SigTyClosed` / `InstSFieldsDet` の隣に置く候補）。`GetEnvFrame` / C0 とは別の文。
* DG-ENV の `userInliner env₀` の同一性（E5 の 2 つ目の conjunct）は、`UserInlinerPh` を**供給しない**（同一の `inl` であることを言うだけ）。

### 3.4 DG-ENV 側で供給する案（書くだけ。DG-ENV Issue は変えない）

案 E-1（接続補題。新しい前提なし）: DG-ENV の `ReadsAt env₀` の 3 つの世界（`w1` / `w5` / `w7`）から、`shapeInputs_of_direct` の `(env := env₀) (hci : CiDirect env₀ ci₀)` と `structEnv envR = structEnv env₀` を出す補題。型の骨格（未 elaborate）:

```lean
theorem ciDirect_of_readsAt {env₀ : Environment} {X : Name} {w w' : Void IO.RealWorld} {ci : ConstantInfo}
    (hget : RunsTo (Lean.getConstInfo X : MetaM ConstantInfo) mctx mref cctx cref w ci w')
    (h : ReadsAt env₀ cref w) : CiDirect env₀ ci   -- := ⟨X, ci_of_readsAt hget h⟩
```

これは `ci_of_readsAt` の言い換え（1 行）。**規模: 極小**。ただし `CiDirect env₀ ci` の `ci` は `getConstInfo` が返す `ci₀` であって、`shapePre` に渡る `ci = entryConst … ci₀ …` ではない。`ci = ci₀` を出すには上の「非 inline 枝の静的条件」`entryConst … ci₀ … = ci₀` が要る。

案 E-2: `GetEnvFrame` を供給する案（rev17 §2.3 (a)）は、新しい runtime law（`T1L-36` の行: "an environment frame law would be a new runtime law = user decision, not adopted"）で、**採らない**（C0 の経路で足りるため）。

### 3.5 台帳への影響

| 項目 | 消える行 | 増える候補 |
|---|---|---|
| `GetEnvFrame` / 2 回の `getEnv`（rev17 の (a)(b)） | 台帳の行は元から無い（未解消の義務として note にあったもの）。**C.EN-6（C0）の供給に付け替え**: C0 が供給されれば (a)(b) が付いてくる | 0（C.EN-6 は既存の FG 行。新しい行ではない） |
| `entryConst … ci₀ … = ci₀` の宣言ごとの事実 | 0 | E6 の `hg1 hg2 hsh` と同族の宣言ごとの事実。**行にするかは未判断**（未計数）。行にしないなら DG-ENV の入力として扱う |
| 今回 | 0 | 0 |

## 4. まとめ

| 項目 | 供給経路 | 新しい前提 | 止まる箇所 | 台帳 |
|---|---|---|---|---|
| `hdom` | D-b: 成功した run の最終 `st.dom` の保存（`DomKeep`）+ `shapePost` の `machDom?` で変換後 `dom'` が atomic。`DomAtomic dom` を型から外す | なし（D-b）。D-b が閉じなければ D-a の `DomAtomicRun` FG +1（未計数） | `DomKeep` が全 7 腕で閉じるか未証明。`shapeStart_trace` / `MidInputs` の型変更（承認要） | 今回 0/0。D-b 受理時に `hdom` binder が消える（行は元から無い） |
| `hbs` | `nDecl := nDeclOfCi ci` と固定し、`shapePre_facts` の決定性で等式 | なし | `kDOf d = nDeclOfCi ci`（`hnD` / `hnIn`、DG-DATAOF の義務）に付け替わる。消えたのではない | 今回 0/0 |
| `GetEnvFrame` / 2 回の `getEnv` | DG-ENV の C0（`ReadsAt` at `w1` / `w5` / `w7`）の E4 / E5。`GetEnvFrame` は要らない | なし（案 E-1）。`GetEnvFrame` を供給する案 E-2 は新 law で採らない | C0 自体が未供給（C.EN-6）。非 inline 枝の静的条件 `entryConst … = ci₀`。`DeclValuePh` は別の文 | 今回 0/0。C.EN-6 の供給に付け替え |

**次は coder**（reviewer の番ではない: 調査のみ、台帳の変更なし）。coder が選ぶ選択肢: (i) D-b の freeze（`DomKeep` と `shapeStart_trace` / `MidInputs` の型変更、reviewer 承認が要る型の変更）、(ii) `nDeclOfCi` で `hbs` を消す署名変更の freeze（小）、(iii) 案 E-1 の接続補題を DG-ENV 再開時に用意。

## 5. scratch の probe 結果

`kjob lake build Scratch.RtDomProbe`: `Build completed successfully (774 jobs)`、exit 0（Pod 内、`set_option autoImplicit false`、import は `Tools.ShippingGen5ReaderTraceShapeIn` のみ）。probe ファイル自体の警告・エラーは無し（ログの警告は既存ファイルの未使用 simp 引数 lint のみ）。`bs_len_eq` の証明は `obtain ⟨hci, hpeel, -⟩ := shapePre_facts h; subst hci; simp [nDeclOfCi, hpeel]`、`hbs_of_nDeclOfCi` は `Nat.le_of_eq (bs_len_eq h)`。sorry / axiom / native_decide なし。

これが示すのは「`nDecl := nDeclOfCi ci` と**定義すれば** `hbs` の型の文が定理になる」ことだけ。`nDeclOfCi ci` が reader / Cover 側で使う `nDecl`（`kDOf d`）と等しいことは示していない（§2.3 の残る義務）。probe の Lean はコミットしていない（scratchpad 内）。

## 6. 主張しないこと

`hdom` / `hbs` / `hci` が実際の run で供給されること。`DomKeep` が成り立つこと（全腕で確認していない）。D-b が証明できること。変換前の `dom` が成功から atomic と言えること（経路が見つからなかっただけで、無いとは言わない）。`kDOf d = nDeclOfCi ci`（DG-DATAOF の義務）。C0（C.EN-6）が成り立つこと。`entryConst` がどの宣言でどちらの腕を取るか。inline 枝（`UserInlinerPh`、S1 / S2）。N1〜N3 の登録、C.RT-2 等の減算、`ShapeInputs` 全体の供給。意味的反例は作っていない。コンパイラ・共有定義・TRUSTED 境界・law は変えていない。`GenWF` は強化しない。DG-ENV の freeze 文書は読んでいない（§0）。
