# RT U2 freeze: N1-a / N2-b / N3-b（×2）の登録と C.RT-2 / C.CV-2 / C.CV-3 の除去（両枝の合成）

Issue `sparkle-rt-u2-compose`（親 `sparkle-gen5-dg-readertrace`）。base: `par/rt-int2` c21e00a6（= `par/rt-int1` + `par/gd-int2`）。根拠: `scripts/gen5/RT_CLOSE_PLAN.md` §2・§3.1・§5 の U2（`git show 1da2e5ee:scripts/gen5/RT_CLOSE_PLAN.md`）、`RT_BRANCH_MEASURE.md`（`6babf063`）、`RT_U1_FREEZE.md`（`cc745270`）、FG 台帳 `par/fg-ledger-sync:scripts/gen2/premise_ledger/C_M5dg.md` §CV-2 / CV-3 / RT-2。
**台帳: FG 103（U1 −3 は受理待ちで FG 100）/ T1 56（今回 FG -0 +0 / T1 -0 +0）。** この文書の時点では何も登録・除去していない。下の ±n はすべて**承認後の見込み**。
この文書は、台帳前提の追加（N1-a / N2-b / N3-b×2）と行の除去（RT-2 / CV-2 / CV-3）を含むので reviewer の承認が要る freeze。コンパイラ・共有定義・TRUSTED 境界・law・FG 範囲・`GenWF` は変えていない。mutant は使っていない（Check 計画の mutant は signature / defeq での棄却であって意味的反例ではない）。
用語: 「見つからなかった」は「この調査で辿った経路では供給元・経路が見つからなかった」の意味で、不可能・導出不能の主張ではない。

## 0. 結論と reviewer に判断してほしい点

1. 合成定理 `u2_compose`（§3）は、**直接枝**（`entryConst` が元の `ci0` を返す、`CiDirect`）と **inline 枝**（`inlinedConst (userInliner env) ci0` を返す）の**両方**で、消費側 `rowC_of_reader_canon` の `hi : FullInv (kDOf d) st` と `hnl : LetsNoLoose st` を出す。`RT_BRANCH_MEASURE` の集計（機械経路 475 件のうち 267 件＝56% が inline 版で value/type が変わる）に基づき、直接枝だけに限る束 A は採らず、inline 枝を含める**束 B**とする（Issue 指示）。
2. 合成は scratch ではなく実ファイルの skeleton `Tools/ShippingGen5ReaderTraceU2Compose.lean` として `kjob lake build Tools.ShippingGen5ReaderTraceU2Compose` が通っている（§6）。**この skeleton に sorry は 0 件**。葉（`KDOfLeaf` / `SameStLeaf` / `InlineInputs` / `FuelBridge`）は定理の仮説として取っているので、未供給の部分は仮説の形で見える。
3. 登録する前提は 4 件（N1-a `DeclValuePh`、N2-b `PackTupleInputsBridge`、N3-b `RawNodePh` と `NormNodePh`）。完全型は `Tools/ShippingGen5ReaderTraceDirect.lean` の既存の形のまま（§1）。
4. 除去する行は 3 件（C.RT-2、C.CV-2、C.CV-3）。**C.RT-2 を除去してよいか（RT-2 の文が `ShapeInputs'` で尽きるか）は reviewer の判断**（RT_CLOSE_PLAN §2 / REV16 §7 が未決と記録、§2.2）。
5. 純差分は **FG +4 −3 = +1**（U1 の −3 と合わせて −2）。inline 枝の仮説 `RecRulePh`（FG +1）と `pass_ph`（案 A: 0 / 案 B: +1）を含めると **U1 と合わせて FG −1 または 0**（§5）。束 B は、束 A の −2 より台帳は良くならない。範囲が縮まないことの代償であり、(1)/(2) の選択（RT_CLOSE_PLAN §4）はユーザー判断として残る。
6. reviewer 判断: (a) 4 件の登録とその置き場所（§1.3）、(b) 3 行の除去（§2）と RT-2 の判定、(c) 合成定理の型（§3）と葉の取り方、(d) inline 枝の仮説の取り方（§4）、(e) 純差分の数え方（§5）、(f) Check 計画（§7）。

## 1. 登録する前提（4 件）

### 1.1 完全型（`set_option autoImplicit false` の下で elaborate した `#print` の出力、一字一句）

```
def Tools.Assume.EnvDeclValue.DeclValuePh : Lean.Environment → Prop :=
fun env =>
  ∀ (n : Lean.Name) (d : Lean.DefinitionVal),
    env.find? n = some (Lean.ConstantInfo.defnInfo d) →
      Tools.ShippingGen5ReaderTrace.NoPh d.value = true ∧ Tools.ShippingGen5ReaderTrace.BvarLt 0 d.value = true
def Tools.Assume.PackTupleBridge.PackTupleInputsBridge : Prop :=
∀ (e : Lean.Expr),
  Tools.ShippingGen5ReaderTrace.NoPh e = true →
    Tools.ShippingGen5ReaderTrace.BvarLt 0 e = true →
      Sparkle.Compiler.MachTupleIn.packTupleInputs e =
        Tools.ShippingGen5ReaderTracePack.packTupleInputsF (Tools.ShippingGen5ReaderTracePack.lamDepth e) e
def Tools.Assume.NormNodePh.RawNodePh : Sparkle.Compiler.Elab.StructEnv → Prop :=
fun senv =>
  ∀ (L : Nat) (f a e' : Lean.Expr),
    Tools.ShippingGen5ReaderTrace.NoPh f = true →
      Tools.ShippingGen5ReaderTrace.NoPh a = true →
        Tools.ShippingGen5ReaderTrace.BvarLt L f = true →
          Tools.ShippingGen5ReaderTrace.BvarLt L a = true →
            Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch (f.app a) = some e' →
              Tools.ShippingGen5ReaderTrace.NoPh e' = true ∧ Tools.ShippingGen5ReaderTrace.BvarLt L e' = true
def Tools.Assume.NormNodePh.NormNodePh : Sparkle.Compiler.Elab.StructEnv → Prop :=
fun senv =>
  ∀ (L : Nat) (f a : Lean.Expr),
    Tools.ShippingGen5ReaderTrace.NoPh f = true →
      Tools.ShippingGen5ReaderTrace.NoPh a = true →
        Tools.ShippingGen5ReaderTrace.BvarLt L f = true →
          Tools.ShippingGen5ReaderTrace.BvarLt L a = true →
            Tools.ShippingGen5ReaderTrace.NoPh (Sparkle.Compiler.Elab.machNormNode senv (f.app a)) = true ∧
              Tools.ShippingGen5ReaderTrace.BvarLt L (Sparkle.Compiler.Elab.machNormNode senv (f.app a)) = true
```

`PackTupleInputsBridge` の右辺が使う双子モデルは `Tools/ShippingGen5ReaderTraceDirect.lean` の既存定義で、登録の際に同じ型で一緒に移る（登録する前提の一部ではなく、前提の文を読むための定義）:

```
def Tools.ShippingGen5ReaderTracePack.lamDepth : Lean.Expr → Nat
  | .lam _ _ b _ => lamDepth b + 1
  | _ => 0
def Tools.ShippingGen5ReaderTracePack.packTupleInputsF : Nat → Lean.Expr → Lean.Expr   -- Direct.lean:27-37
```
（`packTupleInputsF` の本体は `Direct.lean` の該当行をそのまま移す。ここには再掲しない。移設後の Check で値を比較する。）

### 1.2 各前提の意味・成立の根拠・限界

| 前提 | 内容 | どこで使うか | 成立の根拠として見つかっているもの | 限界（主張しないこと） |
|---|---|---|---|---|
| N1-a `DeclValuePh env` | env の `defnInfo` の値が `NoPh ∧ BvarLt 0`（placeholder を含まず、束縛変数が閉じている） | `shapeInputs_of_direct'` の `hdecl`、inline 枝の P1（`userDefinition?_ph`）・S1（`inlAbbrevs_ph`） | Lean の kernel は定義の値が閉じていることを検査する（通常の理解）。placeholder `_machIn` 等は Sparkle のコンパイラが作る項で、ユーザーの定義の値には現れない見込み | 実際の受理済みソースの env で成り立つことは示していない。「NoPh」は Sparkle 内部の定義で、kernel の検査ではない |
| N2-b `PackTupleInputsBridge` | `NoPh ∧ BvarLt 0` の入力で、production の `packTupleInputs`（`partial`）が全域モデル `packTupleInputsF (lamDepth e)` に一致 | `packTupleInputsF_ph` 経由で `shapeInputs_of_direct'` の `hpack` | `packTupleInputs` の再帰は `lam` の本体への構造再帰で、`lamDepth` 回で止まる見込み（読み。形式証明はしていない） | `partial def` の本体は論理に見えない。一致は読みであって証明ではない |
| N3-b `RawNodePh senv` | `rawNode` が `NoPh ∧ BvarLt L` の `app` を `NoPh ∧ BvarLt L` に写す | `machNormF_ph`（`hraw`） | `rawNode` の各腕が部分項の再構成であることを読んだ範囲 | `rawNode` の全腕の証明はしていない。`MachRawSurface.rawNode` の中の `zeroLit` は S1 の `ReplaceAgrees` の領域 |
| N3-b `NormNodePh senv` | `machNormNode` が同様に保存 | 同上（`hnode`） | 同上 | 同上 |

* 4 件とも**保存則**（`NoPh ∧ BvarLt` を保つ）か**モデル一致**で、`LiftAgrees` / `Inst1Agrees` のような C++ extern との一致ではない。T1 ではなく FG として数える（RT_CLOSE_PLAN §3.1 と同じ）。
* 「全域化して証明」の方針（ユーザー）との関係: N2-b / N3-b は `partial def` の挙動なので、ptot-m4 の前例どおり fuel 版へ全域化すれば除ける可能性がある。ただし production の変更（compiler）でユーザー承認が要るため、この freeze では**仮定として登録する**（RT_CLOSE_PLAN §3.1 末尾と同じ。全域化できれば +4 は減る可能性がある）。
* これらを**実 run で成り立つと主張しない**。`hci : CiDirect env ci0`（C0 の `ci_of_readsAt`）と同様、名前付きの入力条件。

### 1.3 置き場所（reviewer 判断）

現在、4 件の `def` は `Tools/ShippingGen5ReaderTraceDirect.lean` の中（`namespace Tools.Assume.EnvDeclValue` / `Tools.Assume.PackTupleBridge` / `Tools.Assume.NormNodePh`）にあり、`Tools/Assume/` には無い。登録は次の形を提案する（承認後に実施）:

* 新規 `Tools/Assume/EnvDeclValue.lean`、`Tools/Assume/PackTupleBridge.lean`（`lamDepth` / `packTupleInputsF` を含む）、`Tools/Assume/NormNodePh.lean`。名前空間・名前・型は §1.1 のまま。ヘッダに既存の `Tools/Assume/EnvSigTy.lean` / `AbbrevExtern.lean` と同じ形で「なぜ証明できないか」「根拠」「限界」を書く。
* `Direct.lean` は**定義の移動だけ**を行う（`def` を消して `import Tools.Assume.…` を足す。定理の本体は変えない）。受理済みファイルの編集になる。
* 代替案: `Direct.lean` を触らず、`Tools/Assume/` の新規ファイルを `Direct.lean` に import させる形はできない（定義が二重になる）。したがって移動が必要。
* 移動後の Check: 4 件の `def` と 2 つの双子定義を値で比較（旧 `Direct.lean` の綴りから独立に Check 内に書く）。`shapeInputs_of_direct'` / `shapeInputs_of_direct` の型が不変であること。
* この移動は skeleton には含めない（skeleton は仮説として取る）。

## 2. 除去する行（3 件）と消費側の原文

### 2.1 FG 台帳の原文（`par/fg-ledger-sync:scripts/gen2/premise_ledger/C_M5dg.md`、分類は索引 UN-C）

**C.CV-2** `hnl : LetsNoLoose st`（R-nl）
- 完全な型: `LetsNoLoose (st : MachRead) : Prop := ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr), st.lets[j]? = some (nm, kd, v) → ∀ b, ¬ LooseOcc 0 v b`（Cover3.lean:699）
- 仮定している定理: `rowC_of_reader`, `rowC_of_reader_ok`。支払い予定: dg-readertrace。分類: 未供給の義務

**C.CV-3** `hi : FullInv nDecl st`／`FReachC`（readF の trace）
- 完全な型: `FullInv (nDecl : Nat) (st : MachRead) : Prop := CallOrderInv st ∧ RangeInv nDecl st ∧ OrigAligned st ∧ EntryKinds st`（Cover3.lean:316）; `fullInv_reachC {nDecl} {st0 st} (h : FullInv nDecl st0) (hr : FReachC nDecl st0 st) : FullInv nDecl st`（Cover6）
- 仮定している定理: `rowA3_of_inv`, `rowA4B23_mem_of_inv`, `rowB1_of_inv`, `rowC_of_reader(_ok)`, `fullInv_reachC`。分類: 未供給の義務

**C.RT-2** `hpre : TracePre senv nDecl (Call.…)`
- 完全な型: `TracePre senv nDecl c := Pre c ∧ PhPre senv nDecl c`、`PhPre` は call 種別ごと（conv/nested/inst/instS/chain/loopBody/loopRoot）に `TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (… + nDecl) e = true` 等を課す（ReaderTraceCtl.lean:47-70）
- 仮定している定理: `chain_basic_trace`, `conv_basic_trace`。FG/T1: DG-COVER R-in。支払い予定: dg-readertrace。分類: 未供給の義務

### 2.2 行と出す定理の対応

消費側（`Tools/ShippingGen5Cover3Canon.lean`、`#check` の出力）:

```
@Tools.ShippingGen5Cover3Canon.rowC_of_reader_canon : ∀ {d : Tools.ShippingMachineAuto.MachineData}
  {st : Sparkle.Compiler.Elab.MachRead},
  Tools.ShippingGen5Cover3.ShapeAgree d st →
    Tools.ShippingGen5Cover3.FullInv (Tools.ShippingGen5Sem.kDOf d) st →            -- hi   ← C.CV-3
      Tools.ShippingGen5Cover3Canon.LetQuoteEqC d st →
        Tools.ShippingGen5Cover3.LetsNoLoose st →                                     -- hnl  ← C.CV-2
          (∀ (j : Nat), d.bpos j < d.nIn + d.ss.length + d.ls.length) →
            (∀ (j : Nat), d.vpos j < d.nIn + d.ss.length + d.ls.length) →
              ∀ (k : Nat), k < d.shape.insts.length →
                ∀ (l : Nat), l ∈ Tools.ShippingGen5Sem.callArgs d k → (Tools.ShippingGen5Sem.cleanLets d k)[l]? = some true
```

| 行 | 消費側の文（原文） | 出す定理（結論の該当部分） | どう消えるか |
|---|---|---|---|
| **C.CV-3** | `hi : FullInv (kDOf d) st` | `u2_compose` の結論の `FullInv (kDOf d) st` | `machineShapeF_reach'`（`Shape2.lean:82`）の `TrInv senv nDecl st`（`.1 : FullInv nDecl st`）を、`nDecl := nDeclOfCi E` で得て、`KDOfLeaf`（`kDOf d = nDeclOfCi E`、`sparkle-rt-kdof`）で `nDecl` を `kDOf d` に書き換える |
| **C.CV-2** | `hnl : LetsNoLoose st` | `u2_compose` の結論の `LetsNoLoose st` | `TrInv.2 : CtlPh`（`Ctl.lean:24-32`）の第 5 成分が `LetsNoLoose st`。`SameStLeaf` で W 系の `st` と reach 側の `st` を同一にして渡す |
| **C.RT-2** | `hpre : TracePre senv nDecl (Call.…)`（chain / conv の arm 補題の仮説） | `u2_compose` の仮説が尽きること（入口の `TracePre` は `shapeStart_trace'` が `ShapeInputs'` から作り、他の呼び出しの `TracePre` は `step_trace` が内部で作る） | **`ShapeInputs'` が `shapeInputs_of_direct'`（直接枝）／`InlineInputs`（inline 枝）で供給されれば、`machineShapeF_reach'` が内部で `TracePre` を作る**。RT-2 の文が `ShapeInputs'` で尽きるかは reviewer の判断（REV16 §7 が未決と記録）。**尽きないと判定された場合、RT-2 は残し、純差分は +4 −2 = +2（U1 と合わせて −1）になる** |

* 重要な正直な点: `u2_compose` は `hpre` を**引数として受け取らない**（`TracePre` は定理の内部で `shapeStart_trace'` と `step_trace` が作る）。したがって「RT-2 が消える」は、arm 補題の `hpre` 仮説が合成の内部で閉じる、という意味。
* `FReachC`（CV-3 の原文に含まれる）は `machineShapeF_reach'` の結論に含まれるが、消費側 `rowC_of_reader_canon` は `FullInv` だけを取るので、`u2_compose` の結論には出さない。`fullInv_reachC` を通す他の消費者（`rowA3_of_inv` 等）が `FReachC` を別に要求するかは、この freeze では確かめていない。

## 3. 合成定理の完全型

### 3.1 補助定義（`Tools/ShippingGen5ReaderTraceU2Compose.lean`、`#print` の出力、一字一句）

```
def Tools.ShippingGen5ReaderTraceU2.FuelBridge : Prop :=
∀ (E : Lean.ConstantInfo) (senv : Sparkle.Compiler.Elab.StructEnv) (sp : Sparkle.Compiler.Elab.MachineShape),
  Sparkle.Compiler.Elab.machineShape? false [] E senv = some sp →
    ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv = some (some sp)

def Tools.ShippingGen5ReaderTraceU2.KDOfLeaf : Prop :=
∀ (lvl : Lean.Expr → Nat) (E : Lean.ConstantInfo) (senv : Sparkle.Compiler.Elab.StructEnv)
  (sp : Sparkle.Compiler.Elab.MachineShape) (d : Tools.ShippingMachineAuto.MachineData) (dd : Lean.DefinitionVal),
  E = Lean.ConstantInfo.defnInfo dd →
    Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d →
      Tools.ShippingGen5Sem.kDOf d = Tools.ShippingGen5ReaderTrace.nDeclOfCi E

def Tools.ShippingGen5ReaderTraceU2.SameStLeaf : Prop :=
∀ (E : Lean.ConstantInfo) (senv : Sparkle.Compiler.Elab.StructEnv) (sp : Sparkle.Compiler.Elab.MachineShape) (n : Nat)
  (p : Tools.ShippingReaderFuel.ShapePre) (en : Lean.Expr) (st0 : Sparkle.Compiler.Elab.MachRead)
  (env : List Sparkle.Compiler.Elab.MachVal) (st1 st : Sparkle.Compiler.Elab.MachRead) (v : Lean.Expr)
  (p' : Tools.ShippingReaderFuel.ShapePre) (en' : Lean.Expr) (st0' : Sparkle.Compiler.Elab.MachRead)
  (env' : List Sparkle.Compiler.Elab.MachVal) (st1' st' : Sparkle.Compiler.Elab.MachRead) (v' : Lean.Expr),
  Tools.ShippingGen5GDCover1.StateSideWitness E senv sp n p en st0 env st1 st v →
    Tools.ShippingGen5GDCover1.StateSideWitness E senv sp n p' en' st0' env' st1' st' v' → st = st'

def Tools.ShippingGen5ReaderTraceU2.InlineInputs : Lean.Environment → Prop :=
fun env =>
  ∀ (ci0 : Lean.ConstantInfo),
    Tools.ShippingGen5ReaderTrace.CiDirect env ci0 →
      ∀ (sm : Bool) (ps : List (String × Nat)) (n : Nat),
        Tools.ShippingGen5ReaderTrace.ShapeInputs'
          (Tools.ShippingGen5ReaderTrace.nDeclOfCi
            (Sparkle.Compiler.Elab.inlinedConst (Sparkle.Compiler.Elab.userInliner env) ci0))
          (Sparkle.Compiler.Elab.structEnv env) sm ps
          (Sparkle.Compiler.Elab.inlinedConst (Sparkle.Compiler.Elab.userInliner env) ci0) n
```

* `FuelBridge` は C.CV-4（`ShapeFuelBridge`、残る行）の `hbr` の原文と同じ型（`GDCover1.stateSide_of_production` の binder と一致）。**行は増えも減りもしない**。
* `KDOfLeaf` は `sparkle-rt-kdof` が与える定理の型、`SameStLeaf` は `sparkle-rt-samest` が与える定理の型として**この freeze が要求する形**。両 Issue の skeleton の型が違う場合は、この freeze の型へ薄い wrapper で合わせる（新しい前提は足さない）。`KDOfLeaf` が `E = .defnInfo dd` を仮定するのは、`nDeclOfCi` が非 `defnInfo` で 0 を返す定義のため（`shapePre_facts` で受理済みの `shapePre` は `defnInfo` を返す）。
* `SameStLeaf` は `machineShapeF n … = some (some sp)` が決定的であること（同じ fuel・同じ入力の二つの run は同じ結果）から出る見込み。経路は読んだが、この freeze では証明していない（`sparkle-rt-samest` の範囲）。
* `InlineInputs` は `sparkle-rt-inline-compose` の結論（`userInliner_ph` から作る inline 枝の `ShapeInputs'`）の型。**`RecRulePh` と `pass_ph` はこの型に現れない**（inline-compose の定理の仮説になる、§4）。

### 3.2 合成定理（`#check` の出力）

```
u2_compose : Tools.Assume.ExprEqv.EqvAtom →
  Tools.Assume.N3Extern.ZeroLitAgrees0 →
    Tools.ShippingLetsReaderInv.LiftAgrees →
      Tools.ShippingLetsReaderInv.Inst1Agrees →
        ∀ (env : Lean.Environment),
          Tools.ShippingLetsReaderInv.EnvTypesFVarFree env →
            Tools.Assume.EnvSigTy.SigTyClosed (Sparkle.Compiler.Elab.structEnv env) →
              Tools.Assume.EnvInstS.InstSFieldsDet (Sparkle.Compiler.Elab.structEnv env) →
                Tools.Assume.EnvDeclValue.DeclValuePh env →
                  Tools.Assume.PackTupleBridge.PackTupleInputsBridge →
                    Tools.Assume.NormNodePh.RawNodePh (Sparkle.Compiler.Elab.structEnv env) →
                      Tools.Assume.NormNodePh.NormNodePh (Sparkle.Compiler.Elab.structEnv env) →
                        InlineInputs env →
                          FuelBridge →
                            KDOfLeaf →
                              SameStLeaf →
                                ∀ {ci0 E : Lean.ConstantInfo},
                                  Tools.ShippingGen5ReaderTrace.CiDirect env ci0 →
                                    E = ci0 ∨
                                        E = Sparkle.Compiler.Elab.inlinedConst (Sparkle.Compiler.Elab.userInliner env) ci0 →
                                      ∀ {dd : Lean.DefinitionVal},
                                        E = Lean.ConstantInfo.defnInfo dd →
                                          ∀ {sp : Sparkle.Compiler.Elab.MachineShape},
                                            Sparkle.Compiler.Elab.machineShape? false [] E
                                                  (Sparkle.Compiler.Elab.structEnv env) = some sp →
                                              ∀ {lvl : Lean.Expr → Nat} {d : Tools.ShippingMachineAuto.MachineData},
                                                Tools.ShippingGen5DataOf.dataOfAt lvl E
                                                      (Sparkle.Compiler.Elab.structEnv env) sp = some d →
                                                  ∃ n p en st0 env' st1 st v,
                                                    Tools.ShippingGen5GDCover1.StateSideWitness E
                                                        (Sparkle.Compiler.Elab.structEnv env) sp n p en st0 env' st1 st v ∧
                                                      Tools.ShippingGen5Cover3.ShapeAgree d st ∧
                                                        Tools.ShippingGen5Cover3.FullInv (Tools.ShippingGen5Sem.kDOf d) st ∧
                                                          Tools.ShippingGen5Cover3.LetsNoLoose st
```
公理: `propext, Classical.choice, Quot.sound`（`#print axioms`、`u2_compose` と `u2_rowC`）。

* 前提の内訳（`hbranch` の左の枝は N1-a / N2-b / N3-b を使い、右の枝は `InlineInputs` を使う。どちらの枝も同じ定理の仮説に並ぶ）:
  * U1 の数えた行: `EnvTypesFVarFree env`（T1L-53）、`SigTyClosed (structEnv env)`、`InstSFieldsDet (structEnv env)`（FG 登録済み）、`LiftAgrees`（T1L-50）、`Inst1Agrees`（T1L-51）。`RootFloatAgrees` は `rootFloatAgrees hla` で導出（ptot-m4）。
  * 既存の T1 行: `EqvAtom`（T1L-72）、`ZeroLitAgrees0`（T1L-54。S1 が `ReplaceAgrees` へ付け替える候補、§5）。
  * 登録する 4 件（本 freeze）: `DeclValuePh` / `PackTupleInputsBridge` / `RawNodePh` / `NormNodePh`。
  * 残る行: C.CV-4（`FuelBridge`）、C.EN-6（`hci : CiDirect env ci0` は C0 の名前付き入力で、行にしない）。
  * 葉（別 Issue の定理）: `KDOfLeaf`、`SameStLeaf`、`InlineInputs env`。
* 補助定理 `u2_compose_direct`（直接枝、`hci : CiDirect env E`、`InlineInputs` を取らない）、`u2_compose_inline`（inline 枝、N1-a / N2-b / N3-b / `ZeroLitAgrees0` を取らない）、`u2_core`（`hIn : ∀ n, ShapeInputs' (nDeclOfCi E) …` から結論を出す共通部分）、`dims_of_dataOfAt`、`u2_rowC`（`rowC_of_reader_canon` の `hi` / `hnl` を `u2_compose` で作って適用）。すべて同じファイルで sorry なしに通っている。
* 証明の流れ（`u2_core`）: `FuelBridge` で `n` を得る → `machineShapeF_state_side`（W 系の witness）→ `readF_traceGood_of_premises`（U1）→ `machineShapeF_reach'`（`EqvAtom`、`ShapeInputs'`）→ reach 側の最終状態から `StateSideWitness` を組む → `SameStLeaf` で W 系の `st` と同一視 → `ShapeAgree`（`shapeAgree_of_sides`、`dims_of_dataOfAt`）→ `KDOfLeaf` で `nDecl` を書き換え → `TrInv.1` と `CtlPh` の第 5 成分。

## 4. inline 枝の仮説の取り方（`RecRulePh` / `pass_ph`）

`InlineInputs env`（§3.1）は inline-compose の定理の結論で、**その定理の仮説**として `RecRulePh` と `pass_ph` が入る。この freeze は `InlineInputs env` を仮説として取り、中身を展開しない:

| inline 枝の部品 | 状態 | 供給元 | この freeze での扱い |
|---|---|---|---|
| P1 `inlineDefs_ph` / `userDefinition?_ph` | 受理済み（`par/rt-inline-p1`、base に含まれる） | — | `InlineInputs` の中。N1-a `DeclValuePh` を使う |
| S1 `inlAbbrevs_ph`（`ReplaceAgrees` U-1 / `HeadBetaAgrees0` U-2） | rt-abbrev-s1（base に含まれる。`Tools/Assume/AbbrevExtern.lean`） | 別 Issue（T1 の登録はそちらの freeze） | `InlineInputs` の中。U2 では数えない |
| `rounds` / `relevantClosure` の場合分け・`inlFoldNat` の合成 | `sparkle-rt-inline-compose` が担当 | 別 Issue | `InlineInputs` の中 |
| `pass_ph`（`MachRecUnfold.pass` の保存） | 全域化は `sparkle-rt-pass-total`。案 A（fuel 化、compiler 変更でユーザー承認）／案 B（`PassPh`、FG +1） | 別 Issue | inline-compose の定理の仮説。U2 は取らない |
| `RecRulePh`（`rec` 規則の閉性） | `sparkle-rt-recrule` の freeze | 別 Issue | inline-compose の定理の仮説。U2 は取らない |

* 完成形では、`u2_compose` を呼ぶ側が `hInl : InlineInputs env := inlineCompose_thm … hRec hPass …` の形で `RecRulePh env` と `pass_ph` を仮説として持ち込む。型が確定するのは inline-compose / pass-total / recrule の freeze の後。**この freeze は `RecRulePh` / `pass_ph` の型を固定しない**（固定すると他 Issue の型とずれるため）。台帳の数え方だけ §5 に書く。
* 直接枝だけを使う場合（`hbranch` の左）でも、定理の型は `InlineInputs env` を仮説に要求する。直接枝専用には `u2_compose_direct` を使う。
* 範囲の確認（`RT_BRANCH_MEASURE`）: 直接枝（`CiDirect`、inline しても構造が変わらない）は機械経路 475 件中 208 件。inline 枝は変わる 267 件を含む。束 B はこの 267 件を範囲に残す。ただし 267 件に対して `InlineInputs` が成り立つことは、`RecRulePh` / `pass_ph` / S1 が成り立つ範囲の話で、この freeze では示していない。

## 5. 台帳の純差分

| 単位 | 足す行 | 消える行 | FG 純差分 | T1 |
|---|---|---|---|---|
| U1（`sparkle-rt-u1`、受理待ち） | 0 | RT-1, RT-3, RT-4（−3） | −3 | 0 |
| **U2 本体（この freeze）** | N1-a, N2-b, N3-b `RawNodePh`, N3-b `NormNodePh`（+4） | RT-2, CV-2, CV-3（−3） | **+1** | 0 |
| U1 + U2 | +4 | −6 | **−2**（103 → 101。U1 を受理済み FG 100 から数えると 100 → 101） | 0 |
| ＋ `RecRulePh`（inline 枝、`sparkle-rt-recrule`、FG +1 候補） | +1 | 0 | U2 を含む束で **+2**、U1 と合わせて **−1**（103 → 102） | 0 |
| ＋ `pass_ph` 案 A（fuel 化。compiler 変更でユーザー承認） | 0 | 0 | 0 | 0 |
| ＋ `pass_ph` 案 B（`PassPh`、FG +1） | +1 | 0 | +1 | 0 |
| **U1 + U2 + RecRulePh + pass_ph 案 A** | +5 | −6 | **−1**（103 → 102） | 0 |
| **U1 + U2 + RecRulePh + pass_ph 案 B** | +6 | −6 | **0**（103 → 103） | 0 |
| （参考）S1（rt-abbrev-s1） | — | — | 0 | S1 の freeze 記載で T1 純 +1（`HeadBetaAgrees0` +1、`ReplaceAgrees` が `ZeroLitAgrees0` を置換して ±0）。U2 では数え直さない。現在の T1 56 に含まれているかを私は数えていない（未計数） |

* 数字は**すべて見込み**で、登録・除去の反映は reviewer 承認後。FG と T1 は合算しない。
* 束 A（直接枝のみ）の U1 + U2 は FG −2（RT_CLOSE_PLAN §3.1）と同じ数。**束 B は同じ −2 に `RecRulePh` と `pass_ph` が加わるので、案 A でも −1 に留まる**。範囲を縮めない代わりに、台帳の減りが小さい。
* RT-2 が `ShapeInputs'` で尽きないと reviewer が判断した場合: U2 本体は +4 −2 = +2（U1 と合わせて −1、案 A まで含めて 0）。
* 前提 delta の増加（+4）を含むので、承認済み freeze の証明実装として manifest 付き proof-accept にするには、**この freeze の承認が先**。

## 6. skeleton の状態（Issue 指示 2）

* ファイル: `Tools/ShippingGen5ReaderTraceU2Compose.lean`（新規）。`lakefile.lean` に `lean_lib «Tools.ShippingGen5ReaderTraceU2Compose»` を追加。
* 検証: `kjob lake build Tools.ShippingGen5ReaderTraceU2Compose`（Pod 内、キャッシュ付き target build）exit 0、`declaration uses sorry` 警告 0。`#print axioms` は標準 3 公理。
* **sorry の一覧: なし**。葉は sorry ではなく定理の仮説（`KDOfLeaf` / `SameStLeaf` / `InlineInputs` / `FuelBridge`）として取っているので、未供給の部分が型に現れる。葉を埋める担当: `KDOfLeaf` = `sparkle-rt-kdof`、`SameStLeaf` = `sparkle-rt-samest`、`InlineInputs` = `sparkle-rt-inline-compose`（`RecRulePh` = `sparkle-rt-recrule`、`pass_ph` = `sparkle-rt-pass-total`）。
* base の build: 統合 tree（rt-int2 c21e00a6）で、skeleton の import（`Tools.ShippingGen5ReaderTraceDirect2` / `Dispatch` / `GDCover1` / `Cover3Canon`）を含む 817 モジュールが通った（キャッシュなしの初回は約 18 分）。
* 登録用の `Tools/Assume/` ファイルは**承認後**に作る（skeleton は仮説として取る）。
* この skeleton は sorry なしだが、**葉が仮説のため受入・台帳の減算には数えない**。台帳の減算は、葉の定理が受理され、仮説が定理で置き換わり、登録が済んだ後。

## 7. Check の計画（承認後。`Tests/Gen5/ReaderTraceU2Check.lean`、新規）

`Tests/Gen3/ExpectedType` の `checkExpected`（Rev21Check / U1Check と同じ方法）。

1. **TYPE**: §1.1 の 4 件の `def` と `lamDepth` / `packTupleInputsF`（値）、§3.1 の 4 つの補助定義、`u2_compose` / `u2_compose_direct` / `u2_compose_inline` / `u2_core` / `u2_rowC` の型を、Check 内に自分の綴りで書いた `Exp…` と defeq で比較。mutant（well-typed な単一変更を signature / defeq で棄却。意味的反例ではない）: N1-a の `BvarLt 0` を `BvarLt 1` に、`hbranch` の `∨` を `∧` に、`KDOfLeaf` の `=` の向きを逆に、`InlineInputs` の `inlinedConst` を外す、`FullInv (kDOf d) st` を `FullInv (nDeclOfCi E) st` に。
2. **BINDERS**: `u2_compose` の型の Prop binder の先頭定数の集合が、§3.2 の許された集合（U1 の 5 + `EqvAtom` + `ZeroLitAgrees0` + 登録 4 + `InlineInputs` + `FuelBridge` + `KDOfLeaf` + `SameStLeaf` + `CiDirect` + `machineShape?` と `dataOfAt` の等式）に過不足なく一致すること。
3. **CLOSURE / WATCH**: 閉包に `sorryAx` / `Lean.ofReduceBool` / `Lean.trustCompiler` が無いこと、監視リストの名前（登録外の前提候補: `RecRulePh`、`PassPh`、`ReplaceAgrees`、`HeadBetaAgrees0`、`ShapeFuelBridge` 等）が `u2_compose` の閉包に**入らない**こと（それらは `InlineInputs` の中身であり、型に現れない）。完全修飾 `Name` の照合（U1Check と同じ）。
4. **AXIOMS**: 標準 3 公理のみ。
5. **POSITIVE**: 葉を埋めた最終形では、`InlineInputs env` を `inlineCompose` の定理から作り、`KDOfLeaf` / `SameStLeaf` を定理で渡して、`u2_compose` を前提の数だけの binder で呼べること。

## 8. 主張しないこと

N1-a / N2-b / N3-b が実際の run や受理されたソースで成り立つこと。`hci`（C0）、`FuelBridge`（C.CV-4）が成り立つこと。`KDOfLeaf` / `SameStLeaf` / `InlineInputs` が証明できること（別 Issue の範囲で、ここでは型を固定しただけ）。RT-2 が `ShapeInputs'` で尽きること（reviewer の判断）。`RecRulePh` / `pass_ph` の型（他 Issue の freeze に従う）。T1 の現在値 56 に S1 の +1 が含まれるか（数えていない）。純差分の数字は見込みで、登録・反映済みではない。inline 枝の 267 件に対して `InlineInputs` が成り立つこと。mutant は signature / defeq での棄却であって意味的反例ではない。
