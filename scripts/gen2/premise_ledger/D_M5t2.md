# 前提台帳 D_M5t2（M5 t2 系 10 Issue）

読み取り専用調査。Lean 型は `git show <branch>@<SHA>:<path>` の原文。「この調査では見つからなかった」は経路/供給元を見つけられなかったという意味のみ。mutant の棄却は signature/defeq での棄却であり、意味的反例ではない。

FG は scripts/gen2/GENERAL_SPEC.md §1.1 を指す。binder は `L`、`Start`、RunsTo の二択、`ReflectsAll`、結論 `∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D`。T1 側は `T1Hyp` のフィールド `pkg`、`defines`、`closes`、`dec`、`closed`（Tools/ShippingGen2Defs.lean:201）。

## 0. Issue ごとの履歴要約

| Issue | 最新 approved/done | 対象SHA / branch | 検証 | 残り・後続 |
|---|---|---|---|---|
| sparkle-gen5-t2probe | seq2447 done（seq2446 scoped-approved） | par/gen5-t2 source 0bb53938（docs 47b9b679、wording 8db3b877） | g5t2-0bb53938 exit 0、930 jobs。P1 は 2 呼び出し（topshare2 k=0、wrapQ k=0）の十分性のみ。P2 は GenFacts+CallOut が LetTie を決めないことの非含意のみ | `¬HPointAt` は主張しない。一般の生成 package coverage は未証明。M5/G-CALLDEC/FG は open。後続の changes_requested はなし |
| sparkle-gen5-t2cover | seq2832 approved → seq2834 done（設計のみ） | par/gen5-t2 c398021c（T2COVER_FREEZE.md rev2） | 設計レビューのみ、ビルドなし。Lean 文は未 elaborate の提案 | E1 は ClosingRun/GeneratedAt の全 field の供給まで条件付き。hrow と G-SERVED は残る。DC-FORM/DC-SUPPLY、全成功 run coverage、共有 ClosingRun/hrow、dataOf_sound、genSem/causality は供給側 Issue。E2 は検証証拠のみで DeclConnect の代替ではない。新 TRUSTED/law/compiler 変更/Nonempty/GenWF 強化は無し |
| sparkle-gen5-t2-tie | seq3923 approved、seq3925 approved（header 同期） | kjob/g5tt-cr6 456699fc（Lean af02c300）。header 同期 632f365d（kjob/g5tt-sync、コメントのみ） | ttcr6-456699fc exit 0、776 jobs、src=base=end、dirty=false。TYPE 6、MUTANT 14（signature/defeq 棄却）、AXIOMS 4 標準、REACH 4。sorry なし | hDG_SEM は dg-sem の P4e 待ち。hOW/hkidW/hrows は data-supply 待ち。非空虚性と depth0 stop は dg-closingrun 待ち。GENP の全成功 run coverage は未完。Issue は doing。changes_requested/doing の後続はなし |
| sparkle-gen5-dc-connect | seq5310 approved（U-RUNT 5 定理）。seq5327 は U-CORENR の freeze のみ approved | 承認済み Lean は kjob/g5dc-r21〜r23 の 0fcce4e7。U-CORENR 実装は 74343ad8（kjob/g5dc-r23、base 28f2627c）で未レビュー | dc21v-0fcce4e7 exit 0、751 jobs。TYPE5、SOURCE-PIN4、MUT39、AX5（propext のみ）。74343ad8 は agent 増分ビルドのみで、clean ビルド dc23v-74343ad8 は実行中 | 後続は seq5333/5351/5501/5504 の doing。MachineDefines/MachineClosesAtA/Start 自体、leaf（insts=[]）、最適化 body との (a3)、TopShips on D′、O3、実 EntryWitness/ReflectsAll/Post/FG は未供給。前提台帳の回答待ちで次単位は起こさない |
| sparkle-gen5-boundary-audit | seq5081 approved（U8 freeze のみ。U8 の Lean は未実装）。最後の実装承認は seq5064（U7） | kjob/g5ba-r16 の U7 3f5bcb2e。U8 freeze は 96e862fe | ba15v exit 0（U7）。U5 は ba11v-76ae2e8e exit 0、724 jobs、TYPE1/MUTANT4/AXIOMS1 | seq5572 todo「台帳待ちで一時停止」。再開条件は前提が実 run から払う 2〜3 本に選ばれたとき |
| sparkle-gen5-t2-emit | 履歴は created と dependencies のみ（承認なし） | なし | なし | 依存: dg-sem、dg-dataof。内容は「#machine_call_ties validation (E2, new files, evidence only)」 |
| sparkle-gen5-gencall-proof | 履歴は created と dependencies のみ | なし | なし | 依存: dgen、t2cover。内容は「生成器から LetTie/CallOut/HPointAt を一般に供給」 |
| sparkle-gen5-package-coverage | todo のみ（seq2797。相談で未承認） | par/gen2-spec d795c916（§6 Q5） | design only | Q5 ShapeFuelBridge (O1/O2) を DG-COVER D2(b) の境界として 1 回だけ述べ、SRC-ARGW SIG が消費する。並行する Prop は作らない |
| sparkle-gen5-decl-bridge | todo のみ（seq2795。相談で未承認） | par/gen2-spec d795c916 scripts/gen3/SRC_ARGW_SUPPLY_FREEZE.md §6 Q1/Q2 | design only | Q1 kind 添字の source-kinding carrier（SrcKinding/SrcKindingLaws。Bool と `.bits 1` の区別を含む）。Q2 `adapterOf_portWidths` |
| sparkle-gen5-reader-bridge | todo のみ（seq2796。相談で未承認） | par/gen2-spec d795c916 §6 Q3/Q4 | design only | Q3 DG-ENV C0 が inst と instS の両方で全 world の SigEq を与えること。Q4 `packTupleInputs`（partial）の total 置換 |

t2-emit、gencall-proof、package-coverage、decl-bridge、reader-bridge には Lean 成果も approved note もない。このため前提ブロックは作らない。上記の残りの記述だけを記録する。

## 1. sparkle-gen5-t2probe（前提 3 件）

承認済み定理の宣言は次のとおり。par/gen5-t2@0bb53938:Tools/ShippingGen2T2Probe.lean:63。公理は標準のみ。
```lean
theorem hPointAt_of_ties (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q)
    (A : ArgFamB ι dom) (B : ArgFamV ι dom)
    (h2 : LetTie p q k hk A B) (h13 : CallOut p q k A B) :
    Tools.ShippingQuadHPoint.HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k
```
十分性のみ。逆は未証明（seq2446 の指摘）。

### P1: hP
- **Lean名**: `hP`
- **完全な型**: `P (p.d.shape.insts[k]'hk).1 = some q`
- **仮定している定理**: `hPointAt_of_ties`（par/gen5-t2@0bb53938）
- **FG/T1 のどこに効くか**: T1 の `pkg`（G3-GEN）に対応する package 存在。T1Hyp のどのフィールドに載るかは、この Issue の文書では不明
- **別名**: T2-TIE では `hDG_GENP`（同じ型）。下の T-7 を参照
- **支払い予定**: 後続の t2-tie（`calleePkg_of_t1ND`、条件付き）と dg-acc
- **実runから払えそうか**: 不明。この Issue の履歴・結果文書に根拠は書かれていない
- **分類**: 入力条件

### P2: h2（LetTie、t2）
- **Lean名**: `h2`（`LetTie`）
- **完全な型**: par/gen5-t2@0bb53938:Tools/ShippingGen2T2Probe.lean:38
```lean
def LetTie (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) (A : ArgFamB ι dom)
    (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
        (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1) =
      A i bools bits ∧
    Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
        (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1) =
      B i bools bits
```
  `ArgFamB`/`ArgFamV` は同ファイル 26/31 行で、`(i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → …` という families。
- **仮定している定理**: `hPointAt_of_ties`
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の CallDec/HPointAt の引数 tie（G-CALLDEC）
- **別名**: `LetTie p q k hk (decA p q k hk) (decB p q k hk)` は par/gen5-t2 の T2COVER_FREEZE rev2 §0 によると `rfl`。`letTie_dec`（Tools/ShippingGen5T2Dec.lean:47、632f365d で読んだ。T2-DEC 部分は ca10ee64 で承認 seq2856）として証明済み
- **支払い予定**: t2-tie（decoded family 経由で証明済み）。生成器の family に対する tie は gencall-proof（未開始）
- **実runから払えそうか**: decoded family 版は はい（`letTie_dec`）。生成器の family 版は、P2 が GenFacts+CallOut でも `¬LetTie` を満たす package を作れることを示した（`t1_not_letTie`、`t1_gen`）。そのため GenFacts だけからは出ない。結果文書はこの範囲に留める
- **分類**: 未供給の義務（生成器の family 版）。decoded family 版は証明済み

### P3: h13（CallOut、t1+t3）
- **Lean名**: `h13`（`CallOut`）
- **完全な型**: par/gen5-t2@0bb53938:Tools/ShippingGen2T2Probe.lean:50
```lean
def CallOut (p q : Pkg ι dom) (k : Nat) (A : ArgFamB ι dom) (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
      q.d.shape.layout.outs[k']? = some o ∧ o.name = p.d.shape.instFields.getD k "" ∧
      (q.src i (A i bools bits) (B i bools bits))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
          (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ
```
- **仮定している定理**: `hPointAt_of_ties`
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の CallDec（G-CALLDEC）
- **別名**: 一人出力 parent では name 条件が名前依存のままなので、`CallOutG`（Tools/ShippingGen2CallField.lean:90、`CallField` 版）に置き換える（seq2676 R3）。`CallOutF`（Tools/ShippingGen5T2Dec.lean:56）も同系
- **支払い予定**: t2-tie / T2-DEC（`hPointG_iff_callOutG`、`hPointG_iff_callOutDec`）。生成器側は gencall-proof
- **実runから払えそうか**: 不明。2 呼び出しの個別検証（`tm2_callOut`、`wQ_callOut` はカーネル rfl）のみ。一般の生成 package への拡張は未証明（seq2446/2447）
- **分類**: 未供給の義務

## 2. sparkle-gen5-t2cover（Lean 無し。設計 c398021c）

設計文書 par/gen5-t2@c398021c:scripts/gen5/T2COVER_FREEZE.md（305 行）。key 型は未 elaborate の提案。note に明記された未供給入力は次のとおり（seq2832/2834）。
- `ClosingRun`/`GeneratedAt` の全 field（E1 の条件）。
- `hrow` と G-SERVED（`closingRun_of_run` の明示前提）。
- `DeclConnect`（G3-DECL。E2 では代替できない）。
- DC-FORM / DC-SUPPLY（ConstValue 用）。
- 全成功 run の coverage、dataOf_sound、genSem/causality。
- `FieldOk` の静的供給（`callField_at` からは出ない）。

これらの支払い先は note に t2-tie、dg-closingrun、dc-connect、dg-sem 等の供給側 Issue と書かれている。個別 binder の詳細は各 Issue のブロックで扱う。ここでは前提ブロックを立てない（Lean 型なし）。

## 3. sparkle-gen5-t2-tie（前提 12 件）

対象: kjob/g5tt-cr6@456699fc。Lean 本体は Tools/ShippingGen5T2Tie.lean、T2Dec、T2Range、T2Conn、T2OutTy、T1ND、T2TieCR、T2TieCR2（par/gen2-spec 系の同一 tree。header 同期は kjob/g5tt-sync@632f365d）。読んだ SHA は 632f365d。

承認済みの主要定理は次の 6 本。
1. `callTie_of_dgen`（T2Tie.lean:259）
2. `callTie_of_served`（T2Tie.lean:276）
3. `stepDec_of_ties`（T2Tie.lean:312）
4. `callTie_of_served_widths` / `_oneOut` / `_kidW`（T2Conn.lean:35/49/65）
5. `callTie_of_closingShared_one_ex`（T2TieCR2.lean）
6. `callTie_of_closingShared_group_kidW`（T2TieCR2.lean）

`CallTie` の定義（T2Tie.lean:231）:
```lean
def CallTie (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : Prop :=
  LetTie p q k hk (decA p q k hk) (Tools.ShippingGen2.decB p q k hk) ∧
    CallOutF p q k (decA p q k hk) (Tools.ShippingGen2.decB p q k hk)
```
`stepDec_of_ties` は `T1Hyp.dec` の形（`MemDec ∨ ∃ q, CallDec`）を結論とする。T2-TIE 全体の FG 上の位置は `T1Hyp.dec`（G-CALLDEC / G-MEMCALLS）。

### T-1: hDG_SEM（GenExtAtCall）
- **Lean名**: `hDG_SEM`
- **完全な型**: Tools/ShippingGen5T2Tie.lean:238（632f365d）
```lean
def GenExtAtCall (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f →
    SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f
```
  形は `callTie_of_closingShared_one_ex` では `∀ q, P (insts[k]).1 = some q → GenExtAtCall p q k hk`。
- **仮定している定理**: `callTie_of_dgen`、`callTie_of_served`、`callTie_of_served_widths`/`_oneOut`/`_kidW`、`callTie_of_closingShared_one_ex`、`callTie_of_closingShared_group_kidW`、`callTie_of_closingShared_one`、`callTie_of_closingRun0_one`（いずれも kjob/g5tt-cr6@456699fc）
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の CallDec の「parent の call 結果 signal = callee src の出力」の部分（posEnc = f τ）
- **別名**: `hDG_SEM`（T2-TIE の呼称）。DG-SEM 行 `ext at nDecl+k`
- **支払い予定**: sparkle-gen5-dg-sem の P4e（`genExtAtCall_of_genSem`。DG_SEM_FREEZE_P4.md §8、under S1-S3）
- **実runから払えそうか**: この調査では見つからなかった。T2TIE_NEXT_FREEZE_R0 §1 row 2 は「GenExtAtCall の形の定理は built も frozen も無い」と記録している
- **分類**: 未供給の義務

### T-2: hDG_SEM_range（CallOutRange）
- **Lean名**: `hDG_SEM_range`
- **完全な型**: Tools/ShippingGen5T2Tie.lean:250（632f365d）
```lean
def CallOutRange (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f →
    OutRange (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f
```
- **仮定している定理**: `callTie_of_dgen`、`callTie_of_served`、`callTie_of_closingShared_one`、`callTie_of_closingRun0_one`。T2Conn 系（`callTie_of_served_widths` 等）と `_one_ex` / `_group_kidW` では別の前提（下記 T-3/T-4/houtTy）に置換されている
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の CallDec。旧 `T1Hyp.dec` が暗黙に含んでいた範囲条件（`posEnc = f τ` の成立に必要）
- **別名**: `CallOutWidthAt`（T2Range.lean:155、width 版）
- **支払い予定**: 置換版 `callOutRange_of_widths`（T2Range.lean:162）が `Pkg.src_range`（T2Range.lean:122）と `houtTy` と `CallOutWidthAt` から導出する。一人出力は T-3、group は T-4 が残る
- **実runから払えそうか**: `Pkg.src_range`、`callOutRange_of_widths` は built・承認済み。一人出力は `hOW`、group は `hkidW` を渡す必要があり、その払い元は T-3/T-4（この調査では見つからなかった）
- **分類**: 未供給の義務（組み立て済み、末端は T-3/T-4）

### T-3: hOW（OneOutWidth）
- **Lean名**: `hOW`（`OneOutWidth P p k`）
- **完全な型**: Tools/ShippingGen2FitChain.lean:893（632f365d）
```lean
def OneOutWidth (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length) (q : Pkg ι dom), P (p.d.shape.insts[k]).1 = some q →
    ∀ o : OutField, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth
```
- **仮定している定理**: `callTie_of_served_oneOut`（T2Conn.lean:49）、`callTie_of_closingShared_one_ex`（T2TieCR2.lean）
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の CallDec（範囲、一人出力 parent）。M3 の result-width 義務の再添字
- **別名**: `CallOutWidthAt`（`callOutWidthAt_of_oneOut`、T2Range.lean:188 で変換）。M3 側の G-ONEOUT-WID
- **支払い予定**: sparkle-gen3-data-supply（G-ONEOUT-WID / G-DATA）。T2TIE_NEXT_FREEZE_R0 §1 row 5 による
- **実runから払えそうか**: 補題 `oneOutWidth_of_strictP`（Tools/ShippingGen2DataBridge.lean:143、built）が `callWidthsStrict p.d p.kD (kidOutsP P p) = true` と `instFields = []` から導く。この Bool 行を `DataOk` や run から導く定理は、この調査では見つからなかった
- **分類**: 未供給の義務（M3/gen3 側。T1 台帳を参照）

### T-4: hkidW（group parent の幅）
- **Lean名**: `hkidW`
- **完全な型**: Tools/ShippingGen5T2Conn.lean:105（`callOutRange_of_closing_kidW`）、:131（`callTie_of_served_kidW_closing`）、T2TieCR2.lean（`callTie_of_closingShared_group_kidW`）
```lean
(hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
  Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
  ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
    (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
      some pt.ty.bitWidth)
```
- **仮定している定理**: `callOutRange_of_closing_kidW`、`callTie_of_served_kidW_closing`、`callTie_of_closingShared_group_kidW`（kjob/g5tt-cr6@456699fc）
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の CallDec（範囲、group parent）
- **別名**: `CallOutWidthAt`（`callOutWidthAt_of_kidW`）。M3 の hkidW
- **支払い予定**: sparkle-gen3-data-supply（T2TIE_NEXT_FREEZE_R0 §1 row 6）
- **実runから払えそうか**: この調査では見つからなかった。候補 `hkidW_of_data`（CallWidths.lean:62）、`hkidW_of_dataAM`（Srm4Core6.lean:115、`KidTA` 形）は `callWidthsOk` 行を要し、その行を供給する定理は無い。`∀ k, RealChildA` 形は `hkidW_of_dataAM` で覆われない（R0 文書の記述）
- **分類**: 未供給の義務（M3/gen3 側。T1 台帳を参照）

### T-5: hsh / hDG_CLOSINGRUN（ClosingShared、ClosingRun0）
- **Lean名**: `hsh`（`ClosingShared`）、`h`（`ClosingRun0`）、`hDG_CLOSINGRUN`（`callTie_of_served` 系の存在形）
- **完全な型**: `ClosingShared` は Tools/ShippingGen5ClosingRun2.lean:28（632f365d）
```lean
def ClosingShared (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc
```
  `hDG_CLOSINGRUN` は `callTie_of_served`（T2Tie.lean:276）の
```lean
∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
  ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
  (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
  Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1
```
- **仮定している定理**: `servedCall_of_closingShared_one`、`callTie_of_closingShared_one`、`callTie_of_closingRun0_one`、`servedCall_of_closingShared_group`、`callTie_of_closingShared_one_ex`、`callTie_of_closingShared_group_kidW`
- **FG/T1 のどこに効くか**: FG の RunsTo 仮定（実 run）から、`T1Hyp.dec` の CallDec に必要な child 結果 `r` を取り出す接続
- **別名**: dg-closingrun の `ClosingRun`（Tools/ShippingGen5ClosingRun.lean:48）の `shared` block。`ClosingRun0`（ClosingRun2.lean:118）
- **支払い予定**: sparkle-gen5-dg-closingrun（非空虚性、depth0 `stop`）
- **実runから払えそうか**: 履歴は、`ClosingShared` が `ClosingRun.shared` として実 run から得られる接続（`closingRun0_of_run`、`closingShared_of_run`）を built と記す。ただし `hrow`、`hord`、`hGen`、`hIH`、`hKI`、非空虚性、depth0 stop は未供給（R0 §1 rows 7-13）
- **分類**: 未供給の義務（dg-closingrun 側。各 binder は dg-closingrun の台帳を参照）

### T-6: hT（T1HypND）
- **Lean名**: `hT : T1HypND L P Reach DataOk`
- **完全な型**: Tools/ShippingGen5T1ND.lean:35（structure。フィールド `pkg`、`defines`、`closes`、`closed`。`T1Hyp` から `dec` を除いた verbatim コピー）
- **仮定している定理**: `calleePkg_of_t1ND`、`servedCall_of_closingShared_*`、`callTie_of_closingShared_*`、`houtTy_of_closingND`
- **FG/T1 のどこに効くか**: T1Hyp の 4 フィールドそのもの
- **別名**: `T1Hyp`（`T1Hyp.toND`、T1ND.lean）
- **支払い予定**: T1 側
- **実runから払えそうか**: T1 台帳を参照
- **分類**: T1 台帳を参照

### T-7: hDG_GENP
- **Lean名**: `hDG_GENP`
- **完全な型**: `P (p.d.shape.insts[k]'hk).1 = some q`
- **仮定している定理**: `callTie_of_served`、`callTie_of_served_widths` 系、`callTie_of_closingShared_one`
- **FG/T1 のどこに効くか**: T1 の `pkg`（G3-GEN）
- **別名**: t2probe の P1 `hP`
- **支払い予定**: `_one_ex` と `_group_kidW` では `calleePkg_of_t1ND`（T2TieCR2.lean）が `hT.pkg`・`hT.closed` から存在形で導出済み。`pkg` 自体は dg-acc の `genP_pkg`（A3、`kjob/g5ac-r3`）で、`GenSFacts K`、`hacc`、`hcl`、`ReachCover`、`hOk` が条件
- **実runから払えそうか**: 存在形は はい（`calleePkg_of_t1ND`、built）。T1 の `pkg` 自体は T1 台帳を参照
- **分類**: 入力条件（T1 の `pkg` に帰着）

### T-8: hT2_FIELD（CallField の per-i 存在）と FieldRowAt
- **Lean名**: `hT2_FIELD`、`hrow : FieldRowAt p k r.1`
- **完全な型**: `hT2_FIELD : ∀ i : ι, ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o`。`FieldRowAt`（T2Tie.lean:173）:
```lean
def FieldRowAt (p : Pkg ι dom) (k : Nat) (mc : Sparkle.IR.AST.Module) : Prop :=
  if p.d.shape.instFields = [] then ∃ outP, mc.outputs = [outP]
  else p.d.shape.instFields.getD k "" ∈ mc.outputs.map (·.name)
```
- **仮定している定理**: `callTie_of_dgen`（`hT2_FIELD`）、`callField_at`（T2Tie.lean:215、`hrow`）
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の `CallField`（出力選択）
- **別名**: `FieldOk`（T2COVER。静的版は別途要）
- **支払い予定**: 一人出力は `fieldRow_one_of_callStmt`（T2Tie.lean:178）が run の `CallStmt` から導出（built）。group は `servedCall_of_closingShared_group`（T2TieCR2.lean）が `closeInstsG_calls` / `closeInstsG_names` から導出（built・承認 seq3923）
- **実runから払えそうか**: はい（上記 2 補題）。ただし `hsh`（T-5）が前提
- **分類**: 組み立て済み。末端は T-5

### T-9: houtTy
- **Lean名**: `houtTy`
- **完全な型**: `∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width`
- **仮定している定理**: `callTie_of_served_widths` / `_oneOut` / `_kidW`、`callOutRange_of_widths`、`callOutRange_of_closing_kidW`
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の範囲条件
- **別名**: なし
- **支払い予定**: T2-OUTTY H1-H4（`houtTy_of_realChildND`、`reach_callee_of_t1ND`、`houtTy_of_closingND`。Tools/ShippingGen5T1ND.lean、seq2970 承認 20d6dfd3+392fc978）
- **実runから払えそうか**: はい。`hT.defines`/`hT.closed` と closing witness から導出（`outTy_of_core`、`synthesizeCombinational_reads`）。`T1Hyp.dec` は使わない（closure 監査で確認）
- **分類**: 組み立て済み。末端は T-5 / T-6

### T-10: hG_DATA_CALL_*（4 個）
- **Lean名**: `hG_DATA_CALL_co`、`hG_DATA_CALL_slots`、`hG_DATA_CALL_args`、`hG_DATA_CALL_len`
- **完全な型**: T2Tie.lean:298-306（`callDec_of_callTie`）、:312-321（`stepDec_of_ties`）
```lean
(hG_DATA_CALL_co : p.d.callsOk p.kD = true)
(hG_DATA_CALL_slots : p.d.ss.length = p.d.shape.layout.slots.length)
(hG_DATA_CALL_args : callArgsOkAt p.d p.kD k q.portWidths = true)
(hG_DATA_CALL_len : (p.d.shape.insts[k]'hk).2.1.length = q.ports.length)
```
  `stepDec_of_ties` 内は `∀ k hk, … → ∀ q, P (insts[k]).1 = some q → callArgsOkAt p.d p.kD k q.portWidths = true ∧ (insts[k]).2.1.length = q.ports.length`。
- **仮定している定理**: `callDec_of_callTie`、`stepDec_of_ties`
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の CallDec 内の「引数が range 内」部分
- **別名**: GENERAL_SPEC §4.4 の DataOk の Bool 行
- **支払い予定**: 未割当（この調査の履歴・文書には支払い先が書かれていない）
- **実runから払えそうか**: この調査では見つからなかった
- **分類**: 未供給の義務

### T-11: hG_MEMCALLS
- **Lean名**: `hG_MEMCALLS`
- **完全な型**: `∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? ≠ none → MemDec p k (p.d.shape.insts[k]).1`（T2Tie.lean:322、`stepDec_of_ties`）
- **仮定している定理**: `stepDec_of_ties`
- **FG/T1 のどこに効くか**: `T1Hyp.dec` の `MemDec` 側（G-MEMCALLS）
- **別名**: なし
- **支払い予定**: GENERAL_SPEC.md:364 の表で「G-MEMCALLS: `MemDec` from the package」は M2-a。M2-a は gen2 側
- **実runから払えそうか**: この調査では見つからなかった
- **分類**: 未供給の義務（M2/gen2 側。T1 台帳を参照）

### T-12: closingRun0_of_run 系の statement-level binder
- **Lean名**: `hord`、`hrow`/`hrows`、`hGen`、`hIH`、`hKI`、`hs`、`hd0`、`hrun`
- **完全な型**: `hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] → ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none`（`closingShared_of_run`、T2TieCR2 と同ファイル ClosingRun2.lean）。`hs : Start L mctx cctx w`、`hd0 : dv w = 0`、`hIH : IHAt L P Reach 1`、`hKI : ChildKeepsInv L P Reach 1`、`hGen : ∀ b ci envR envR' w5 w6, RunReadsAt … → Gen ci envR envR'`、`hrun : RunsTo (synthesizeCombinationalCore X [] false) …`。`hrow : ∀ q, DataOk q → OneOutNoMemRow q = true`（`hord_of_row`、DataBridge.lean:57）
- **仮定している定理**: `closingShared_of_run`、`closingRun0_of_run`（ClosingRun2.lean）
- **FG/T1 のどこに効くか**: `hs`/`hd0` は FG の `Start`。`hrun` は FG の RunsTo。`hGen` は `T1Hyp.pkg` の生成性。`hIH`/`hKI` は T1 の帰納仮定
- **別名**: dg-closingrun の同名 binder
- **支払い予定**: R0 §1 の owner 列による。`hord`/`hrow`/`hrows`/`hIH` は sparkle-gen3-data-supply / DG-WFCOVER / G-CALLDEC。`hGen` は dg-acc / dg-cover / dg-env。`hs`/`hrun` は statement-level（FG の仮定そのもの）
- **実runから払えそうか**: `hs`、`hd0`、`hrun` は FG の仮定そのもの。他は、この調査では見つからなかった
- **分類**: 入力条件（`hs`、`hd0`、`hrun`）。未供給の義務（`hord`、`hrow`、`hGen`、`hIH`、`hKI`）

## 4. sparkle-gen5-dc-connect（前提 9 件）

承認済み Lean: kjob/g5dc-r21〜r23@0fcce4e7（Tools/ShippingGen5FG.lean、DeclConnect、DeclConnectAbs、DCEntry*）。U-CORENR は 74343ad8（未レビュー）。
`FG_CONNECT` は条件付きの中間定理で、最終保証ではない。`fgCond_trivial`（FG.lean）が `Post := False`、`GP := none`、`CV := ∅` で成り立つことを示す。同ファイルのヘッダがこの点を明記している。

### D-1: ReflectsAll
- **Lean名**: `ReflectsAll`
- **完全な型**: `Laws mref cref → Name → List (String × Nat) → Prop`（`FG_COND`/`FG_CONNECT`/`EntryWitness` の binder。Tools/ShippingGen5FG.lean:30,42,54）
- **仮定している定理**: `FG_COND`、`FG_CONNECT`、`entryWitness_postEntry`、`entryWitness_left_postEntry`（Tools/ShippingGen5DCEntryW.lean:19,34）
- **FG/T1 のどこに効くか**: FG の `ReflectsAll` binder（G3、per route、per reached declaration）
- **別名**: boundary-audit §4 の表の `ReflectsAll`
- **支払い予定**: boundary-audit §4 の表（kjob/g5ba-r16@96e862fe、scripts/gen5/BOUNDARY_AUDIT_FREEZE.md）は「M4/M5 G3（T2/DGEN family、package coverage）」を supplier とし、state は OPEN
- **実runから払えそうか**: この調査では見つからなかった
- **分類**: 未供給の義務（FG の仮定として残る）。`ReflectsAll = False` 型の scope 縮小は不採用（seq3553）

### D-2: Post
- **Lean名**: `Post`
- **完全な型**: `Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop`。default route の具体 `PostEntry`（DCEntryD.lean:22）:
```lean
def PostEntry (b raw : Sparkle.IR.AST.Module) (D D' : Sparkle.IR.AST.Design) : Prop :=
  (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∧
    D' = topMap Sparkle.IR.ZeroWidth.dropZeroWidthModule raw D) ∨
  (b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ∧
    D' = topMap Sparkle.IR.RefineCheck.mergeChecked raw (topMap Sparkle.IR.ZeroWidth.dropZeroWidthModule raw D))
```
- **仮定している定理**: `FG_CONNECT`（O1 `∃ raw, Post b raw`、O3）。`nv_post`
- **FG/T1 のどこに効くか**: FG の結論の `b ↔ raw` 関係（§1.1「(b, raw) related by the entry's post-processing」）
- **別名**: `PostT1`（DCEntry.lean:17）。`postEntry_postT1` で `PostEntry → PostT1`
- **支払い予定**: default route は証明済み（`synthesizeCombinational_postEntry`、`o1_default`。`h : RunsTo (synthesizeCombinational declName) …` のみを仮定。承認 seq4318/4497）。parametric route の postprocessing は未供給。Post の最終採用も未承認（seq4318）
- **実runから払えそうか**: default route は はい（`synthesizeCombinational_postEntry`）。parametric route は、この調査では見つからなかった
- **分類**: default route は入力条件（RunsTo）のみ。parametric route は未供給の義務

### D-3: GP（package 割り当て）
- **Lean名**: `GP`
- **完全な型**: `Environment → Pkgs ι dom`（`Pkgs` は `Name → Option (Pkg ι dom)`。FG.lean:42）
- **仮定している定理**: `FG_COND`、`FG_CONNECT`、`nv_gp`、`nv_cv`、`o2_of_o1_o3`
- **FG/T1 のどこに効くか**: FG の `Pk declName = some p`、T1 の `pkg`
- **別名**: FG 文書の `Pk`。T2/DGEN 系の `genP`。t2probe の `P`
- **支払い予定**: package-coverage（todo、未割当の設計）、dg-acc の `genP_pkg`（条件付き）
- **実runから払えそうか**: この調査では見つからなかった。`nv_gp` は、EntryWitness があれば `GP := none` が反駁されることを示すだけ
- **分類**: 未供給の義務

### D-4: CV（ConstValueRel）と ConstValueFunctional
- **Lean名**: `CV`、`ConstValueFunctional CV`
- **完全な型**: `abbrev ConstValueRel := Environment → Name → (α : Type) → α → Prop`（DeclConnect.lean）。
```lean
def ConstValueFunctional (CV : ConstValueRel) : Prop :=
  ∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w
```
- **仮定している定理**: `FG_CONNECT`（第 1 conjunct が `ConstValueFunctional CV`）、`FG_COND`、`declConnect_of_rows`、`dcImp_of_dcGen`（Abs U4a、`hV2`）
- **FG/T1 のどこに効くか**: G3-DECL（生成 package と元宣言の意味の接続）
- **別名**: dc-connect の ConstValue。ConstValue 定義は DCF unit のもので未記述（DeclConnect.lean のコメント）
- **支払い予定**: decl-bridge（todo）。`seq3553` は「新 TRUSTED 採用は未承認」。DC-FORM/DC-SUPPLY は t2cover seq2721 で study unit とされる
- **実runから払えそうか**: この調査では見つからなかった
- **分類**: 未供給の義務（TRUSTED 境界としては明示されていない。「no TRUSTED default」と記録）

### D-5: DeclConnect の rows 前提（hAcc / hclosed / hstep、順序 R）
- **Lean名**: `hAcc`、`hclosed`、`hstep`、`R`
- **完全な型**: Tools/ShippingGen5DeclConnect.lean（0fcce4e7）
```lean
theorem declConnect_of_rows (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) {R : Name → Name → Prop}
    (hAcc : ∀ X, Tgt X → Acc R X) (hclosed : ∀ X c, Tgt X → R c X → Tgt c)
    (hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DeclConnectAt CV env₀ P c) → DeclConnectAt CV env₀ P X) :
    DeclConnect CV env₀ P Tgt
```
  `DeclConnect`（展開形 `declConnect_eq`）は
  `∀ X, Tgt X → ∀ p, P X = some p → ∃ (ci : ConstantInfo) (sh : SigShape) (v : sh.Ty), env₀.find? X = some ci ∧ shapeOf ci = some sh ∧ ShapeMatches sh p.d p.kD ∧ CV env₀ X sh.Ty v ∧ ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits`。
- **仮定している定理**: `declConnect_of_rows`、`dcGen_of_rows`（DeclConnectAbs.lean）、`FG_COND`/`FG_CONNECT` の第 4 conjunct
- **FG/T1 のどこに効くか**: G3-DECL。FG の結論の `src` と元宣言の意味の接続
- **別名**: 元の `hstep` はコメントで「rows 0-4 の未供給内容（値の存在、本体の unfold、shape/body、quote/eval の一致、`src = obs (stateLoop …)`、calls）」。`TgtRun` が `Tgt`（FG.lean:30）
- **支払い予定**: decl-bridge（todo。設計のみ）、dg-sem、dg-dataof、dg-acc
- **実runから払えそうか**: この調査では見つからなかった
- **分類**: 未供給の義務

### D-6: Start / Laws（EntryWitness の条件）
- **Lean名**: `Start L mctx cctx w`（`EntryWitness` の第 1 conjunct）、`L : Laws mref cref`
- **完全な型**: `def Start … : Prop := AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`（Tools/ShippingGen2Defs.lean:52、0fcce4e7）。`structure Laws … where O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref  T : RefLawsATele O.quiet mref cref`
- **仮定している定理**: `entryWitness_postEntry`、`noRawBelow_of_coreRun`（74343ad8）、`coreRun_transport`（74343ad8）、`FG_COND`/`FG_CONNECT`
- **FG/T1 のどこに効くか**: FG の `L`、`Start`
- **別名**: boundary-audit E-11/E-12
- **支払い予定**: boundary-audit §2 の分類による（下記 E-11/E-12）
- **実runから払えそうか**: boundary-audit の記述では `AdmCtx` は `Command.mkMetaContext` に対してのみ証明（`mkMetaContext_canUnfold`）。「entry がそこで走る」は読み筋であって定理ではない
- **分類**: 入力条件（Start）、CONTRACT 境界（Laws）。boundary-audit の分類による

### D-7: NoRawBelow（hno）
- **Lean名**: `hno`（`NoRawBelow D raw.name (n+1) raw`）、`noRawBelow_of_closeInsts` の `h`
- **完全な型**: DCEntryR.lean:14
```lean
def NoRawBelow (D : Sparkle.IR.AST.Design) (rn : String) : Nat → Sparkle.IR.AST.Module → Prop
  | 0, _ => True
  | k + 1, mc =>
    (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body → mn ≠ rn) ∧
    (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (mc' : Sparkle.IR.AST.Module),
        Sparkle.IR.AST.Stmt.inst mn iname conns ∈ mc.body →
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc' → NoRawBelow D rn k mc')
```
  `noRawBelow_of_closeInsts`（DCEntryS.lean:27）は前提 `h : Sparkle.IR.Machine.closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)`。`noRawBelow_of_closeInstsG`（:36）は `closeInstsG … = some (m, d)`。U-CORENR（74343ad8）の `noRawBelow_of_coreRun`（DCEntryU.lean:17）は
  `(d : MachineData) (hS : Start L mctx cctx w) (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1) (hdef : MachineDefines mctx mref cctx cref declName d.shape) (hcl : MachineClosesAtA L.O mctx cctx declName d.shape) (hins : d.shape.insts ≠ []) (hf : d.shape.instFields = [])`
  から `∀ k, NoRawBelow D raw.name k raw` を与える。
- **仮定している定理**: `resetNk_transport`（DCEntryR.lean:50）、`resetN_transport`、`KSn_transport`、`runModuleTG_transport`（DCEntryT.lean:119,156）
- **FG/T1 のどこに効くか**: FG の結論 `TopShips p n declName b raw D` を `D'`（返却 design）側へ運ぶ輸送。結論 O3 の `TopShips … D`
- **別名**: closeInsts 非循環性。`NoRawBelow` は「成功 lookup が無い inst にも `mn ≠ rn` を要求する強い十分条件」（seq5187）
- **支払い予定**: U-CORENR（74343ad8。freeze 28f2627c は seq5327 で承認、実装はレビュー待ち）。leaf（insts=[]）と最適化 body との (a3) は未供給
- **実runから払えそうか**: 承認済みの根拠は `noRawBelow_of_closeInsts`（実 run の closing 等式からの導出）。実 core run との接続は 74343ad8 の `noRawBelow_of_coreRun`（agent 増分ビルドのみ）。leaf と (a3) は、この調査では見つからなかった
- **分類**: 未供給の義務（実供給は 74343ad8 待ち。leaf と (a3) は未）

### D-8: hlk（D と D′ の lookup 同一）
- **Lean名**: `hlk`
- **完全な型**: `∀ mn : String, mn ≠ rn → Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn`（DCEntryR.lean:24、DCEntryT.lean:13,120,157）
- **仮定している定理**: `resetN_transport`、`childMap_transport`、`KSn_transport`、`runModuleTG_transport`
- **FG/T1 のどこに効くか**: D から D′ への輸送（O3）
- **別名**: なし
- **支払い予定**: 証明済み。`postEntry_lookup_ne`（DCEntryN.lean:84、承認 seq4700）と `hlk_of_postEntry`（DCEntryU.lean:37、74343ad8 で未レビュー）が `PostEntry` から導出
- **実runから払えそうか**: はい（`postEntry_lookup_ne` は承認済み）。`PostEntry` は D-2 のとおり default route では実 run から出る
- **分類**: 入力条件（default route では証明済み）

### D-9: MachineDefines / MachineClosesAtA（hdef / hcl）
- **Lean名**: `hdef`、`hcl`
- **完全な型**: `MachineDefines mctx mref cctx cref declName d.shape`、`MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape`（DCEntryU.lean:26-27、74343ad8）
- **仮定している定理**: `noRawBelow_of_coreRun`、`coreRun_transport`
- **FG/T1 のどこに効くか**: T1Hyp の `defines`、`closes`
- **別名**: T1Hyp の同名フィールド
- **支払い予定**: T1 側
- **実runから払えそうか**: T1 台帳を参照
- **分類**: T1 台帳を参照

## 5. sparkle-gen5-boundary-audit（前提 13 件）

承認済み Lean: NameKids U1〜U7（Tools/ShippingGen5NameKids.lean〜NameKids7.lean、最後の実装承認は kjob/g5ba-r16@3f5bcb2e）。型は 96e862fe（U8 freeze の commit。NameKids ファイル自体は U7 から変更なし）で読んだ。U8（`graphAgrees_of_mem`）は freeze のみ。実装は無い。文書は scripts/gen5/BOUNDARY_AUDIT_FREEZE.md（96e862fe）。

### E-1: hmemSame
- **Lean名**: `hmemSame`
- **完全な型**: `hsep_of_kidNames`（NameKids.lean、U1 freeze）:
```lean
(hmemSame : ∀ (k : Nat) (hk : k < insts.length) (k' : Nat) (hk' : k' < insts.length),
  memKey (org k) ≠ none → memKey (org k) = memKey (org k') → (insts[k]'hk).1 = (insts[k']'hk').1)
```
- **仮定している定理**: `hsep_of_kidNames`（U1）。U2 の `hmemSame_of_memTagsNamed`（NameKids2.lean:71）が `MemTagsNamed shape` から導出
- **FG/T1 のどこに効くか**: T1 の `closes`（G-CLOSES）の supplier `memCallee_closesA` → `machineClosesAtA_of_memKids'` の `hsep`（`MemCalleeData.sepK`）
- **別名**: `sepK` の mem vs mem の conjunct（B1）
- **支払い予定**: `MemTagsNamed` は U4 の `hmem_of_machineShapeF`（E-5 参照）で `machineShapeF` の成功から導出
- **実runから払えそうか**: 文書によると mem 同士の `insts[k].1 = insts[k'].1` は名前からは出ない（二つの別 callee が同じ `(cb,aw,dw)` を作り得る）。`MemTagsNamed` 経由の導出は U4 で built
- **分類**: 未供給の義務（`MemTagsNamed` に帰着）

### E-2: hself
- **Lean名**: `hself`
- **完全な型**: `∀ (k : Nat) (hk : k < insts.length), memKey (org k) = none → (insts[k]'hk).1 ≠ declName`
- **仮定している定理**: `hparent_of_kidNames`（U1）。U2 `hself_of_rank`（NameKids2.lean:80）が `hgraph : callees g declName = some shape.instTagged` と `hr : declRank g F declName = some r` から導出。U3 `hself_all_reached`（NameKids3.lean:99）が全到達宣言へ拡張
- **FG/T1 のどこに効くか**: T1 の `closes` の `hparent`（B2）
- **別名**: なし
- **支払い予定**: U3 の `hself_all_reached` は `hin : InClass g B top = true`、`hg : GraphAgrees g Reach S`、`hsp : ReachSpans g top Reach` を前提とする。これらは E-6〜E-9
- **実runから払えそうか**: 文書によると「無条件の定理は見つからなかった」。条件付きで U2/U3 が built
- **分類**: 未供給の義務（E-6〜E-9 に帰着）

### E-3: hn（kid モジュール名）
- **Lean名**: `hn`
- **完全な型**: `∀ (k : Nat) (hk : k < insts.length), nameK k = kidModName ((insts[k]'hk).1, org k)`。U2 で `kidNameAt shape k = kidModName (…)` として `hn_kidNameAt`（NameKids2.lean:58）が証明済み
- **仮定している定理**: `hsep_of_kidNames`、`hparent_of_kidNames`
- **FG/T1 のどこに効くか**: T1 の `closes`（B7）
- **別名**: `RealChildA O c y → y.1.name = ofDecl c`（`kidTA_name` の前提。B7）
- **支払い予定**: 文書は「synthesis run についての事実」とし、供給元は不明
- **実runから払えそうか**: `hn_kidNames`（kidNameAt の定義による）は はい（built）。ordinary kid の `y.1.name = ofDecl c`（B7）は、この調査では見つからなかった
- **分類**: 未供給の義務（B7 部分）

### E-4: B3 hparentD / B4 hdisjD / B5 hfresh（残余）
- **Lean名**: `hparentD`、`hdisjD`、`hfresh`（`MemCalleeData.outHead`）
- **完全な型**: BOUNDARY_AUDIT_FREEZE.md §1.2 の B3/B4/B5 の Prop。
  - B3: `∀ k, k < insts.length → ofDecl declName ∉ namesK k`
  - B4: `∀ k k', ¬(insts[k].1 = insts[k'].1 ∧ memKey = memKey) → nameK k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k'`
  - B5: `∀ gi k (hk : k < insts.length), ∀ o ∈ shape.layout.outs, o.name ≠ s!"inst{gi}_{nameK k}"`
- **仮定している定理**: `machineClosesAtA_of_memKids'`（CallsMemPinned.lean:330）の binder。boundary-audit の補題には含まれない
- **FG/T1 のどこに効くか**: T1 の `closes`
- **別名**: B5 は G-CLOSES-FRESH。generator 側に `outHead` チェック（`ShippingNoPortsMemSeqCommand.lean:380`、throwError）がある
- **支払い予定**: B3/B4 は call-graph/rank 系。B5 は文書が「FG がそのような設計を覆うべきなら user の判断事項」と記す
- **実runから払えそうか**: この調査では見つからなかった。B5 は出力名が `inst{gi}_…` と衝突する設計がコンパイルを通るかを確認していない
- **分類**: 未供給の義務

### E-5: U3 の GraphAgrees / ReachSpans / InClass / hmem
- **Lean名**: `hg`、`hsp`、`hin`、`hmem`
- **完全な型**: NameKids3.lean（96e862fe）
```lean
def GraphAgrees (g : CallGraph) (Reach : Name → Prop) (S : Name → Option MachineShape) : Prop :=
  ∀ c, Reach c → callees g c = (S c).map MachineShape.instTagged
def ReachSpans (g : CallGraph) (top : Name) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → OrdPath g top c
```
  `hin : InClass g B top = true`（`InClass g B top := WfG g && (declRank g B top).isSome`、Srm7Rank.lean:72）、`hmem : ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp`。`MemTagsNamed shape := ∀ (k : Nat) (hk : k < shape.insts.length) (cb : Bool) (aw dw : Nat), originAt shape k = InstOrigin.mem cb aw dw → (shape.insts[k]'hk).1 = memChildName cb aw dw`（NameKids2.lean:31）
- **仮定している定理**: `hself_all_reached`（NameKids3.lean:99）、`sepK_parent_all_reached`（:109）、`reach_of_ordEdges`（:75）
- **FG/T1 のどこに効くか**: T1 の `closed`（`ReachClosed` は `T1Hyp.closed` を `S` で再記述したもの、NameKids3.lean:31）と `closes`
- **別名**: `ReachSpans` は `ReachClosed` の逆で、このユニットでは供給されない（定義コメント）
- **支払い予定**: `hmem` は U4（`hmem_of_machineShapeF`、NameKids4.lean:33、実装承認 seq4841 39c565c4）。`hg` は U5/U8。`hin` は U6
- **実runから払えそうか**: 上記 U4〜U6 は built。ただし `ReachSpans`、production の `Reach`/`S`/`ds`、bridge は、この調査では見つからなかった
- **分類**: 未供給の義務

### E-6: U4 の hF（machineShapeF）
- **Lean名**: `hF`
- **完全な型**: NameKids4.lean:33
```lean
(hF : ∀ c, Reach c → ∀ sp, S c = some sp →
  ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (senv : StructEnv) (ai : Bool),
    machineShapeF n sm ps ci senv ai = some (some sp))
```
- **仮定している定理**: `hmem_of_machineShapeF`（NameKids4.lean:33）
- **FG/T1 のどこに効くか**: T1 の `defines`（G3-SHAPE、`MachineDefines` が `machineShape? = some`）の読み取り
- **別名**: なし
- **支払い予定**: reader-bridge（`machineDefines_of_readsAll`、boundary-audit §4 の表。partial）
- **実runから払えそうか**: この調査では見つからなかった。production bridge は未供給（seq4841）
- **分類**: 未供給の義務

### E-7: U5 の hfo（FirstOcc）
- **Lean名**: `hfo`
- **完全な型**: NameKids5.lean:20
```lean
(hfo : ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ S c = some d.shape)
```
  `FirstOcc ds c d := ds.find? (fun p => p.1 == c) = some (c, d)`（Srm15Graph.lean:36）。結論 `GraphAgrees (graphOf ds) Reach S`
- **仮定している定理**: `graphAgrees_of_firstOcc`（承認 76ae2e8e）
- **FG/T1 のどこに効くか**: E-5 の `hg`
- **別名**: ヘッダによると十分条件で、`GraphAgrees` と同値ではない（両側 none も許す）
- **支払い予定**: 未割当（production の `ds`/`Reach`/`S` が未供給）
- **実runから払えそうか**: この調査では見つからなかった
- **分類**: 未供給の義務

### E-8: U6 の hnd / hr
- **Lean名**: `hnd`、`hr`
- **完全な型**: NameKids6.lean:18
```lean
theorem inClass_graphOf {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hnd : (ds.map Prod.fst).eraseDups.length = ds.length)
    (hr : (declRank (graphOf ds) B top).isSome = true) :
    InClass (graphOf ds) B top = true
```
- **仮定している定理**: `inClass_graphOf`（承認 b07cfcec）
- **FG/T1 のどこに効くか**: E-5 の `hin`
- **別名**: U8 freeze は同じ `hnd` と `(c,d)∈ds` の所属を前提とする（Lean 未実装）
- **支払い予定**: 未割当。production の `hnd`/`hr` は、この調査では見つからなかった（seq5081）
- **実runから払えそうか**: この調査では見つからなかった
- **分類**: 未供給の義務

### E-9: U7 の hg（OrdPath 上の GraphAgrees）
- **Lean名**: `hg`
- **完全な型**: NameKids7.lean:20
```lean
theorem reachClosed_ordPath {g : CallGraph} {top : Name} {S : Name → Option MachineShape}
    (hg : GraphAgrees g (OrdPath g top) S) :
    ReachClosed (OrdPath g top) S
```
- **仮定している定理**: `reachClosed_ordPath`（承認 3f5bcb2e）
- **FG/T1 のどこに効くか**: T1Hyp の `closed`
- **別名**: `ReachClosed Reach S` は `T1Hyp.closed` の再記述（定義コメント）
- **支払い予定**: U8（`graphAgrees_of_mem`）の freeze のみ承認。実装は無い（seq5081）
- **実runから払えそうか**: この調査では見つからなかった。`Reach` が `OrdPath` と一致する保証もない（`ReachSpans` が逆向きの未供給）
- **分類**: 未供給の義務

### E-10: Laws の 14 フィールド（G5）
- **Lean名**: `L.O.quiet`、`O.diag`、`O.frameT`、`O.excOk`、`O.frameQ`、`O.cacheSetQ`、`O.depthSetQ`、`O.frame`、`O.cacheSet`、`O.depthSet`、`T.telescope`、`T.lamTelescope`、`T.localDecl`、`T.letDecl`
- **完全な型**: `Laws` は `structure Laws … where O : RefLawsAOps … T : RefLawsATele O.quiet …`（Tools/ShippingGen2Defs.lean、GEN2_DEFS §2）。各フィールドの完全な Prop 本文は読んでいない（`RefLawsAOps`/`RefLawsATele` の定義元）。これは読めなかったものとして記録する
- **仮定している定理**: FG の `L` binder。T1 の全チェーン
- **FG/T1 のどこに効くか**: FG の `L : Laws mref cref`
- **別名**: 旧 `RefLaws.frame` は REFUTED（Gaps §1 G5 行）。現在の境界の runtime fit と joint satisfiability は OPEN（Gaps row 127）
- **支払い予定**: 未割当。GENERAL_SPEC §5 M5 は「G5: a model of `Laws`, or an explicit TRUSTED status」と要求する。model は tree に見つからなかった
- **実runから払えそうか**: この調査では見つからなかった。フィールドごとの使用トレースは未実施（FG の閉じた証明項がまだ無いため）
- **分類**: boundary-audit は CONTRACT と分類（「approved boundary」。Gaps G5 行の CONTRACT / OPEN）。TRUSTED としては明示されていない

### E-11: Start の 2 conjunct
- **Lean名**: `Start.1`（`AdmCtx`）、`Start.2`（`JQC O 0 w`）
- **完全な型**: `AdmCtx quiet mctx _ := ∀ f, mctx.canUnfold? = some f → InertUnfold quiet f`。`JQC O D w := JQ O.quiet D w ∧ CacheInvA O (cv w)`、`JQ quiet D w := quiet w ∧ sv w = some synthesizeChild ∧ dv w = D`、`CacheInvA O m := ∀ c r, m.get? c = some r → RealChildA O c r`（BOUNDARY_AUDIT_FREEZE.md §2）
- **仮定している定理**: FG の `Start` binder
- **FG/T1 のどこに効くか**: FG の `Start`
- **別名**: dc-connect の D-6
- **支払い予定**: 未割当
- **実runから払えそうか**: `Start.1` は `Command.mkMetaContext` に対してのみ証明。`Start.2` の `CacheInvA` は空 cache で証明（`cacheInvA_empty`）。entry が実際にその context で走ることは、この調査では見つからなかった
- **分類**: 入力条件（CONTRACT。start-world invariant at depth 0、Gaps row 14）

### E-12: G7 の hno / htop
- **Lean名**: `hno`、`htop`
- **完全な型**: `writer_prints_endpoint_artifact`（Tools/ShippingDesignWriterRun.lean:119）の `hno : ∀ x ∈ D.modules, x.name ≠ raw.name`、`htop : D.topModule = raw.name`。結論 `designArtifact dH = D.modules ++ [checkedOptimize b] ∧ toVerilogDesignChecked dH = … ∧ ∀ mn r, childMap D.modules mn = some r → childMap (designArtifact dH) mn = some r`
- **仮定している定理**: `writer_prints_endpoint_artifact`
- **FG/T1 のどこに効くか**: FG の保証は `runModuleTG` on `checkedOptimize b` まで（`TopShips`、Gen2Defs.lean:280）。出力 artifact との接続（G7-a）
- **別名**: なし
- **支払い予定**: 未割当
- **実runから払えそうか**: `hno`/`htop` が全成功 run で成り立つかは、この調査では見つからなかった。G7-b（`runModuleTG` ⇒ `DesignSV`）の定理も見つからなかった
- **分類**: 未供給の義務（G7-a/b）

### E-13: G7-c 印字（printer）
- **Lean名**: `emitModule`（Verilog/SystemVerilog 印字）
- **完全な型**: 型は読んでいない
- **仮定している定理**: なし（保証の外側）
- **FG/T1 のどこに効くか**: FG 結論の後段
- **別名**: Gaps row 129
- **支払い予定**: なし
- **実runから払えそうか**: 対象外
- **分類**: TRUSTED 境界（boundary-audit §3 が「TRUSTED by design（printer）。parse-back は validation のみ」と記す。GENERAL_SPEC §5 M5 の「G7 is TRUSTED and stated」に対応）

## 6. 件数の集計

| Issue | ブロック数 | 内訳 |
|---|---|---|
| t2probe | 3 | P1〜P3 |
| t2cover | 0 | Lean 無し（設計の残りのみ §2 に記録） |
| t2-tie | 12 | T-1〜T-12。組み立て済み（末端は他へ帰着）T-2、T-7、T-8、T-9。T1 台帳参照 T-6。未供給または入力条件の残りは T-1、T-3、T-4、T-5、T-10、T-11、T-12 |
| dc-connect | 9 | D-1〜D-9。T1 台帳参照 D-9 |
| boundary-audit | 13 | E-1〜E-13 |
| t2-emit、gencall-proof、package-coverage、decl-bridge、reader-bridge | 0 | Lean 成果なし |

合計 37 ブロック。同じ前提が複数名で現れるもの: P1=T-7 (`hDG_GENP`)、`FG_CONNECT.GP`(D-3)=`P`(P1)、`dec` は T-1〜T-4 と T-10/T-11 の結論先。

## 7. 読んだ文書・branch@SHA 一覧

- 履歴 JSON: 各 Issue の履歴 JSON（`$S/h/sparkle-gen5-{t2probe,t2cover,t2-tie,dc-connect,t2-emit,gencall-proof,package-coverage,decl-bridge,reader-bridge,boundary-audit}.json`）。
- par/gen5-t2@0bb53938: Tools/ShippingGen2T2Probe.lean。
- par/gen5-t2@c398021c: scripts/gen5/T2COVER_FREEZE.md（先頭 110 行）。
- kjob/g5tt-sync@632f365d（= g5tt-cr6@456699fc + コメント同期）:
  - Tools/ShippingGen5T2Tie.lean、T2Dec.lean、T2Range.lean、T2Conn.lean、T1ND.lean（先頭）、T2TieCR.lean、T2TieCR2.lean、ClosingRun2.lean（先頭）
  - Tools/ShippingGen2Defs.lean（85-135、195-260 行）、Tools/ShippingGen2CallField.lean（70-110 行）、Tools/ShippingGen2FitChain.lean:885-905
  - scripts/gen5/T2TIE_NEXT_FREEZE_R0.md（先頭 120 行）
- kjob/g5dc-r23@0fcce4e7: Tools/ShippingGen5FG.lean、DeclConnect.lean、DeclConnectAbs.lean、DCEntry.lean、DCEntryD/N/R/S/T/W.lean（シグネチャ）。Tools/ShippingGen2Defs.lean（40-60 行、TopShips 280-302 行）。
- kjob/g5dc-r23@74343ad8: Tools/ShippingGen5DCEntryU.lean。
- kjob/g5ba-r16@96e862fe: scripts/gen5/BOUNDARY_AUDIT_FREEZE.md（先頭 150 行）、Tools/ShippingGen5NameKids2〜7.lean、Tools/ShippingSrm15Graph.lean（30-44 行）。
- scripts/gen2/GENERAL_SPEC.md §1.1〜1.3（kjob/fg-ledger1）。
- 参照のみ: 履歴 note に書かれた SHA（3425 08e97dba、3553 c07b5f66、3582 c07b5f66、4097 6bd33fd7、4318 db171c2e、4497 4523f2e9、4700 6d6c9b22、4905 135aa0ac、5187 1c948e47、5258 716d342b、5310 0fcce4e7）は note のみ。それぞれ該当ファイルは読んでいない。

## 8. 読めなかったもの

- `RefLawsAOps` / `RefLawsATele` の各フィールドの完全な Prop 本文（Laws の 14 フィールド。E-10）。
- `ClosingRun`（Tools/ShippingGen5ClosingRun.lean:48）と `ClosingRun0`（ClosingRun2.lean:118）の本文、`RunReadsAt`、`CloseCalls`、`ChildrenShipsI`、`MachineTraceLBX` の本文（dg-closingrun / dg-runreads の担当と判断）。
- `MachineDefines`、`MachineClosesAtA`、`IHAt`、`ChildKeepsInv`、`InvAt` の本文（T1 側）。
- `hkidW_of_data`、`hkidW_of_dataAM`、`oneOutWidth_of_strictP` の本文。
- `Pkg`/`SrcPkg`/`MachineData` 構造体の本文（Gen2Defs 冒頭）。
- DC_CONNECT_FREEZE.md、DC_CONNECT_*_FREEZE.md、DG_CLOSINGRUN_FREEZE_R6.md の本文は、DC-CONNECT 側では履歴 note と Lean ヘッダに依拠した。DC_CONNECT_CORENR_FREEZE.md は未読。
- 74343ad8 の `DCEntryUCheck.lean`（718 行）は未読。
- NameKids2〜7 の Lean は 3f5bcb2e ではなく 96e862fe で読んだ。両者の Tools 差分は NameKids7.lean の 1 行のみ（コメント同期と思われるが内容は未確認）。
- T2TIE の `ClosingRun0` 系の `closingRun0_of_run` 完全型（T-12 は binder 名と文書の記述のみ）。
- t2-emit、gencall-proof、package-coverage、decl-bridge、reader-bridge の設計文書本体（SRC_ARGW_SUPPLY_FREEZE.md §6 Q1〜Q5）。note の記述のみ。
