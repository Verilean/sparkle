# DG-READERTRACE freeze rev7 — 単位 U-R4c（構造的補題群）と U-R4d（`app` の一般分岐）の完全な型

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt12` b1f14f7c（U-R4b、Pod build exit 0）。`DG_READERTRACE_FREEZE_REV5.md` §1 の U-R4c / U-R4d、`..._REV6.md` の続き。**文書のみ。未 elaborate。** 通らない箇所は addendum で直す。
**記録（順序）**: part 1 の Lean 下書き（`Tools/ShippingGen5ReaderTraceIota.lean`、未コミット・未 build）を、この文書より先にワークツリーへ書いた。コミットと build はこの文書のコミット後。型はこの文書が基準で、下書きが違えば下書きを直す。
用語: mutant は signature / defeq での棄却であって意味的反例ではない。条件付きの結果は中間結果。

**台帳の差分: なし**（FG 102 / T1 54、今回 FG -0 +0 / T1 -0 +0）。承認済み rev5 §1 の範囲内で新しい前提・law・TRUSTED・共有定義変更なし。`bundleIota` / `machProjIota` / `liftSpec` / `rootFloatS` は等式仮定なしの**構造的補題**（既存の `bundleIotaRange` / `projIota_ok` / `liftSpec_ok` / `rootFloatS_ok` と同じ方法で述語だけ変える）。lift / rootFloat の extern との接続（`LiftAgrees` T1L-50 / `RootFloatAgrees` T1L-52）は U-R5 の arm 単位で名前付き仮説として使うもので、ここでは使わない。

## 1. U-R4c part 1: 新規 `Tools/ShippingGen5ReaderTraceIota.lean`（namespace `Tools.ShippingGen5ReaderTrace`）
Imports: `Tools.ShippingBundleIotaRange`、`Tools.ShippingGen5ReaderTraceApp`。`set_option autoImplicit false`。lakefile に `lean_lib` をファイルと Check にそれぞれ追加（追加のみ）。

```lean
def QApp (Q : Lean.Expr → Prop) : Prop := ∀ f a, Q (.app f a) ↔ Q f ∧ Q a
def QConst (Q : Lean.Expr → Prop) : Prop := ∀ c ls, Q (.const c ls)

theorem q_getAppArgs (Q : Lean.Expr → Prop) (happ : QApp Q) {e : Lean.Expr} (he : Q e) : ∀ a ∈ e.getAppArgs, Q a
theorem bundleIota_pres (Q : Lean.Expr → Prop) (happ : QApp Q) (hconst : QConst Q) (e : Lean.Expr) (he : Q e) :
    Q (Sparkle.Compiler.MachRawSurface.bundleIota e)
theorem projIota_pres (Q : Lean.Expr → Prop) (happ : QApp Q) (projs : Name → Option (Name × Nat × Nat))
    (e : Lean.Expr) (he : Q e) : Q (machProjIota projs e)
theorem qApp_inRangeNoLoose (nDecl : Nat) (st : MachRead) (k d : Nat) : QApp (fun e => InRange nDecl st k e ∧ NoLoose d e)
theorem qConst_inRangeNoLoose (nDecl : Nat) (st : MachRead) (k d : Nat) : QConst (fun e => InRange nDecl st k e ∧ NoLoose d e)
theorem bundleProj_ph {nDecl : Nat} {st : MachRead} {k d : Nat} (proj : Name → Option (Name × Nat × Nat))
    {f' a' : Lean.Expr} (hf : InRange nDecl st k f' ∧ NoLoose d f') (ha : InRange nDecl st k a' ∧ NoLoose d a') :
    InRange nDecl st k (bundleIota (machProjIota proj (.app f' a'))) ∧ NoLoose d (bundleIota (machProjIota proj (.app f' a')))
```
補助（凍結対象外）: `q_argsAcc`、`q_spine`、`bundleIota_key1/2/3`（`bundleIotaRange` の 3 つの内側 `match` 補題の述語一般版。`bundleIota_pres` の証明部品）。Check では AXIOMS / CLOSURE のみ。
`bundleIota_pres` の方法: `ShippingBundleIotaRange.lean` のタクティク列の `LetOk n` を `Q`、`ok_getAppArgs` を `q_getAppArgs`、`simp_all [LetOk, …]` を `simp_all [happ, hconst, …]` に置換。`projIota_pres`: `projIota_ok` の `ok_spine` を `q_spine` にした同形。

## 2. U-R4c part 2: 新規 `Tools/ShippingGen5ReaderTraceLift.lean`
Imports: `Tools.ShippingGen5ReaderTraceCtl`（`NoPh` / `BvarLt` は `ShippingGen5ReaderTrace`）、`Tools.ShippingLetsExternSpec`（`liftSpec` / `rootFloatS`）。
```lean
theorem liftSpec_noPh : ∀ (e : Lean.Expr) (s d : Nat), NoPh e = true → NoPh (Tools.ShippingLetsReaderInv.liftSpec e s d) = true
theorem liftSpec_bvarLt : ∀ (e : Lean.Expr) (s d L : Nat), BvarLt L e = true →
    BvarLt (L + d) (Tools.ShippingLetsReaderInv.liftSpec e s d) = true
theorem rootFloatS_noPh : ∀ e : Lean.Expr, NoPh e = true → NoPh (Tools.ShippingLetsReaderInv.rootFloatS e) = true
theorem rootFloatS_bvarLt : ∀ (L : Nat) (e : Lean.Expr), BvarLt L e = true → BvarLt L (Tools.ShippingLetsReaderInv.rootFloatS e) = true
```
`rootFloatS_*` は `rootFloatS_ok` と同じ `rootFloatS.induct`。`BvarLt` の letE 本体は `L + 1`、`liftSpec` の本体は `s + 1`、`BvarLt (L + 1 + d) = BvarLt (L + d + 1)` は `omega`。

## 3. U-R4d: `app` の一般分岐（新規 `Tools/ShippingGen5ReaderTraceAppGen.lean`）
```lean
theorem conv_app_general_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (hl : machLoopRead? env d (.app f a) = none)
    (hrun : machRunApp? (.app f a) = none)
    (hic : machInstCall? senv (.app f a) = none)
    (hics : machInstCallS? senv (.app f a) = none)
    (hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none)
    (hr : machReadV env d (.app f a) = none)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
```
証明: `conv_basic_trace` の `lam` と同じ 2 回の `cConv` 連鎖（`hT` を 2 回）、`NoPh` / `BvarLt` は `phArgs`（`app` の `NoPh` / `BvarLt` を `simp [NoPh, BvarLt]` で分解）、結果は `bundleProj_ph senv.proj`（`inRange_mono` で `f'` を `s2` へ）。新しい仮説なし。

## 4. Check と手順
各ファイルに `Tests/Gen5/ReaderTrace{Iota,Lift,AppGen}Check.lean`（`ReaderTraceRegCheck` と同じ要件: TYPE / MUTANT（signature・defeq 棄却）/ AXIOMS / CLOSURE / 負例）。ビルドは `kjob lake build` を 1 つずつ。成功 SHA はヘッダーにコメントだけのコミットで反映。Lean コミット後は `doing` のまま「clean build は coder」。

## 5. この rev7 が主張しないこと
`TraceGood senv nDecl (readF senv n)` の成立、他の arm（U-R4e 以降）、実 run / FG、型が elaborate すること、台帳の数の変更。U-R4e / U-R8 前の A4 / `SigTyPh` は reviewer へ（この rev7 に含まれない）。
