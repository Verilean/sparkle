# DG-READERTRACE freeze rev6 — 単位 U-R4b（`convStep` `app` の新しい bare register）の完全な型

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt12` = `kjob/rt11` c059c76d（U-R4a、Pod build exit 0）。`DG_READERTRACE_FREEZE_REV5.md` §1 の単位 **U-R4b** の型。**文書のみ。未 elaborate。** 通らない箇所は addendum で直す。
用語: mutant は signature / defeq での棄却であって意味的反例ではない。条件付きの結果は中間結果で、`TraceGood senv nDecl (readF senv n)` 全体の成立ではない。

**台帳の差分: なし**（FG 102 / T1 54、今回 FG -0 +0 / T1 -0 +0）。承認済み rev5 §1 の範囲内（新しい前提・law・TRUSTED・共有定義変更なし）。reviewer 分担合意（2026-11-01）により review に出さない。

## 1. 新規 `Tools/ShippingGen5ReaderTraceReg.lean`（namespace `Tools.ShippingGen5ReaderTrace`）

Imports: `Tools.ShippingGen5ReaderTraceApp`、`Tools.ShippingGen3ArgSupply4`（`regView?_all` の再利用のみ）。`set_option autoImplicit false`。Opens は App と同じ。`lakefile.lean` に `lean_lib` をファイルと Check にそれぞれ追加（追加のみ）。

```lean
theorem phArgs_getAppArgs {L : Nat} {e : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true) :
    ∀ a ∈ e.getAppArgs, NoPh a = true ∧ BvarLt L a = true

theorem regView_ph {L : Nat} {e dom α init x : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : regView? e.getAppFn e.getAppArgs = some (dom, α, init, x)) :
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh x = true ∧ BvarLt L x = true)

theorem conv_app_bareNew_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (dom α init x : Lean.Expr)
    (hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x))
    (hgate : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false)
    (hfind : st.bareRegs.find? (·.1 == Lean.Expr.app f a) = none)
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v
```

* `phArgs_getAppArgs`: `ok_argsAcc` と同形の帰納（`NoPh` / `BvarLt` は `.app f a` で両側に降りる）。`regView_ph`: `regView?_all` に述語 `fun a => NoPh a = true ∧ BvarLt L a = true` を渡す。
* `conv_app_bareNew_trace`: `hgate` から `d = 0`。`convStep` を `hreg` / `hgate` / `hfind` で展開した `optK (machSlotKind? α) … optK (machInit? …) … bindO (cConv env 0 dom st) … domGuard … bindO (cConv env 0 x st2) … okO (machSlot base, {st3 with ws := ws.push (base, x')})` を、`conv_basic_trace` の `lam` arm と同じ `SatP` / `satp_optK` / `satp_bindO` / `satp_domGuard` / `satp_okO` で追う。`hT` を 2 回の `cConv` に使う。
  * `dom` 呼び出しの `PhPre`: `regView_ph` と `hpre` の `NoPh` / `BvarLt`（`d = 0`）、`noPh_letOk`。
  * 中間状態 `st2 = {s1 with kinds/inits/names push, dom := some dom', bareRegs push}`: `FReachC s1 st2` は `FStep.slot` の後に `CtrlEq`（`lets/insts/instOrigins/kinds/inits/names/ws` 不変）の `ctrl`。`TrInv st2`: `FullInv` は `fullInv_reachC`、`CtlPh` は `loopWs` / `bareRegs` を kinds の増加で、`nested` を `inRange_mono`、`DomPh` を `dom'` の `ExprPh` と `inRange_mono`、`LetsNoLoose` / `GroupsPh` は `lets` / `insts` / `instOrigins` 不変。`RdOk st2`（`Pre` 側）は `lets` / `nested` 不変と `dom'` の `LetOk`（`Post`）。
  * `x` 呼び出し後: `reachC_ws`（旧 `ws` は `FullInv` の `RangeInv`、新要素は `base < s3.kinds.size` と `x'` の `InRange`）。結果は `machSlot base`（`inRange_machSlot`、`noLoose_fvar`）、`TrInv` は `ws` 以外不変。
* どの補題も新しい仮説（law / extern 事実 / `PureFacts`）を取らない。`hT` は fuel `n` の表の `TraceGood`（rev3 の `conv_basic_trace` と同じ形）。

### Check（新規 `Tests/Gen5/ReaderTraceRegCheck.lean`、`ReaderTraceAppCheck` と同じ要件）
TYPE（3 定理を own spelling の独立な `Exp…` と `checkExpected`）、MUTANT（well-typed な単一変更のみ。signature / defeq での棄却で意味的反例ではない。数は測定値）、AXIOMS（標準 3 つのみ）、CLOSURE（3 宣言を root、`seen` を assert、禁止 root の自己ヒット対照、unknown / clean 対照、`withoutModifyingEnv` 内の負例）。ソースに `sorry` / `axiom` / `native_decide` なし。

## 2. この rev6 が主張しないこと
`TraceGood senv nDecl (readF senv n)` の成立、他の arm、実 run / FG、型が elaborate すること。台帳の数の変更なし。
