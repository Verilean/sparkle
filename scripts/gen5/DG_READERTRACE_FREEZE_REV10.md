# DG-READERTRACE freeze rev10 — U-R5a: `convStep` `letE` arm (no new premise; document only, not for review)

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt14` bf83660b（U-R4e2 まで）。`DG_READERTRACE_FREEZE_REV5.md` の単位表 U-R5a、`..._REV9.md` の続き。
用語: 「見つからなかった」は「この調査で辿った経路では見つからなかった」の意味で、不可能の主張ではない。mutant は signature / defeq での棄却で意味的反例ではない。条件付きの結果は中間結果。
分担ルール（2026-11-01）により、承認済みの文（REV5 の U-R5a 行: 前提は既存 T1L-50 `LiftAgrees` / T1L-52 `RootFloatAgrees`、台帳差分 -0 +0）の中で前提を増やさない単位なので、台帳差分を書いて進め、review には出さない。

**台帳差分: なし**（FG 102 / T1 54 のまま。SigTyClosed の FG +1 は 4d6b9719 で別に計上済み。今回 FG -0 +0 / T1 -0 +0）。

## 1. 型（Lean は新ファイル `Tools/ShippingGen5ReaderTraceLet.lean`、Check は `Tests/Gen5/ReaderTraceLetCheck.lean`）

```lean
-- 既存の名前付き仮説だけを取る（新しい仮説・axiom は無い）
theorem lift01_ph (hla : LiftAgrees) {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true) :
    NoPh (e.liftLooseBVars 0 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 0 1) = true
theorem lift11_ph (hla : LiftAgrees) {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true) :
    NoPh (e.liftLooseBVars 1 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 1 1) = true
theorem rootFloat_ph (hrf : RootFloatAgrees) {v : Lean.Expr} {L : Nat} (hn : NoPh v = true) (hb : BvarLt L v = true) :
    NoPh (Sparkle.Compiler.MachRawSurface.rootFloat v) = true ∧ BvarLt L (Sparkle.Compiler.MachRawSurface.rootFloat v) = true

-- 状態・環境の補助（前提なし）
theorem envPh_cons_regs {nDecl : Nat} {st : MachRead} {env : List MachVal} (h : EnvPh nDecl st env) (p : Nat) :
    EnvPh nDecl st (MachVal.regs p :: env)
theorem envPh_cons_handle {nDecl : Nat} {st : MachRead} {env : List MachVal} (h : EnvPh nDecl st env) (i : Nat) :
    EnvPh nDecl st (MachVal.handle i :: env)
theorem envPh_cons_root {nDecl : Nat} {st : MachRead} {env : List MachVal} {mv : MachVal} (h : EnvPh nDecl st env)
    (hs : ∀ b n, mv = MachVal.state b n → b + n ≤ st.kinds.size)
    (hv : ∀ v, mv = MachVal.val v → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) : EnvPh nDecl st (mv :: env)
theorem trInv_bindLet {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {ty v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    TrInv senv nDecl { st with lets := (machBindLet nm ty v' st.lets).2 }

-- 本体（`letE` arm 全体。discriminant は theorem の中で場合分けする）
theorem conv_letE_trace (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.letE nm ty v b nd) st))
    (r : (Call.conv env d (.letE nm ty v b nd) st).Res)
    (hv : (convStep senv env d (.letE nm ty v b nd) st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.conv env d (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.conv env d (.letE nm ty v b nd) st) r
```
* 使う既存: `liftSpec_noPh` / `liftSpec_bvarLt`、`rootFloatS_noPh` / `rootFloatS_bvarLt`（U-R4c）、`bindLet_reach`、`envPh_cons_val`、`envPh_mono`、`reachC_trans`、`fullInv_reachC`、`machBindLet_noAlias` / `machBindLet_range` / `adv_lets`（旧 `conv_letE_sat` と同じ経路で `Pre` を作る）、`noPh_letOk`。
* arm の分岐（`d ≠ 0` で失敗 / `rootFloat v` が `letE` / `Signal.loop` / `machTailV` / `machHandleV` / 既定）を全部この 1 つの theorem で覆う。`hT` から再帰呼び出し（`cConv`、`cLoopRoot`）の `TracePost` を取る。
* 前提: `LiftAgrees`（T1L-50）、`RootFloatAgrees`（T1L-52）。どちらも既存の名前付き仮説で、行は変えない。`Inst1` / `SigTyClosed` は使わない。
* 主張しないこと: 他の arm、`TraceGood senv nDecl (readF senv n)` 全体、`RootFloatAgrees` / `LiftAgrees` が真であること。

## 2. Addendum: U-R5b — `chainStep` の `letE` arm（台帳差分 -0 +0、前提は §1 と同じ既存 2 件、review に出さない）

新ファイル `Tools/ShippingGen5ReaderTraceChainLet.lean`（+ `Tests/Gen5/ReaderTraceChainLetCheck.lean`）。§1 の補助補題（`lift01_ph` 他）を再利用し、新しい補助は無い。
```lean
theorem chain_letE_trace (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.chain env (.letE nm ty v b nd) st))
    (r : (Call.chain env (.letE nm ty v b nd) st).Res)
    (hv : (chainStep senv env (.letE nm ty v b nd) st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.chain env (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.chain env (.letE nm ty v b nd) st) r
```
5 つの分岐（rootFloat が `letE` / `Signal.loop` / `machTailV` / `machHandleV` / 既定）は §1 と同形で、再帰が `cChain`（`d` なし。`PhPre` の `BvarLt` は `env.length + nDecl`）になるだけ。台帳差分 FG -0 +0 / T1 -0 +0。

## 3. Addendum: U-R6 — `nestedStep`（台帳差分 -0 +0、前提なし、review に出さない）

新ファイル `Tools/ShippingGen5ReaderTraceNested.lean`（+ `Tests/Gen5/ReaderTraceNestedCheck.lean`）。`machReserve` の reach 補題は、この調査では既存名 `machReserve_some`（`Tools/ShippingReaderLenOkReserve.lean`、`machReserve` の結果が `reserved st dom' body kinds inits`）と `reserved_reachC`（`Tools/ShippingGen5Cover6.lean`）が見つかった（REV5 表の「新規かも」は不要）。LiftAgrees / RootFloatAgrees / SigTyClosed は使わない。
```lean
theorem trInv_reserved {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    {dom' : Lean.Expr} (hdr : InRange nDecl s s.lets.size dom') (hdn : NoLoose 0 dom')
    (body : Lean.Expr) (kinds : List MixedGateBinder) (inits : List Nat) :
    FReachC nDecl s (reserved s dom' body kinds inits) ∧ TrInv senv nDecl (reserved s dom' body kinds inits)

theorem trInv_pushNested {senv : StructEnv} {nDecl : Nat} {s : MachRead} (hTr : TrInv senv nDecl s)
    (ob : Bool) (e : Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr)
    (hv : InRange nDecl s s.lets.size e.2.2.2.2.2) (hn : NoLoose 0 e.2.2.2.2.2) :
    FReachC nDecl s { s with inInner := ob, nested := s.nested.push e } ∧
    TrInv senv nDecl { s with inInner := ob, nested := s.nested.push e }

theorem nested_trace (senv : StructEnv) (nDecl n : Nat)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.nested env dom αs initsE body st))
    (r : (Call.nested env dom αs initsE body st).Res)
    (hv : (nestedStep senv env dom αs initsE body st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.nested env dom αs initsE body st) r) ∧
    PhPost senv nDecl (Call.nested env dom αs initsE body st) r
```
* 内容: `inInner` で失敗 / `cConv dom` / `findSomeO nestedProbe`（共有: 各候補は `cChain (.regs base :: env) body` を呼び、`CtlPh` の nested 節から保存済みの `v` の `InRange` / `NoLoose` を単調性で持ち上げる）/ `machReserve`（`machReserve_some` + `trInv_reserved`）/ `cChain`（`inInner := true` の状態）/ `ws ++` と nested の push（`reachC_ws` + `trInv_pushNested`）。
* 前提: なし。台帳差分 FG -0 +0 / T1 -0 +0。

## 4. Addendum: U-R7 — `instStep`（台帳差分 -0 +0、前提なし、review に出さない）

新ファイル `Tools/ShippingGen5ReaderTraceInst.lean`（+ `Tests/Gen5/ReaderTraceInstCheck.lean`）。`foldO` の帰納は、REV5 表の「`foldO_js_length` 相当は新規かも」のとおりこの単位で自前に証明する（js の長さを数える依存付き帰納。既存名はこの調査では見つからなかった）。LiftAgrees / RootFloatAgrees / SigTyClosed は使わない。
```lean
def InstFold (senv : StructEnv) (nDecl : Nat) (st0 : MachRead) (p : List Nat × MachRead) : Prop :=
  Adv st0 p.2 ∧ FReachC nDecl st0 p.2 ∧ TrInv senv nDecl p.2 ∧ ∀ a ∈ p.1, a < p.2.lets.size

def nonDom : MixedGateBinder → Nat
  | .domain => 0
  | _ => 1

theorem inRange_machInstOut {nDecl k' kk : Nat} {st : MachRead} (h : k' < st.insts.size) :
    InRange nDecl st kk (machInstOut k')
theorem trInv_letIndex {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {kd : MixedGateBinder} {v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    TrInv senv nDecl { st with lets := (machLetIndex nm kd v' st.lets).2 }
theorem trInv_dom {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with dom := some v' } ∧ TrInv senv nDecl { st with dom := some v' }
theorem trInv_pushInst {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st)
    (c : Name) (js : List Nat) (r : MixedGateBinder) (o : Sparkle.Compiler.MachInstOrigin.InstOrigin) (f : String)
    (hj : ∀ a ∈ js, a < st.lets.size) (hr : r ≠ .domain)
    (ho : ∀ cb aw dw, o = .mem cb aw dw → js.length = 4 ∧ r = .bits dw) (hf : ∀ i, o ≠ .field i) :
    FReachC nDecl st { st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f,
                               instOrigins := st.instOrigins.push o } ∧
    TrInv senv nDecl { st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f,
                               instOrigins := st.instOrigins.push o }

theorem instArg_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (kind : MixedGateBinder) (arg : Lean.Expr) (harg : NoPh arg = true ∧ BvarLt (env.length + nDecl) arg = true)
    (js : List Nat) (st : MachRead) (hI : InstFold senv nDecl st0 (js, st)) :
    SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧ p.1.length = js.length + nonDom kind)
      (instArg env k (js, st) (kind, arg))

theorem instFold_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env) :
    ∀ (l : List (MixedGateBinder × Lean.Expr)), (∀ a ∈ l, NoPh a.2 = true ∧ BvarLt (env.length + nDecl) a.2 = true) →
    ∀ (js : List Nat) (st : MachRead), InstFold senv nDecl st0 (js, st) →
      SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧
          p.1.length = js.length + (l.map fun a => nonDom a.1).sum)
        (foldO (instArg env k) (js, st) l)

theorem inst_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Name) (org : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.inst env c org kinds res args st))
    (r : (Call.inst env c org kinds res args st).Res)
    (hv : (instStep env c org kinds res args st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.inst env c org kinds res args st) r) ∧
    PhPost senv nDecl (Call.inst env c org kinds res args st) r
```
* `trInv_pushInst` の `hf` は `GroupsPh` の `.field 0` 節に新しい entry が当たらないための条件（`PhPre inst` の origin は `ord` か `mem`）。`inst_trace` の `args.length = kinds.length` は `PhPre inst` に無いので使わず、`kinds.zip args` の `mem` の場合の長さ 4 は `PhPre` の `kinds = [domain, bits aw, bits dw, bool, bits aw] ∧ args.length = 5` から数える。
* 前提: なし。台帳差分 FG -0 +0 / T1 -0 +0。
