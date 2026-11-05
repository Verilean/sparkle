# DG-READERTRACE freeze rev13 — U-R9 `loopBodyStep` と U-R10 `loopRootStep`（前提なし、文書のみ、review に出さない）

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt15`（rev12 `bdb4d79b` の後）。`DG_READERTRACE_FREEZE_REV5.md` の単位表 U-R9 / U-R10、`..._REV12.md`（U-R8 の判断依頼、承認待ち）と独立。
用語: 「見つからなかった」は「この調査で辿った経路では見つからなかった」の意味で、不可能の主張ではない。mutant は signature / defeq での棄却で意味的反例ではない。条件付きの結果は中間結果。以下の Lean は読んだファイルに合わせた未 elaborate の型で、elaborate 後に見つかった誤りは addendum で直す（黙って直さない）。
分担ルール（2026-11-01）: REV5 の U-R9 / U-R10 行（前提なし、台帳差分 -0 +0）の中で前提を増やさない単位なので、台帳差分を書いて進め、review には出さない。

**台帳差分: なし**（現在値 FG 103 / T1 54。今回 FG -0 +0 / T1 -0 +0）。`InstSFieldsDet` / `SigTyPh` / `LiftAgrees` / `RootFloatAgrees` / `Inst1` は使わない（`loopBodyStep` / `loopRootStep` は `rootFloat`・`lift`・`instantiate1`・`bundleIota` を呼ばない）。U-R8 は承認まで触らない。

## 1. U-R9 — `Tools/ShippingGen5ReaderTraceLoop.lean`（+ `Tests/Gen5/ReaderTraceLoopCheck.lean`）
```lean
-- machLoopRegs の結果の次値は入力の部分項（NoPh / BvarLt を引き継ぐ）
theorem loopRegs_ph {L : Nat} : ∀ (e : Lean.Expr) (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)),
    NoPh e = true → BvarLt L e = true → machLoopRegs e = some regs →
    ∀ r ∈ regs, NoPh r.2.2 = true ∧ BvarLt L r.2.2 = true
theorem machLetTail_nonLet {e : Lean.Expr} (h : ∀ nm ty v b nd, e ≠ .letE nm ty v b nd) : machLetTail e = e

-- bindLetAlias の reach（REV5: この調査では既存補題が見つからなかった。ここで証明する）
theorem bindLetAlias_reach {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (hTr : FullInv nDecl st) (hln : LetsNoLoose st)
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with lets := (machBindLetAlias nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLetAlias nm ty v' st.lets).2 } (machBindLetAlias nm ty v' st.lets).2.size
      (machBindLetAlias nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLetAlias nm ty v' st.lets).1

-- loopBodyStep の letE の 3 択（slot なら Named、let 変数なら Alias、他は machBindLet）
theorem trInv_bindLetAlias ... 同様の TrInv 保存  -- (形は elaborate 時に確定。TrInv senv nDecl { st with lets := … })
theorem loopLet_ph {senv nDecl st nm ty v'} (hTr : TrInv senv nDecl st) (h : InRange …) (hn : NoLoose 0 v') :
    let bl := if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets else machBindLet nm ty v' st.lets
    FReachC nDecl st { st with lets := bl.2 } ∧ TrInv senv nDecl { st with lets := bl.2 } ∧
    InRange nDecl { st with lets := bl.2 } bl.2.size bl.1 ∧ NoLoose 0 bl.1

-- 末尾の foldO loopNext
def LoopFold (senv : StructEnv) (nDecl : Nat) (base : Nat) (st0 : MachRead) (p : List (Nat × Lean.Expr) × MachRead) : Prop :=
  Adv st0 p.2 ∧ FReachC nDecl st0 p.2 ∧ TrInv senv nDecl p.2 ∧
  (∀ w ∈ p.1, w.1 < p.2.kinds.size ∧ InRange nDecl p.2 p.2.lets.size w.2)

theorem loopNext_trace (senv nDecl n) (hT : TraceGood senv nDecl (readF senv n)) (env) (base : Nat) {st0} (hE0 …) (hEp0 …)
    (regs) (hregs : ∀ r ∈ regs, NoPh r.2.2 = true ∧ BvarLt (env.length + nDecl) r.2.2 = true)
    (hbase : base + regs.length ≤ st0.kinds.size) :
    ∀ s a, a ∈ regs → LoopFold … s → SatP (readF senv n) (fun p => LoopFold … p ∧ p.1.length = s.1.length + 1) (loopNext env base s a)
-- foldO の帰納（長さを数える）
theorem loopFold_trace … (foldO (loopNext env base) ([], st) regs)

theorem loopBody_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopBody base env e st))
    (r : (Call.loopBody base env e st).Res)
    (hv : (loopBodyStep base env e st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.loopBody base env e st) r) ∧
    PhPost senv nDecl (Call.loopBody base env e st) r
```
* `letE` arm: `cConv env 0 v st`（`hT` から、`PhPre` の `NoPh/BvarLt` を `letE` の 3 成分に分ける）→ 3 択 → `cLoopBody base (.val x :: env) b …`（`hT` から、`PhPre loopBody` の追加条件 `base + regs.length ≤ kinds.size` は `machLetTail (.letE …) = machLetTail b` と `reachC_sizes_mono` で持ち上げる）。旧 `Pre/Post` 側の `Adv` は `loopLet_facts`（既存）と `alias_premise rfl`（変換値の `LetOk` は `hT` の `Post`）で作る。
* それ以外の arm: `machLoopRegs e`（`optK`）→ `foldO (loopNext env base)` → `{ st with ws := st.ws ++ ws.toArray }`（`reachC_ws`。各 `w.1 = base + ws.length < base + regs.length ≤ kinds.size` と `InRange` は `loopNext` の post）。
* 前提: なし。

## 2. U-R10 — `Tools/ShippingGen5ReaderTraceLoopRoot.lean`（+ `Tests/Gen5/ReaderTraceLoopRootCheck.lean`）
```lean
theorem loopView_ph {L : Nat} {e dom body : Lean.Expr} (hn : NoPh e = true) (hb : BvarLt L e = true)
    (h : loopView? e = some (dom, body)) :
    (NoPh dom = true ∧ BvarLt L dom = true) ∧ (NoPh body = true ∧ BvarLt (L + 1) body = true)

theorem trInv_pushLoop {senv nDecl} {s1 : MachRead} (hTr : TrInv senv nDecl s1) {dom' : Lean.Expr}
    (hdr : InRange nDecl s1 s1.lets.size dom') (hdn : NoLoose 0 dom')
    (kinds : List MixedGateBinder) (inits : List Nat) (names : List Name) (loops nestedLoops loopDepth …) :
    FReachC nDecl s1 { s1 with kinds := s1.kinds ++ kinds.toArray, inits := s1.inits ++ inits.toArray,
        names := s1.names ++ names.toArray, dom := some dom', loops := …, nestedLoops := …, loopDepth := … } ∧
    TrInv senv nDecl { s1 with … }          -- 同じ状態
theorem trInv_pushLoopWs … -- loopWs := st.loopWs.push (base, n, ws)、loopDepth := d の復元（CtrlEq 内、base + n ≤ kinds.size を要する）

theorem loopProbe_trace … : ∀ a, SatP (readF senv n) (fun p : Nat × MachRead => FReachC nDecl st1 p.2 ∧ TrInv senv nDecl p.2 ∧ p.1 + n ≤ p.2.kinds.size) (loopProbe env body n st1 a)

theorem loopRoot_trace (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.loopRoot env e st))
    (r : (Call.loopRoot env e st).Res)
    (hv : (loopRootStep senv env e st).run (readF senv n) = some (some r)) :
    FReachC nDecl st (callOut (Call.loopRoot env e st) r) ∧
    PhPost senv nDecl (Call.loopRoot env e st) r
```
* 内容: `loopView?`（`loopView_ph`）→ `inInner` で失敗 → `machLoopRegs (machLetTail body)`／`loopRegBad`／`machSlotKind?`／`machInit?`（純粋、成分の長さ `regs.length = kinds.length = n` を `mapM` から数える）→ `cConv env 0 dom st`（`hT`）→ `domGuard`（`satp_domGuard`）→ `findSomeO (loopProbe …)`（共有: `CtlPh` の `loopWs` 節の `x.1 + x.2.1 ≤ kinds.size` と `n0 = n` から `.state b0 n` は範囲内、probe 内の `cLoopBody` は `PhPre loopBody` の `base + regs.length ≤ kinds.size` を `b0 + n ≤ kinds.size` と `regs.length = n`（`n0 = n` 確認済み）で満たす。`ws := #[]` は空の `FStep.ws`、戻しは `reachC_ws`（`st.ws` の各要素は単調性で持ち上げ））／新規: `trInv_pushLoop` → `cLoopBody base (.state base n :: env) body` → `loopWs` の push（`base + n ≤ kinds.size`）と `loopDepth` の復元。
* 前提: なし（`InstSFieldsDet` 等は使わない）。台帳差分 FG -0 +0 / T1 -0 +0。
* 主張しないこと: U-R8 / U-R11、`TraceGood senv nDecl (readF senv n)` 全体、dispatch、real run と FG。
