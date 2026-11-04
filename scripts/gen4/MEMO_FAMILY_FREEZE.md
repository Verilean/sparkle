# MEMO_FAMILY_FREEZE (rev3): 型の freeze — memo 法則家族 `MemoFamily`（15 文、Diag の狭い 3 文と Triple 形の `lamTelescope`、数え方 R-1）

状態: **rev3（rev2 = 承認済み、base fc68442e からの改訂）。freeze 提案（文書 + scratch の Check のみ）。reviewer の承認まで `Tools/Assume/MemoFamily.lean` 本体には文を足さない。** 本単位で編集した Lean は新規の `Tests/Gen4/MemoFamilyRev3Check.lean`（と `lakefile.lean` への `lean_lib` 1 行）だけ。`Elab.lean`・`Tools/ShippingGen2Defs.lean`・T1Hyp / T1HypND・`MemoFamily.lean` は変えていない。
根拠: ユーザー判断 2026-11-04（`git show 723361ff:scripts/gen4/M4_DECISION.md` §8: Diag は A（reviewer の条件で狭める）、窓は A（Triple 形、失敗側に `OkExc`）、quiet は C）。reviewer 相談: `scripts/gen4/M4_CONSULT_2026-11-04.md`。判断資料: `KWALK_DIAG_DECISION.md`、`KWALK_LEGACY_WINDOW_DECISION.md`。
台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。rev3 の承認だけでは変わらない。受理待ち・見込みは §R7 の「条件付き台帳」に分けて書く。
用語: **elaborated** = scratch の `kjob lake build` exit 0。**read** = 私の読みで Lean は通していない。mutant は **signature/defeq での棄却** であって意味的反例ではない。「見つからなかった」は「この調査では見つからなかった」の意味で、不可能・導出不能とは書かない。

## R0. 結論（rev3）

1. 家族は **15 文**（rev2 の 12 文 + Diag の 3 文。`lamTelescope` は置き換えなので ±0）。Diag を 1 文で包まず、`profLogIO` が実際に使う固定の列だけの文 `logProf`、固定の stderr 2 操作の文 `stderrLine`、`ppExpr` / 印字関数のための `OkEnv` の memo 版 `printersMv` に分けた（§R2）。reviewer の「暫定 14 文」より 1 文多い。理由は §R2.7 の選択肢表（`printersMv` を外せば 14 文）。
2. `lamTelescope` は **Triple 形に置き換える**（§R3）。旧 `Keeps` 版は、Triple 形から **同名・同型の定理 `MemoTele.lamTelescope`** として導出できた（elaborated）ので、文は増えない。既存の利用側 2 か所（`Tools/ShippingGen4KWalk.lean:296`、`Tools/ShippingGen4KWalkLegacyTail.lean:84`）の本文は変えずに通る（Check で複製した本文を elaborate、さらに `MemoFamily.lean` を候補版に差し替えた使い捨ての worktree で実際の build、§R6）。
3. 導けたもの: `LogMvK` は `logProf` そのもの。`PpMvK` は `printersMv` と既存の `frame` から導けた（elaborated、§R2.5）。6973-6977 の 5 連の lift と 6423-6425 の対も扱える（§R2.4）。
4. 導けなかったもの: Elab.lean 6605 の `ex.toMessageData.toString`（`msgToString`）。この調査では供給元・経路が見つからなかった。`OkMsg` の `withContext c` が求めるのは 3 つの ref の `OkEnv c.env` だけで、`c` は throw 時に捕えた環境であり現在の world の環境ではない。memo 版の `OkMsg` と、例外がその類に入るという新しい法（`excOk` の memo 版）が要る。rev3 には入れず、仮説 `MsgMvK`（def）として残す（§R2.6）。
5. 台帳は R-1（`MemoFamily` の 1 行）のまま。rev3 の承認だけでは FG ±0。K walk 全体の受入で +1（91→92）。ただし `MsgMvK` が残る間は K walk は条件付きで、全体の受入にはならない（§R7）。
6. scratch の Check: `Tests.Gen4.MemoFamilyRev3Check`（`kjob lake build` exit 0、756 jobs、対象 SHA は note に記載）。`TYPE 15/15 / MUTANT 11/11 / OUTSIDE 18/18 / AXIOMS 20 standard-only / CLOSURE 4 clean (+2 positive controls) / MODEL 1`（§R5）。sorry・axiom・native_decide なし。

## R1. M4_DECISION §8 の reviewer の条件への対応

| 条件（§8） | rev3 での扱い |
|---|---|
| Diag 全体を 1 文で包まない | 3 文に分割: `logProf`（固定の profile logger）、`stderrLine`（固定の stderr 2 操作）、`printersMv`（印字関数の条件）。`Diag` の構成子 9 個のうち家族に入るのは固定の列と印字だけ（§R2.1） |
| `ppExpr`: 任意の printer は memo を書きうる。safe printer / `OkEnv` を完全型に含めるか、経路から除く | **含められた**（`OkEnvMv`、memo 版の `OkEnv`、完全型を elaborate）。`PpMvK` を導出できた。外す案との比較は §R2.7 |
| `Handle.mk` / `putStrLn` / `flush`: `profLogIO` が使う固定の path・mode・操作列に限る | `logProf` は `profLogIO b msg` の 1 項。path `"/tmp/sparkle-profile.log"`、mode `.append`、操作列は `profLogIO` の定義に固定（§R2.3）。任意の path・mode・Handle・Stream の文は家族に入れない（境界の外の Prop として型は書けるが、新しい文のどれとも defeq でないことを Check で確認、OUTSIDE 18/18） |
| stderr 系と `OkMsg` 制約つき `msgToString` は別の文に分けてよい | stderr は `stderrLine` に分けた。`msgToString` は §R2.6 の理由で家族に入れず、仮説 `MsgMvK` として残す |
| 窓: Triple 形が旧 `Keeps` 版を導けるなら置き換え。導出と全利用側を Check で確認。できなければ追加（暫定 14 文） | **導けた**ので置き換え（§R3.2）。全利用側 2 か所を確認（§R3.3、§R6） |

## R2. Diag

### R2.1 実際の呼び出し箇所（`Sparkle/Compiler/Elab.lean`、数えた）

grep した語: `ppExpr` / `IO.eprintln` / `flushStderr` / `Handle.mk` / `toMessageData` / `.toString`（`MessageData` 用）/ `getStderr` / `IO.println` / `dbg_trace` / `logInfo` / `IO.print` / `getStdout`。最後の 5 語（`IO.println` 以降）は Elab.lean にヒットなし。`trace[...]` は 28 か所あり、`Diag` ではなく既存の `FramedNM` 側（`coreModifyTrace` 等）で扱われている（rev2 から変更なし）。

| 行 | 操作 | rev3 での扱い |
|---|---|---|
| 5436-5442 | `logProf`（`profile` の下で `IO.eprintln msg; flushStderr; Handle.mk "/tmp/sparkle-profile.log" .append; putStrLn msg; flush`） | `logProf`（`Diag.profLog` と同じ項 `liftM (profLogIO b msg)`） |
| 9009-9015 | 同じ列（`#synthesizeVerilog` コマンド側の `logProf`、`CommandElabM`） | 同じ列。K walk の対象（translator）ではない |
| 6423-6425 | `SPARKLE_DEBUG_HWCALL` のとき `eprintln` + `flushStderr`（2 個の `liftMetaM`） | `stderrLine` |
| 6973-6977 | 10000 回ごとの profile tick: `eprintln body; flushStderr; Handle.mk 同 path .append; putStrLn; flush`（5 個の lift） | `logProf` + 補題 `profBlock_eq`（§R2.4） |
| 681, 686, 715 | `ppExpr`（helper のエラー文の整形、`throwError` の直前） | `printersMv` から導く `PpMvK` |
| 5709 | `ppExpr _e`（`handleErrorPatterns`） | 同上 |
| 7025 | `try ppExpr ty catch _ => ...` | 同上 |
| 7366 | `ppExpr e`（ite/dite のエラー） | 同上 |
| 6605 | `ex.toMessageData.toString`（`handleDefinitionUnfold` の catch） | **含めない**（§R2.6）。仮説 `MsgMvK` |

KWALK_DIAG_DECISION.md §2 の数え（`ppExpr` 3 箇所、eprintln 2 組）には、6605 の `msgToString` と helper の `ppExpr` 3 箇所が入っていなかった（helper の 3 箇所は KWALK_LEGACY_WINDOW_DECISION.md §5 で訂正済み。6605 は本調査で追加）。

### R2.2 既存の A 境界が述べること

`RefLawsAOps.diag`（`Tools/ShippingChildInvA.lean:266`）は `Diag p` について `cv` / `sv` / `dv` の保存と `quiet` の保存だけを述べる。`mv`（memo 表）は述べない。`quiet` の説明（`Tools/ShippingChildInv.lean`、`RefLaws.quiet`）は「3 つの ref を書かない」世界であり、memo は 4 つ目の ref。したがって `mv` の保存は quiet から出ない。

### R2.3 rev3 の Diag の文（完全な型。構造全体は §2）

```lean
  logProf : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (b : Bool) (msg : String) w, O.quiet w →
    mv (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) = mv w
  stderrLine : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (s : String) w, O.quiet w →
    mv (endW mctx mref cctx cref ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w) = mv w
  printersMv : ∀ w, O.quiet w → OkEnvMv (readOf cref w).env
```

`profLogIO`（`Tools/ShippingChildInv.lean:60`）は Elab.lean の `logProf` を写したもの（read）:

```lean
def profLogIO (profile : Bool) (msg : String) : IO Unit := do
  if profile then
    IO.eprintln msg
    Sparkle.Compiler.flushStderr
    let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append
    h.putStrLn msg
    h.flush
```

固定されるのは path `"/tmp/sparkle-profile.log"`、mode `.append`、操作列（eprintln → flushStderr → Handle.mk → putStrLn → flush）。データとして動くのは `b` と `msg` だけ。`profLogIO false msg = pure ()` は `rfl`（Check の `profLogIO_false`）。**この文は「任意の path・mode・Handle・Stream」については何も言わない。**

1 文説明:
- `logProf`: profile logger を 1 回走らせても（quiet な世界・許される文脈のとき）メモ表は変わらない。
- `stderrLine`: 標準エラーに 1 行書いてフラッシュしても、メモ表は変わらない（インストールされた stderr が memo を書かないという仮定。`IO.eprintln` の引数は文字列データ）。
- `printersMv`: quiet な世界の環境について、その環境の印字関数（`ppExprWithInfos` / `ppConstNameWithInfos`、任意の印字文脈、任意の世界から）はメモ表を変えない。`OkEnv`（3 つの ref 用、`Tools/ShippingChildInv.lean:122`）の memo 版。

### R2.4 6973-6977 の 5 連と 6423-6425 の対

- 6973-6977 は MetaM の 1 つの `do` ブロック内で IO 操作が 1 つずつ lift される。`logProf` は `liftM (profLogIO true msg)`（IO 全体を 1 回 lift）。両者の等式を補題で示した（elaborated）:

```lean
theorem liftIOCore_bind {α β : Type} (x : IO α) (f : α → IO β) :
    (Core.liftIOCore (x >>= f) : CoreM β) = (Core.liftIOCore x >>= fun a => Core.liftIOCore (f a) : CoreM β) := by
  funext c s w
  unfold Core.liftIOCore
  cases h : x w with
  | ok a w1 =>
    simp [StateRefT'.instMonad._aux_13, StateRefT'.instMonad._aux_5, instMonadEIO._aux_13, EIO.adapt, EStateM.adaptExcept,
      EStateM.bind, ReaderT.bind, readThe, MonadReaderOf.read, ReaderT.read, StateRefT'.lift, h, pure, ReaderT.pure,
      EStateM.pure, ReaderT.run, StateRefT'.get, StateRefT'.set, bind, getRef, EST.bind, liftM, monadLift,
      MonadLift.monadLift, IO.toEIO, EST.pure, EStateM.adaptExcept, EIO.adapt, EST.Out.ok, read, MonadReader.read, instMonadEIO._aux_5, EST.Out.ok, EStateM.pure]
  | error e w1 =>
    simp [StateRefT'.instMonad._aux_13, StateRefT'.instMonad._aux_5, instMonadEIO._aux_13, EIO.adapt, EStateM.adaptExcept,
      EStateM.bind, ReaderT.bind, readThe, MonadReaderOf.read, ReaderT.read, StateRefT'.lift, h, pure, ReaderT.pure,
      EStateM.pure, ReaderT.run, StateRefT'.get, StateRefT'.set, bind, getRef, EST.bind, liftM, monadLift,
      MonadLift.monadLift, IO.toEIO, EST.pure, EStateM.adaptExcept, EIO.adapt, EST.Out.ok, read, MonadReader.read, instMonadEIO._aux_5, EST.Out.ok, EStateM.pure]

theorem liftM_bind_metaM {α β : Type} (x : IO α) (f : α → IO β) :
    (liftM (x >>= f) : MetaM β) = ((liftM x : MetaM α) >>= fun a => (liftM (f a) : MetaM β)) := by
  funext mctx mref cctx cref w
  simp only [liftM, monadLift, MonadLift.monadLift]
  show Core.liftIOCore (x >>= f) cctx cref w = ((Core.liftIOCore x : CoreM α) >>= fun a => Core.liftIOCore (f a)) cctx cref w
  rw [liftIOCore_bind]
```

  `profBlock_eq`（`simp only [profLogIO, ↓reduceIte, liftM_bind_metaM]` で閉じる、elaborated）:

```lean
theorem profBlock_eq (s : String) :
    ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit) >>= fun _ =>
      (liftM (IO.FS.Handle.mk "/tmp/sparkle-profile.log" IO.FS.Mode.append) : MetaM IO.FS.Handle) >>= fun h =>
      (liftM (h.putStrLn s) : MetaM Unit) >>= fun _ =>
      (liftM h.flush : MetaM Unit)) = (liftM (profLogIO true s) : MetaM Unit)
```

 `theorem profBlock_mv` が 5 連の `endW` の `mv` 保存を `logProf true` から出す。
- 6423-6425 は `liftMetaM (eprintln …)` と `liftMetaM flushStderr` の 2 呼び出しで、`stderrLine` の項そのもの（`theorem stderrPair_mv`）。実際の K walk では CompilerM の 2 つの bind を 1 単位（`stderrLine`）として扱う必要がある。TripleC がこの融合をできるかは walk 時に確認する（未確認）。

### R2.5 `ppExpr`: 含められるか（調査結果）

`Lean.Meta.ppExpr e = (·.fmt) <$> ppExprWithInfos e`、`Meta.ppExprWithInfos e = do let ctx ← getPPContext; Lean.ppExprWithInfos ctx e`（`Lean/Meta/Basic.lean:2224-2237`、toolchain v4.32.1、read）。`getPPContext` は `getEnv`、`getMCtx`、`getLCtx`、`getOptions`、`getCurrNamespace`、`getOpenDecls` を読む。印字の本体 `Lean.ppExprWithInfos ctx e` は `BaseIO` で、`ppExt.getState ctx.env` に登録された印字関数（delaborator を含む）を `ctx.env` から取り出して走らせる（`Lean/Util/PPExt.lean:69-85`、read）。つまり **任意の登録 printer は memo の ref を書きうる**（reviewer の指摘どおり）。`ctx.env` は world の `cref` の環境なので、条件は「その環境の印字関数が memo を変えない」と型で書ける:

```lean
def MvInert {α : Type} (x : BaseIO α) : Prop :=
  ∀ w, match x w with
    | .mk _ w' => readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w
def OkEnvMv (env : Environment) : Prop :=
  ∀ ctx : PPContext, ctx.env = env →
    (∀ e : Lean.Expr, MvInert (ppExprWithInfos ctx e)) ∧ (∀ n : Name, MvInert (ppConstNameWithInfos ctx n))
-- 家族の文: printersMv : ∀ w, O.quiet w → OkEnvMv (readOf cref w).env
```

**導出（elaborated）**: `printersMv` と既存の `frame`（`getEnv` = `FramedNM.env`、`getMCtx` = `FramedNM.metaGet`）と `O.frameQ` から `PpMvK` が出る。`getLCtx` などの純粋な読みは `rfl`、最後の `BaseIO` の lift は `MvInert`:

```lean
open Tools.ShippingGen4KWalk in
theorem ppExpr_mv (M : MemoFamilyR3 O)
    (hA : AdmCtx O.quiet mctx cctx) (e : Lean.Expr) (w : Void IO.RealWorld) (hq : O.quiet w) :
    mv (endW mctx mref cctx cref (Lean.Meta.ppExpr e) w) = mv w := by
  unfold Lean.Meta.ppExpr Lean.Meta.ppExprWithInfos Lean.Meta.getPPContext
  have M2 := M.toRev2
  -- the two state reads
  have hf1 : mv (endW mctx mref cctx cref (getEnv : MetaM Environment) w) = mv w := M2.frame hA _ FramedNM.env w hq
  have hq1 : O.quiet (endW mctx mref cctx cref (getEnv : MetaM Environment) w) :=
    O.frameQ hA _ (framedNM_toA FramedNM.env) w hq
  have hf2 : mv (endW mctx mref cctx cref (getMCtx : MetaM MetavarContext)
      (endW mctx mref cctx cref (getEnv : MetaM Environment) w)) = mv (endW mctx mref cctx cref (getEnv : MetaM Environment) w) := by
    rw [getMCtx_endW mctx cctx]; exact M2.frame hA _ FramedNM.metaGet _ hq1
  let w1 := endW mctx mref cctx cref (getEnv : MetaM Environment) w
  let w2 := endW mctx mref cctx cref (getMCtx : MetaM MetavarContext) w1
  let ctx0 : PPContext :=
    { env := (readOf cref w).env, mctx := (readOf mref w1).mctx, lctx := Meta.Context.lctx mctx,
      opts := cctx.options, currNamespace := cctx.currNamespace, openDecls := cctx.openDecls }
  have hCB : (do
      let __do_lift ← getEnv
      let __do_lift_1 ← getMCtx
      let __do_lift_2 ← getLCtx
      let __do_lift_3 ← getOptions
      let __do_lift_4 ← getCurrNamespace
      let __do_lift_5 ← getOpenDecls
      pure { env := __do_lift, mctx := __do_lift_1, lctx := __do_lift_2, opts := __do_lift_3,
             currNamespace := __do_lift_4, openDecls := __do_lift_5 } : MetaM PPContext) mctx mref cctx cref w
      = .ok ctx0 w2 := rfl
  obtain ⟨a, w3, hx, hl⟩ := liftBaseIO_run mctx cctx (Lean.ppExprWithInfos ctx0 e) w2
  have hB := bind_ok mctx cctx (f := fun ctx => liftM (Lean.ppExprWithInfos ctx e)) hCB
  have hB' : ((do
      let __do_lift ← getEnv
      let __do_lift_1 ← getMCtx
      let __do_lift_2 ← getLCtx
      let __do_lift_3 ← getOptions
      let __do_lift_4 ← getCurrNamespace
      let __do_lift_5 ← getOpenDecls
      pure { env := __do_lift, mctx := __do_lift_1, lctx := __do_lift_2, opts := __do_lift_3,
             currNamespace := __do_lift_4, openDecls := __do_lift_5 } : MetaM PPContext) >>=
      fun ctx => (liftM (Lean.ppExprWithInfos ctx e) : MetaM FormatWithInfos)) mctx mref cctx cref w = .ok a w3 :=
    hB.trans hl
  have hM := map_ok mctx cctx (g := fun x => FormatWithInfos.fmt x) hB'
  have hend : endW mctx mref cctx cref ((fun x => FormatWithInfos.fmt x) <$> ((do
      let __do_lift ← getEnv
      let __do_lift_1 ← getMCtx
      let __do_lift_2 ← getLCtx
      let __do_lift_3 ← getOptions
      let __do_lift_4 ← getCurrNamespace
      let __do_lift_5 ← getOpenDecls
      pure { env := __do_lift, mctx := __do_lift_1, lctx := __do_lift_2, opts := __do_lift_3,
             currNamespace := __do_lift_4, openDecls := __do_lift_5 } : MetaM PPContext) >>=
      fun ctx => (liftM (Lean.ppExprWithInfos ctx e) : MetaM FormatWithInfos))) w = w3 := by
    unfold endW; rw [hM]
  have hm3 : mv w3 = mv w2 := by
    have := ((M.printersMv w hq ctx0 rfl).1 e) w2
    rw [hx] at this
    exact this
  refine Eq.trans (congrArg mv hend) ?_
  exact hm3.trans (hf2.trans hf1)
```

`theorem ppMvK_of (M : MemoFamilyR3 O) : PpMvK O` として elaborate 済み。**この文は universal（quiet な世界すべて）なので、K walk が「環境が変わらない」ことを別に示す必要はない。**（world ごとの環境の不変量を持ち回る案は、環境を変える操作の frame の文が要り、不採用。）

主張しないこと: `printersMv` が真であるとは主張しない。T3（`RefLaws.excOk`、`Tools/ShippingChildInv.lean:363-371`）が既に「エラーが捕える環境の印字関数は不活性（`OkEnv`）」という環境についての仮定を含んでおり、`printersMv` は同じ種類の仮定を memo に対して言うだけである。`Laws` との無矛盾性は D.E-10 で OPEN のまま。

### R2.6 `msgToString`（6605）を含められなかった理由

`ex.toMessageData.toString` は `Diag.msgToString m (_ : OkMsg m)` の形（A 側の既存、`O.diag`）。`OkMsg` の `withContext c a` は `OkEnv c.env`（3 つの ref）だけを求める。memo 版には (i) `OkMsg` の memo 版（`OkEnvMv c.env` を求める類）と、(ii) 例外がその類に入るという法（`excOk` の memo 版）が要る。`c` は **throw 時に捕えた環境** なので、`printersMv`（現在の world の環境について）からは出ない。この調査では (ii) の供給元・経路は見つからなかった。これは 2 つの新しい文（類の言い直しと `excOk` の memo 版）になるので、rev3 には入れない。

残る仮説（def、家族の文ではない）:

```lean
def MsgMvK (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ (m : MessageData), OkMsg m → ∀ w,
    O.quiet w → mv (endW mctx mref cctx cref (liftM m.toString : MetaM String) w) = mv w
```

（`LogMvK` / `PpMvK` と同じ流儀。Check で型を elaborate 済み。）影響: `LegacyImplK` を K で歩くとき、`handleDefinitionUnfold` の catch の 1 か所がこの仮説に依存する。K walk 全体の受入は `MsgMvK` を閉じるか、別の判断（§R7）が要る。

### R2.7 選択肢（`ppExpr` / 印字関数）

| | 内容 | 家族の文 | LegacyImplK・legacy 腕に残る仮説 | 可逆性 |
|---|---|---|---|---|
| **P-incl（本 freeze の提案）** | `printersMv` を家族に入れる | 15 | `MsgMvK`（6605 の 1 か所） | 文を消せば `PpMvK` が仮説に戻る |
| P-excl | 印字関数の条件を入れず、`ppExpr` の経路を対象から除く | 14 | `PpMvK`（6 か所: 681, 686, 715, 5709, 7025, 7366）と `MsgMvK`（6605） | 後から P-incl に上げられる |
| P-world | `printersMv` を world の不変量にして K walk が持ち回る | 15 + 環境を変える操作の frame の文 | `MsgMvK` | 不採用（frame の文が増え、S0-S6 の `StableK` の作り直し） |

推奨: P-incl。理由: 条件は `OkEnv` と同じ種類の環境についての仮定で、完全型に入り（elaborated）、`PpMvK` を導出できた。P-excl は文が 1 つ減るが、6 か所の仮説が残る。判断は reviewer / ユーザー。

## R3. 窓: `MemoTele.lamTelescope` を Triple 形に

### R3.1 完全な型

```lean
  lamTelescopeT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      P w → P w') →
    (∀ a w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      Q a w → Q a w') →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      R w → R w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
```

`Triple`（`Tools/ShippingChildKeeps.lean:50`、名前空間 `Tools.ShippingChildInv`）: `Triple P m Q R` = 「`P` の world から `m` が返れば `Q a w'`、投げれば `R e w'`」。成功の事後条件 `Q` と失敗の事後条件 `R ∧ OkExc` が分かれている。1 文説明: `lambdaTelescope e k` は束縛を開いて続き `k` を 1 回走らせて閉じる（`Lean/Meta/Basic.lean:1598-1606`、`k` は最後の動作、read）。続きが `P` から始まり、返れば `Q`、投げれば `R`（かつ例外の message が `OkExc`）で終わるなら、telescope 全体も同じ。telescope 自身の副作用（fvar の確保など）は `cv`/`sv`/`dv`/`mv` と quiet の保存だけの world 変換で、`P`/`Q`/`R` はそれで保たれる（転送の 3 前提）。

### R3.2 旧 `Keeps` 版の導出（elaborated）

`Keeps I m ⇔ Triple I m (fun _ => I) (fun e w => I w ∧ OkExc e)`（`keeps_iff`、既存）なので、`Q := fun _ => I`、`R := I` を入れると旧文が出る:

```lean
theorem MemoTele.lamTelescope (T : MemoTele O) : -- rev2 のフィールド lamTelescope と同じ型
    ∀ {mctx} {cctx} {α : Type} (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') → I w → I w') →
    ∀ e k cleanup, (∀ mctx' cctx' xs b, AdmCtx O.quiet mctx' cctx' → Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup) := by
  intro mctx cctx α I hA hIq htr e k cleanup hk
  exact keeps_iff.mpr (T.lamTelescopeT I (fun _ => I) I hA hIq (fun _ => hIq) hIq htr (fun _ => htr) htr e k cleanup
    (fun mctx' cctx' xs b hA' => keeps_iff.mp (hk mctx' cctx' xs b hA')))
```

（完全な型は §2 の最後のブロック。）さらに `MemoFamilyR3.toRev2 : MemoFamilyR3 O → MemoFamily O`（rev3 の 15 文から rev2 の 12 文を全部作る）を elaborate した。したがって `M : MemoFamily O` を取る既存の定理（30 ファイル）は rev3 の家族をそのまま受ける。**置き換えで文は増えない**（旧版を足す必要がない）。フィールド名は、旧名 `lamTelescope` を導出定理に譲るため、Triple 形のフィールドを `lamTelescopeT` とする。

### R3.3 既存の利用側（grep で数えた）

`M.tele.lamTelescope` / `T.lamTelescope`（`MemoTele` 由来）の使用: **2 か所**。

| 場所 | 形 | 結果 |
|---|---|---|
| `Tools/ShippingGen4KWalk.lean:296`（`keeps_KW_lambdaTelescope`） | `M.tele.lamTelescope (KW O P) hA (fun _ h => h.1) (kw_tele_transfer P) e k cleanup hk` | 本文のまま elaborate（Check の `replay_keeps_KW_lambdaTelescope`）、使い捨て worktree の実 build も通過（§R6） |
| `Tools/ShippingGen4KWalkLegacyTail.lean:84`（`kwalkM` のリスト内） | `M.tele.lamTelescope I _ hS.1 hS.2 _ _ _` | Check の `replay_legacyTail`、使い捨て worktree の `Tools.ShippingGen4KWalkLegacyTail` build 通過（§R6） |

他に `MemoTele` のフィールドを構築する箇所は `Tools/Assume/MemoFamily.lean` 自身と `Tests/Gen4/MemoFamilyCheck.lean`（rev2 の TYPE / vacuous model）。後者は rev3 の実装単位で更新する（本単位では触らない）。`RefLawsATele.lamTelescopeLaw`（`Tools/ShippingChildLegacyTailA.lean:200` など）は別の構造（A 境界側）で、本件とは無関係。

### R3.4 他の 3 つの telescope 文

`telescope` / `localDecl` / `letDecl` は変えない。変える理由は見つからなかった。ただし K walk がこれらの失敗側を `Keeps` 形で使うとき窓と同じ問題（成功と失敗で事後条件が違う）が出るかは、今の walk では `forallTelescopeReducing` / `withLocalDecl*` の内側に memo 書き込みが無い（read）ので未確認。必要になったら別 freeze で書く。

## R4. rev3 の完全な Lean 型

§2 のコードブロックに全文を置く（`MvInert` / `OkEnvMv`、`MemoTele`、`MemoFamily`、導出定理 `MemoTele.lamTelescope`）。差分は §R2.3（Diag の 3 文）と §R3.1（`lamTelescopeT`）に抜粋した。

## R5. scratch の Check（`Tests/Gen4/MemoFamilyRev3Check.lean`）

`kjob lake build Tests.Gen4.MemoFamilyRev3Check` exit 0（756 jobs、対象 SHA は note）。出力 1 行:
`MEMOFAMILY REV3 CHECK: TYPE 15/15 (11 unchanged vs rev2 Expected, 4 new/changed) / MUTANT 11/11 / OUTSIDE 18/18 (6 statements x 3 new fields, none defeq) / AXIOMS 20 standard-only / CLOSURE 4 clean (+2 positive controls) / MODEL 1 (vacuous quiet=False; type satisfiability only)`

- **TYPE**: 15 文それぞれが `Expected.*` と `isDefEq`。変わらない 11 文は rev2 の `Tests.Gen4.MemoFamilyCheck.Expected.*`（rev2 の Check が別に書いたもの）と照合。新規・変更の 4 文（`lamTelescopeT`、`logProf`、`stderrLine`、`printersMv`）は本 Check の `Expected` に別に書いた。
- **置換の導出**（theorem、AXIOMS で standard のみ）: `MemoTeleR3.lamTelescope`（旧 `Keeps` 版）、`MemoTeleR3.toRev2`、`MemoFamilyR3.toRev2`（rev3 → rev2 の全 12 文）、`logMvK_of`、`profBlock_eq` / `profBlock_mv` / `stderrPair_mv`、`ppExpr_mv` / `ppMvK_of`、利用側の複製 `replay_keeps_KW_lambdaTelescope` / `replay_legacyTail`。
- **MUTANT**（signature/defeq での棄却。変えた文が偽だとか実行系で破れるという意味ではない）11 件:

| # | 対象 | 変更 |
|---|---|---|
| L1 | `lamTelescopeT` | `Q a w → quiet w` を外す |
| L2 | 同 | 失敗側の `OkExc` を外す（`R w` だけ） |
| L3 | 同 | `R` の転送前提を外す |
| L4 | 同 | 結論の成功側を `Q` から `True` にする |
| L5 | 同 | rev2 の `Keeps` 形（旧文）に戻す。型が違うことの確認 |
| L6 | 同 | `P w → quiet w` を外す |
| D1 | `logProf` | `O.quiet w →` を外す |
| D2 | `stderrLine` | `flushStderr` を外す（print だけ） |
| D3 | `printersMv` | `O.quiet w →` を外す |
| D4 | `printersMv` | `OkEnvMv` を 3 つの ref 用の `OkEnv` に取り替える |
| D5 | `logProf` | `AdmCtx` を外す |

- **OUTSIDE（境界の外）**: 次の 6 つの Prop は型として書けるが、`logProf` / `stderrLine` / `printersMv` のどれとも defeq でない（6 × 3 = 18 件の棄却）。これらは家族に入っていない。
  1. `arbPath`: 任意の path・mode の `Handle.mk` + `putStrLn` + `flush`
  2. `arbHandlePut`: 任意の `Handle` の `putStrLn`
  3. `arbHandleFlush`: 任意の `Handle` の `flush`
  4. `arbStreamFlush`: 任意の `IO.FS.Stream` の `flush`（`Stream` は closure の構造体）
  5. `arbPrinter`: 無条件の `ppExpr`（= `PpMvK`）。`printersMv` とは別の文
  6. `msgRender`: `OkMsg` の message の描画（= `MsgMvK`）。§R2.6
- **AXIOMS**: 20 の対象（構造 2、`mk` 2、vacuous model、導出定理、`OkEnvMv` / `MvInert` / `MsgMvK`）がすべて `propext` / `Classical.choice` / `Quot.sound` のみ。`sorryAx` / `ofReduceBool` なし。
- **CLOSURE**: `MemoFamilyR3` / `MemoTeleR3` / `OkEnvMv` / `MvInert` の推移閉包（型と thm/def の本体、opaque の本体は追わない）に `Laws` / `T1Hyp` / `T1HypND` は含まれない。検出器は `T1Hyp` / `T1HypND` では反応する（positive control 2 件）。
- **MODEL**: `vacuous_model_R3`（`quiet = False`）で 15 文がすべて充足する。型が空でないことの確認であって、実行系についての証拠ではない。

## R6. 既存の利用側の実 build（使い捨ての worktree）

`MemoFamily.lean` を候補版（本文書 §2 の構造 + 導出定理、`import Tools.ShippingChildKeeps` 追加）に差し替えた **使い捨ての worktree**（コミットしない、使用後に削除）で、次を `kjob lake build`:

| target | 結果 |
|---|---|
| `Tools.Assume.MemoFamily` | exit 0（313 jobs） |
| `Tools.ShippingGen4KWalk`（利用側 296） | exit 0（317 jobs）、error 0 |
| `Tools.ShippingGen4KWalkLegacyTail`（利用側 84） | exit 0（350 jobs）、error 0 |
| `Tests.Gen4.KWalkDepthCheck`（`topEntry_K` の Check。K walk の全依存を含む） | exit 0（761 jobs）、error 0。出力は変更前と同じ: `TYPE 8/8 / MUTANT 7/7 / AXIOMS 26/26 / CLOSURE 26/26`、`topEntry_K` の型の仮説は 3 つ（LogMvK, LegacyImplK, LegacyArmD） |

候補版の `MemoFamily.lean` と、それを使った Check は **本ブランチにはコミットしていない**（本体に文を足すのは freeze の承認の後）。差し替え後に `Tests.Gen4.MemoFamilyCheck`（rev2 の TYPE 12/12）は通らない（期待どおり。rev3 の実装単位で更新する）。この build は clean build ではない（キャッシュあり。最終受理は coder の clean build）。

## R7. 台帳（R-1）

| 項目 | 内容 |
|---|---|
| 案 ID | `M4.MEMO-01`（rev2 から変更なし。FG 側 1 行。T1 側へは数えない） |
| 1 行 | `MemoFamily`（15 文）を 1 行。`Laws`（A.P-01 = T1L-01）とは別行。R-1 は維持 |
| rev3 の承認 | FG ±0（文が 12 → 15 に増えるが 1 行のまま。R-3 / R-10 の文数換算は採らない） |
| FG +1 のタイミング | **家族を使う証明が受入された時点**（K walk 全体の受入。91 → 92）。ただし K walk には `MsgMvK` と `LegacyArmD` が残るので、これらが閉じるか別の判断が出るまで全体の受入にはならない |
| 消えうる行 | B.P-8 −1、B.P-1 −1（parametric の残りが全部揃った場合だけ。90） |
| T1 | 家族の文が T1 の件数に数えられるかは reviewer / ユーザーが決める（KWALK_DIAG_DECISION.md §3）。今は T1 57 のまま |
| quiet C | D.E-12 の `hno` 単独では減らず ±0（M4_CONSULT） |

`台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）`
`条件付き台帳: M4.MEMO-01 +1（家族を使う証明の受入時）/ B.P-8 -1 / B.P-1 -1（全項目揃った場合のみ）`

## R8. 限界（やっていないこと・主張しないこと）

- 15 文のどれも、実行系について真であるとは主張しない（`logProf` / `stderrLine` / `printersMv` は仮定。`Laws` との無矛盾性は D.E-10 で OPEN のまま）。vacuous model は型の充足可能性だけ。
- `printersMv` の真偽は、環境に登録された印字関数（delaborator を含む）の実装に依る。Sparkle の compile 環境で全ての登録 delaborator が memo を書かないことを、この調査では確かめていない（確かめる手段も見つかっていない）。
- `MsgMvK`（6605）は閉じていない。K walk は `LegacyImplK` を歩く段階で `MsgMvK` に依存する（歩いていない）。
- `stderrLine` と `logProf` が実際の K walk の項（CompilerM の bind、`TripleC`）にそのまま当てはまるかは、`LegacyImplK` を歩く段階で確認する（`Keeps` / `TripleC` への融合は未確認）。
- `lamTelescopeT` の転送前提（3 つ）は、`lambdaTelescope` の telescope 自身の副作用が `cv`/`sv`/`dv`/`mv`/quiet の保存だけだという仮定を含む。実行系との一致は読み（`Lean/Meta/Basic.lean:1598-1606`）だけで、証明ではない。
- 本単位は `MemoFamily.lean` 本体・`Elab.lean`・shared 定義を編集していない。worktree の実験はコミットしていない。clean build は coder が実行する。

## R9. 再現手順（reviewer 用）と次

1. `git show <本コミット>:Tests/Gen4/MemoFamilyRev3Check.lean` を読み、`kjob lake build Tests.Gen4.MemoFamilyRev3Check`。
2. §R6 の再現: 作業ツリーのコピーで `Tools/Assume/MemoFamily.lean` を §2 の構造 + 導出定理に差し替え（`import Tools.ShippingChildKeeps` を追加）、`Tools.ShippingGen4KWalk` / `Tools.ShippingGen4KWalkLegacyTail` / `Tests.Gen4.KWalkDepthCheck` を build。
3. 承認後の実装単位（別）: `MemoFamily.lean` の差し替え、`Tests/Gen4/MemoFamilyCheck.lean` の更新（TYPE 12 → 15、mutant、vacuous model）、`hleg`（窓 A）、`LegacyImplK` の K 版。

---

# 以下: rev2 から引き継ぐ本体

以降は rev2 の本文。**変更した箇所は「(rev3)」と明記**。`modify` 関連（§1）と `FramedNM` / `SideRefNM`（§2 の生成物）は変更なし。

## 1. `modify` の実行側と論理側（reviewer 指摘の中心）

### 1.1 `ST.Ref.modify` の論理定義と実装（toolchain、read）

toolchain `leanprover/lean4:v4.32.1`、`src/lean/Init/System/ST.lean`:
- 186-196: `@[extern "lean_st_mk_ref"] opaque mkRef`、`@[extern "lean_st_ref_get"] opaque Ref.get`、`@[extern "lean_st_ref_set"] opaque Ref.set`、`@[extern "lean_st_ref_swap"] opaque Ref.swap`、`@[extern "lean_st_ref_take"] unsafe opaque Ref.take`（195）、`@[extern "lean_st_ref_ptr_eq"] opaque Ref.ptrEq`。論理側では `get` / `set` / `take` はいずれも opaque。
- 199-201: `@[inline] unsafe def Ref.modifyUnsafe … := do let v ← Ref.take r; Ref.set r (f v)`。
- 209-213: `@[implemented_by Ref.modifyUnsafe] def Ref.modify … := do let v ← Ref.get r; Ref.set r (f v)` — **論理（証明）側の定義は `get; set`、コンパイル後の実行は `modifyUnsafe` = `take; set`**。`modifyGet` も同様（203-207 / 214-219）。

### 1.2 論理側で出ること（rev1 の導出、事実として残す）

`Tools/ShippingChildBndCore.lean:54` の `modify_split`（build 済み）は `RunsTo (modify r f) w u w' → ∃ w1, RunsTo (get r) w (readOf r w) w1 ∧ RunsTo (set r (f (readOf r w))) w1 u w'` を与える。これと既存 `Laws.O.frameQ` と `memoSet` から `memoModify` の結論が出る（rev1 の scratch `memoModify_of_get_set`、312 jobs exit 0）。**この導出は `RunsTo` が論理側の定義 `get; set` として読まれる場合の話である。**

### 1.3 選択肢 (A) を採らない理由（この調査では示せなかった）

(A) は「`RunsTo` と実際の実行の対応を示し、`modifyUnsafe`（`take; set`）も家族の law に覆われる」ことを要求する。確認できたこと:
- `RunsTo`（`Tools/ShippingChildInv.lean`）は `ST.Ref.modify` を `modify_split` が使う論理側の定義（`@[implemented_by]` の付いた定義本体）で展開する。`implemented_by` は論理側の項には現れない。したがって **`RunsTo` は論理側の意味で読まれ、`modifyUnsafe`（`take; set`）の実行を直接には表さない**（read）。
- `Ref.take` は `@[extern "lean_st_ref_take"] unsafe opaque` で、`get` との同値を与える定理も、既存の承認済み仮定も、この調査では見つからなかった。C 実装 `lean_st_ref_take` は toolchain に同梱されておらず、読んでいない。
- 以上から、`modifyUnsafe` が law に覆われることを、証明でも既存仮定への帰着でも示せなかった。指示どおり (B) にする。これは (A) が不可能という主張ではない。

### 1.4 (B): compiler が memo / child cache / depth を modify で更新する箇所（`Sparkle/Compiler/Elab.lean`、数えた）

| cell | modify 箇所 | 数 | 家族の文 |
|---|---|---|---|
| `sparkleSubModuleCache`（memo） | 5297, 5304, 5323, 5388（いずれも `.modify (·.insert declName result)`） | 4 | `memoModify` |
| `sparkleChildCache` | 8932（`.modify (·.insert n r)`） | 1 | `frameCacheModify` |
| `sparkleSynthDepth` | 5577（`.modify (· - 1)`、`finally` 内） | 1 | `frameDepthModify` |
| 計 | | 6 | |

`Sparkle/` 全体を、3 つの cell 名と `modify|modifyGet|take|swap` の同一行共起で grep し、`Elab.lean` 以外に該当は無かった（この調査では見つからなかった。複数行にまたがる記述は grep していない）。

get/set だけを使う cell には modify の文を足していない: `sparkleSubModuleCache` の get（5335）と set（5540）、`sparkleChildCache` の get（8930）と set（5541）、`sparkleSynthDepth` の get（5464）と set（5561）。これらは `memoGet` / `memoSet` / `frameCacheSet` / `frameDepthSet`（child cache・depth の get は `FramedNM` の `cacheGet` / `depthGet`）で覆う。その他の cell の modify は `FramedNM` の `sideModify` 系 constructor が覆う（rev1 から変更なし）。

## 2. 家族の完全な Lean 型 (rev3)

置き場所（予定）: `Tools/Assume/MemoFamily.lean`（既存。rev3 で差し替え。`import Tools.ShippingChildKeeps` を追加。`lean_lib «Tools.Assume.MemoFamily»` は既存）。`import Tools.ShippingChildFresh`（`MkRefd`）と `import Tools.ShippingChildBndCore`（`cv sv dv`、`modify_split`）。名前空間 `Tools.Assume.MemoFamily`。**変えないもの**: `Laws`（`Tools/ShippingGen2Defs.lean:46`）、`RefLawsAOps` / `RefLawsATele` / `FramedA` / `SideRef`（`Tools/ShippingChildInvA.lean` / `ShippingChildInv.lean`）、`RefLawsM`（`Tools/ShippingMemoLaws.lean`、使わない）、T1Hyp / T1HypND / Elab*.lean。

(rev3) 下のブロックのうち `mv` / `SideRefNM` / `FramedNM` は rev2 と同一（承認済み、`Tools/Assume/MemoFamily.lean` の既存部分）。**`MvInert` / `OkEnvMv`、`MemoTele`（`lamTelescope` → `lamTelescopeT`）、`MemoFamily`（`logProf` / `stderrLine` / `printersMv` を追加）、導出定理 `MemoTele.lamTelescope` が rev3 の差分。** `MemoTele` / `MemoFamily` の全文は scratch の `Tests/Gen4/MemoFamilyRev3Check.lean`（`MemoTeleR3` / `MemoFamilyR3`）と同一（名前だけ違う）で、elaborated（§R5）:

```lean
def mv (w : Void IO.RealWorld) : Std.HashMap Name Res := readOf sparkleSubModuleCache w

-- GENERATED
inductive SideRefNM : {σ : Type} → IO.Ref σ → Prop
  | wireWidth : SideRefNM sparkleWireWidthCache
  | fvarValue : SideRefNM sparkleFvarValueMap
  | letWire : SideRefNM sparkleLetWireCache
  | loopWire : SideRefNM sparkleLoopWireCache
  | wireCanon : SideRefNM sparkleWireCanon
  | subInstOut : SideRefNM sparkleSubInstanceOutputs
  | singleOut : SideRefNM sparkleSingleOutInstanceCache
  | typeCache : SideRefNM sparkleTypeCache
  | typeHits : SideRefNM sparkleTypeCacheHits
  | typeMiss : SideRefNM sparkleTypeCacheMiss
  | callCounter : SideRefNM sparkleCallCounter
  | cacheHits : SideRefNM sparkleCacheHits
  | hwInferCalls : SideRefNM sparkleHWInferCalls
  | hwInferMs : SideRefNM sparkleHWInferMs
  | fvarZetaVisited : SideRefNM sparkleFvarZetaVisited
  | whnfCalls : SideRefNM sparkleWhnfCalls
  | inferCalls : SideRefNM sparkleInferCalls
  | unfoldDefCalls : SideRefNM sparkleUnfoldDefCalls
  | whnfMs : SideRefNM sparkleWhnfMs
  | inferMs : SideRefNM sparkleInferMs
  | unfoldDefMs : SideRefNM sparkleUnfoldDefMs
  | handlerCalls : SideRefNM sparkleHandlerCalls
  | handlerMs : SideRefNM sparkleHandlerMs

inductive FramedNM (Fresh : (σ : Type) → IO.Ref σ → Prop) : {α : Type} → MetaM α → Prop
  | cacheGet : FramedNM Fresh (sparkleChildCache.get : MetaM _)
  | synthGet : FramedNM Fresh (sparkleChildSynth.get : MetaM _)
  | depthGet : FramedNM Fresh (ST.Ref.get sparkleSynthDepth : MetaM Nat)
  | sideGet {σ : Type} {r : IO.Ref σ} : SideRefNM r → FramedNM Fresh (ST.Ref.get r : MetaM σ)
  | sideSet {σ : Type} {r : IO.Ref σ} (v : σ) : SideRefNM r →
      FramedNM Fresh (ST.Ref.set r v : MetaM Unit)
  | sideModify {σ : Type} {r : IO.Ref σ} (f : σ → σ) : SideRefNM r →
      FramedNM Fresh (ST.Ref.modify r f : MetaM Unit)
  | sideModifyGet {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) : SideRefNM r →
      FramedNM Fresh (ST.Ref.modifyGet r f : MetaM β)
  | sideModifyGetIO {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) : SideRefNM r →
      FramedNM Fresh (liftM (ST.Ref.modifyGet r f : IO β) : MetaM β)
  | sideGetIO {σ : Type} {r : IO.Ref σ} : SideRefNM r →
      FramedNM Fresh (liftM (ST.Ref.get r : IO σ) : MetaM σ)
  | sideSetIO {σ : Type} {r : IO.Ref σ} (v : σ) : SideRefNM r →
      FramedNM Fresh (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit)
  | sideModifyIO {σ : Type} {r : IO.Ref σ} (f : σ → σ) : SideRefNM r →
      FramedNM Fresh (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit)
  | ioEnv (n : String) : FramedNM Fresh (liftM (IO.getEnv n) : MetaM _)
  | constInfo (n : Name) : FramedNM Fresh (getConstInfo n : MetaM _)
  | env : FramedNM Fresh (getEnv : MetaM Environment)
  | fvarThrowUnknown {α : Type} (id : FVarId) :
      FramedNM Fresh (liftM (id.throwUnknown : CoreM α) : MetaM α)
  | whnf (e : Lean.Expr) : FramedNM Fresh (Lean.Meta.whnf e)
  | inferType (e : Lean.Expr) : FramedNM Fresh (Lean.Meta.inferType e)
  | isClass? (e : Lean.Expr) : FramedNM Fresh (Lean.Meta.isClass? e)
  | whnfUntil (e : Lean.Expr) (n : Name) : FramedNM Fresh (Lean.Meta.whnfUntil e n)
  | instantiateForall (e : Lean.Expr) (ps : Array Lean.Expr) :
      FramedNM Fresh (Lean.Meta.instantiateForall e ps)
  | mkLambdaFVars (xs : Array Lean.Expr) (e : Lean.Expr) (usedOnly usedLetOnly etaReduce
      generalizeNondepLet : Bool) (bi : BinderInfo) :
      FramedNM Fresh (Lean.Meta.mkLambdaFVars xs e usedOnly usedLetOnly etaReduce generalizeNondepLet bi)
  | mkAppM (c : Name) (xs : Array Lean.Expr) : FramedNM Fresh (Lean.Meta.mkAppM c xs)
  | unfoldDefinition? (e : Lean.Expr) : FramedNM Fresh (Lean.Meta.unfoldDefinition? e)
  | reduce (e : Lean.Expr) (explicitOnly skipTypes skipProofs : Bool) :
      FramedNM Fresh (Lean.Meta.reduce e explicitOnly skipTypes skipProofs)
  | metaGet : FramedNM Fresh (get : MetaM Meta.State)
  | coreModifyTrace (f : TraceState → TraceState) :
      FramedNM Fresh (liftM (modifyTraceState f : CoreM Unit) : MetaM Unit)
  | metaModify (f : Meta.State → Meta.State) : FramedNM Fresh (modify f : MetaM Unit)
  | freshFVar : FramedNM Fresh (mkFreshFVarId : MetaM FVarId)
  | monoMs : FramedNM Fresh (liftM IO.monoMsNow : MetaM Nat)
  | mkExprCache (v : Lean.ExprStructMap String) :
      FramedNM Fresh (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
  | exprCacheGet (r : IO.Ref (Lean.ExprStructMap String)) : Fresh _ r →
      FramedNM Fresh (ST.Ref.get r : MetaM (Lean.ExprStructMap String))
  | exprCacheGetIO (r : IO.Ref (Lean.ExprStructMap String)) : Fresh _ r →
      FramedNM Fresh (liftM (ST.Ref.get r : IO (Lean.ExprStructMap String)) : MetaM _)
  | localMk {σ : Type} (v : σ) : LocalRefType σ →
      FramedNM Fresh (liftM (IO.mkRef v) : MetaM (IO.Ref σ))
  | localGet {σ : Type} (r : IO.Ref σ) : LocalRefType σ → Fresh σ r →
      FramedNM Fresh (ST.Ref.get r : MetaM σ)
  | localSet {σ : Type} (r : IO.Ref σ) (v : σ) : LocalRefType σ → Fresh σ r →
      FramedNM Fresh (ST.Ref.set r v : MetaM Unit)
  | localModify {σ : Type} (r : IO.Ref σ) (f : σ → σ) : LocalRefType σ → Fresh σ r →
      FramedNM Fresh (ST.Ref.modify r f : MetaM Unit)
  | localGetIO {σ : Type} (r : IO.Ref σ) : LocalRefType σ → Fresh σ r →
      FramedNM Fresh (liftM (ST.Ref.get r : IO σ) : MetaM σ)
  | localSetIO {σ : Type} (r : IO.Ref σ) (v : σ) : LocalRefType σ → Fresh σ r →
      FramedNM Fresh (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit)
  | localModifyIO {σ : Type} (r : IO.Ref σ) (f : σ → σ) : LocalRefType σ → Fresh σ r →
      FramedNM Fresh (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit)
  | exprCacheModify (r : IO.Ref (Lean.ExprStructMap String))
      (f : Lean.ExprStructMap String → Lean.ExprStructMap String) : Fresh _ r →
      FramedNM Fresh (ST.Ref.modify r f : MetaM Unit)

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- A `BaseIO` action leaves what the memo cell reads (from every world). -/
def MvInert {α : Type} (x : BaseIO α) : Prop :=
  ∀ w, match x w with
    | .mk _ w' => readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w

/-- The memo version of `OkEnv`: the two printer entry points over this environment leave the memo as it was. -/
def OkEnvMv (env : Environment) : Prop :=
  ∀ ctx : PPContext, ctx.env = env →
    (∀ e : Lean.Expr, MvInert (ppExprWithInfos ctx e)) ∧ (∀ n : Name, MvInert (ppConstNameWithInfos ctx n))


structure MemoTele (O : RefLawsAOps MkRefd mref cref) : Prop where
  telescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
  lamTelescopeT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (P : Void IO.RealWorld → Prop) (Q : α → Void IO.RealWorld → Prop) (R : Void IO.RealWorld → Prop),
    AdmCtx O.quiet mctx cctx →
    (∀ w, P w → O.quiet w) → (∀ a w, Q a w → O.quiet w) → (∀ w, R w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      P w → P w') →
    (∀ a w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      Q a w → Q a w') →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      R w → R w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Triple mctx' mref cctx' cref P (k xs b) Q (fun ex w => R w ∧ OkExc ex)) →
    Triple mctx mref cctx cref P (Lean.Meta.lambdaTelescope e k cleanup) Q (fun ex w => R w ∧ OkExc ex)
  localDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
  letDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)

structure MemoFamily (O : RefLawsAOps MkRefd mref cref) : Prop where
  frame : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {α : Type} (p : MetaM α), FramedNM MkRefd p → ∀ w, O.quiet w →
    mv (endW mctx mref cctx cref p w) = mv w
  frameCacheSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = mv w
  frameDepthSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = mv w
  memoGet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ m w w',
    RunsTo (sparkleSubModuleCache.get : MetaM _) mctx mref cctx cref w m w' → O.quiet w → mv w' = mv w
  memoSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleSubModuleCache.set v : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = v
  memoModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleSubModuleCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    mv w' = f (mv w)
  frameCacheModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Std.HashMap Name Res → Std.HashMap Name Res) w u w',
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w → mv w' = mv w
  frameDepthModify : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (f : Nat → Nat) w u w',
    RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w' → O.quiet w →
    mv w' = mv w
  logProf : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (b : Bool) (msg : String) w, O.quiet w →
    mv (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) = mv w
  stderrLine : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ (s : String) w, O.quiet w →
    mv (endW mctx mref cctx cref ((liftM (IO.eprintln s) : MetaM Unit) >>= fun _ =>
      (liftM Sparkle.Compiler.flushStderr : MetaM Unit)) w) = mv w
  printersMv : ∀ w, O.quiet w → OkEnvMv (readOf cref w).env
  tele : MemoTele O


variable {O : RefLawsAOps MkRefd mref cref}

/-- Same statement as the rev2 field `MemoTele.lamTelescope`; derived from the Triple form (`Q = fun _ => I`, `R = I`). -/
theorem MemoTele.lamTelescope (T : MemoTele O) : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup) := by
  intro mctx cctx α I hA hIq htr e k cleanup hk
  exact keeps_iff.mpr (T.lamTelescopeT I (fun _ => I) I hA hIq (fun _ => hIq) hIq htr (fun _ => htr) htr e k cleanup
    (fun mctx' cctx' xs b hA' => keeps_iff.mp (hk mctx' cctx' xs b hA')))
```

(rev3) leaf 数（文の数）: `frame` / `frameCacheSet` / `frameDepthSet` / `memoGet` / `memoSet` / `memoModify` / `frameCacheModify` / `frameDepthModify` の 8 + `logProf` / `stderrLine` / `printersMv` の 3 + `MemoTele` の 4（`telescope` / `lamTelescopeT` / `localDecl` / `letDecl`）= **15**（数えた）。rev2 は 12。`lamTelescopeT` は rev2 の `lamTelescope` の置き換えで、旧文は導出定理 `MemoTele.lamTelescope`（同名・同型）として残る。modify の 3 文の `RunsTo` は `ST.Ref.modify`（論理定義 `get; set`）の項で書かれ、`modifyUnsafe` で実行されることは `RunsTo` の定義には現れない（§1.3）。したがって 3 文は実行系についての仮定である。

`SideRefNM` は `SideRef`（`Tools/ShippingChildInv.lean:60-84`）から `subModule` 1 つを除いた 23 constructor（数えた）。`FramedNM` は `FramedA`（`Tools/ShippingChildInvA.lean:139-203`、40 constructor を数えた）の機械的複製で、7 つの side-ref constructor の `SideRef r` を `SideRefNM r` に置換しただけ（生成手順は §8）。

### 2.1 各文の一文説明と、どの振る舞いについての仮定か

| 文 | 一文の説明（前提知識なし） | 仮定の対象（関数名・ソース行） |
|---|---|---|
| `frame` | メモ表（`sparkleSubModuleCache`）以外のセルを読み書きする、またはセルに触れない通常の操作を 1 回実行しても、メモ表の中身は変わらない（quiet な世界・許される文脈のとき）。 | 23 個の副セルへの `set`/`get`/`modify`、`getConstInfo` / `getEnv` / `whnf` 等の Meta 操作（`FramedNM` の 40 constructor）。runtime: `lean_st_ref_set` / `lean_st_ref_get`（`include/lean/lean.h:2992-2993` で宣言を read。実装 C++ は toolchain に同梱されていないため read していない）が **別のセルを書いても当該セルを変えない**こと、かつ `initialize … ← IO.mkRef` が別セルを割り当てること（旧 `RefLawsM.distinct` に相当、Lean の論理では証明不能）。 |
| `frameCacheSet` | 子キャッシュ（`sparkleChildCache`）に `set` しても、メモ表は変わらない。 | `Sparkle/Compiler/Elab.lean:5541`（`sparkleChildCache.set {}`）。 |
| `frameDepthSet` | 再帰深さカウンタ（`sparkleSynthDepth`）に `set` しても、メモ表は変わらない。 | `Elab.lean:5561`（`sparkleSynthDepth.set (depth + 1)`）。 |
| `memoGet` | メモ表を読んでも、メモ表は変わらない。 | `Elab.lean:5335`（`let memo ← sparkleSubModuleCache.get`）。 |
| `memoSet` | メモ表を `v` に `set` したあと、メモ表は `v` である。 | `Elab.lean:5540`（`sparkleSubModuleCache.set {}`）。 |
| `memoModify` | メモ表を `f` で `modify` したあと、メモ表は元のメモ表に `f` を適用したものである。 | `Elab.lean:5297, 5304, 5323, 5388`（`.modify (·.insert declName result)`）。実行時は `Ref.modifyUnsafe`（`take; set`、`ST.lean:199-201`）。論理の `get; set` 経由の導出は §1.2 だが、家族の文として残す（§1.3）。 |
| `frameCacheModify` | 子キャッシュに `modify` しても、メモ表は変わらない。 | `Elab.lean:8932`（`sparkleChildCache.modify (·.insert n r)`）。実行時は `take; set`。 |
| `frameDepthModify` | 再帰深さカウンタに `modify` しても、メモ表は変わらない。 | `Elab.lean:5577`（`sparkleSynthDepth.modify (· - 1)`）。実行時は `take; set`。 |
| `logProf` (rev3) | profile logger（`profLogIO b msg`: eprintln → flushStderr → `Handle.mk "/tmp/sparkle-profile.log" .append` → putStrLn → flush）を 1 回走らせても、メモ表は変わらない（quiet・許される文脈）。 | `Elab.lean:5436-5442`、`6973-6977`（5 連の lift、`profBlock_eq`）。任意の path・mode・Handle は含まない。 |
| `stderrLine` (rev3) | 標準エラーに 1 行書いてフラッシュしても、メモ表は変わらない。 | `Elab.lean:6423-6425`。インストールされた stderr が memo を書かないという仮定。 |
| `printersMv` (rev3) | quiet な世界の環境の印字関数（`ppExprWithInfos` / `ppConstNameWithInfos`、任意の印字文脈・任意の世界から）はメモ表を変えない。`OkEnv` の memo 版。 | `Elab.lean:681, 686, 715, 5709, 7025, 7366` の `ppExpr`（`PpMvK` を導出、§R2.5）。 |
| `tele`（`MemoTele` の 4 文: `telescope` / `lamTelescopeT` / `localDecl` / `letDecl`） (rev3: `lamTelescope` を Triple 形に置換) | 束縛を開いて続きを実行し閉じる Meta の 4 つの補助関数（`forallTelescopeReducing` / `lambdaTelescope` / `withLocalDeclD` / `withLetDecl`）は、続きが不変量を保つなら（`lambdaTelescope` は: 続きが `P` から返れば `Q`、投げれば `R ∧ OkExc` なら）、子キャッシュ・synth・depth に加えてメモ表も変えない限り同じ事後条件を保つ。 | Lean core の `Lean.Meta.forallTelescopeReducing` 等（`RefLawsATele`、T1L-01 の `Laws.T` と同じ種類の仮定に `mv w' = mv w` の条件を足したもの）。呼び出し側は `Elab.lean` の translator が使うこれらの補助関数。 |

`frame` の「許される文脈」は `AdmCtx O.quiet mctx cctx`（コールバックが inert）、「quiet な世界」は `O.quiet w`。どちらも既存 `Laws.O` が使うのと同じ条件で、新しい条件は足していない。

### 2.2 `FramedNM`（`FramedA` の `subModule` 抜き）にする理由

`FramedA` には `sideSet`/`sideModify` 等が `SideRef`（メモ自身を含む）を通すので、`frame` を `FramedA` に対して言うとメモ自身の `set` に対し `mv w' = mv w` を主張してしまい `memoSet` と矛盾する。`FramedNM` はメモ自身の get/set/modify を除いた類。proposal §0.3 の通り、`¬ MemoOpA p` を項に付ける案は非メモ ref に対する異なる性の事実（distinctness）がないと cases が落ちたので採らない。

## 3. 消費者と、どの文を使うか

| 文 | (a) parametric の K 不変量 walk | (b) fallback の memo hit（F-9 / `outer_miss`） | (c) M3 G-MEMO（任意） |
|---|---|---|---|
| `frame` | 使う（translator の framed 構文すべて） | 使う（8 個の side set、`getConstInfo`、`getEnv`） | 使わない（現状） |
| `frameCacheSet` | 使う（リセット 5541） | 使う | 使わない |
| `frameDepthSet` | 使う（5561） | 使う | 使わない |
| `memoGet` | 使う（読み取り 5335） | 使う | 使わない |
| `memoSet` | 使う（リセット 5540） | 使う（リセット） | 使わない |
| `memoModify` | 使う（書き込み 5297, 5304, 5323, 5388） | 使う（memo への挿入） | 使わない |
| `frameCacheModify` | 使う（挿入 8932） | 使う | 使わない |
| `frameDepthModify` | 使う（5577） | 使う | 使わない |
| `tele`（4 文） | 使う（4 つの結合子） | **使わない** | 使わない |
| `logProf` / `stderrLine` / `printersMv` (rev3) | 使う（`LegacyImplK` の K 版: logger、debug 出力、`ppExpr`。まだ歩いていない） | 使わない | 使わない |

- (a) は K 不変量（`memo keys ⊆ child-cache keys`、PARAM_MEMO_STUDY §3）の walk。K 自体と walk は **未証明**。
- (b) の `outer_miss` は現在 `RefLawsM`（無制限の context・world）の前提でしか存在しない（`Tools/ShippingLegacySemMemoWalk.lean`）。家族は `AdmCtx` / quiet に制限されるので、`outer_miss` をそのまま使うことはできず、再述が要る（Lean 作業、未着手）。
- (c) M3 は `T1Hyp.defines/closes` の dispatch 除外として G-MEMO を扱い、メモ法則を使っていない（`Tools/ShippingGen2T1.lean` header @par/gen3-induct、PROPOSAL §2.1 (c)）。任意の共有: M3 が K 枝の証明に切り替えたときだけ。その場合も家族の +1 は片方の台帳にだけ計上する。

使用が未証明の間は「消費者の表」は予定であって、証明済みを意味しない。FramedA → `FramedNM ∨ MemoAccess` の分類補題（`framedA_cases`）は未証明（PROPOSAL §2）。

## 4. TRUSTED 境界・law・保証への影響

- **新しい TRUSTED 境界は 1 つ**: `MemoFamily`（R-1 で 1 行）。ユーザー承認済み（M4_DECISION §7、案 C・R-1）。reviewer の本 freeze 承認が実装の条件。
- 既存の `Laws`・A.P-01・T1L-01・FG 文・FG（保証）の範囲は **変えない・縮めない**。GenWFを強化しない。
- `memoModify` は rev1 では定理としたが、rev2 では**家族の文に戻した**（§1.3）。10 文案（`memoModify` あり、`frameCacheModify` / `frameDepthModify` なし）に対し rev2 は 12 文（+2）。R-1 なので台帳は 1 行のまま。
- 家族を使う証明が受入されるまで、いかなるツリーの定理も `MemoFamily` を仮説として取らない。

## 5. mutant 案（signature / defeq での棄却。意味的反例ではない）

scratch の `fail_if_success exact (rfl : ∀ O, Stmt O = Mut O)` で、型が defeq でないことを確認した（4 件、exit 0）。**これは文の型が合わないことの検査で、変えた文が偽であるとか、実行系で破れるとかは何も言わない。** 対照として `SetStmt O = <フィールド文のコピー>` は `rfl` で通った。

| # | 変更 | 種類 | 結果 |
|---|---|---|---|
| M1 | `memoSet` の結論 `mv w' = v` を `mv w' = mv w` に（frame と同形に弱める/置換） | 結論の置換 | defeq でなく棄却 |
| M2 | `memoSet` から `O.quiet w →` を外す（強める） | 前提の除去 | 棄却 |
| M3 | `memoSet` から `AdmCtx O.quiet mctx cctx →` を外す（強める） | 前提の除去 | 棄却 |
| M4 | `frame` の `FramedNM` を `FramedA` にする（メモ自身の get/set を含める） | 類の拡大 | 棄却 |

rev2 で足した 3 文の mutant 案（**未実施**。実施済みとは書かない。実装段階の Check で行う。signature/defeq の棄却であって意味的反例ではない）:

| # | 変更 | 種類 |
|---|---|---|
| M5 | `memoModify` の結論 `mv w' = f (mv w)` を `mv w' = mv w` に | 結論の置換 |
| M6 | `frameCacheModify` / `frameDepthModify` の `O.quiet w →` を外す | 前提の除去 |
| M7 | `frameDepthModify` の `RunsTo (modify …)` を `RunsTo (set …)` にする | 操作の置換 |

(rev3) rev3 の新規・変更の 4 文の mutant（L1-L6, D1-D5）と、境界の外の Prop（OUTSIDE）は §R5。M5-M7 も rev2 の Check（`Tests/Gen4/MemoFamilyCheck.lean`）で実施済み。

mutant を作らなかった文: `frameCacheSet` / `frameDepthSet` / `memoGet` / `memoModify` / `frameCacheModify` / `frameDepthModify` / `tele`（同種の変更で棄却されるはずだが未実施。実施済みとは書かない）。

## 6. 台帳（R-1）

| 項目 | 内容 |
|---|---|
| 新 ID 案 | `M4.MEMO-01`（FG 側。T1 側へは数えない。T1L-25 は M3 が家族を採用しない限り不変） |
| 1 行 | `MemoFamily`（rev3 で 15 文、§R7）を 1 行。`Laws`（A.P-01 = T1L-01）とは別行 |
| FG +1 のタイミング | **家族を使う証明が受入された時点**（本 freeze の承認時点ではない） |
| 消えうる行 | B.P-8 −1、B.P-1 −1。F-θ / F-top / F-post / shape / assembly / F-kids が **全部揃った場合だけ**。F-kids 単独では 0 |
| 純差分（全部揃った場合） | +1 −2 = **−1**（条件付き） |
| 今回の台帳 | 台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0） |
| 条件付き台帳 | 条件付き台帳: M4.MEMO-01 +1（家族を使う証明の受入時）/ B.P-8 −1 / B.P-1 −1（全項目揃った場合のみ） |

文数で数える R-10 は +12、R-3 は +3 だが、ユーザー判断は R-1（1 家族 = 1 行）であり、rev2 でも 1 行のまま。R-3 / R-10 は採用しない。

## 7. 家族が矛盾しないことの確認方法

- **確認できたこと（elaborated、exit 0）**: `quiet = False`（`RefLawsAOps.quietFalse`、`Tools/ShippingChildInvA.lean:388`）の自明モデルで `MemoFamily` の 15 文がすべて充足する（rev3 の scratch `Tests.Gen4.MemoFamilyRev3Check`、756 jobs exit 0。rev2 は 12 文、312 jobs）（全 field が `quiet w` の前提を取るため）。`theorem vacuous_model`、`#print axioms` = propext / Classical.choice / Quot.sound、sorry なし。これは **文の型が空でない（型として充足可能）** ことの確認であって、実行系について何かを言う証拠ではない。
- **確認できていないこと**: `quiet` が非自明なモデル（`ST.Prim.Ref.get/set` の実モデル）での充足。Lean の論理では `@[extern]` の opaque で、この調査では供給元・経路が見つからなかった。`Laws` との同時充足は台帳 D.E-10 で OPEN のまま。
- 実行系との整合の確認は、`Elab.lean` の書き込み箇所の read（§2.1 の行番号）と、MemoHitCensus（`Tests/Compiler/MemoHitCensusTest.lean`、観測）に限られ、証明ではない。

```lean
/-! Vacuous model: at quiet = False every statement holds (a satisfiability of the TYPE, not evidence about the runtime). (rev3: 15 statements) -/
def vacO : RefLawsAOps MkRefd mref cref := RefLawsAOps.quietFalse MkRefd mref cref
theorem vacuous_model : MemoFamily (mref := mref) (cref := cref) vacO where
  frame := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  frameCacheSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameDepthSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  memoGet := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  memoSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  memoModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameCacheModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frameDepthModify := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  logProf := by intro _ _ _ _ _ _ hq; exact False.elim hq
  stderrLine := by intro _ _ _ _ _ hq; exact False.elim hq
  printersMv := by intro _ hq; exact False.elim hq
  tele :=
    { telescope := by intro _ _ _ I _ hIq _ _ _ _ w hw; exact False.elim (hIq w hw)
      lamTelescopeT := by intro _ _ _ P _ _ _ hPq _ _ _ _ _ _ _ _ _ w hw; exact False.elim (hPq w hw)
      localDecl := by intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
      letDecl := by intro _ _ _ I _ hIq _ _ _ _ _ _ w hw; exact False.elim (hIq w hw) }
```

## 8. 再現手順（reviewer 用、rev2。rev3 は §R9）

1. `git show par/memo-freeze:scripts/gen4/MEMO_FAMILY_PROPOSAL.md` で §2 の元の 10 文案を読む。
2. 本文書 §1.2・§2 の Lean 抜粋を `Tests/Gen4/` の一時ファイルに貼り、`kjob lake build` する（import は `Tools.ShippingChildFresh` と `Tools.ShippingChildBndCore`）。`SideRefNM` / `FramedNM` の生成: `Tools/ShippingChildInv.lean` の `inductive SideRef` から `| subModule` 行を除き `SideRef` → `SideRefNM`、`Tools/ShippingChildInvA.lean` の `inductive FramedA` を `FramedNM` に改名し `SideRef r` → `SideRefNM r` に置換（constructor 数 23 / 40 を数える）。
3. 実装段階の Check（別単位）: 型の defeq 検査（12 文）、mutant（M1-M7）の signature/defeq 棄却、axioms、constant closure に `Laws` / `T1Hyp` / `T1HypND` を含まないこと。

## 9. 限界（やっていないこと、rev2。rev3 の限界は §R8）

- K 不変量、`framedA_cases`、`MemoFamily` を使う定理は未証明。
- rev2 は `modify` の 3 文を家族に持つので、8932 / 5577 / memo の 4 箇所を `set` の文へ帰着する証明は要らない（その代わり仮定が 3 文多い）。
- 実行側 `Ref.modifyUnsafe`（`take; set`）と論理側の定義（`get; set`）の同値は、仮定にも証明にもしていない。`modify` の 3 文は `ST.Ref.modify` の `RunsTo` について直接述べる（§1.3）。これらが実行系について真であることは主張しない。
- modify の 3 文は (A)（対応の証明）を示せなかったために置いた文であり、将来 (A) が示せれば減らせる可能性がある（その場合は別 freeze）。
- 家族の真偽・実行系との一致・`Laws` との無矛盾性は主張しない（§7）。
- ledger の C_M5dg / D_M5t2 は全行再読していない（PROPOSAL §5 のまま）。
- 本 freeze の承認は TRUSTED 境界 `MemoFamily` の追加の承認を含む。承認までは Lean 実装・仮定としての使用に進まない。

`台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）`
`条件付き台帳: M4.MEMO-01 +1（家族を使う証明の受入時）/ B.P-8 -1 / B.P-1 -1（全項目揃った場合のみ）`
