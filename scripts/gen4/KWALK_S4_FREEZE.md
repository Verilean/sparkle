# KWALK_S4_FREEZE: 入口の腕（certified / mixed / machine / legacy）と窓の開閉の K 版 — 型の freeze

Status: freeze（前提を増やさない単位。review に出さない。共通ルール 14）。base 91082086（kjob/rt167）、作業 kjob/rt169。
台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。新しい law・家族の文・TRUSTED 境界は無い。LegacyImplK / ChildEntryK / MemoFamily は仮説のまま。
「読んだ」= 私の読み、「数えた」= grep の出力。

## 1. Diag の数え（入口側、Elab.lean 5288-5606 と呼び出される emitLeaves）

* 入口側で Diag になるのは `logProf`（`profLogIO b`、Elab.lean:5436-5442 の `IO.eprintln` + `flushStderr` + `IO.FS.Handle.mk` + `putStrLn` + `flush` を 1 つの `IO Unit` にしたもの）の**呼び出し**だけ（`Diag.profLog`）。`ppExpr` は 5288-5606 に 0 件（5709 は翻訳器の範囲で S3 で数え済み）。`IO.eprintln` は 5438 の 1 件（logProf の本体）。
* logProf の呼び出し箇所（数えた）: `synthesizeFromConst` 内 5295, 5302, 5322（腕ごとに 1 回）、5337（memo hit）、5339, 5342, 5344, 5351, 5360, 5376（legacy 腕）。`synthesizeCertified`/`Mixed` は logProf を `emitLeaves` に渡すだけで直接は呼ばない。`emitLeaves`（Elab.lean:2165, 2173）が leaf ごとに 2 回呼ぶ。`synthesizeCombinationalCoreWith` の 5443（entering）。
* したがって **certified / mixed / machine / legacy の 4 つの腕は全て Diag（profLog）を通る**。LegacyImplK と同じ判断待ち（KWALK_DIAG_DECISION.md）の対象。
* 扱い: 仮説 `LogMvK O`（下）を 1 つ取る。内容は「`profLogIO b msg` を 1 回走らせても `mv` は変わらない」で、判断資料の選択肢 A の `frameDiag` のうち `profLog` の場合だけ。`def` の仮説で、家族には足さない。選択肢 A が承認されれば `LogMvK` は家族から導かれる。承認されなければ S4 の定理は `LogMvK` を仮定した条件付きのまま。

## 2. 型（`Tools/ShippingGen4KWalkEntry.lean`、NOT BUILT）

```lean
/-- DIAG-PENDING hypothesis: one run of the profile logger leaves the memo as it was. -/
def LogMvK (O : RefLawsAOps MkRefd mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ b msg w, O.quiet w →
    mv (endW mctx mref cctx cref (liftM (profLogIO b msg) : MetaM Unit) w) = mv w

theorem keepsK_profLog (M) (hA) (hS : StableK O.quiet I) (hlog : LogMvK O) b msg :
    Keeps mctx mref cctx cref I (liftM (profLogIO b msg) : MetaM Unit)

-- K 版の部品（A 版 PathA / FrontA の写し、Diag は keepsK_profLog、FramedA は keepsK_framedNM）
bindInputPortK, bindCertifiedInputsK, bindMixedCertifiedInputsK, emitLeavesK, finishSynthK
certified_keepsK, mixed_keepsK, closeInstsM_keepsK, closeInstsGM_keepsK, machineCert_keepsK  -- hchild : ChildEntryK 相当（synthesizeChild でなく childSynthEntry 経由は不要: closeInsts* は sparkleChildSynth.get → synth c）

-- 窓の開閉
triple_memoInsert (M) (hA) n r : Triple (KWalk O) (memo.modify (·.insert n r)) (fun _ => KWalkX O n) (fun e w => KWalk O w ∧ OkExc e)
fromConst_certified_window / _mixed_window / _machine_window :
    Triple (KWalk O) (synthesizeFromConst translate (profLogIO b) declName [] false true ci isInst)
           (fun _ => KWalkX O declName) (fun e w => KWalk O w ∧ OkExc e)
```
`hchild`（closeInsts の子の入口）は `Keeps (KWalk O) (synthesizeChild c)` を仮説に取る（A 版 FrontA と同じ形。`ChildEntryK` は `childSynthEntry` 版で別。S6 で `synthesizeChild` の帰納に接続）。
`htr`（翻訳器）は `KeepsC (KWalk O) (translate ..)`（S2/S3 の `translate_keepsK` が与える）。

## 3. mutant（signature/defeq での棄却。意味的反例ではない）
1. 窓: 結論の `KWalkX O declName` を `KWalk O` にした型 → 棄却（`triple_memoInsert` は K から K_n）。
2. 失敗側: `fun e w => KWalkX ..` にした型 → 棄却。
3. `LogMvK` の `mv .. = mv w` を `cv .. = cv w` にした型 → 棄却。

## 4. 追記（rt169、実装後。freeze の型は「前提を増やさない単位」の中で次のとおりに広がった。台帳の差分は 0 のまま）

* 仮説 `PpMvK O`（`ppExpr e` が `mv` を変えない、`Tools/ShippingGen4KWalkHelpers.lean`）を追加。`LogMvK` と同じ種類（Diag の判断待ち、選択肢 A の `frameDiag` が `ppExpr` も覆えば解ける）。helper 内の `ppExpr` ×3 は §1 の数えから漏れていた（`KWALK_LEGACY_WINDOW_DECISION.md` §5）。
* `htr`（翻訳器の仮説）は `KeepsC`（全文脈）でなく `KeepsCP`（`CtxOk` の文脈）の形（S3 の `RecK` から与えられる形）。`emitLeavesKP` / `bindCertifiedInputsKP` / `bindMixedCertifiedInputsKP` / `bindInputPortKP`。
* 追加した定理: helper 群（`extractWidthK` / `inferHWTypeK` / `extractDimExprK` / `inferHWTypeWithDimensionsK` / `inferHWTypeFromSignalK` / `isSignalBinderTypeK` / `withDimVarMappingP`）、legacy 腕の部品（`openRecordInputs_keepsK` / `splitReturnLeaves_keepsK` / `bindInputsLegacyKP`）、S5（`tryFinallySplit` / `fin_totalK` / `entryNested_windowK` / `entryTop_windowK`）、S6 の一部（`combWith_nestedK` / `synthesizeChild_windowK`）。型は Check（`Tests/Gen4/KWalkEntryCheck.lean`）の `Expected.*` に別に書いてある。
* 補助の tactic `kwalkM`（`Tools/ShippingGen4KWalkTac.lean`、`Tools/ShippingChildKWalk.lean` の `kwalk` の写しで `Keeps` の目標も歩く）。tactic であって law ではない（kernel が検査する証明項を作るだけ）。
* **新しい判断点**: `KWALK_LEGACY_WINDOW_DECISION.md`（legacy 腕の失敗側）。新しい文・law は足していない。
