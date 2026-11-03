# KWALK_PLAN: K 不変量の walk（K = memo の key は child cache の key）の計画と、共通の土台

Status: 計画 + 土台（Lean は新規ファイル `Tools/ShippingGen4KWalk.lean` / `Tests/Gen4/KWalkCheck.lean`）。base b3e27490（kjob/rt163）。
根拠: PARAM_MEMO_STUDY.md §3、PARAM_INV_ESTIMATE.md §3-4、MEMO_FAMILY_FREEZE.md rev2 §3（消費者の表）、`Sparkle/Compiler/Elab.lean`（行番号は base のもの）。
「数えた」= grep/wc の出力、「読んだ」= 私の読み（Lean では未確認）。

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**前提を増やしていない**: 土台は `MemoFamily`（承認済みの TRUSTED 境界）を仮説 `M` に取るだけで、
新しい law・TRUSTED 境界・axiom は無い。家族の +1 は、この walk の全体が受入されたときだけ。条件付き台帳: M4.MEMO-01 +1 / B.P-8 -1 / B.P-1 -1（F-θ / F-top / F-post / shape / assembly / F-kids が全部揃った場合のみ）。

## 0. 結果

* 土台を証明した（§1、`kjob lake build` 済み、axioms は標準のみ、sorry なし）: FramedNM な段が K を保つ一般補題、memo `get`、各 writer（memo `set`/`modify`、child cache `modify`）の文脈補題、
  K の「窓」（memo 書き込み〜child cache 挿入）の開閉補題、`bind`/`seq`/`ite`/`tryCatch` と 4 つの telescope 結合子。
* 残りは翻訳器の各段（§2 の表）。新しい前提や law が要る段は **この調査では見つからなかった**。ただし 2 点は Lean での証明が未完で、証明できなければ止まって coder に報告する（§4）。
* 見つけた事実で見積りに効くもの: 既存の A-walk（`StableA` を使う）は K に**そのままは使えない**。`StableA` は `cv/sv/dv` が同じなら不変量が移ることを要求するが、K は memo `mv` に依存する（§3）。

## 1. K の完全な Lean の型（`Tools/ShippingGen4KWalk.lean`、BUILT）

`mv w := readOf sparkleSubModuleCache w`（`Tools.Assume.MemoFamily.mv`）、`cv/sv/dv` は `Tools.ShippingChildBndCore`。

```lean
def MemoKeysInChild (m c : Std.HashMap Name Res) : Prop :=
  ∀ k, m.contains k = true → c.contains k = true                       -- K（key だけ。内容は問わない）
def MemoKeysExc (n : Name) (m c : Std.HashMap Name Res) : Prop :=
  ∀ k, m.contains k = true → c.contains k = true ∨ (n == k) = true     -- K_n（飛行中の名前 n を 1 つ許す）
def KW (O : RefLawsAOps MkRefd mref cref) (P : Mem → Mem → Prop) (w : Void IO.RealWorld) : Prop :=
  O.quiet w ∧ sv w = some synthesizeChild ∧ P (mv w) (cv w)
def KWalk  O w := KW O MemoKeysInChild w
def KWalkX O n w := KW O (MemoKeysExc n) w
```

`sv w = some synthesizeChild` を不変量に入れる理由: 深さ 1 以上の子の入口は `childSynthEntry`（Elab.lean:5620、`sparkleChildSynth.get` を読む）で、これが常に child cache を通る `synthesizeChild`（8929）であることを保証するため
（`Rec.synthesizeCombinational := childSynthEntry`、6332-6334 を読んだ）。`sv` は `FramedA` の `frame` で保存される。

証明済みの補題（全部 `#print axioms` で標準のみ）:

| 補題 | 内容 | 使う家族の文 |
|---|---|---|
| `keeps_KW_framedNM` | `FramedNM MkRefd p` の段は任意の `P` について `Keeps (KW O P) p`（全ての結果で） | `frame`（+ `Laws` でない `RefLawsAOps` の `frame/frameQ/excOk`） |
| `keeps_KW_memoGet` | memo `get` が `Keeps (KW O P)`（`refGet_runs` で投げないことを使う） | `memoGet` |
| `memoSet_ctx` / `memoModify_ctx` / `childModify_ctx` | writer 1 回の後の quiet / `cv` / `sv` / `mv` | `memoSet` / `memoModify` / `frameCacheModify`（+ `cacheModify'`, `cacheSetQ`） |
| `kwalk_memoReset` | memo を `{}` に `set` した世界で K（child cache は何でもよい） | `memoSet` |
| `kwalk_memoInsert` | K の世界で `memo.modify (·.insert n r)` → K_n | `memoModify` |
| `kwalk_childInsert` | K_n の世界で `child.modify (·.insert n r)` → K（窓を閉じる） | `frameCacheModify` |
| `kwalk_childMono` | key を減らさない child cache の `modify` は K を保つ | `frameCacheModify` |
| `keeps_KW_pure/bind/seq/ite/tryCatch` | 既存の `Keeps.*` の言い直し | なし |
| `keeps_KW_forallTelescopeReducing/lambdaTelescope/withLocalDeclD/withLetDecl` | 4 結合子 | `MemoTele`（4 文） |
| `framedNM_toA`, `framedA_of_memoAccess`, `framedA_ctx` | `FramedNM` / `MemoAccess` は `FramedA`、その quiet/`cv`/`sv`/例外の枠 | `RefLawsAOps` |

`Tests/Gen4/KWalkCheck.lean`: TYPE 7/7（上の主要補題の型が、`readOf` で別に書いた Expected と defeq）、MUTANT 3/3（signature/defeq での棄却。意味的反例ではない）、
AXIOMS 24/24 標準のみ、CLOSURE 24/24（`Laws` / `T1Hyp` / `T1HypND` が閉包に無い。陽性対照 2 件でこの検出器は T1Hyp / T1HypND を捕まえる）。

## 2. 「翻訳器の各段が K を保つ」補題の一覧（予定。証明済みなのは §1 のみ）

memo の使用箇所（`Elab.lean`、`grep` で数えた）: 読み取り 5335 / 書き込み 5297, 5304, 5323, 5388 / リセット 5540 / `initialize` 1024。**翻訳器（Rec ブロック 5702-8030、step/instance ブロック 8030-8960）には memo への直接アクセスが 0 件**。
したがって翻訳器側の段は全て `FramedNM`（`keeps_KW_framedNM`）と 4 結合子、および子の入口の呼び出しで、`MemoAccess` が現れるのは入口側（下の E 群）だけ。

| 段 | Elab.lean の行 | FramedNM / MemoAccess | 使う家族の文 | 備考 |
|---|---|---|---|---|
| T1 CompilerM 原始操作（`makeWire`/`addInput`/`addOutput`/`emitAssign`/`emitRegister`/`emitMemory`/`emitInstance`/`addModuleToDesign`/`freshName`/`lookupVar`/`bindSourceVariable`） | 170-305 | FramedNM（`wireWidth` 等の side ref、`freshFVar`） | `frame` | A 版は `Tools/ShippingChildTranslateA.lean` 242-340。K 版は `StableK` が要る（§3） |
| T2 翻訳キャッシュ（`cacheLookupValidated`/`recordTranslation`） | 8030 以降（read） | FramedNM（`exprCacheGet(IO)`/`exprCacheModify`/`localMk`） | `frame` | A 版 TranslateA 358/379 |
| T3 `translateSignalPureLiteral`/`CanonicalSignalBinary`/`Core`/`StepWith` と fuel 帰納 | 8030-8250（read）、fuel 8247-8873 | FramedNM + 再帰呼び出し | `frame` | A 版 TranslateA 399-512（`fuelFix_of` は I について一般なので再利用可） |
| T4 fallback と handler（Rec 17 def、step/instance 82 def） | 5702-8030 / 8030-8960（数えた） | FramedNM、`liftMetaM` 110 箇所、`try/catch` 19、`with*` 24（PARAM_INV_ESTIMATE §3.1） | `frame`, `MemoTele`（4 結合子） | A 版 FallbackA（616 行）/ WalkA（873 行）が同形 |
| T5 `withLocalDecl`/`withLetDecl`/telescope（14 箇所、`grep`） | 141, 150 ほか | 結合子 | `tele` | `keeps_KW_*` 済み。継続が `AdmCtx` を保つ側条件は A-walk と同じ |
| T6 子の入口の呼び出し（`childSynthEntry`、`closeInstsM/GM`） | 5620, 5206/5229, 6334, 8712, 8730 | 呼び出し（IH） | なし（IH） | IH = §3 の `EntryK`。`sv` の固定が要る |
| E1 `synthesizeChild` | 8929-8934 | `cacheGet`（FramedNM）、入口の呼び出し（IH）、`child.modify (·.insert n r)`（8932） | `frame`, `frameCacheModify` | `kwalk_childInsert` が窓を閉じる |
| E2 `synthesizeCombinationalCoreWith` の前置き | 5423-5535 | FramedNM（`ioEnv`、side ref の `get`）、`throwError` | `frame`, `excOk` | `Keeps.throwError` 相当は `OkExc` のみ |
| E3 深さ 0 のリセット | 5538-5551（memo 5540、child cache 5541） | **MemoAccess**（5540 `set {}`）、child cache `set {}`（5541）、side ref の `set` | `memoSet`, `frameCacheSet`, `frame` | `kwalk_memoReset`。5541 は `mv` が `{}` のまま `cv` を変えるだけなので K は保たれる（要 Lean: `frameCacheSet` + `cacheSet`/`cacheSetQ` で 3 行程度） |
| E4 深さの `set`/`modify` と `try/finally` | 5561, 5565-5584 | `ST.Ref.set/modify sparkleSynthDepth`、side ref の `set` | `frameDepthSet`, `frameDepthModify`, `frame` | `try … finally` の K 版（`Triple.tryFinally` は `ShippingChildKeeps.lean:128`、I について一般） |
| E5 `synthesizeFromConst` の 4 つの腕と memo 読み取り | 5290-5400（5297/5304/5323/5388 書き込み、5335 読み取り） | **MemoAccess**（`get` 5335、`modify` ×4） | `memoGet`, `memoModify` | 書き込みは各腕の最後の効果（read）。`kwalk_memoInsert` で K → K_n。`!symbolicMode` の下だけ |
| E6 `synthesizeCertified`/`Mixed`/`MachineCertified` と `closeInsts*` | 2934, 2959, 5252, 5206, 5229 | FramedNM + 子の入口（IH） | `frame` | 窓の外（memo 書き込みの前） |
| E7 窓の中の処理（`finally`、`synthesizeCombinationalWith` の純粋な後処理、`IO.getEnv`） | 5577-5584, 5594-5605 | FramedNM（side ref の `set`、`depth modify`、`ioEnv`） | `frame`, `frameDepthModify` | K_n を保つ（`keeps_KW_framedNM` は任意の `P`）。**窓の中で例外が出ない**ことが要る（§4 (a)、解決） |
| E8 入口の帰納（深さに関する） | 5465（深さ限度 1024、Elab.lean:970） | — | — | §3 |

## 3. 証明の順序と行数の見積り

`EntryK`（入口の文。**NOT BUILT、型の案**）: 深さの予算 `r` を取る帰納。
`EntryK O r := ∀ n mctx cctx, AdmCtx O.quiet mctx cctx → ∀ w, KWalk O w → (cv w).contains n = false → sparkleSynthDepthLimit ≤ dv w + r →
 (成功 → KWalkX O n w')（失敗 → KWalk (endW …)）`、すなわち「`synthesizeCombinational n` は child cache に無い名前では K_n を残し（memo の最後の書き込みで窓が開く）、失敗なら K のまま」。
`synthesizeChild` は `EntryK` から `kwalk_childInsert` で K に戻す。深さ 0 の入口は E3 で K から始まる。`EntryK 0` は深さ限度の `throwError`（5465）で空。

| 段階 | 内容 | 状態 | 行数（見積り。実測ではない） |
|---|---|---|---|
| S0 | §1 の土台 + Check | **完了（BUILT）** | 320 + 194（実測） |
| S1 | `StableK`（`cv/sv/dv/mv` が同じなら移る）と T1/T2 の K 版 | **完了（BUILT、rt165）** | 195 + 200 + Env 30（実測。見積り 200-300 に収まった） |
| S2 | T3: `translateStepWith`/`Core`/fuel、T5 の K 版（`translateK_of_fallback`） | **完了（BUILT、rt166、`Tools/ShippingGen4KWalkTranslate.lean`）** | 139 + Check 202（実測。見積り 150-250 に収まった。T5 の telescope 結合子は S0 の `keeps_KW_*` で済み、S2 の T5 相当は fuel 帰納） |
| S3 | T4: fallback と handler（A 版 FallbackA 616 + WalkA 873 に相当） | **部分完了（BUILT、rt167）**: FallbackA 相当（emit / rec 腕 / instance / telescope 腕 / canonHardwareKey / 15 腕の組立て）と LegacyCached。**未着手: `LegacyImplK`（`Rec.translateExprToWireImpl`、A 版 Helpers 171 + Handlers 179 + Impl 120 + Tail 223 と、それを歩く `vca`＝WalkA 873 の K 版）**。下の「S3 の結果」 | 実測 264 + 206 + 130 + 80 + 84 + 85 = 849 + Check 196（FallbackA 616 相当の部分。見積り 1000-1500 の残りは LegacyImplK） |
| S4 | E6/E5: 入口の腕（certified / mixed / machine / legacy）と窓の開閉 | **部分完了（BUILT、rt169）**: certified / mixed / machine の 3 腕と窓を開ける memo 書き込み（`Tools/ShippingGen4KWalkEntry.lean`、`EntryArms.lean`）、legacy 腕の部品（`Helpers.lean`: extractWidth / inferHWType / extractDimExpr / inferHWTypeWithDimensions / inferHWTypeFromSignal / isSignalBinderType、`LegacyTail.lean`: openRecordInputs / splitReturnLeaves / bindInputsLegacy）。**legacy 腕の全体は未証明（失敗側が K で終わることを `MemoTele` の既存 12 文から示せない。下の「legacy 腕で見つかった 2 点」）= 仮説 `hlegacy` のまま** | 実測 Entry 約 410 + Arms 約 190 + Helpers 約 150 + LegacyTail 約 150 + Tac 約 200（見積り 400-600 に対し腕と窓は収まった。legacy 腕は部品まで） |
| S5 | E2-E4/E7: 入口の前置き、リセット、深さ、`try/finally`、窓の中 | **完了（BUILT、rt169、`Tools/ShippingGen4KWalkEntryCore.lean`）**: 入れ子の入口 `entryNested_windowK`（depth ≠ 0）、最外の入口 `entryTop_windowK`（depth 0、リセット）。いずれも腕 `hbody`（legacy 腕は仮説 `hlegacy` のまま）と `LogMvK` の下 | 実測 約 390（見積り 300-400 に収まった） |
| S6 | E1/E8: `synthesizeChild`、深さ帰納、`memo_miss_of_child_miss` への接続 | **完了（BUILT、rt169 + rt170）**: 窓を閉じる部分（rt169、`Child.lean`）に加え、rt170 が `dv` つき不変量 `KWD O K D = KW O K ∧ dv = D` への一般化（`Depth.lean` / `DepthArms.lean` / `DepthEntry.lean`）と、`hchild` / `hbody` / `htr` を同時に閉じる深さ帰納（`DepthInduct.lean`、測度 `sparkleSynthDepthLimit - dv`）、`memo_miss_of_child_miss` への接続（補題 + `childMiss_memoMiss`）。下の「S6 深さ帰納の結果（rt170）」 | 実測 Depth 約 190 + DepthArms 約 180 + DepthEntry 約 170 + DepthInduct 約 150 + Check 約 240（見積り 200-300 を超えたが、腕の写しが大半） |
| 合計 | | | 約 2300-3400（PARAM_INV_ESTIMATE §3.4 の 3500-5000 より小さい見込みだが、同じく推定で実測ではない） |

順序: S1 → S2 → S3（S3 が最大。ここで `StableK` の穴が出るなら早く分かる）→ S4 → S5 → S6。S1 は新ファイル `Tools/ShippingGen4KWalkPrims.lean`、S3 は handler ごとに分ける（`maxHeartbeats` の引き上げが要る前例: `ParamEntry:215`）。
各ファイルの build は `kjob lake build` を 1 つずつ。120 分に収まらない build は coder に頼む。

**`StableA` が使えない件（見積りに効く）**: 既存 A-walk の原始操作（`makeWireA` など）は `hS : StableA O.quiet I`（`ShippingChildVCA.lean:46`）を取る。`StableA` の移送条件は `cv/sv/dv` だけで、K は `mv` に依存するので `StableA O.quiet (KW O P)` は一般に成り立たない（`mv` が違う世界を区別できない）。
共有定義は触れないので、K 版の `StableK`（移送条件に `mv w' = mv w` を足す。`keeps_KW_framedNM` の `kw_transfer` が同じ形）と、それを取る原始操作の写しを新ファイルに作る。補題の証明は A 版と同形で、`hS.2` の呼び出しに `frame` 由来の `mv` の等式を足すだけの見込み（読み。未試行）。

**S3 試験の結果（rt166）**: `Tools/ShippingChildKWalk.lean` の `kwalk [makeWirePK M hA hS, emitAssignP]` で、FallbackA の葉の emitter 3 つ（`emitBoolResult`/`emitSliceResult`/`emitMuxResult`）の K 版が通った（`kjob lake build` 326 jobs exit 0、`unfold` の後に `kwalk` 1 行）。
`kwalk` は `KeepsCP` について `I` に一般なので、`StableK` 版でもそのまま使える。試したのは葉 3 つだけで、`rec` を取る handler、`FramedNM` 以外の腕（`liftMetaM` を含むもの）、telescope を含むもの（`projFieldName?` 等）は試していない。S3 の 1000-1500 行の見積りは変えていない（推定）。

## S3 の結果（rt167、`scripts/gen4/KWALK_S3_FREEZE.md` の型で実装。全て `kjob lake build` 済み、sorry・axiom・native_decide なし、axioms は標準のみ）

* `Tools/ShippingGen4KWalkEmit.lean`（264）: 結果 emitter 7 つ、`translateConcatActsK`、rec を取る腕 20 個（FallbackA 96-325 の K 版）。`kwalk` は K 版でもそのまま動いた。**唯一の止まり**: `loopRegister` / `circuitDo` / `circuitDo2` の腕で `mkFreshFVarId` が `monadNameGeneratorLift ..` に unfold されて止まった（`kwalk` の `Keeps` 規則が `keepsA_framed O hA hS` 固定のため）。`kwalk` の規則に `keepsK_framedNM M hA hS (FramedNM.freshFVar (Fresh := MkRefd))` を渡して解決（家族に文は足していない）。
* `Tools/ShippingGen4KWalkInst.lean`（206）: wrapper、instance helper 群、`translateInstanceUncachedWithK`、`translateProjInstanceUncachedWithK`、`translateInstanceOrFallbackK`。`keepsA_framed O hA hS (FramedA.X)` → `keepsK_framedNM M hA hS (FramedNM.X)` の機械的な写しで通った。
* **telescope 腕** `Tools/ShippingGen4KWalkProjField.lean`（130）: `projFieldNameK`（`forallTelescopeReducing` は `M.tele.telescope`）。止まりかけた点: `getConstInfoInduct/Ctor` の `throwError`。`MemoFamily.frame` は `FramedNM` にしか `mv` を保証せず、`throwError` は `FramedNM` ではない。
  `Lean.throwError` を `getRef`（context 読み）→ `AddErrorMessageContext.add`（= `addMessageContextFull` = `getEnv`(`FramedNM.env`) + `getMCtx`(`FramedNM.metaGet`) + `getLCtx`/`getOptions`(context 読み)）→ `throw` に展開し、前半を `Keeps` の bind で歩き、例外のメッセージ類は既存の `O.excOk`（`Op.throwErr`）で閉じた（`keepsK_throwError`）。**新しい law・家族の文は不要**（この調査では、家族に `throwError` の構成子を足す必要は見つからなかった）。
* `Tools/ShippingGen4KWalkCanon.lean`（80）: `canonHardwareKeyK`（`FramedNM.sideGetIO` ×2、`lookupVarP`、`KeepsCP.forIn_*`、`fuelFixM`）。A 版と同形。
* `Tools/ShippingGen4KWalkFallback.lean`（84）: `translateFallbackK`、`translate_keepsK`。**仮説として残るのは `LegacyImplK`（`Rec.translateExprToWireImpl`）、`LegacyCachedK`、`ChildEntryK`（`childSynthEntry`）の 3 つ**。`canonHardwareKey` と `projFieldName?` は証明済みで仮説から外れた（A 版は 5 つ）。
* `Tools/ShippingGen4KWalkLegacyCached.lean`（85）: `legacyCachedK_of_impl : LegacyImplK → LegacyCachedK`。これで `translate_keepsK` の仮説は `LegacyImplK` と `ChildEntryK`（S4-S6 の入口帰納）の 2 つに実質減る（`translate_keepsK` 自体の型は 3 仮説のまま、`LegacyCachedK` は `legacyCachedK_of_impl` から得る）。
* `Tests/Gen4/KWalkFallbackCheck.lean`（196）: KWALKFALLBACK CHECK: TYPE 5/5 / MUTANT 3/3（signature/defeq での棄却、意味的反例ではない）/ AXIOMS 10/10 標準のみ / CLOSURE 10/10 clean（Laws・T1Hyp・T1HypND 無し、陽性対照 2 件）。
* **終わらなかった handler の一覧**: `LegacyImplK` の全体 — `Rec.translateExprToWireImpl` が呼ぶ `handleApplicative` / `handleBitVecOps` / `handleRegister` / `handleMux` / `handleMemory` / `handleLoop` / `handleCircuitMonad` / `handleDefinitionUnfold` 等（A 版 `ShippingChildLegacyHandlersA` 179 / `HelpersA` 171 / `ImplA` 120 / `TailA` 223 行）と、それを歩く `vca`（`ShippingChildWalkA` 873 行、`keepsA_framed O hA hS` / `keepsA_diag` / telescope の `RefLawsATele` 固定）の K 版。
  **止まり（新しい文が要る）**: 翻訳器の範囲に `Diag` の操作（`ppExpr` 3、`IO.eprintln`+`flushStderr` 2 組、`IO.FS.Handle.mk`/`putStrLn`/`flush`）があり、`MemoFamily` に `Diag` の `mv` 保存の文が無い（`FramedNM` に `Diag` の構成子が無い）。この調査では導く経路が見つからなかった。判断資料: `scripts/gen4/KWALK_DIAG_DECISION.md`。
  `vca` の K 版が要る理由: A 版の handler は `@[keepsA]` 属性と `vca` で歩いており、`kwalk` ではない（`kwalk` は FallbackA 用）。今回は着手していない。見積り: WalkA の写し 600-900 + Helpers/Handlers/Impl/Tail の写し 400-700（推定、実測ではない）。`Diag` の腕（tracing）は `FramedNM` に対応が無い可能性があり、読んだだけで未確認。

## S4 の結果（rt169、`scripts/gen4/KWALK_S4_FREEZE.md` の型で実装。全て `kjob lake build` 済み、sorry・axiom・native_decide なし、axioms は標準のみ）

* **入口側の Diag の数え**（FREEZE §1）: 入口側（Elab.lean 5288-5606）で Diag になるのは `logProf`（`profLogIO b`、5436-5442）の**呼び出し**だけ。呼び出しは `synthesizeFromConst` 内で 5295, 5302, 5322, 5337, 5339, 5342, 5344, 5351, 5360, 5376 の 10 箇所、`emitLeaves`（2165, 2173）で leaf ごと 2 回、`synthesizeCombinationalCoreWith` で 5443 の 1 箇所。`ppExpr` は 0 件（5709 は翻訳器）。`IO.eprintln` は 5438 の 1 件（logProf の本体）。したがって **certified / mixed / machine / legacy の 4 腕は全て Diag（profLog）を通る**。
  扱い: 仮説 `LogMvK O`（`profLogIO b msg` を 1 回走らせても `mv` が変わらない。KWALK_DIAG_DECISION の選択肢 A の `profLog` の場合だけ）を `def` で取った。家族には足していない。選択肢 A が承認されれば `LogMvK` は家族から導かれる。承認されなければ S4 の定理は `LogMvK` を仮定した条件付きのまま。
  **Diag を通る腕の一覧（判断待ちの対象）**: `keepsK_profLog`、`emitLeavesK`、`certRest_keepsK`、`certified_keepsK`、`mixed_keepsK`、`machineCert_keepsK`、`fromConst_{certified,mixed,machine,frontends}_windowK`。
* `Tools/ShippingGen4KWalkEntry.lean`: `keepsK_profLog`、`tripleK_mkExprCache`（`MkRefd` の出所つき）、`bindInputPortK`/`bindCertifiedInputsK`/`bindMixedCertifiedInputsK`、`emitLeavesKP`（翻訳器 `htr` が仮説。`KeepsCP` = `CtxOk` の文脈に限った形で、S3 の `RecK` と同じ。最初は `KeepsC`（全文脈）で証明したが `RecK` から与えられないので `KeepsCP` に直した）、`certRest_keepsK`、`certified_keepsK`、`mixed_keepsK`、`tripleK_synthGet`、`closeInstsM_keepsK`/`closeInstsGM_keepsK`（子の入口 `hchild : ∀ c, Keeps (synthesizeChild c)` が仮説）、`machineCert_keepsK`、**`triple_memoInsert`**（K の世界で `memo.modify (·.insert n r)` は返り、K_n で終わる。投げない）。A 版 PathA/FrontA の機械的な写しで通った（`keepsA_framed` → `keepsK_framedNM`、`keepsA_diag` → `keepsK_profLog`）。
* `Tools/ShippingGen4KWalkEntryArms.lean`: `fromConst_certified_windowK` / `fromConst_mixed_windowK` / `fromConst_machine_windowK` / `fromConst_frontends_windowK`。`synthesizeFromConst … [] false true …` は K から **K_declName（成功）/ K（失敗、`OkExc`）**。memo 書き込みは各腕の最後の効果なので、失敗は常に K のまま（窓が開く前）。machine 腕の fall-through（`machineShape?` が none、または `synthesizeMachineCertified` が none）は legacy 腕の仮説 `hlegacy`（`certifiedFrontEnd = false` の入口が K から K_declName）に流れる。
* `Tests/Gen4/KWalkEntryCheck.lean`: KWALKENTRY CHECK: TYPE 5/5 / MUTANT 3/3（signature/defeq での棄却、意味的反例ではない）/ AXIOMS 24/24 標準のみ / CLOSURE 24/24 clean（Laws・T1Hyp・T1HypND 無し、陽性対照 2 件）/ `LogMvK` が frontends の閉包に入っていること（仮説であること）を確認。型の照合は memo 書き込み、profLog、certified 腕、frontends、入れ子の入口の 5 件。
* **仮説として残るもの（S4 の範囲）**: `LogMvK`（Diag 判断待ち）、`htr`（`translate_keepsK` から）、`hchild`（S6 の `synthesizeChild` 帰納）、`hlegacy`（legacy 腕）。LegacyImplK / ChildEntryK は S3 のとおり仮説のまま。
* **legacy 腕（未着手、A 版 `ShippingChildLegacyTailA` 223 + HelpersA の写し）**: memo の hit は `return cached`（memo は変わらないので K を K_n に弱める `kwalkX_of_kwalk` で足りる、読み）。miss 側は `openRecordInputs`（`forallTelescopeReducing` + `getConstInfoInduct/Ctor` + `instantiateForall` + `mkLambdaFVars`）、`lambdaTelescope`、`splitReturnLeaves`（`fuelFixM2`）、`bindInputsLegacy`（`isSignalBinderType` / `inferHWTypeFromSignal`）、`emitLeaves`、`finishSynth`、memo 書き込み。新しい前提は要らない見込み（`M.tele` と `FramedNM` で足りる、読み）。

* **legacy 腕で見つかった 2 点（rt169、S4 続き）**:
  1. **Diag が増える**: 翻訳器が呼ぶ helper `extractDimExprStep`（Elab.lean 681, 686）と `inferHWTypeWithDimensionsStep`（715）が、`throwError` の前に `ppExpr` を呼ぶ（エラーメッセージの整形、`symbolicMode` の枝）。S3 の Diag の数え（翻訳器の範囲 5700-8960）はこの 3 箇所を数えていない（helper は 5700 より前）。`inferHWTypeFromSignal` はハンドラと legacy 腕の `bindInputsLegacy` の両方から呼ばれるので、**LegacyImplK の Diag 一覧に ppExpr ×3（helper 内）を足す必要がある**。`KWALK_DIAG_DECISION.md` の選択肢 A の `frameDiag` が `ppExpr` も含む形ならこれも解ける。仮説 `PpMvK`（`ppExpr e` が `mv` を変えない）を `Tools/ShippingGen4KWalkHelpers.lean` に `def` で取った（家族には足していない）。helper の K 版（`extractWidthK` / `inferHWTypeK` / `extractDimExprK` / `inferHWTypeWithDimensionsK` / `inferHWTypeFromSignalK` / `isSignalBinderTypeK`）はこの仮説の下で証明した。
  2. **legacy 腕の失敗側が K で終わることを、現在の `MemoTele` では示せない**: 腕の `sparkleSubModuleCache.modify (·.insert declName result)`（Elab.lean 5388）は `Lean.Meta.lambdaTelescope body fun xs innerBody => do …` の継続の**内側**の最後の効果。`MemoTele.lamTelescope` は `Keeps I`（成功も失敗も同じ `I` で終わる）の形なので、継続の不変量 `I` は成功側（insert 後 = K_declName）と失敗側（insert 前 = K）を分けられない。`I := K_declName` を取ると成功側は閉じるが、失敗側は K_declName までしか言えない（K に戻せない）。
     insert の後には `return result` しか無いので意味的には失敗は K（insert 前）のはずだが、これは telescope の外から見える形では書けない。この調査では、`MemoFamily` の既存 12 文から導く経路は見つからなかった。
     必要なもの（新しい文）の候補: (a) `MemoTele` に成功と失敗の事後条件を分けた Triple 形（`lamTelescope` の 1 文）、(b) 「`lambdaTelescope e (fun xs b => k xs b >>= f) = lambdaTelescope e k >>= f`」型の可換則（f が xs, b に依らないとき）、(c) legacy 腕の失敗側を K_declName に弱め、その後の `catch` 側で K を別に示す（K walk の目標を弱める）。**どれも TRUSTED の文または目標の変更で、ユーザー未承認。止まり、判断資料にまとめる。** 証明できた部分（`openRecordInputs` / `splitReturnLeaves` / `bindInputsLegacy` の K 版、legacy 腕の「成功側 K_declName」）は (a)(b) のどれを選んでも使える。
  同じ形（`try … finally` の内側で窓が開き、成功と失敗の事後条件が違う）は S5 の `Triple.tryFinally` にもあるが、こちらは `fin` が任意の `P` を保つ（`FramedNM` の文だけ）ので、成功と失敗で事後条件を分けた `tryFinally` の版を新規に証明すれば足りる見込み（読み）。

## S5 の結果（rt169、`Tools/ShippingGen4KWalkEntryCore.lean`、`kjob lake build` 済み、sorry・axiom・native_decide なし、axioms は標準のみ）

* `tryFinallySplit`: `try x finally fin` で、`x` が返る場合と投げる場合で事後条件を分ける版（`Triple.tryFinally` は両方を同じ `M` にする。窓の中では成功が K_n、失敗が K なので足りない）。`fin` が**投げない**（`Triple … (fun _ _ => False)`）ことを使う。
* `fin_totalK`: depth の `modify`（`M.frameDepthModify`）と 7 つの副セルの `set`（`FramedNM.sideSet`、`refSet_runs` で全域）が、任意の `KW O P` を保ち、投げない。
* `triple_depthSetK` / `triple_depthModifyK` / `triple_framedNM_total` / `tripleK_depthGetNZ` / `tripleK_throwErr`。
* **`entryNested_windowK`**: `depth ≠ 0` の世界の K から `synthesizeCombinationalCoreWith translate declName [] false true` は、成功で K_declName、失敗で K（`OkExc`）。仮説は `LogMvK`（logger、Diag 判断待ち）と `hbody`（腕: `synthesizeFromConst … [] false true` が K から K_declName / 失敗 K。S4 の `fromConst_frontends_windowK` が与える形、legacy 腕の `hlegacy` つき）。ioEnv は `FramedNM.ioEnv`、`depth ≥ 限度` の `throwError` は `tripleK_throwErr`（K のまま失敗）、7 つの保存読みと 7 つの `set` は `FramedNM`。
* **窓の閉じ方**: 窓は `hbody` の最後の memo 書き込みで開き、`finally`（`FramedNM` と depth `modify`）は K_declName を保つ。child cache への挿入（窓を閉じる）は `synthesizeChild`（S6）。
* **未着手**: 深さ 0 の入口（リセット）。`depth == 0` の枝は memo `set {}` → child cache `set {}` → 他の `set` の順で、`kwalk_memoReset` と `M.frameCacheSet` で閉じる見込み（読み。Lean では未試行）。`hbody` を `dv` つきの不変量（`KWalk ∧ dv = D+1`）で与える一般化は S6 で要る（今の腕は `StableK` の不変量 `KWalk` で証明してあるので、`dv` を足した不変量への一般化は機械的な見込み）。

## S5 続きと S6 の結果（rt169）

* **`entryTop_windowK`**（最外の入口、depth 0）: 開始世界は quiet と `sv` だけ（K は要らない）。`depth == 0` の枝の 7 つの `pure {}`、副セル 3 つの `set`、memo `set {}`（`triple_memoResetK`: `memoSet_ctx`、`mv = {}`）、child cache `set {}`（`triple_childResetK`: `O.cacheSet` + `M.frameCacheSet`、`mv = {}` を保つ）、他の 7 つの `set` の後で memo は空 = K が成り立つ。その後は入れ子の入口と同じ（depth `set` 1、`try … finally`、`fin_totalK` は d = 0 で `pure ()`）。成功は K_declName、失敗は quiet と `sv` のみ（リセットの前の失敗がありうるため）。**§4 (b) のとおり、最外の入口は K_declName で終わり K に戻らない**（child cache への挿入が無い）。
* **`synthesizeChild_windowK`**（窓を閉じる）: `sparkleChildCache.get`（`FramedNM.cacheGet`）→ hit なら `return`（K）、miss なら `synthesizeCombinational n`（`hcomb`: K から K_n、失敗は K）→ `sparkleChildCache.modify (·.insert n r)`（`kwalk_childInsert`: K_n から K）→ `return`。前提は `hcomb`（`combWith_nestedK` が `hbody` から与える）と `depth ≠ 0`（不変量 `KWalk ∧ dv ≠ 0`）。
* **S6 の残り（深さ帰納）の読み**: 翻訳器が走る間 `depth ≠ 0` が成り立つ。この不変量 `KD`（`KWalk ∧ dv ≠ 0`）は `StableK`（`dv` を保つ移送）なので、腕の定理（今は `KWalk` だけの不変量で証明）を `KD` に一般化し（`triple_memoInsert` に `dv` を足す）、`hchild := synthesizeChild_windowK`、`hbody := fromConst_frontends_windowK`、`htr := translate_keepsK` を同時に閉じる必要がある。入口は `depth ≥ 限度`（1024）で `throwError` するので、帰納は `限度 - dv` について（`EntryK` の案、§3）。入れ子の入口の成功後の `dv` は `fin` の `modify (· - 1)` で `d` に戻るが、`dv` を事後条件に載せていないので、帰納の一般化（`dv` つきの Triple）が要る。**今回は着手していない**。

## S6 深さ帰納の結果（rt170、`scripts/gen4/KWALK_S6_FREEZE.md` の型。全て `kjob lake build` 済み、sorry・axiom・native_decide なし、axioms は標準のみ）

* `Tools/ShippingGen4KWalkDepth.lean`: `KWD O P D := KW O P ∧ dv = D`、`stableK_KWD`、`tryFinallySplit2`（`fin` の事後条件を成功と失敗で別にする）、`triple_depthSetD`（D → v）/ `triple_depthModifyD`（D → f D）/ `tripleK_depthGetD`、`triple_memoInsertD`（K,D → K_n,D、窓を開く）、`triple_childInsertD`（K_n,D → K,D、窓を閉じる）、`fin_totalD`（`KWD P (D+1)` → `KWD P D`、投げない）。成功後の `dv` が `fin` で元に戻ることは `fin_totalD` と `entryNested_windowD` の事後条件に載っている。
* `Tools/ShippingGen4KWalkDepthArms.lean`: 4 つの腕（certified / mixed / machine / frontends）の `KWD` 版（EntryArms の写し。`certified_keepsK` 等は不変量 `I` について一般だったのでそのまま使えた）。
* `Tools/ShippingGen4KWalkDepthEntry.lean`: `entryNested_windowD`（`D ≠ 0`、`D ≥ sparkleSynthDepthLimit` では `throwError`、本体 `hbody` は `D < limit` のときだけ・深さ `D + 1` で要求）、`combWith_nestedD`、`synthesizeChild_windowD`。
* `Tools/ShippingGen4KWalkDepthInduct.lean`: **`child_step`**（深さ D の `synthesizeChild` を、深さ D+1 の `synthesizeChild`（`D < limit` のときだけ）から導く。`htr := translate_keepsK`（不変量 `KWD K (D+1)`）、`hchild`（`childSynthEntry` は `sparkleChildSynth.get` の後に `synthesizeChild`）、`hbody := fromConst_frontends_windowD`）、**`child_budget`**（予算 k、`limit ≤ D + k` についての帰納。k = 0 は `D ≥ limit` で入口が投げるので IH は要らない）、**`synthesizeChild_depthK`**（全ての `D ≠ 0` で `synthesizeChild` は `KWD K D` を保ち、失敗も `KWD K D`）。
* **結論の仮説として残るもの（指示の範囲内）**: `LogMvK`（Diag 判断待ち）、`hImpl : ∀ D ≠ 0, LegacyImplK O (KWD K D)`（S3 の仮説）、`hleg : ∀ D ≠ 0, LegacyArmD O D`（legacy 腕。窓の判断待ち）。`LegacyCachedK` は `legacyCachedK_of_impl` から導く。これ以外は残っていない（`hchild` / `hbody` / `htr` / `ChildEntryK` は帰納で閉じた）。
* **`PpMvK` は今回の帰納の閉包に入らない**: `PpMvK` を使うのは Helpers の K 版（`extractDimExprK` 等、legacy 腕・`LegacyImplK` の中身）で、legacy 腕は `hleg`、`LegacyImplK` は `hImpl` として仮説のままなので、帰納の結論の型には現れない。`hleg` / `hImpl` を証明するときに `PpMvK`（Diag 判断待ち）が要る見込み（読み）。
* **`memo_miss_of_child_miss` への接続**: `memo_miss_of_child_miss`（K だけから「child cache に無い名前は memo にも無い」）、`memo_miss_of_child_miss_KWD`、`tripleK_cacheGetD`、`childMiss_memoMiss`（`synthesizeChild` の child cache 読みが miss のとき、その世界で memo にも `n` が無い）。補題と Triple の形で、`MemoFamily` に文は足していない。消費者（legacy 腕の memo hit が起きない側）への接続自体は `hleg` の証明の中身で、今回は未着手。
* `Tests/Gen4/KWalkDepthCheck.lean`: KWALKDEPTH CHECK: TYPE 5/5 / MUTANT 4/4（signature/defeq での棄却、意味的反例ではない）/ AXIOMS 22/22 標準のみ / CLOSURE 22/22 clean（Laws・T1Hyp・T1HypND 無し、陽性対照 2 件）/ 見出しの定理の閉包に `LogMvK`・`LegacyImplK`・`LegacyArmD` が入る（true、true、true）、`PpMvK` は入らない（false）。
* 未着手（変わらず）: legacy 腕の全体（`hleg`、窓の判断待ち）、`LegacyImplK`（Diag の判断待ち）、最外の入口（depth 0）の `hbody` を `KWD K 1` で受ける版（`entryTop_windowK` は `KWalk` 前提の `hbody` のまま。`dv = 1` を載せるにはリセットの手前の部品に `dv = 0` を通す小さな補題が要る）。

## 4. 前提を増やさないことの確認と、止まる点

* 土台は `MemoFamily` を仮説に取るだけ。`Laws` / `T1Hyp` / `T1HypND` は閉包に入らない（Check CLOSURE）。新しい law・TRUSTED 境界・FG/保証の変更は無い。FG の縮小も GenWF の強化も無い。台帳の差分 0。
* **(a) 窓の中で例外が出ないこと**（E7）。memo に `n` を書いてから child cache に `n` を入れるまでの間に例外が出ると、`catch` の先で K が崩れる（memo に `n` があり child cache に無い → その後の `synthesizeChild n` が memo hit する）。窓の中の効果は、純粋な後処理、`finally` の `set`/`modify`、`IO.getEnv`。
  `ref` の `get/set/modify` が投げないことは既存の `refGet_runs`/`refSet_runs`/`refModify_runs`（ShippingChildInv:690-）で足りる。
  **(a) の IO.getEnv 部分は解決（窓の中のその他の効果の「投げない」は §2 E7 の通り FramedNM の枠で扱い、ここで新たに示したのは IO.getEnv だけ）（rt165、`Tools/ShippingGen4KWalkEnv.lean`、BUILT）**: `Tools.ShippingGen4KWalkEnv.ioEnv_runs : ∀ n w, ∃ a w', RunsTo (IO.getEnv n : MetaM (Option String)) mctx mref cctx cref w a w'`（axioms は標準のみ、sorry なし）。
  根拠: toolchain v4.32.1 の `IO.getEnv` は `@[extern "lean_io_getenv"] opaque getEnv (var : @& String) : BaseIO (Option String)`（`Init/System/IO.lean:951`、ビルドが使う版で確認）。
  `MetaM` への持ち上げは `BaseIO.toEIO`（`Init/System/IO.lean:71`: `fun s => match act s with | .mk a s => .ok a s`、`.ok` のみ）を通る。証明は `refGet_runs` と同形: `IO.getEnv n w` を `cases` して `ST.Out.mk a w'` に分け、持ち上げの定義を `change` で展開し `rw`。
  `@[extern]` の本体は見ていない（opaque のまま）。`BaseIO` の型が「エラーの場合が無い」ことだけを使うので、外部実装には依存しない。
  したがって家族に 1 文足す必要は無く、新しい TRUSTED 文・前提は無い。Check ファイルは作っていない（定理 1 つ、`#print axioms` を同ファイルに置いた）。
  **窓の中で実際に呼ぶ形の確認（rt166、`Tests/Gen4/KWalkEnvShape.lean`、BUILT）**: Elab.lean:5602 `if (← IO.getEnv "SPARKLE_NO_REGDEDUP").isSome then …`（MetaM の do）を同じ形で書いて `pp.explicit` で出した。
  elaborated term は `liftM (IO.getEnv "…")` で、持ち上げの連鎖は `BaseIO →(instMonadLiftBaseIOEIO IO.Error) IO →(Core.instMonadLiftIOCoreM) CoreM → StateRefT' → ReaderT`、すなわち **`Core.instMonadLiftIOCoreM`（`liftIOCore`）を通る**。`(IO.getEnv n : MetaM (Option String))` と書いた `ioEnv_runs` の文の項と同じ連鎖で、`example : probeGetEnv = bind (IO.getEnv … : MetaM _) …` が `rfl` で通った。
  `ioEnv_runs` の証明はこの連鎖（`liftIOCore` を含む）を `change` で展開して `.ok` に落としており、build 済みなので、**Elab.lean:5602 の形は `ioEnv_runs` の文そのもの**。別の補題は要らない。同じ形の 5435（窓の外）も同じ。CompilerM 内の 6419・6938・6950 は `liftMetaM` 経由の別の形で、窓（`synthesizeChild` 内の memo 書き込みから child cache 挿入まで）の外（read。Lean では確認していない）。
  （以前の記述）なお `Core.liftIOCore (IO.getEnv n).toEIO` の形（`IO.toEIO` 経由で例外を作る版）は証明していない: 窓の中の呼び出し（Elab.lean:5602、`(← IO.getEnv ..)` を `MetaM` で書いた形）は上の `liftM (IO.getEnv n)` の形で、`FramedNM.ioEnv` の型もこの形。
* (b) 深さ 0 の入口は、最後に top の名前 `n` を memo に書いて K_n で終わり、K に戻らない（child cache への挿入がない）。この後に翻訳器のコードは走らない（read）ので消費者は影響を受けないが、`EntryK` を深さ 0 に使わないこと（深さ 0 は E3 から始める別の文にする）。
* (c) `memo` の中身（pair が `PairPF` か）は扱わない。K は key だけの不変量で、内容の不変量は案 A（`RefLawsM`）の領分であり、本 walk は案 B（hit を除く）。
* (d) `outer_miss`（`Tools/ShippingLegacySemMemoWalk.lean:495`）の述べ直しは別単位（AdmCtx/quiet 制限下）。

## 5. 限界

* 土台のみ証明。翻訳器の段（§2 の T1-T6、E1-E8）は**全て未証明**で、行数は推定。
* mutant は signature / defeq での棄却で、意味的反例ではない。家族の真偽・`Laws` との無矛盾は主張しない。
* Elab.lean の行番号は base のもの。§2 の「read」は私の読みで Lean では確認していない。
