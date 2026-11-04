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

* **`entryTop_windowK`**（最外の入口、depth 0）: 開始世界は quiet と `sv` だけ（K は要らない）。`depth == 0` の枝の 7 つの `pure {}`、副セル 3 つの `set`、memo `set {}`（`triple_memoResetK`: `memoSet_ctx`、`mv = {}`）、child cache `set {}`（`triple_childResetK`: `O.cacheSet` + `M.frameCacheSet`、`mv = {}` を保つ）、他の 7 つの `set` の後で memo は空 = K が成り立つ。その後は入れ子の入口と同じ（depth `set` 1、`try … finally`、`fin_totalK` は d = 0 で `pure ()`）。成功は K_declName、失敗は quiet と `sv` のみ（リセットの前の失敗では K を言えないため。リセットの後の本体の失敗（KWD K）も同じ quiet ∧ `sv` に弱めて、事後条件を 1 つにしている）。**§4 (b) のとおり、最外の入口は K_declName で終わり K に戻らない**（child cache への挿入が無い）。
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
* 未着手（rt171 で更新）: legacy 腕の全体（`hleg`、窓の判断待ち）、`LegacyImplK`（Diag の判断待ち）。最外の入口（depth 0）の KWD 版は下の「最外の入口（rt171）」で完了。

## 最外の入口（rt171、`Tools/ShippingGen4KWalkDepthTop.lean`、`scripts/gen4/KWALK_S6_TOP_FREEZE.md` の型。`kjob lake build` 済み、sorry・axiom・native_decide なし、axioms は標準のみ）

* `triple_memoResetD`（memo `set {}` が `dv` を保つ。リセットの前の部品に `dv = 0` を通す小さな補題）、`triple_childResetD`（child cache `set` が `dv` と、child cache を見ない述語を保つ）。リセットの前の `pure` と副セル `set` は `stableK_KWD O (fun _ _ => True) 0` で `dv = 0` を保つ。
* **`entryTop_windowD`**: 開始は `KWD O True 0`（quiet、`sv`、depth 0。K は要らない）。本体 `hbody` は `KWD K 1`（`0 < sparkleSynthDepthLimit` のときだけ）で受ける。成功は `KWD K_declName 0`（K_declName で終わり、depth は 0 に戻る）、失敗は quiet ∧ `sv`（リセットの前の失敗では K を言えないため。リセットの後の本体の失敗（KWD K）も同じ quiet ∧ `sv` に弱めて、事後条件を 1 つにしている）。
* **`topEntry_K`**: `hbody` を `synthesizeChild_depthK`（D = 1）と `fromConst_frontends_windowD` から `child_step` と同じ形で作り、実際の翻訳器 `translateExprToWire` で閉じた。仮説は `LogMvK`・`LegacyImplK`（D≠0 ごと）・`LegacyArmD`（D≠0 ごと）の 3 つだけ。
* `Tests/Gen4/KWalkDepthCheck.lean` に追加: TYPE 8/8（+3: memoResetD / entryTopD / topEntryK）、MUTANT 7/7（+3: M5 深さを戻さない成功、M6 ガード `0 < limit` なし、M7 失敗側に完全な K を要求。signature/defeq での棄却で、意味的反例ではない）、AXIOMS/CLOSURE 26/26。`topEntry_K` の型に現れる仮説定義は 3 つだけ（LogMvK / LegacyImplK / LegacyArmD）であることを検査。`PpMvK` は `synthesizeChild_depthK` の閉包に入らない。`topEntry_K` の閉包には証明項の中で構成する `LegacyCachedK` / `ChildEntryK` も現れる（型には現れず、仮説ではない）。
* 残り: `hleg`（窓の判断待ち）と `LegacyImplK`（Diag の判断待ち）だけ。新しい law・前提・家族の文は無い。台帳の差分 0。

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

## rt173: MemoFamily rev3 の実装と legacy 腕（hleg）（base c595b472、承認済み freeze MEMO_FAMILY_FREEZE rev3 の型のまま。全て `kjob lake build` 済み、sorry・axiom・native_decide なし、axioms は標準のみ。clean build は coder）

**段 1（コミット 155e13c4、header c3df0603）**
* `Tools/Assume/MemoFamily.lean` を rev3 の 15 文に差し替えた（`MvInert` / `OkEnvMv`、`MemoTele.lamTelescopeT`、`logProf` / `stderrLine` / `printersMv`）。旧 `MemoTele.lamTelescope` は同名・同型の導出定理として残した。構造の本体が freeze §2 のコードブロックと一致することは、freeze §2 のブロックと実装の diff（空白・`open` 行を除く）で**完全一致**を確かめた（TYPE の isDefEq とは別に実施）。
* `Tests/Gen4/MemoFamilyCheck.lean` を rev3 に更新（scratch の `MemoFamilyRev3Check` は本体へ統合して削除、lakefile も差し替え）: TYPE 15/15 / MUTANT 19/19（18 ラベル。signature/defeq での棄却で、意味的反例ではない）/ OUTSIDE 18/18 / AXIOMS 19 / CLOSURE 7（+2 陽性対照）/ MODEL 1（vacuous、型の充足可能性のみ）。
* **LogMvK / PpMvK の導出**: 新ファイル `Tools/ShippingGen4KWalkDiag.lean`（`MemoFamily` と Entry / Helpers の両方を import するため別ファイル）に `logMvK_of`（= `logProf`）、`ppExpr_mv` / `ppMvK_of`（`printersMv` + 既存の `frame`）、`profBlock_mv` / `stderrPair_mv`。`MsgMvK`（Elab.lean 6605）は家族に入れていないので、ここに仮説 `def` として置いた（まだどの定理にも使われていない: 使うのは `LegacyImplK` の中身）。
* **K walk の定理から `LogMvK` / `PpMvK` を外したか**: 既存の S4-S6 の定理（`Entry` / `EntryArms` / `Depth*` など）の型は**変えていない**（`LogMvK` を仮説に取ったまま。導出定理 `logMvK_of` を置いただけ）。新しい `topEntry_K_of_family`（下）だけが `LogMvK` を `logMvK_of M` で自分で渡し、型から外れる。`PpMvK` は legacy 腕の中で `ppMvK_of M` として渡す。
* KWalk の全 Check（KWalkCheck / Prims / Translate / Fallback / Entry / Depth）を rev3 の `MemoFamily` に対して `kjob lake build` で確認した（全て exit 0。出力の数は rev2 のときと同じ: TYPE 7/7・7/7・4/4・5/5・7/7・8/8、AXIOMS 24・14・6・10・27・26）。既存の利用側（`M.tele.lamTelescope`）は導出定理に解決され、本文は変更なし。

**段 2（コミット 8f112bcc、header 206be00a）: legacy 腕**
* `Tools/ShippingGen4KWalkLegacyArm.lean`: `legacy_windowD`（`synthesizeFromConst … [] false false ci isInst` = 両ゲートが外れ、certified front end OFF の legacy 腕。`KWD K D` から、成功は `KWD K_declName D`、失敗は `KWD K D ∧ OkExc`）。部品は rt169 のもの（`openRecordInputs_keepsK` / `splitReturnLeaves_keepsK` / `bindInputsLegacyKP` / `emitLeavesKP` / `finishSynthA`）に、`MemoTele.lamTelescopeT`（Triple 形: `P = KWD K D`、`Q _ = KWD K_declName D`、`R = KWD K D`）と memo 書き込み `triple_memoInsertD` を組み合わせた。memo hit は `kwdX_of_kwd`（K を K_declName に弱める）で扱った（`tripleK_memoGetD` は memo の `get` が `KWD K D` を保つ補題）。
* **仮説**: `LogMvK`（`legacy_windowD` の型）と、翻訳器の前提 `htr : RecK O (KWD K D) translate`（**全ての admissible な文脈で**。telescope の中で文脈が変わるため、固定した `mctx cctx` では足りない）。`LegacyArmD`（旧 `hleg`）は**仮説ではなくなった**: 翻訳器の前提は深さ帰納の中の `translate_keepsK`（`LegacyImplK` から）で作られ、`legacy_windowD` に渡される。
* `Tools/ShippingGen4KWalkLegacyInduct.lean`: `child_stepL` / `child_budgetL` / `synthesizeChild_depthKL`（`hleg` なしの深さ帰納）、`topEntry_KL`、`topEntry_K_of_family`（`LogMvK` も `logMvK_of M` で渡し、型に現れる仮説は **`LegacyImplK`（D ≠ 0 ごと）だけ**）。旧版（`Depth*` の `hleg` 付き）は変えていない。
* `Tests/Gen4/KWalkLegacyCheck.lean`: KWALKLEGACY CHECK: TYPE 4/4 / MUTANT 6/6（signature/defeq での棄却で意味的反例ではない）/ AXIOMS 8/8 / CLOSURE 8/8 clean（+2 陽性対照）。`topEntry_K_of_family` の型の仮説は `LegacyImplK` のみ、閉包に `LegacyArmD` は無い。閉包には `LogMvK` / `PpMvK` が出るが、型には無い（家族から導かれたもの）。**`MsgMvK` は閉包に入らない**（これを使うのは `LegacyImplK` の中身で、`LegacyImplK` 自体はまだ仮説のため。`LegacyImplK` を証明するときに初めて入る見込み）。
* **指示と違った点（正直に）**: 「残る仮説は LegacyImplK と MsgMvK だけ」としていたが、現時点の閉包に入る仮説は **LegacyImplK だけ**（`MsgMvK` は、`LegacyImplK` の証明側に属し、まだ使われていない）。新しい仮説・law・家族の文は増えていない。
* 台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。`MemoFamily` を使う K walk 全体の受入（FG +1）は `LegacyImplK` と `MsgMvK` が閉じるまで起きない。

**残り**: `LegacyImplK`（`Rec.translateExprToWireImpl` の各 handler。`PpMvK` は家族から出るようになり、`MsgMvK`（6605）が残る）。

## rt174: LegacyImplK その 1（base b92c90f6。承認済み freeze の型のまま。新しい仮説・law・家族の文なし。sorry・axiom・native_decide なし）

**vca の K 版**: `kwalk`（`Tools/ShippingChildKWalk.lean`）/ `kwalkM`（`Tools/ShippingGen4KWalkTac.lean`）は rt167-169 で既にあった。rt174 で `Tools/ShippingGen4KWalkTac2.lean`（`kwalkN`）を追加: `kwalkM` のコピーに (1) `Keeps` の FramedNM 操作を `keepsK_framedNM M hA hS (by constructor …)` で自動に閉じる、(2) context の読み（`getRef`/`getOptions`/`liftM` など）を `Keeps.of_ok`、(3) `CompilerM` の `liftM`/`liftIO`/`ST.Ref.*`/`read`/`bindRead`、(4) `throwE`（EarlyReturn）と `Except.rec`、(5) instance projection の reduce と `KeepsCP.forIn_*`、(6) 再帰呼び出しの局所仮説（∀ 付き）、(7) `tryInlineUnfold` の bind に `KeepsCP.bindCaught`（局所仮説 `htri`）を足した。`@[keepsK]` 属性は作らず、規則の一覧は `Tools/ShippingGen4KWalkLegacyRules.lean` の `kwAll`（タクティクマクロ）に置いた（rule 引数は M / hpp / hA / hS という名前の節変数を取る）。

**済んだ handler（各モジュール別、`kjob lake build` 済みのもの。「BUILT」はコミット時点のビルド成功で、clean build は coder）**

| モジュール | 内容 |
|---|---|
| `LegacyH1` | `snapshotWireCaches` / `restoreWireCaches`（exprCache の set は `FramedNM.localSetIO`）/ `handleErrorPatterns` |
| `LegacyH2` | A 版 Helpers のうち K 版が無かったもの: `isTracingEnabledFor` / `addTrace`（`modifyTraces` を unfold、`keepsK_addMessageContext`）/ `extractNat`・`extractBitVecLiteral`・`extractNatLiteral`・`extractBitVecList`・`extractBitVecArray`（`fuelFixM_keepsCP`）/ `cachedInferType` / `getWireWidth(Dim)` / `lowerZeroExtendWire` |
| `LegacyH4` | `CompilerM.withLocalDecl` / `withLetDecl`（`MemoTele.localDecl` / `letDecl` から） |
| `LegacyRules` | 規則マクロ `kwAll` |
| `LegacyH3` | `handleTupleProjections` / `handleBitVecOps` / `handleRegister`（EarlyReturn）/ `handleMux` / `handleMemory` / `handleCircuitMonad`（いずれも `tr`＋`htr` を取る） |
| `LegacyH5` | `handleApplicative`（`lower` を signals の帰納）/ `translateShiftAmount` |
| `LegacyH6` | `handleLoop`（`canonHardwareKeyK` を規則に追加） |
| `LegacyH7` | `tryInlineUnfold` の `TripleCP` 版（`tryInlineUnfold_tripleCPK`） |

**残り**
* `handleDefinitionUnfold`（`Tools/ShippingGen4KWalkLegacyH8.lean`、`hchild`＝`childSynthEntry` の `Keeps` と `htri`＝`tryInlineUnfold_tripleCPK` を使う形）: **ビルド未成功**。`kjob lake build` が `whnf` の deterministic timeout（maxHeartbeats 4M と 20M の 2 回、20M で 18 分）。原因は特定できていない（`KWALK_DEBUG` の記録では約 1000 step 進んで止まる。この調査では、どの step で止まるかまでは見つからなかった）。lakefile には登録しておらず、BUILT とは書かない。次の rt の候補: (a) 腕（`hint` の分岐ごと）に分けて別定理にする、(b) `kloop` の fuel 400 と 1 step あたりの `exact … (by constructor)` の試行を減らす、(c) 子の呼び出しまわりを手で書く。
* `translateExprToWireApp`（`normSpine` の fuel 帰納を含む）、`toIR`（`sizeOf` 帰納）、`getPrimitiveNameFromLambda`、そして本体 `Rec.translateExprToWireImpl`（Elab.lean 6930-7985 約 1050 行）と `LegacyImplK` の組立て。
* **見つけた点（新しい仮説ではないが、組立てで必要）**: `handleDefinitionUnfold` は `childSynthEntry c` を呼ぶ。`LegacyImplK O (KWD K D)` の中でこれを閉じるには、A 版の `hchild` に当たる `ChildEntryK`（深さ D の子の入口）が要る。これは仮説として足さず、`Tools/ShippingGen4KWalkLegacyInduct.lean` の深さ帰納（`child_stepL` / `child_budgetL`）から、深さの上限（`sparkleSynthDepthLimit`）に向かう減少帰納で与える形になる見込み（この調査では、`LegacyImplK` を `hchild` なしに単独で立てる経路は見つからなかった）。この帰納の形（`LegacyImplK` の証明を `D` の帰納の中に入れるか、`hchild` を取る形の `LegacyImplK'` を作って最後に閉じるか）は次の rt で決める。
* `MsgMvK`（Elab.lean 6605 の `msgToString`）は上のどの handler にもまだ登場していない（使うのは本体の該当箇所）。
* その後: `topEntry_K_of_family` から `LegacyImplK` を外した版と Check（TYPE / MUTANT / AXIOMS / CLOSURE、閉包の仮説の一覧）。

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## rt175: LegacyImplK その 2（base b59b08cd。承認済み freeze の型のまま。新しい仮説・law・家族の文なし。sorry・axiom・native_decide なし）

**H8 `handleDefinitionUnfold` が通った**（`Tools/ShippingGen4KWalkLegacyH8.lean`、BUILT: `kjob lake build Tools.ShippingGen4KWalkLegacyH8` exit 0、H8 本体 40 秒、全体（Tac2 から H1-H7、Rules、H8a、H8 の再ビルド込み）約 2 分。`#print axioms` は propext / Classical.choice / Quot.sound のみ。clean build は coder）。

**timeout の原因（この調査で特定できたもの）**: 腕に分ける必要はなかった。`kwalkN` の `kstep` は `have __do_jp := fun r => …; body`（do 記法の join point）を zeta で本体に**コピー**していた。`handleDefinitionUnfold` は `if` / `match` / `try` が多く、join point（継続全体）が分岐ごとに複製され、開いたゴールが 311 個になり、1 つの定理の中でステップ数が爆発して `maxHeartbeats` に当たっていた（Dbg 計測: 400k で約 2400 step、4M で 2739 step 時点でゴール 311 個）。「whnf の timeout」は予算が尽きた場所にすぎず、特定の step が止まっていたのではない（最後の step を RUNTAC で確かめた: 通常の `refine KeepsCP.bind`）。
**対処（Tac2 の変更、law なし）**: `__do_jp` で始まる `have` の値が lambda のとき、`∀ x̄, KeepsCP (v x̄)` を**1 回だけ**証明し、本体は join point を不透明な局所 `jp_n` とその事実 `hjp_n` で歩く。`.fvar` の呼び出しは同じ fvar についての仮説だけを使う。ほかに、(1) 標準エラーの対（Elab 6423-6425）を 1 単位の規則 `stderrPairCPk`（`stderrLine`）にする（bind の規則枠 `Bind.bind` を追加）、(2) `bindRead` は context の読みにだけ試す、(3) `Keeps` の `tryCatch` / `Except.rec` / early return の `throw`、(4) catch した `some ex` の `OkMsg`（`OkOpt (…, some ex).snd` から）。
**新モジュール** `Tools/ShippingGen4KWalkLegacyH8a.lean`（BUILT）: `stderrPairCPk`（`eprintln` + `flushStderr` を `stderrLine` と `O.diag` で `Keeps` に）、`keepsK_msgToStringR`（`msgToString`、Elab 6605。memo の法は仮説 `MsgMvK`）、規則マクロ `kwAll2`（= `kwAll` + 上の 2 規則）。**`MsgMvK` は H8 で初めて使われ、H8 の型の仮説 `hmsg : MsgMvK O` として現れる**（これは指示どおりの唯一の新しい仮説）。`hchild`（`childSynthEntry` の `Keeps`）も仮説として取る形（A 版と同じ）。
**ヒント**: `maxHeartbeats` は H8 で 4M（1M では不足。時間は 40 秒なので「押し切り」ではなく、join point の抽象後の通常のコスト）。

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

**ChildEntryK の形（rt175 で決めた）**: 仮説として足さない。A 版と同じく **`hchild`（= `ChildEntryK O I`）を取る形**で handler と本体を証明する（`handleDefinitionUnfoldK` は `hchild` を取る、H9 / H10 も同じ）。最後に `LegacyImplK` を `∀ D ≠ 0, ChildEntryK O (KWD O MemoKeysInChild D) → LegacyImplK O (KWD O MemoKeysInChild D)`（= `LegacyImplK'`）として立て、`Induct` の `child_stepL` / `topEntry_KL` の中で、`hEntry`（`IH` から `tripleK_synthGet` で作る `ChildEntryK`）を `hImpl` に渡す形に書き換えた版で深さ帰納を閉じる。`child_stepL` はすでに `hEntry` を `IH` から作ってから `hImpl (D+1)` を使うので、`hImpl` に `hEntry` を渡せば循環しない（次の rt）。

**H9**（`Tools/ShippingGen4KWalkLegacyH9.lean`）: `normSpineK`（`fuel` の帰納）、`translateExprToWireAppK`（9 つの handler を規則として歩く）。`withTransparency` は kstep の「lambda になった Meta.Context の更新」規則（`Keeps.withReaderA`）で通る。`profHandler`（private）も unfold で歩けた。

**rt175 の終わりの状態**
* BUILT: `Tac2`（join point 規則ほか）、`LegacyH8a`、`LegacyH8`（handleDefinitionUnfold）、`LegacyH9`（`normSpineK`、`translateExprToWireAppK`）。lakefile 登録済み。
* **未ビルド（lakefile 未登録、BUILT と書かない）**: `LegacyH10`（`getPrimK`、`toIRK`。`kjob lake build` が 9 分で終わらず自分の timeout で止めた。heartbeat エラーではなく、原因は未特定。getPrim と toIR のどちらが重いかも未分離）、`LegacyH11`（本体 `Rec.translateExprToWireImpl`。11 分 40 秒で終わらず止めた。H10 が未ビルドなので H11 は H10 に依存したまま未検証）、`LegacyInduct2`（`hImpl : ∀ D ≠ 0, ChildEntryK → LegacyImplK` の形の深さ帰納。ビルド未実行）。
* 次: H10 の `getPrimK` と `toIRK` を別モジュールにして時間を測る（toIR は `sizeOf` の帰納で `kwAll3` を歩くので、`__do_jp` 以外の複製が残っていないか Dbg で数える）。H11 は coder が `kjob run` で長い上限を付けて回すか、本体を `Elab 6930-7985` の腕ごとに分ける。その後 `Induct2` をビルドし、`LegacyImplK'` を組んで `MsgMvK` だけが仮説の `topEntry` と Check（TYPE / MUTANT / AXIOMS / CLOSURE）。
* `MsgMvK` 以外の新しい仮説は出ていない。

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## rt176: LegacyImplK その 3（base 67e3bef1。新しい仮説・law・家族の文なし。sorry・axiom・native_decide なし。Elab.lean は未編集）

**H10 を分けて測った（BUILT・lakefile 登録済み）**
* `Tools/ShippingGen4KWalkLegacyH10a.lean`（`getPrimK`）: 3.4 秒。
* `Tools/ShippingGen4KWalkLegacyH10b.lean`（`toIRK_bound` / `toIRK`）: 重い方。分ける前は 9 分で終わらず、分けた後も 9 分で自分の timeout（`timeout 540`）で止めた。
* **toIR の原因（この調査で特定）**: `__do_jp` ではなく、**帰納仮説が一度も当たっていなかった**。`toIRK_bound` の `ih` が `∀ e', sizeOf e' < n → ∀ mctx cctx, AdmCtx → …` の形で、Tac2 の「局所仮説（再帰呼び出しの IH）」の `exact ih _ _ (by assumption) …` の引数の並びのどれにも合わなかった。そのため再帰呼び出し `toIR a` / `toIR b` のたびに `toIR` を `unfold` し、Dbg では `toIR` の unfold が 103 回（match の継続のコピーではなく、同じ定義の再展開）。
* **対処（Tac2 の規則、law なし）**: `ih` を `∀ mctx cctx, AdmCtx → ∀ e', sizeOf e' < n → …` の順にし、Tac2 に `exact ih _ _ (by assumption) _ (by simp_all <;> omega)` の規則を追加（サイズの条件は文脈から出す）。結果: Dbg（maxHeartbeats 400k）で H10b が通った。ステップ数は 2417（toIR の unfold は消えた）。H10b の本体の時間は 1 秒未満。
* 「mutant」: 該当なし（この作業は証明だけで、型は変えていない）。

**Tac2 のほかの変更（law なし、H1–H10 を現在の Tac2 で再ビルドして exit 0）**
1. `.fvar` の呼び出し（join point など）に対して、**定数を頭にもつ仮説（`hchild`）と別の fvar の仮説は試さない**（失敗する elaboration の無駄打ち。H11 の runTac 失敗が 497 → 215 に減った）。
2. `kloop`: step が当たらなかったゴール（stuck）は以後のラウンドで再試行しない（効果はステップ数に出なかったが害もない。安全側の変更）。
3. 規則の `apply … <;> first | assumption | skip` を `applyRule` にし、**大きい新ゴール（approxDepth ≥ 14）には assumption を試さない**（継続 `k` が大きいときの `∀ …, KeepsCP (k x)` と `htr` などとの defeq が `k x` を beta して do ブロック全体を whnf するのを避ける）。H11 の状況は変わらなかった（下記）。
4. 計測用: `KWALK_DEBUG` のとき、step ごとの heartbeat 差（`kwalk hb N goals G`）と、2M を超える `runTac` の構文を出す。

**H11（本体 `Rec.translateExprToWireImpl`）: 終わっていない（BUILT と書かない・lakefile 未登録）**
* `toIRK` の規則の引数の順が H11 の `kwMain` で `toIRK M hpp hS hmsg hA _ _ _` になっていた（実際は `wireS fvarId hA e`）→ `_ _ hA _` に直した。
* 本体の `maxHeartbeats` 4M で、step 1055 件（Dbg で数えた）で `whnf` の deterministic timeout（約 5 分 40 秒）。400k のときは約 490 step。**ステップ数の増加と heartbeat の関係**: 1 ステップあたりの中央値は小さい（数十万）が、`@liftM` / `@monadLift` / `@MonadLift.monadLift` / `@ST.Ref.modifyGet` の step が 1 回 3000 万〜6800 万 heartbeat（全体の約 1/4 を占める）。runTac の計測では、その大半は **`keepsK_framedNM … (by constructor <;> first | constructor | assumption)`**（`FramedNM` の構成子を `constructor` で探す）が 1 回 1300 万〜3500 万。この試行を given rule の後ろに回しても step 数は変わらず、成功している試行のコストだった（失敗の無駄ではない）。
* **最後に始まって終わらない step は `@CompilerM.withLocalDecl`**（ステップ 1055 件目）。ステップ末尾の `kwalk hb` 行が出ず、runTac の失敗も出ていない（heartbeat の例外は握りつぶされず上に抜ける）。同じ頭の step はそれ以前に成功している。なので「どの withLocalDecl か（束縛する型・継続の形）」で何かが異なる。**この調査では、その step の中のどの `apply`/`unify` が止まっているかまでは見つからなかった**。Dbg（`kwalk wld`）で、止まる `withLocalDecl nm ty k` は束縛名・型が `nm✝` / `ty✝`（match の変数）、プログラム `p` の approxDepth は 8 と小さい（継続 `k` が巨大で whnf に落ちる、という仮説は、この 1 件では支持されない。`applyRule` の大ゴール除外も効かなかった）。止まる場所は step の最初の分岐（`ty.isForall`、join point の `have`、`isHeadBetaTarget`）か `.const` 側の `Bind` 以外の規則のどれかで、step 内の部分ごとの heartbeat は未計測。
* **次の rt の候補**: (a) その withLocalDecl step の `p` の引数（型 `ty` と継続 `k`）を Dbg で出して、規則 `withLocalDeclPK` の `apply` の単一化が `k` の beta/whnf に落ちていないか確かめる（`withLocalDeclPK` の `k` を `fun x => ?_` でなく、`refine withLocalDeclPK … (fun _ _ _ x => ?_)` の形の専用 step にする）、(b) `framedNM` の試行を、頭が `liftM` / `monadLift` で引数が `FramedNM` の構成子に当たると分かる場合だけにする（`constructor` を使わず、`FramedNM` の各構成子に対応する `exact` の候補を直接並べる）、(c) 本体を腕ごとの別補題に分ける（`Elab 6930-7985` を `handleSynthesize…` ごとの `let rec` ではなく、モジュール境界で）— ただし本体は 1 つの定義なので、腕を別定理にするには腕の型を `Rec.translateExprToWireImpl` の `match` から取り出す補題（`unfold` 後の部分項の抽出）が要る。

**Induct2 は BUILT**（`Tools/ShippingGen4KWalkLegacyInduct2.lean`、lakefile 登録、`kjob lake build` exit 0、33 秒、`#print axioms` は `synthesizeChild_depthKL2` / `topEntry_KL2` / `topEntry_K_of_family2` とも propext / Classical.choice / Quot.sound のみ）。`hImpl : ∀ D ≠ 0, ChildEntryK … → LegacyImplK …` を仮説として取る形なので、`LegacyImplK` 自体の証明（H11）が済むまで、`topEntry_K_of_family` から LegacyImplK を外した版にはならない。組立て・Check は未着手（H11 が通っていないため）。MsgMvK 以外の新しい仮説は出ていない。

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## rt180: LegacyImplK その 7（base b2efa8c0。新しい仮説・law・家族の文なし。sorry・axiom・native_decide なし。Elab.lean 未編集）

**H11 が通った（BUILT）。本体を腕ごとに分ける必要はなかった。** `kjob lake build Tools.ShippingGen4KWalkLegacyH11` exit 0、H11 本体 8.6 秒、ビルド全体 42 秒、最大 RSS 3.8 GB。`#print axioms legacyImplKcore` は propext / Classical.choice / Quot.sound のみ。

**OOM の原因（この調査で特定）**
* `ulimit -v 20000000` では Lean が動かない（`failed to create thread`、H10a で確認）。代わりに、子プロセス木の RSS を 1 秒ごとに見て上限を超えたら自分の process group だけを kill する guard（スクリプトはスクラッチパッド、ソースツリー外）を使った。H10a は guard 下で exit 0（最大 4.0 GB）。
* 歩き（kloop）は 1500 step 前後で **未解決ゴール 0 で終わる**。その間の RSS は 1.7〜1.8 GB で増えない（`KWALK_TRACE` で step ごとに /proc/self/statm を記録）。つまり heartbeat・step 数・KWALK_DEBUG の出力ではなかった。
* 歩きの後、タクティクブロックの証明項の `instantiateMVars` で RSS が 5 GB → 20 GB 超（guard が kill）。`debug.skipKernelTC` と linter 停止では変わらない（kernel でも linter でもない）。
* 原因: do 記法の join point を `(fun jp hj => body) v hv` の beta-redex としてゴールに割り当てていたため、`instantiateMVars` が beta 簡約で `v`（継続全体）を `body` 中の `jp` の使用箇所ごとにコピーした（join point が入れ子で指数的）。
* 対処（Tac2 の変更、law なし）: join point と事実を **let 束縛**（`let jp := v; let hj := hv; body`、`withLetDecl` + `mkLetFVars`）にする。これに合わせ `runTac` を `zetaDelta := false` で動かす（let 束縛の `jp ?u =?= jp ()` を展開させない）。ほかに: `Except.rec` の一般の場合（主引数がコンストラクタなら iota、fvar なら `cases` して各腕を歩く。腕が `pure` でなくてもよい。これが未解決ゴール 1 件の原因で、既定の "unsolved goals" の表示がゴール全体（do ブロック）を整形して 20 GB を使っていた）、`kwalkS`（歩き終わりに未解決ゴールがあれば短いメッセージ［先頭 5 つの head と depth］で失敗する。H11 の `kwMain` で使用）、`KWALK_TRACE=パス`（step ごとの head・depth・RSS を追記）。
* 腕ごとの別補題・別モジュールには**していない**（原因が項の組立てだったため不要になった）。腕ごとの時間・メモリの測定は行っていない（本体 1 つで 8.6 秒・3.8 GB）。

**再ビルド（Tac2 変更後、guard 下）**: H10b（H1〜H10a、H8d を含む依存）、H11、Induct2（Final の依存として）、Final、Check がすべて exit 0。

**LegacyImplK を外した版**: `Tools/ShippingGen4KWalkLegacyFinal.lean`（BUILT）
* `legacyImplK_of_entry M hmsg hS hchild : LegacyImplK O I`（`legacyImplKcore` と `ppMvK_of M` から）。
* `topEntry_K_of_family3 M hmsg hA declName`（Induct2 の `topEntry_K_of_family2` に `hImpl := fun D _ hEntry => legacyImplK_of_entry M hmsg (stableK_KWD O MemoKeysInChild D) hEntry` を渡す）。**型の仮説は `MsgMvK` だけ**（と家族 `M`、`AdmCtx`）。
* 新しい仮説・law・家族の文は増えていない。axioms: propext / Classical.choice / Quot.sound。

**Check**: `Tests/Gen4/KWalkLegacyFinalCheck.lean`（BUILT、787 jobs）KWALKLEGACYFINAL CHECK: TYPE 2/2 / MUTANT 5/5（signature/defeq での棄却で意味的反例ではない）/ AXIOMS 2/2 / CLOSURE 2/2 clean（+2 陽性対照）。閉包の仮説様の定義: `topEntry_K_of_family3` は 型 [MsgMvK] / 閉包 [LogMvK, LegacyImplK, PpMvK, MsgMvK, LegacyCachedK, ChildEntryK]（`LogMvK` と `PpMvK` は家族から導かれたもの、`LegacyImplK` と `ChildEntryK` は `legacyImplK_of_entry` と深さ帰納の中で証明されたもので、型には現れない。`LegacyArmD` は閉包に無い）。

**残り**: `MsgMvK`（Elab.lean 6605 の `msgToString`）は仮説のまま（これが FG 受入の残り。新しい仮説ではなく、指示どおりの唯一の仮説）。clean build は coder。

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。`MemoFamily` を使う K walk 全体の受入は `MsgMvK` が閉じるまで起きない。
