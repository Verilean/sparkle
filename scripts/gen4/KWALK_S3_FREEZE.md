# KWALK_S3_FREEZE: S3 (T4 fallback と handler の K 版) の完全な型

Status: freeze（Lean 実装の前）。base 77cb38f3（kjob/rt166）、branch kjob/rt167。
台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**前提を増やさない単位**: 承認済みの `MemoFamily`（仮説 `M`）の中で、`FallbackA`（616 行）を `StableK` で写すだけ。
新しい law / TRUSTED 境界 / axiom / `Laws` の変更 / FG の縮小 / GenWF の強化は無い。reviewer の承認が要る freeze ではない（分担 §14）。

## 1. 規則（A 版 → K 版の機械的な写し）

| A 版（`Tools/ShippingChildFallbackA.lean`） | K 版（新規ファイル） |
|---|---|
| `(O) (hA : AdmCtx O.quiet mctx cctx) (hS : StableA O.quiet I)` | `{O} (M : MemoFamily O) (hA : AdmCtx O.quiet mctx cctx) (hS : StableK O.quiet I)` |
| `makeWireP O hA hS` / `addInputP` / `emitRegisterA` / `emitMemoryA` | `makeWirePK M hA hS` / `addInputPK` / `emitRegisterK` / `emitMemoryK`（S1、BUILT） |
| `cacheLookupValidatedA` / `recordTranslationA` | `cacheLookupValidatedK` / `recordTranslationK`（S1、BUILT） |
| `keepsA_framed O hA hS (FramedA.X)` | `keepsK_framedNM M hA hS (FramedNM.X)`（`FramedNM` に `sideGet/sideModify .singleOut/.subInstOut` がある） |
| 法則なしの `emitAssignP` / `emitInstanceA` / `addModuleToDesignA` / `freshNameA` / `lookupVarP` / `emitRegisterStmtA` | そのまま再利用（`I` について一般） |
| `RecA O I rec` | `RecK O I rec`（S2、BUILT） |
| `LegacyImplA` / `LegacyCachedA` / `CanonKeyA` / `ProjFieldNameA` / `ChildEntryA` | 同じ形の `…K` 述語。**定理の仮説**として取る（前提ではなく、各 handler の未証明の部分。証明したものは一覧に残す） |

## 2. 型（ファイル別。名前は A 版の `A` → `K`）

ファイル 1 `Tools/ShippingGen4KWalkEmit.lean`（emitters + rec 腕）:
`emitBoolResultK / emitCompareResultK / emitBoolLiteralK / emitCastResultK / emitSliceResultK / emitMuxResultK / emitConcatConstK / translateConcatActsK`、
`translateMuxWithK / translateBoolBinaryK / translateSignalCompareK / translateAppCompareK / translateAppBoolBinaryK / translateAppBool2K / translateAppBoolK / translateBoolUncachedWithK / translateVectorMuxUncachedWithK / translateSetWidthUncachedWithK / translateSliceUncachedWithK / translateSliceFUncachedWithK / translateConcatUncachedWithK / translateConcatLitUncachedWithK / translateRegisterUncachedWithK / translateRegisterEnableUncachedWithK / translateLoopRegisterUncachedWithK / translateCircuitDoUncachedWithK / translateCircuitDo2UncachedWithK / translateMemoryUncachedWithK / instArgsK`。
全て `KeepsCP mctx mref cctx cref I (<program>)` の形（`<program>` は A 版と同じ Elab 定義、仮説に `hrec : ∀ e hint top named, KeepsCP … I (rec e hint top named)`）。

ファイル 2 `Tools/ShippingGen4KWalkInst.lean`（wrapper + instance + telescope 腕）:
`translateControlCachedWithK`、`instArmCacheGetK / instArmCachePutK / instArmOutGetK / instArmOutPutK`（`Keeps … I`）、`instAddModulesK / instRegisterChildK / instClkRstK / instOutWiresK`、`instArityCheckK / instLinkCheckK / instCallKeyK`（`hcanon` 仮説）、
`translateInstanceUncachedWithK`、`translateProjInstanceUncachedWithK`、`translateInstanceOrFallbackK`、`projFieldNameK`（telescope 腕: `forallTelescopeReducing` を `M.tele.telescope` で。`getConstInfoInduct` 等は `FramedNM.constInfo/env` の範囲で試す。閉じなければ止まった goal を KWALK_PLAN §3 に書く）。

ファイル 3 `Tools/ShippingGen4KWalkFallback.lean`（組立て）:
`translateFallbackK : (M) (hS : StableK O.quiet I) (tenv) (hImpl hCached hcanon hpf hchild : …K) (rec) (hrec : RecK O I rec) : RecK O I (translateFallback tenv rec)`、
`translate_keepsK : RecK O I (fun e h t n => translateExprToWire tenv e h t n)`（S2 の `translateK_of_fallback` を使う）。

## 3. 各ファイルの Check（`Tests/Gen4/KWalkFallbackCheck.lean` 他）

TYPE（`readOf`/`KeepsCP` で別に書いた Expected と defeq）、MUTANT（signature/defeq での棄却。意味的反例ではない）、AXIOMS（標準のみ）、CLOSURE（`Laws` / `T1Hyp` / `T1HypND` が閉包に無い、陽性対照付き）。

## 4. 止まる条件

新しい前提・law が要る腕（`MemoFamily` の文の追加、`FramedNM` 構成子の追加など）に当たったら、その腕を明記して止まり coder に報告する。家族に文は足さない。
`LegacyImplK`（`Rec.translateExprToWireImpl`）は A 版でも未分解の仮説で、本 S3 でも同様に**仮説のまま**（証明済みとは書かない）。
