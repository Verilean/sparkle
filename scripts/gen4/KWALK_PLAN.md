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
| S2 | T3: `translateStepWith`/`Core`/fuel、T5 | 未着手 | 150-250 |
| S3 | T4: fallback と handler（A 版 FallbackA 616 + WalkA 873 に相当） | 未着手 | 1000-1500。**不確実が最大**。既存の `kwalk` タクティク（`Tools/ShippingChildKWalk.lean`、`KeepsCP` について I に一般）が使える見込みだが、使えるかは試していない |
| S4 | E6/E5: 入口の腕（certified / mixed / machine / legacy）と窓の開閉 | 未着手 | 400-600 |
| S5 | E2-E4/E7: 入口の前置き、リセット、深さ、`try/finally`、窓の中 | 未着手 | 300-400 |
| S6 | E1/E8: `synthesizeChild`、深さ帰納、`memo_miss_of_child_miss` への接続 | 未着手 | 200-300 |
| 合計 | | | 約 2300-3400（PARAM_INV_ESTIMATE §3.4 の 3500-5000 より小さい見込みだが、同じく推定で実測ではない） |

順序: S1 → S2 → S3（S3 が最大。ここで `StableK` の穴が出るなら早く分かる）→ S4 → S5 → S6。S1 は新ファイル `Tools/ShippingGen4KWalkPrims.lean`、S3 は handler ごとに分ける（`maxHeartbeats` の引き上げが要る前例: `ParamEntry:215`）。
各ファイルの build は `kjob lake build` を 1 つずつ。120 分に収まらない build は coder に頼む。

**`StableA` が使えない件（見積りに効く）**: 既存 A-walk の原始操作（`makeWireA` など）は `hS : StableA O.quiet I`（`ShippingChildVCA.lean:46`）を取る。`StableA` の移送条件は `cv/sv/dv` だけで、K は `mv` に依存するので `StableA O.quiet (KW O P)` は一般に成り立たない（`mv` が違う世界を区別できない）。
共有定義は触れないので、K 版の `StableK`（移送条件に `mv w' = mv w` を足す。`keeps_KW_framedNM` の `kw_transfer` が同じ形）と、それを取る原始操作の写しを新ファイルに作る。補題の証明は A 版と同形で、`hS.2` の呼び出しに `frame` 由来の `mv` の等式を足すだけの見込み（読み。未試行）。

## 4. 前提を増やさないことの確認と、止まる点

* 土台は `MemoFamily` を仮説に取るだけ。`Laws` / `T1Hyp` / `T1HypND` は閉包に入らない（Check CLOSURE）。新しい law・TRUSTED 境界・FG/保証の変更は無い。FG の縮小も GenWF の強化も無い。台帳の差分 0。
* **(a) 窓の中で例外が出ないこと**（E7）。memo に `n` を書いてから child cache に `n` を入れるまでの間に例外が出ると、`catch` の先で K が崩れる（memo に `n` があり child cache に無い → その後の `synthesizeChild n` が memo hit する）。窓の中の効果は、純粋な後処理、`finally` の `set`/`modify`、`IO.getEnv`。
  `ref` の `get/set/modify` が投げないことは既存の `refGet_runs`/`refSet_runs`/`refModify_runs`（ShippingChildInv:690-）で足りる。
  **(a) の IO.getEnv 部分は解決（窓の中のその他の効果の「投げない」は §2 E7 の通り FramedNM の枠で扱い、ここで新たに示したのは IO.getEnv だけ）（rt165、`Tools/ShippingGen4KWalkEnv.lean`、BUILT）**: `Tools.ShippingGen4KWalkEnv.ioEnv_runs : ∀ n w, ∃ a w', RunsTo (IO.getEnv n : MetaM (Option String)) mctx mref cctx cref w a w'`（axioms は標準のみ、sorry なし）。
  根拠: toolchain v4.32.1 の `IO.getEnv` は `@[extern "lean_io_getenv"] opaque getEnv (var : @& String) : BaseIO (Option String)`（`Init/System/IO.lean:951`、ビルドが使う版で確認）。
  `MetaM` への持ち上げは `BaseIO.toEIO`（`Init/System/IO.lean:71`: `fun s => match act s with | .mk a s => .ok a s`、`.ok` のみ）を通る。証明は `refGet_runs` と同形: `IO.getEnv n w` を `cases` して `ST.Out.mk a w'` に分け、持ち上げの定義を `change` で展開し `rw`。
  `@[extern]` の本体は見ていない（opaque のまま）。`BaseIO` の型が「エラーの場合が無い」ことだけを使うので、外部実装には依存しない。
  したがって家族に 1 文足す必要は無く、新しい TRUSTED 文・前提は無い。Check ファイルは作っていない（定理 1 つ、`#print axioms` を同ファイルに置いた）。
  なお `Core.liftIOCore (IO.getEnv n).toEIO` の形（`IO.toEIO` 経由で例外を作る版）は証明していない: 窓の中の呼び出し（Elab.lean:5602、`(← IO.getEnv ..)` を `MetaM` で書いた形）は上の `liftM (IO.getEnv n)` の形で、`FramedNM.ioEnv` の型もこの形。
* (b) 深さ 0 の入口は、最後に top の名前 `n` を memo に書いて K_n で終わり、K に戻らない（child cache への挿入がない）。この後に翻訳器のコードは走らない（read）ので消費者は影響を受けないが、`EntryK` を深さ 0 に使わないこと（深さ 0 は E3 から始める別の文にする）。
* (c) `memo` の中身（pair が `PairPF` か）は扱わない。K は key だけの不変量で、内容の不変量は案 A（`RefLawsM`）の領分であり、本 walk は案 B（hit を除く）。
* (d) `outer_miss`（`Tools/ShippingLegacySemMemoWalk.lean:495`）の述べ直しは別単位（AdmCtx/quiet 制限下）。

## 5. 限界

* 土台のみ証明。翻訳器の段（§2 の T1-T6、E1-E8）は**全て未証明**で、行数は推定。
* mutant は signature / defeq での棄却で、意味的反例ではない。家族の真偽・`Laws` との無矛盾は主張しない。
* Elab.lean の行番号は base のもの。§2 の「read」は私の読みで Lean では確認していない。
