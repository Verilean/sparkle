# KWALK_S6_FREEZE: 深さ帰納（dv つき不変量、hchild / hbody / htr を同時に閉じる）— 型の freeze

Status: freeze（前提を増やさない単位。review に出さない。共通ルール 14）。base 3f4fc792、作業 kjob/rt170。
台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。新しい law・家族の文・TRUSTED 境界は無い。残る仮説は LogMvK / PpMvK / hlegacy / LegacyImplK のみ（指示どおり）。MemoFamily は仮説 `M`。
「読んだ」= 私の読み。mutant は signature/defeq での棄却で意味的反例ではない。

## 1. 不変量
```lean
def KWD (O) (P) (D : Nat) (w) : Prop := KW O P w ∧ dv w = D        -- KD = KWD O MemoKeysInChild D、KDX n = KWD O (MemoKeysExc n) D
theorem stableK_KWD : StableK O.quiet (KWD O P D)
```
## 2. 部品（Tools/ShippingGen4KWalkDepth.lean）
`triple_memoInsertD`（KWD K D → KWD K_n D）、`triple_childInsertD`（窓を閉じる、dv 保存）、`triple_depthSetD`（D → v）、`triple_depthModifyD`（D → f D）、`tripleK_depthGetD`、
`fin_totalD`（KWD P (D+1) → KWD P D、投げない）、`tryFinallySplit2`（成功と失敗の fin の事後条件を別にする）。
## 3. 腕と入口（DepthArms / DepthEntry）
```lean
fromConst_frontends_windowD : (htr : ∀ e hint top named, KeepsCP (KWD K D) (translate ..)) (hchild : ∀ c, Keeps (KWD K D) (synthesizeChild c)) (hlegacy : certifiedShape? = none → mixedCertifiedShape? = none →
   Triple (KWD K D) (synthesizeFromConst translate (profLogIO b) n [] false false ci isInst) (KWD K_n D) (KWD K D ∧ OkExc)) →
   Triple (KWD K D) (synthesizeFromConst translate (profLogIO b) n [] false true ci isInst) (fun _ => KWD K_n D) (fun e w => KWD K D w ∧ OkExc e)
entryNested_windowD (D ≠ 0) (hbody : D < sparkleSynthDepthLimit → ∀ b env ci isInst, Triple (KWD K (D+1)) (synthesizeFromConst (translate env) ..) (KWD K_n (D+1)) (KWD K (D+1) ∧ OkExc)) :
   Triple (KWD K D) (synthesizeCombinationalCoreWith translate n [] false true) (KWD K_n D) (KWD K D ∧ OkExc)
combWith_nestedD / synthesizeChild_windowD (Triple (KWD K D) (synthesizeChild n) (fun _ => KWD K D) (KWD K D ∧ OkExc))
entryTop_windowD : 最外の入口（depth 0）の hbody は KWD K 1。
```
## 4. 帰納（DepthInduct）
測度は `sparkleSynthDepthLimit - dv`（予算 k、`limit ≤ D + k`）。`Child k := ∀ mctx cctx, AdmCtx → ∀ D ≠ 0, limit ≤ D + k → ∀ n, Triple (KWD K D) (synthesizeChild n) ..`。
Child 0 は D ≥ limit で入口が throwError（K のまま失敗）。Child (k+1) は、入口の本体を D+1 で歩き、`htr := translate_keepsK`（I = KWD K (D+1)）、`hchild := Child k`（`childSynthEntry` は `sparkleChildSynth.get` 後に `synthesizeChild`）、`hbody := fromConst_frontends_windowD` から得る。
仮説: `LogMvK`、`PpMvK`（LegacyImplK の中）、`hlegacy : ∀ D ≠ 0, …`、`LegacyImplK O (KWD K D)`（D ≠ 0）。`LegacyCachedK` は `legacyCachedK_of_impl` から導く。

## 5. Check（Tests/Gen4/KWalkDepthCheck.lean）
TYPE / MUTANT（窓の dv を落とした型、予算を外した型は棄却。signature/defeq での棄却）/ AXIOMS / CLOSURE（LogMvK・PpMvK が閉包に入る）。

## 6. 追記（rt170、実装後。台帳の差分は 0 のまま）
* 型は §3 の案のとおりに BUILT。`child_step`（1 段）、`child_budget`（予算 k）、`synthesizeChild_depthK`（見出し）。`hlegacy` は `LegacyArmD O D`（実 translator `translateExprToWire env` を固定、`D ≠ 0`、`AdmCtx` つき）として取った。
* 追加: `memo_miss_of_child_miss` / `memo_miss_of_child_miss_KWD` / `tripleK_cacheGetD` / `childMiss_memoMiss`。
* `PpMvK` は帰納の閉包に入らない（`hleg` / `hImpl` の中身で使う）。残る仮説は `LogMvK`、`LegacyImplK`（D ≠ 0 ごと）、`LegacyArmD`（D ≠ 0 ごと）だけ。
