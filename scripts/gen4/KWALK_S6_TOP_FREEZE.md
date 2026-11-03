# K walk S6 続き: 最外の入口（depth 0）の KWD 版（rt171）— 型の freeze

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。新しい前提・law・TRUSTED 境界は無い（承認済み S6 の文の中の単位。review には出さない）。
新規ファイル `Tools/ShippingGen4KWalkDepthTop.lean`（`DepthInduct` を import）。MemoFamily は仮説 `M` として取るだけ。

```
-- リセット前後の部品（dv = 0 を通す）
triple_memoResetD   : Triple (KWD O P 0) (sparkleSubModuleCache.set {}) (fun _ => KWD O (fun m _ => m = {}) 0) R
triple_childResetD  : (hP : ∀ m c c', P m c → P m c') → Triple (KWD O P 0) (sparkleChildCache.set v) (fun _ => KWD O P 0) R

entryTop_windowD (hlog : LogMvK O) translate declName
  (hbody : 0 < sparkleSynthDepthLimit → ∀ b env ci isInst,
     Triple (KWD O MemoKeysInChild 1) (synthesizeFromConst (translate env) (profLogIO b) declName [] false true ci isInst)
       (fun _ => KWD O (MemoKeysExc declName) 1) (fun e w => KWD O MemoKeysInChild 1 w ∧ OkExc e)) :
  Triple (fun w => KW O (fun _ _ => True) w ∧ dv w = 0) (synthesizeCombinationalCoreWith translate declName [] false true)
    (fun _ => KWD O (MemoKeysExc declName) 0) (fun e w => KW O (fun _ _ => True) w ∧ OkExc e)

topEntry_K (M) (hlog : LogMvK O) (hImpl : ∀ D ≠ 0, LegacyImplK O (KWD O MemoKeysInChild D)) (hleg : ∀ D ≠ 0, LegacyArmD O D) env declName :
  Triple (KW True ∧ dv = 0) (synthesizeCombinationalCoreWith (fun env e h t n => translateExprToWire env e h t n) declName [] false true)
    (成功: KWD (MemoKeysExc declName) 0 = K_declName) (失敗: quiet ∧ sv = some synthesizeChild ∧ OkExc)
```
仮説は LogMvK / LegacyImplK / LegacyArmD の 3 つだけ（Check の CLOSURE で確認する）。hbody は `synthesizeChild_depthK` (D = 1) と `fromConst_frontends_windowD` から `child_step` と同じ形で作る。
Check は signature/defeq での棄却で、意味的反例ではない。
