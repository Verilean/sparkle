# MEMO_FAMILY_FREEZE (rev2): 型の freeze — memo 法則家族 `MemoFamily`（12 文、`Laws` とは別の 1 構造、数え方 R-1）

状態: **rev2（reviewer の changes requested への改訂。rev1 = a7d2d345）。freeze 提案（文書のみ）。reviewer の承認まで Lean 実装（Tools/ 以下）には進まない。** 本単位で Lean のソースは編集していない（scratch の elaborate のみ、scratch はソースツリーに残していない）。
根拠: ユーザー判断 2026-11-03（`git show par/m4-decision:scripts/gen4/M4_DECISION.md` §7: 項目 3 = 案 C、数え方 R-1）。base = par/memo-freeze = 13562271（`scripts/gen4/MEMO_FAMILY_PROPOSAL.md`、reviewer が設計資料として承認）。
台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。受理待ち・見込みは §6 の「条件付き台帳」に分けて書く。
用語: **elaborated** = `kjob lake build`（scratch）exit 0。**read** = 私の読みで Lean は通していない。mutant は **signature/defeq での棄却** であって意味的反例ではない。「見つからなかった」は「この調査では見つからなかった」の意味で、不可能・導出不能とは書かない。

## 0. rev2 で直した点（reviewer の指摘ごと）

| 指摘 | rev2 の扱い |
|---|---|
| 1. `memoModify_of_get_set` は論理上は導けるが、`ST.Ref.modify` の実装（`Ref.modifyUnsafe` = `take; set`）と論理定義（`get; set`）が実際の動作で同じか未確認 | **選択肢 (B) を採る**（推奨どおり）。(A) を採らない理由は §1.3。論理上の導出は事実として §1.2 に残すが、**文の削減根拠には使わない** |
| 2. compiler は memo / child cache / depth の更新に modify を使う | §1.4 に modify 箇所をファイル・行で数えた（memo 4、child cache 1、depth 1、計 6）。get/set しか使わない cell には modify の文を足していない（§1.4 末尾） |
| 3. 実行時の振る舞いを TRUSTED law として固定するなら、論理の modify_split だけでは law を落とす根拠が足りない | `memoModify` を**家族の文に戻し**、`frameCacheModify` / `frameDepthModify` を**追加**。家族は 9 → **12 文**（§2）。完全型・消費者表（§3）・mutant（§5）・Check（§8）を更新 |
| 4. R-1（1 家族 = TRUSTED 1 行）の維持 | 維持（§6）。文数は 12 だが台帳上は `M4.MEMO-01` 1 行のまま |

## 0.1 結論（rev2）

1. 家族は **12 文**: `frame` / `frameCacheSet` / `frameDepthSet` / `memoGet` / `memoSet` / `memoModify` / `frameCacheModify` / `frameDepthModify` + `tele`（`MemoTele` の 4 文）。rev1 の 9 文に `memoModify`・`frameCacheModify`・`frameDepthModify` の 3 文を足した。3 文は modify 呼び出しそのものの `RunsTo` について述べるので、論理側の `modify_split`（`get; set` への展開）には依存しない。
2. 家族は **新規ファイル `Tools/Assume/MemoFamily.lean`**（予定パス）に置く 1 つの `structure MemoFamily`。`Laws`（A.P-01 = T1L-01）・`Tools/ShippingGen2Defs.lean`・`RefLawsAOps` / `RefLawsATele` は **変えない**。`Laws` の第 3 field にはしない（案 D は採らない）。
3. 消費者は (a) parametric の K 不変量 walk と (b) fallback の memo hit（F-9 / `outer_miss`）。M3 の G-MEMO（T1L-25）は任意（現状は使わない）。表は §3。
4. 台帳 R-1: 家族 1 行（案 ID `M4.MEMO-01`）。**家族を使う証明が受入された時点で FG +1**。B.P-8 / B.P-1 の −1/−1 は F-θ / F-top / F-post / shape / assembly / F-kids が全部揃った場合だけ。§6。
5. 家族が真であるとも、`Laws` / `RefLaws` と無矛盾であるとも主張しない（`Laws` の同時充足は台帳 D.E-10 で OPEN のまま）。§7 の充足確認は `quiet = False` の自明モデルだけで、型の充足であって実行系についての証拠ではない。
6. scratch で 12 文の完全型を elaborate した（§2、§7）: `kjob lake build`（scratch、312 jobs）exit 0、`#print axioms vacuous_model` = propext / Classical.choice / Quot.sound、sorry なし。scratch はソースツリーに残していない。

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

## 2. 家族の完全な Lean 型

置き場所（予定）: `Tools/Assume/MemoFamily.lean`（新規。`lakefile.lean` に `lean_lib «Tools.Assume.MemoFamily»` を追加）。`import Tools.ShippingChildFresh`（`MkRefd`）と `import Tools.ShippingChildBndCore`（`cv sv dv`、`modify_split`）。名前空間 `Tools.Assume.MemoFamily`。**変えないもの**: `Laws`（`Tools/ShippingGen2Defs.lean:46`）、`RefLawsAOps` / `RefLawsATele` / `FramedA` / `SideRef`（`Tools/ShippingChildInvA.lean` / `ShippingChildInv.lean`）、`RefLawsM`（`Tools/ShippingMemoLaws.lean`、使わない）、T1Hyp / T1HypND / Elab*.lean。

elaborated した全文（scratch からの抜粋。`SideRefNM` / `FramedNM` / `MemoTele` は rev1 と同一。`namespace Scratch.MemoFamily` は予定パスでは `Tools.Assume.MemoFamily`）:

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

structure MemoTele (O : RefLawsAOps MkRefd mref cref) : Prop where
  telescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
  lamTelescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx O.quiet mctx cctx → (∀ w, I w → O.quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → mv w' = mv w → (O.quiet w → O.quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)
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
  tele : MemoTele O
```

leaf 数（文の数）: `frame` / `frameCacheSet` / `frameDepthSet` / `memoGet` / `memoSet` / `memoModify` / `frameCacheModify` / `frameDepthModify` の 8 + `MemoTele` の 4（`telescope` / `lamTelescope` / `localDecl` / `letDecl`）= **12**（数えた）。rev1 は 9。modify の 3 文の `RunsTo` は `ST.Ref.modify`（論理定義 `get; set`）の項で書かれ、`modifyUnsafe` で実行されることは `RunsTo` の定義には現れない（§1.3）。したがって 3 文は実行系についての仮定である（§2.1 の最後の列）。

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
| `tele`（`MemoTele` の 4 文: `telescope` / `lamTelescope` / `localDecl` / `letDecl`） | 束縛を開いて続きを実行し閉じる Meta の 4 つの補助関数（`forallTelescopeReducing` / `lambdaTelescope` / `withLocalDeclD` / `withLetDecl`）は、続きが不変量を保つなら、子キャッシュ・synth・depth に加えてメモ表も変えない限り不変量を保つ。 | Lean core の `Lean.Meta.forallTelescopeReducing` 等（`RefLawsATele`、T1L-01 の `Laws.T` と同じ種類の仮定に `mv w' = mv w` の条件を足したもの）。呼び出し側は `Elab.lean` の translator が使うこれらの補助関数。 |

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

mutant を作らなかった文: `frameCacheSet` / `frameDepthSet` / `memoGet` / `memoModify` / `frameCacheModify` / `frameDepthModify` / `tele`（同種の変更で棄却されるはずだが未実施。実施済みとは書かない）。

## 6. 台帳（R-1）

| 項目 | 内容 |
|---|---|
| 新 ID 案 | `M4.MEMO-01`（FG 側。T1 側へは数えない。T1L-25 は M3 が家族を採用しない限り不変） |
| 1 行 | `MemoFamily`（12 文）を 1 行。`Laws`（A.P-01 = T1L-01）とは別行 |
| FG +1 のタイミング | **家族を使う証明が受入された時点**（本 freeze の承認時点ではない） |
| 消えうる行 | B.P-8 −1、B.P-1 −1。F-θ / F-top / F-post / shape / assembly / F-kids が **全部揃った場合だけ**。F-kids 単独では 0 |
| 純差分（全部揃った場合） | +1 −2 = **−1**（条件付き） |
| 今回の台帳 | 台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0） |
| 条件付き台帳 | 条件付き台帳: M4.MEMO-01 +1（家族を使う証明の受入時）/ B.P-8 −1 / B.P-1 −1（全項目揃った場合のみ） |

文数で数える R-10 は +12、R-3 は +3 だが、ユーザー判断は R-1（1 家族 = 1 行）であり、rev2 でも 1 行のまま。R-3 / R-10 は採用しない。

## 7. 家族が矛盾しないことの確認方法

- **確認できたこと（elaborated、exit 0）**: `quiet = False`（`RefLawsAOps.quietFalse`、`Tools/ShippingChildInvA.lean:388`）の自明モデルで `MemoFamily` の 12 文がすべて充足する（rev2 で scratch 再実行、312 jobs exit 0）（全 field が `quiet w` の前提を取るため）。`theorem vacuous_model`、`#print axioms` = propext / Classical.choice / Quot.sound、sorry なし。これは **文の型が空でない（型として充足可能）** ことの確認であって、実行系について何かを言う証拠ではない。
- **確認できていないこと**: `quiet` が非自明なモデル（`ST.Prim.Ref.get/set` の実モデル）での充足。Lean の論理では `@[extern]` の opaque で、この調査では供給元・経路が見つからなかった。`Laws` との同時充足は台帳 D.E-10 で OPEN のまま。
- 実行系との整合の確認は、`Elab.lean` の書き込み箇所の read（§2.1 の行番号）と、MemoHitCensus（`Tests/Compiler/MemoHitCensusTest.lean`、観測）に限られ、証明ではない。

```lean
/-! Vacuous model: at quiet = False every statement holds (a satisfiability of the TYPE, not evidence about the runtime). -/
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
  tele :=
    { telescope := by intro _ _ _ I _ hIq _ _ _ _ w hw; exact False.elim (hIq w hw)
      lamTelescope := by intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
      localDecl := by intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
      letDecl := by intro _ _ _ I _ hIq _ _ _ _ _ _ w hw; exact False.elim (hIq w hw) }
```

## 8. 再現手順（reviewer 用）

1. `git show par/memo-freeze:scripts/gen4/MEMO_FAMILY_PROPOSAL.md` で §2 の元の 10 文案を読む。
2. 本文書 §1.2・§2 の Lean 抜粋を `Tests/Gen4/` の一時ファイルに貼り、`kjob lake build` する（import は `Tools.ShippingChildFresh` と `Tools.ShippingChildBndCore`）。`SideRefNM` / `FramedNM` の生成: `Tools/ShippingChildInv.lean` の `inductive SideRef` から `| subModule` 行を除き `SideRef` → `SideRefNM`、`Tools/ShippingChildInvA.lean` の `inductive FramedA` を `FramedNM` に改名し `SideRef r` → `SideRefNM r` に置換（constructor 数 23 / 40 を数える）。
3. 実装段階の Check（別単位）: 型の defeq 検査（12 文）、mutant（M1-M7）の signature/defeq 棄却、axioms、constant closure に `Laws` / `T1Hyp` / `T1HypND` を含まないこと。

## 9. 限界（やっていないこと）

- K 不変量、`framedA_cases`、`MemoFamily` を使う定理は未証明。
- rev2 は `modify` の 3 文を家族に持つので、8932 / 5577 / memo の 4 箇所を `set` の文へ帰着する証明は要らない（その代わり仮定が 3 文多い）。
- 実行側 `Ref.modifyUnsafe`（`take; set`）と論理側の定義（`get; set`）の同値は、仮定にも証明にもしていない。`modify` の 3 文は `ST.Ref.modify` の `RunsTo` について直接述べる（§1.3）。これらが実行系について真であることは主張しない。
- modify の 3 文は (A)（対応の証明）を示せなかったために置いた文であり、将来 (A) が示せれば減らせる可能性がある（その場合は別 freeze）。
- 家族の真偽・実行系との一致・`Laws` との無矛盾性は主張しない（§7）。
- ledger の C_M5dg / D_M5t2 は全行再読していない（PROPOSAL §5 のまま）。
- 本 freeze の承認は TRUSTED 境界 `MemoFamily` の追加の承認を含む。承認までは Lean 実装・仮定としての使用に進まない。

`台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）`
`条件付き台帳: M4.MEMO-01 +1（家族を使う証明の受入時）/ B.P-8 -1 / B.P-1 -1（全項目揃った場合のみ）`
