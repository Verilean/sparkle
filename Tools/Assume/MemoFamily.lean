import Tools.ShippingChildFresh
import Tools.ShippingChildBndCore
import Tools.ShippingChildKeeps
-- BUILT: kjob lake build Tools.Assume.MemoFamily exit 0 (part of the 756-job Tests.Gen4.MemoFamilyCheck build) (rt173, source as of 155e13c4). Clean build is the coder's.
-- TRUSTED: hypotheses about the RUNTIME behaviour of the memo / child-cache / depth cells and of the profile / stderr / printer calls
-- (`@[extern]` opaque `ST.Ref.get/set/modify`, `lean_st_ref_*`, file and stream I/O); they are NOT proved and NOT axioms: `MemoFamily` is a
-- `structure` passed as a HYPOTHESIS (R-1: one ledger row, `M4.MEMO-01`). The family is not claimed true of the runtime,
-- and not claimed consistent with `Laws` (ledger D.E-10 stays OPEN).
-- Frozen type: scripts/gen4/MEMO_FAMILY_FREEZE.md rev3 at c595b472 (section 2), 15 statements:
--   frame, frameCacheSet, frameDepthSet, memoGet, memoSet, memoModify, frameCacheModify, frameDepthModify,
--   logProf, stderrLine, printersMv, and MemoTele (telescope, lamTelescopeT, localDecl, letDecl).
-- The rev2 `lamTelescope` (Keeps form) is the derived theorem `MemoTele.lamTelescope` (same name, same type).
-- Nothing here changes `Laws`, T1Hyp, T1HypND or any shared definition. No `sorry`, no `axiom`, no `native_decide`.
-- Types copied verbatim from the freeze section 2 code block.

namespace Tools.Assume.MemoFamily
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildFresh

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

end Tools.Assume.MemoFamily
