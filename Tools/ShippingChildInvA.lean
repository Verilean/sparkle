import Tools.ShippingChildBndCore
-- BUILT by the integrator: ba3 exit 0 (310 jobs; axioms standard, ax7) (round par/bnd3, base 204e857f): revision of the file built ba2 (exit 0, 310 jobs,
-- ax4). Isolated: no existing file uses it. No `sorry`, no `axiom`, no `native_decide`.
-- Revision (reviewer finding P1): every law AdmCtx licenses now also asks the START world quiet
-- (`quiet w →`), and the telescope family asks `∀ w, I w → quiet w`. `RefLawsAOps.quietFalse` /
-- `RefLawsATele.quietFalse` / `frame_quietFalse_vacuous` audit the degenerate `quiet = False`;
-- `oldFrame_covers_writer` records why the ba2 shape was wrong; `outQ_end` / `keeps_outQ` thread
-- the world premise to a consumer.
-- Design: docs/parallel/boundary-admissible.md.
-- Writing-time guesses (marked `-- guess:` below; G1-G4 were accepted by ba2):
--  G1 the callback type `Meta.Config → ConstantInfo → CoreM Bool` (Lean/Meta/Basic.lean:504 says
--     `Config → ConstantInfo → CoreM Bool` inside `namespace Lean.Meta`);
--  G2 applying a `CoreM` action to `cctx cref w` and matching `.ok _ w'`/`.error e w'` (as `endW` does
--     for `MetaM`);
--  G3 the `admCtx_*` lemmas close by `intro f hf; exact h f hf` (the projection of a record update
--     reduces definitionally);
--  G4 `intro` introduces the implicit binders `{mctx} {cctx} {α}` of the field types in `toAOps`;
--  G5 (new) `intro` counts in `quietFalse` / `toAOps` (one name per binder, incl. implicits; `intro`
--     unfolds `Keeps`/`AdmCtx`/`InertUnfold` to reach binders) and `False.elim hq` with
--     `hq : (fun _ => False) w` (beta by defeq);
--  G6 (new) `depthWriter`: `sparkleSynthDepth.set 41 : CoreM Unit` lifts (as in the probe
--     Tests/Compiler/CanUnfoldProbe.lean:49) and `{ mctx with canUnfold? := some depthWriter }`;
--  G7 (new) in `keeps_outQ`, `cases hm : p mctx mref cctx cref w` rewrites the `ErrOk` match in the
--     goal, and the `.ok`/`.error` arms close by `True.intro` / `exact` up to iota;
--  G8 (new) `some synthesizeChild` has type `Option (Name → MetaM Res)` (`Res` is an abbrev of
--     `Module × Design`, as `ShippingChildBalance.Out0` uses it).

/-! # The admissible-context boundary (isolated; `RefLaws` untouched)

`RefLaws`/`RefLawsCore` quantify `frame`, `excOk`, … over EVERY `Meta.Context`.
`Meta.Context.canUnfold?` is caller code run by `whnf`; probe cu2 (case W)
showed a run in which it changed `sparkleSynthDepth` inside `Framed.whnf`.
Here the laws are restricted to ADMISSIBLE contexts (`AdmCtx`: no callback, or
an inert one — a predicate on the callback, not assumed) AND to QUIET start
worlds, and the ref-taking local operations to refs with a provenance proof
(`FramedA Fresh`).

Why the start world must be quiet: `InertUnfold quiet f` only says the
callback is safe FROM quiet worlds. A law that asks `AdmCtx` but holds at every
world would, at `quiet := fun _ => False` (where every callback is
`InertUnfold`, `admCtx_quietFalse`), again claim the frame for the writing
callback of case W (`oldFrame_covers_writer`). With the `quiet w` premise the
degenerate `quiet = False` gives no consequences at all (`RefLawsAOps.quietFalse`,
`frame_quietFalse_vacuous`).

Relation to the old bundle: the operations laws (`RefLawsAOps`) FOLLOW from
the old ones (`RefLawsCore.toAOps`, proved). The continuation laws
(`RefLawsATele`) are a DIFFERENT assumption, NOT derived from the old ones
(`RefLawsCore.toA` takes them as an argument). -/

namespace Tools.ShippingChildInvA
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildBndCore

/-! ## Admissible contexts -/

/-- A `canUnfold?` callback is INERT for `quiet`: from a quiet world, every
run of it leaves the three tracked values and quietness, and an exception it
throws is in the class. A predicate on the callback, not an assumption. -/
def InertUnfold (quiet : Void IO.RealWorld → Prop)
    (f : Meta.Config → ConstantInfo → CoreM Bool) : Prop :=  -- guess: G1
  ∀ cfg info (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld),
    quiet w →
    match f cfg info cctx cref w with  -- guess: G2
    | .ok _ w' => cv w' = cv w ∧ sv w' = sv w ∧ dv w' = dv w ∧ quiet w'
    | .error e w' => cv w' = cv w ∧ sv w' = sv w ∧ dv w' = dv w ∧ quiet w' ∧ OkExc e

/-- **Admissible contexts**: the Meta context's `canUnfold?` callback, if any,
is inert. Nothing is asked of the Core context (audit in the design doc: its
only non-data field is the cancel token, which writes none of the three refs;
the interrupt exception's class is open item O-cancel). -/
def AdmCtx (quiet : Void IO.RealWorld → Prop) (mctx : Meta.Context) (_cctx : Core.Context) : Prop :=
  ∀ f, mctx.canUnfold? = some f → InertUnfold quiet f

variable {quiet : Void IO.RealWorld → Prop} {mctx : Meta.Context} {cctx : Core.Context}

theorem admCtx_none (h : mctx.canUnfold? = none) : AdmCtx quiet mctx cctx := by
  intro f hf; rw [h] at hf; exact absurd hf (by intro hc; cases hc)

/-! ### Preservation by the context updates the compile performs
(`withLocalDecl*`/`withLetDecl`/telescopes: `lctx`, `localInstances`;
`withTransparency`: `keyedConfig`; `withIncRecDepth`: the Core context). -/

theorem admCtx_lctx (h : AdmCtx quiet mctx cctx) (l : LocalContext) :
    AdmCtx quiet { mctx with lctx := l } cctx := by
  intro f hf; exact h f hf  -- guess: G3

theorem admCtx_localInsts (h : AdmCtx quiet mctx cctx) (li : LocalInstances) :
    AdmCtx quiet { mctx with localInstances := li } cctx := by
  intro f hf; exact h f hf  -- guess: G3

theorem admCtx_lctx_insts (h : AdmCtx quiet mctx cctx) (l : LocalContext) (li : LocalInstances) :
    AdmCtx quiet { mctx with lctx := l, localInstances := li } cctx := by
  intro f hf; exact h f hf  -- guess: G3

theorem admCtx_config (h : AdmCtx quiet mctx cctx) (c : ConfigWithKey) :
    AdmCtx quiet { mctx with keyedConfig := c } cctx := by
  intro f hf; exact h f hf  -- guess: G3

theorem admCtx_cctx (h : AdmCtx quiet mctx cctx) (cctx' : Core.Context) :
    AdmCtx quiet mctx cctx' := h

/-! ### Audit: `AdmCtx` is trivial at `quiet = False` -/

/-- **`AdmCtx` at `quiet = False` holds of EVERY context**, whatever its
callback: `InertUnfold` only constrains runs from quiet worlds, and there are
none. So `AdmCtx` alone restricts nothing; the restriction must come from the
start world being quiet (the `quiet w` premises of the laws below). -/
theorem admCtx_quietFalse (mctx : Meta.Context) (cctx : Core.Context) :
    AdmCtx (fun _ => False) mctx cctx := by
  intro f _ cfg info cctx' cref' w hw  -- guess: G5
  exact False.elim hw

/-- The writing callback of probe case W (`Tests/Compiler/CanUnfoldProbe.lean`,
case W): it changes `sparkleSynthDepth`. -/
def depthWriter : Meta.Config → ConstantInfo → CoreM Bool :=  -- guess: G6
  fun _ _ => do
    sparkleSynthDepth.set 41
    return true

/-- In particular a context carrying the writing callback is admissible at
`quiet = False`. -/
theorem admCtx_quietFalse_writer (mctx : Meta.Context) (cctx : Core.Context) :
    AdmCtx (fun _ => False) { mctx with canUnfold? := some depthWriter } cctx :=
  admCtx_quietFalse _ cctx

/-! ## Framed operations with provenance of local refs -/

/-- `Framed`, with every constructor that takes a caller-supplied ref of a
run-local type (`exprCache*`, `local*` other than `localMk`) asking a
provenance proof `Fresh σ r` (intended: `r` was allocated by an `IO.mkRef` of
this run). Every other constructor copied verbatim from
`ShippingChildInv.lean:189-258`. -/
inductive FramedA (Fresh : (σ : Type) → IO.Ref σ → Prop) : {α : Type} → MetaM α → Prop
  | cacheGet : FramedA Fresh (sparkleChildCache.get : MetaM _)
  | synthGet : FramedA Fresh (sparkleChildSynth.get : MetaM _)
  | depthGet : FramedA Fresh (ST.Ref.get sparkleSynthDepth : MetaM Nat)
  | sideGet {σ : Type} {r : IO.Ref σ} : SideRef r → FramedA Fresh (ST.Ref.get r : MetaM σ)
  | sideSet {σ : Type} {r : IO.Ref σ} (v : σ) : SideRef r →
      FramedA Fresh (ST.Ref.set r v : MetaM Unit)
  | sideModify {σ : Type} {r : IO.Ref σ} (f : σ → σ) : SideRef r →
      FramedA Fresh (ST.Ref.modify r f : MetaM Unit)
  | sideModifyGet {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) : SideRef r →
      FramedA Fresh (ST.Ref.modifyGet r f : MetaM β)
  | sideModifyGetIO {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) : SideRef r →
      FramedA Fresh (liftM (ST.Ref.modifyGet r f : IO β) : MetaM β)
  | sideGetIO {σ : Type} {r : IO.Ref σ} : SideRef r →
      FramedA Fresh (liftM (ST.Ref.get r : IO σ) : MetaM σ)
  | sideSetIO {σ : Type} {r : IO.Ref σ} (v : σ) : SideRef r →
      FramedA Fresh (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit)
  | sideModifyIO {σ : Type} {r : IO.Ref σ} (f : σ → σ) : SideRef r →
      FramedA Fresh (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit)
  | ioEnv (n : String) : FramedA Fresh (liftM (IO.getEnv n) : MetaM _)
  | constInfo (n : Name) : FramedA Fresh (getConstInfo n : MetaM _)
  | env : FramedA Fresh (getEnv : MetaM Environment)
  | fvarThrowUnknown {α : Type} (id : FVarId) :
      FramedA Fresh (liftM (id.throwUnknown : CoreM α) : MetaM α)
  | whnf (e : Lean.Expr) : FramedA Fresh (Lean.Meta.whnf e)
  | inferType (e : Lean.Expr) : FramedA Fresh (Lean.Meta.inferType e)
  | isClass? (e : Lean.Expr) : FramedA Fresh (Lean.Meta.isClass? e)
  | whnfUntil (e : Lean.Expr) (n : Name) : FramedA Fresh (Lean.Meta.whnfUntil e n)
  | instantiateForall (e : Lean.Expr) (ps : Array Lean.Expr) :
      FramedA Fresh (Lean.Meta.instantiateForall e ps)
  | mkLambdaFVars (xs : Array Lean.Expr) (e : Lean.Expr) (usedOnly usedLetOnly etaReduce
      generalizeNondepLet : Bool) (bi : BinderInfo) :
      FramedA Fresh (Lean.Meta.mkLambdaFVars xs e usedOnly usedLetOnly etaReduce generalizeNondepLet bi)
  | mkAppM (c : Name) (xs : Array Lean.Expr) : FramedA Fresh (Lean.Meta.mkAppM c xs)
  | unfoldDefinition? (e : Lean.Expr) : FramedA Fresh (Lean.Meta.unfoldDefinition? e)
  | reduce (e : Lean.Expr) (explicitOnly skipTypes skipProofs : Bool) :
      FramedA Fresh (Lean.Meta.reduce e explicitOnly skipTypes skipProofs)
  | metaGet : FramedA Fresh (get : MetaM Meta.State)
  | coreModifyTrace (f : TraceState → TraceState) :
      FramedA Fresh (liftM (modifyTraceState f : CoreM Unit) : MetaM Unit)
  | metaModify (f : Meta.State → Meta.State) : FramedA Fresh (modify f : MetaM Unit)
  | freshFVar : FramedA Fresh (mkFreshFVarId : MetaM FVarId)
  | monoMs : FramedA Fresh (liftM IO.monoMsNow : MetaM Nat)
  | mkExprCache (v : Lean.ExprStructMap String) :
      FramedA Fresh (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
  | exprCacheGet (r : IO.Ref (Lean.ExprStructMap String)) : Fresh _ r →
      FramedA Fresh (ST.Ref.get r : MetaM (Lean.ExprStructMap String))
  | exprCacheGetIO (r : IO.Ref (Lean.ExprStructMap String)) : Fresh _ r →
      FramedA Fresh (liftM (ST.Ref.get r : IO (Lean.ExprStructMap String)) : MetaM _)
  | localMk {σ : Type} (v : σ) : LocalRefType σ →
      FramedA Fresh (liftM (IO.mkRef v) : MetaM (IO.Ref σ))
  | localGet {σ : Type} (r : IO.Ref σ) : LocalRefType σ → Fresh σ r →
      FramedA Fresh (ST.Ref.get r : MetaM σ)
  | localSet {σ : Type} (r : IO.Ref σ) (v : σ) : LocalRefType σ → Fresh σ r →
      FramedA Fresh (ST.Ref.set r v : MetaM Unit)
  | localModify {σ : Type} (r : IO.Ref σ) (f : σ → σ) : LocalRefType σ → Fresh σ r →
      FramedA Fresh (ST.Ref.modify r f : MetaM Unit)
  | localGetIO {σ : Type} (r : IO.Ref σ) : LocalRefType σ → Fresh σ r →
      FramedA Fresh (liftM (ST.Ref.get r : IO σ) : MetaM σ)
  | localSetIO {σ : Type} (r : IO.Ref σ) (v : σ) : LocalRefType σ → Fresh σ r →
      FramedA Fresh (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit)
  | localModifyIO {σ : Type} (r : IO.Ref σ) (f : σ → σ) : LocalRefType σ → Fresh σ r →
      FramedA Fresh (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit)
  | exprCacheModify (r : IO.Ref (Lean.ExprStructMap String))
      (f : Lean.ExprStructMap String → Lean.ExprStructMap String) : Fresh _ r →
      FramedA Fresh (ST.Ref.modify r f : MetaM Unit)

/-- Every provenance-restricted operation is a `Framed` one: laws about
`Framed` restrict to `FramedA`. -/
theorem FramedA.toFramed {Fresh : (σ : Type) → IO.Ref σ → Prop} {α : Type} {p : MetaM α} :
    FramedA Fresh p → Framed p
  | .cacheGet => .cacheGet
  | .synthGet => .synthGet
  | .depthGet => .depthGet
  | .sideGet h => .sideGet h
  | .sideSet v h => .sideSet v h
  | .sideModify f h => .sideModify f h
  | .sideModifyGet f h => .sideModifyGet f h
  | .sideModifyGetIO f h => .sideModifyGetIO f h
  | .sideGetIO h => .sideGetIO h
  | .sideSetIO v h => .sideSetIO v h
  | .sideModifyIO f h => .sideModifyIO f h
  | .ioEnv n => .ioEnv n
  | .constInfo n => .constInfo n
  | .env => .env
  | .fvarThrowUnknown id => .fvarThrowUnknown id
  | .whnf e => .whnf e
  | .inferType e => .inferType e
  | .isClass? e => .isClass? e
  | .whnfUntil e n => .whnfUntil e n
  | .instantiateForall e ps => .instantiateForall e ps
  | .mkLambdaFVars xs e a b c d bi => .mkLambdaFVars xs e a b c d bi
  | .mkAppM c xs => .mkAppM c xs
  | .unfoldDefinition? e => .unfoldDefinition? e
  | .reduce e a b c => .reduce e a b c
  | .metaGet => .metaGet
  | .coreModifyTrace f => .coreModifyTrace f
  | .metaModify f => .metaModify f
  | .freshFVar => .freshFVar
  | .monoMs => .monoMs
  | .mkExprCache v => .mkExprCache v
  | .exprCacheGet r _ => .exprCacheGet r
  | .exprCacheGetIO r _ => .exprCacheGetIO r
  | .localMk v h => .localMk v h
  | .localGet r h _ => .localGet r h
  | .localSet r v h _ => .localSet r v h
  | .localModify r f h _ => .localModify r f h
  | .localGetIO r h _ => .localGetIO r h
  | .localSetIO r v h _ => .localSetIO r v h
  | .localModifyIO r f h _ => .localModifyIO r f h
  | .exprCacheModify r f _ => .exprCacheModify r f

/-! ## The restricted laws

Every field asks `AdmCtx` of the context AND `quiet w` of the start world: the
callback of an admissible context is only known safe from quiet worlds
(`InertUnfold`), so a law at an admissible context is only licensed there. -/

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- The non-continuation fields of `RefLawsCore`
(`ShippingChildBndCore.lean:102-160`), each with its context quantifier
restricted to `AdmCtx`, its world quantifier to quiet worlds, and `Framed`
replaced by `FramedA Fresh`. -/
structure RefLawsAOps (Fresh : (σ : Type) → IO.Ref σ → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) where
  quiet : Void IO.RealWorld → Prop
  diag : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), Diag p → ∀ w, quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w)
  frameT : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ quiet (endW mctx mref cctx cref p w)
  excOk : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), Op p →
    ∀ w e w', quiet w → p mctx mref cctx cref w = .error e w' → OkExc e
  frameQ : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), FramedA Fresh p → ∀ w,
    quiet w → quiet (endW mctx mref cctx cref p w)
  cacheSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → quiet w → quiet w'
  depthSetQ : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    quiet w → quiet w'
  frame : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), FramedA Fresh p → ∀ w, quiet w →
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w
  cacheSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → quiet w →
    cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w
  depthSet : ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → quiet w →
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = v

/-- The continuation-passing fields, restricted: the outer context is
admissible, the invariant implies quietness (`∀ w, I w → quiet w`, so `Keeps`
— which starts from an `I` world — only ever starts from quiet worlds), and
the continuation is asked to keep `I` ONLY in admissible contexts. NOT
derived from the old `RefLawsCore` fields (a different assumption). -/
structure RefLawsATele (quiet : Void IO.RealWorld → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) : Prop where
  telescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k)
  lamTelescope : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (e : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α) (cleanup : Bool),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k xs b)) →
    Keeps mctx mref cctx cref I (Lean.Meta.lambdaTelescope e k cleanup)
  localDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLocalDeclD n ty k)
  letDecl : ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}
    (I : Void IO.RealWorld → Prop), AdmCtx quiet mctx cctx → (∀ w, I w → quiet w) →
    (∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (quiet w → quiet w') →
      I w → I w') →
    ∀ (n : Name) (ty v : Lean.Expr) (k : Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) x, AdmCtx quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref I (k x)) →
    Keeps mctx mref cctx cref I (Lean.Meta.withLetDecl n ty v k)

/-- **The restricted bundle** `RefLawsA`: the RefLawsCore fields with every
context quantifier restricted to `AdmCtx`, world quantifiers to quiet worlds
(the telescope family: invariants implying quiet), and local refs to `Fresh`
ones. -/
structure RefLawsA (Fresh : (σ : Type) → IO.Ref σ → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) where
  ops : RefLawsAOps Fresh mref cref
  tele : RefLawsATele ops.quiet mref cref

/-- **Old ⇒ new for the non-continuation fields**: every `RefLawsCore` model
gives the restricted operations bundle (drop `AdmCtx` and the `quiet w`
premise, `FramedA.toFramed`). -/
def RefLawsCore.toAOps (C : RefLawsCore mref cref) (Fresh : (σ : Type) → IO.Ref σ → Prop) :
    RefLawsAOps Fresh mref cref where
  quiet := C.quiet
  diag := by intro _ _ _ _ p hp w hq; exact C.diag p hp w hq  -- guess: G4
  frameT := by
    intro _ _ _ _ p hp w hq
    exact ⟨(C.frameT p hp w).1, (C.frameT p hp w).2 hq⟩
  excOk := by intro _ _ _ _ p hp w e w' hq hm; exact C.excOk p hp w e w' hq hm
  frameQ := by intro _ _ _ _ p hp w hq; exact C.frameQ p hp.toFramed w hq
  cacheSetQ := by intro _ _ _ v w u w' h hq; exact C.cacheSetQ v w u w' h hq
  depthSetQ := by intro _ _ _ v w u w' h hq; exact C.depthSetQ v w u w' h hq
  frame := by intro _ _ _ _ p hp w _; exact C.frame p hp.toFramed w
  cacheSet := by intro _ _ _ v w u w' h _; exact C.cacheSet v w u w' h
  depthSet := by intro _ _ _ v w u w' h _; exact C.depthSet v w u w' h

/-- `RefLawsA` from a `RefLawsCore` model and the restricted continuation
laws (which the old fields do NOT imply: they ask less of the continuation). -/
def RefLawsCore.toA (C : RefLawsCore mref cref) (Fresh : (σ : Type) → IO.Ref σ → Prop)
    (T : RefLawsATele C.quiet mref cref) : RefLawsA Fresh mref cref :=
  ⟨Tools.ShippingChildInvA.RefLawsCore.toAOps C Fresh, T⟩

/-- The restricted continuation law is STRONGER than the old one at
admissible outer contexts and quiet-implying invariants: from the old premise
(continuation kept in every context) it concludes the old conclusion. -/
theorem RefLawsATele.telescope_old {q : Void IO.RealWorld → Prop} (T : RefLawsATele q mref cref)
    {α : Type} (I : Void IO.RealWorld → Prop) (hA : AdmCtx q mctx cctx)
    (hIq : ∀ w, I w → q w)
    (hI : ∀ w w', cv w' = cv w → sv w' = sv w → dv w' = dv w → (q w → q w') → I w → I w')
    (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α)
    (hk : ∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b,
      Keeps mctx' mref cctx' cref I (k xs b)) :
    Keeps mctx mref cctx cref I (Lean.Meta.forallTelescopeReducing ty k) :=
  T.telescope I hA hIq hI ty k (fun mctx' cctx' xs b _ => hk mctx' cctx' xs b)

/-! ## Audit: `quiet = False` gives no consequences -/

/-- **At `quiet = False` every restricted operations law is vacuous**: the
whole bundle is inhabited by `False.elim` on the start world's quietness, for
any `Fresh`, `mref`, `cref` (in particular at the writing callback's context,
which is admissible there by `admCtx_quietFalse_writer`). -/
def RefLawsAOps.quietFalse (Fresh : (σ : Type) → IO.Ref σ → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) :
    RefLawsAOps Fresh mref cref where
  quiet := fun _ => False
  diag := by intro _ _ _ _ _ _ _ hq; exact False.elim hq  -- guess: G5
  frameT := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  excOk := by intro _ _ _ _ _ _ _ _ _ hq _; exact False.elim hq
  frameQ := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  cacheSetQ := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  depthSetQ := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  frame := by intro _ _ _ _ _ _ _ hq; exact False.elim hq
  cacheSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq
  depthSet := by intro _ _ _ _ _ _ _ _ hq; exact False.elim hq

/-- Likewise the continuation laws at `quiet = False`: an invariant implying
`False` holds at no world, so every `Keeps` is vacuous. -/
theorem RefLawsATele.quietFalse (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : RefLawsATele (fun _ => False) mref cref where
  telescope := by
    intro _ _ _ I _ hIq _ _ _ _ w hw; exact False.elim (hIq w hw)  -- guess: G5
  lamTelescope := by
    intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
  localDecl := by
    intro _ _ _ I _ hIq _ _ _ _ _ w hw; exact False.elim (hIq w hw)
  letDecl := by
    intro _ _ _ I _ hIq _ _ _ _ _ _ w hw; exact False.elim (hIq w hw)

/-- **The `frame` field's statement at `quiet = False` is trivially true**
(stated verbatim as the field type with `quiet := fun _ => False`): no frame
consequence follows from it; the vacuity now sits in the start condition
`quiet w`, which a caller must supply. -/
theorem frame_quietFalse_vacuous (Fresh : (σ : Type) → IO.Ref σ → Prop) :
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type},
    AdmCtx (fun _ => False) mctx cctx →
    ∀ (p : MetaM α), FramedA Fresh p → ∀ w, (fun _ => False) w →
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w :=
  (RefLawsAOps.quietFalse Fresh mref cref).frame

/-- **Why the ba2 shape was wrong.** The ba2 `frame` field (`AdmCtx` premise,
NO `quiet w` premise), as a predicate of `quiet`. -/
def OldFrameA (quiet : Void IO.RealWorld → Prop) (Fresh : (σ : Type) → IO.Ref σ → Prop)
    (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx quiet mctx cctx →
    ∀ (p : MetaM α), FramedA Fresh p → ∀ w,
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w

/-- Under the ba2 shape, `quiet = False` + `AdmCtx` (trivial there) demands the
frame of `whnf` at EVERY world in the context carrying the writing callback
`depthWriter` — the run that probe case W shows changing `sparkleSynthDepth`.
So the ba2 field was again a claim about that run; the revised field is not
(`frame_quietFalse_vacuous`). -/
theorem oldFrame_covers_writer {Fresh : (σ : Type) → IO.Ref σ → Prop}
    (h : OldFrameA (fun _ => False) Fresh mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    (e : Lean.Expr) (w : Void IO.RealWorld) :
    let m' := { mctx with canUnfold? := some depthWriter }
    dv (endW m' mref cctx cref (Lean.Meta.whnf e) w) = dv w :=
  (h (admCtx_quietFalse_writer mctx cctx) _ (FramedA.whnf e) w).2.2

/-! ## Consumers re-derived under the restricted laws: the start world's
quietness is threaded. The cache's `modify` (the `RefLawsCore.cacheModify'`
pattern, `ShippingChildBndCore.lean:166`), now at an admissible context and a
quiet start world. -/
theorem RefLawsAOps.cacheModify' {Fresh : (σ : Type) → IO.Ref σ → Prop}
    (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (f : Std.HashMap Name Res → Std.HashMap Name Res) {w : Void IO.RealWorld}
    {u : Unit} {w' : Void IO.RealWorld} (hq : O.quiet w)
    (h : RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w') :
    cv w' = f (cv w) ∧ sv w' = sv w ∧ dv w' = dv w := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleChildCache f h
  have h1 := O.frame hA _ FramedA.cacheGet w hq
  have hq1 := O.frameQ hA _ FramedA.cacheGet w hq
  rw [endW_of_runs hg] at h1 hq1
  have h2 := O.cacheSet hA _ _ _ _ hs hq1
  exact ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem RefLawsAOps.depthModify' {Fresh : (σ : Type) → IO.Ref σ → Prop}
    (O : RefLawsAOps Fresh mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (f : Nat → Nat) {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (hq : O.quiet w)
    (h : RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w') :
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = f (dv w) := by
  obtain ⟨w1, hg, hs⟩ := modify_split sparkleSynthDepth f h
  have h1 := O.frame hA _ FramedA.depthGet w hq
  have hq1 := O.frameQ hA _ FramedA.depthGet w hq
  rw [endW_of_runs hg] at h1 hq1
  have h2 := O.depthSet hA _ _ _ _ hs hq1
  exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2⟩

/-! ### A prefix step (`ShippingChildBalance.out0_end`/`tripleO_op` style):
the invariant carries quietness, so the `quiet w` premise is available
exactly where the invariant holds. -/

/-- The outermost condition, with quietness as its first conjunct. -/
def OutQ (quiet : Void IO.RealWorld → Prop) (w : Void IO.RealWorld) : Prop :=
  quiet w ∧ sv w = some synthesizeChild ∧ dv w = 0  -- guess: G8

/-- A provenance-framed operation in an admissible context, from an `OutQ`
world, ends in an `OutQ` world on every outcome. -/
theorem outQ_end {Fresh : (σ : Type) → IO.Ref σ → Prop} (O : RefLawsAOps Fresh mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {α : Type} {p : MetaM α} (hp : FramedA Fresh p)
    {w : Void IO.RealWorld} (hw : OutQ O.quiet w) :
    OutQ O.quiet (endW mctx mref cctx cref p w) := by
  have hk := O.frame hA p hp w hw.1
  exact ⟨O.frameQ hA p hp w hw.1, hk.2.1.trans hw.2.1, hk.2.2.trans hw.2.2⟩

/-- `OutQ` is KEPT by a provenance-framed operation in an admissible context,
exceptions in the class (`excOk` at the quiet start world). -/
theorem keeps_outQ {Fresh : (σ : Type) → IO.Ref σ → Prop} (O : RefLawsAOps Fresh mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {α : Type} {p : MetaM α} (hp : FramedA Fresh p) :
    Keeps mctx mref cctx cref (OutQ O.quiet) p := by
  intro w hw
  refine ⟨outQ_end O hA hp hw, ?_⟩
  unfold ErrOk
  cases hm : p mctx mref cctx cref w with  -- guess: G7
  | ok a w1 => exact True.intro
  | error e w1 => exact O.excOk hA p (.framed hp.toFramed) w e w1 hw.1 hm

end Tools.ShippingChildInvA
