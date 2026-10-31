import Tests.Gen5.EnvFrame2Check
import Tools.ShippingGen5EnvFrame3
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Pod build exit 0, 756 jobs, at 3261e98d (Lean content); clean issue-linked build is the coder's (freeze r9 scripts/gen5/DG_ENV_T2_U3_FREEZE.md). Pod build of this Lean: TYPE 27 (13 DRow ctors + 2 def bodies + 12 theorems), MUTANT 13, PARTITION 13/40/27, CLOSURE 4 law-free + 8 field roots, AXIOMS 15 standard.
-- Counting rule: TYPE = Expected comparisons (DRow constructors + definition bodies + theorems); MUTANT = single well-typed changes rejected by the same comparator;
-- CLOSURE = law-free roots + field roots; negatives are per mode (direct + helper); unresolved = throwing controls; self-root = forbidden constant as root; clean = not-flagged controls.

/-! # DG-ENV unit U3 checks (Tools/ShippingGen5EnvFrame3.lean)

1. TYPE: Expected propositions written from freeze §4 (statements and binders), through ONE comparator: `withReducible` around `checkExpected`
   (constructors of `DRow` through the same `cmpTele`).
2. MUTANT (13): well-typed single changes N1-N13 rejected by that comparator. Signature/defeq rejections, NOT semantic counterexamples.
3. PARTITION: counts read from the environment (a constructor count only; no claim of non-overlap or of a `¬ DRow` supplier).
4. CLOSURE in three modes (freeze §7): LAW-FREE (E1-E4, the U2 walker `reach`), QUIET-ONLY (E4 instantiated at the laws), FIELD ROOTS (8 F theorems).
   The mode walker `reachQ` is the `reach` walker with `leaf` constants that are recorded and not descended into (the allowed projections are
   themselves raw-projection definitions); with `leaf = []` it is checked to agree with `reach` on the U1 / U2 controls.
5. AXIOMS: standard only. -/

namespace Tests.Gen5.EnvFrame3Fixture
open Lean
open Tools.ShippingGen2 (Laws)
open Tools.ShippingChildInvA (AdmCtx)
-- positive quiet-only fixture: E4 instantiated at the quiet components of two law bundles
theorem e4AtLaws {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L L' : Laws mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} (h : mctx.canUnfold? = none) :
    AdmCtx L'.O.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx :=
  Tools.ShippingGen5EnvFrame3.admCtx_down_of_none h
-- negatives in the quiet-only mode (each reaches a law-bearing constant)
theorem qLawsT : True := (fun _ => trivial) @Tools.ShippingGen2.Laws.T
theorem qDiag : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.diag
theorem qTeleViaL {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) : True :=
  (fun _ => trivial) (@Tools.ShippingChildInvA.RefLawsATele.telescope _ _ _ L.T)
-- a law-bearing field used next to the allowed quiet projection
theorem qFrameViaL {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) : True :=
  (fun _ => trivial) (@L.O.frame)
theorem hQDiag : True := qDiag
end Tests.Gen5.EnvFrame3Fixture

namespace Tests.Gen5.EnvFrame3Check
open Lean Meta
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (endW Throws Op SideRef LocalRefType OkExc)
open Tools.ShippingChildBndCore (cv sv dv)
open Tools.ShippingChildInvA (FramedA AdmCtx)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingStRefCorrespondence (ReadWorld SetFrame SetGet)
open Tools.ShippingGen5EnvFrame (EnvFrameEnd)
open Tools.ShippingGen5EnvQ (QuietStrength AdmDown)
open Tools.ShippingGen2 (Laws)
open Sparkle.Compiler.Elab (sparkleChildCache sparkleChildSynth sparkleSynthDepth)
open Tools.ShippingGen5EnvFrame3
open Tests.Gen3.ExpectedType
open Tests.Gen5.EnvFrameCheck (mkForbid badProj reach guarded body? recsOf)

/-! ## 1. Expected types, written from freeze §4 -/
def ExpDRowIoEnv : Prop := ∀ (n : String), DRow (liftM (IO.getEnv n) : MetaM _)
def ExpDRowMonoMs : Prop := DRow (liftM IO.monoMsNow : MetaM Nat)
def ExpDRowMkExprCache : Prop :=
  ∀ (v : Lean.ExprStructMap String), DRow (IO.mkRef v : MetaM (IO.Ref (Lean.ExprStructMap String)))
def ExpDRowLocalMk : Prop :=
  ∀ {σ : Type} (v : σ), LocalRefType σ → DRow (liftM (IO.mkRef v) : MetaM (IO.Ref σ))
def ExpDRowWhnf : Prop := ∀ (e : Lean.Expr), DRow (Lean.Meta.whnf e)
def ExpDRowInferType : Prop := ∀ (e : Lean.Expr), DRow (Lean.Meta.inferType e)
def ExpDRowIsClass : Prop := ∀ (e : Lean.Expr), DRow (Lean.Meta.isClass? e)
def ExpDRowWhnfUntil : Prop := ∀ (e : Lean.Expr) (n : Name), DRow (Lean.Meta.whnfUntil e n)
def ExpDRowInstForall : Prop := ∀ (e : Lean.Expr) (ps : Array Lean.Expr), DRow (Lean.Meta.instantiateForall e ps)
def ExpDRowMkLam : Prop :=
  ∀ (xs : Array Lean.Expr) (e : Lean.Expr) (usedOnly usedLetOnly etaReduce generalizeNondepLet : Bool) (bi : BinderInfo),
    DRow (Lean.Meta.mkLambdaFVars xs e usedOnly usedLetOnly etaReduce generalizeNondepLet bi)
def ExpDRowMkAppM : Prop := ∀ (c : Name) (xs : Array Lean.Expr), DRow (Lean.Meta.mkAppM c xs)
def ExpDRowUnfold : Prop := ∀ (e : Lean.Expr), DRow (Lean.Meta.unfoldDefinition? e)
def ExpDRowReduce : Prop :=
  ∀ (e : Lean.Expr) (explicitOnly skipTypes skipProofs : Bool), DRow (Lean.Meta.reduce e explicitOnly skipTypes skipProofs)

def ExpCellOK {σ : Type} (cref : ST.Ref IO.RealWorld Core.State) (r : IO.Ref σ) : Prop :=
  ReadWorld r ∧ r.ref ≠ cref.ref ∧ SetFrame r cref

def ExpCellPrem (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  CellOK cref sparkleChildCache ∧ CellOK cref sparkleChildSynth ∧ CellOK cref sparkleSynthDepth ∧
  (∀ {σ : Type} (r : IO.Ref σ), SideRef r → CellOK cref r) ∧
  (∀ (σ : Type) (r : IO.Ref σ), Fresh σ r → CellOK cref r) ∧
  ReadWorld mref ∧ SetFrame mref cref ∧ mref.ref ≠ cref.ref ∧ ReadWorld cref ∧ SetGet cref

def ExpE1 : Prop :=
  ∀ {Fresh : (σ : Type) → IO.Ref σ → Prop} {α : Type} {p : MetaM α} (h : DRow p), FramedA Fresh p

def ExpE2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {Fresh : (σ : Type) → IO.Ref σ → Prop} (hcell : CellPrem Fresh mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α} (hp : FramedA Fresh p) (hnd : ¬ DRow p),
    EnvFrameEnd p mctx mref cctx cref

def ExpE3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α}
    (hp : Throws p) (hc : ReadWorld cref) (hm : ReadWorld mref), EnvFrameEnd p mctx mref cctx cref

def ExpE4 : Prop :=
  ∀ {q q' : Void IO.RealWorld → Prop} {mctx : Meta.Context} {cctx : Core.Context}
    (h : mctx.canUnfold? = none), AdmCtx q' mctx cctx → AdmCtx q mctx cctx

def ExpFrameT : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, L'.O.quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w) ∧ L'.O.quiet (endW mctx mref cctx cref p w)

def ExpExcOk : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀) (hd : AdmDown L L'),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Op p →
    ∀ w e w', L'.O.quiet w → p mctx mref cctx cref w = .error e w' → OkExc e

def ExpFrameQ : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ¬ DRow p → ∀ w, L'.O.quiet w →
    L'.O.quiet (endW mctx mref cctx cref p w)

def ExpCacheSetQ : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w → L'.O.quiet w'

def ExpDepthSetQ : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    L'.O.quiet w → L'.O.quiet w'

def ExpFrame : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀) (hd : AdmDown L L'),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ∀ w, L'.O.quiet w →
    cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w

def ExpCacheSet : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀) (hd : AdmDown L L'),
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w →
    cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w

def ExpDepthSet : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀) (hd : AdmDown L L'),
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' →
    L'.O.quiet w →
    cv w' = cv w ∧ sv w' = sv w ∧ dv w' = v

/-! ## Mutants (well-typed single changes) -/
def MutN1 : Prop := -- frameQ_plus without `¬ DRow p`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ∀ w, L'.O.quiet w →
    L'.O.quiet (endW mctx mref cctx cref p w)
def MutN2 : Prop := -- frameQ_plus without `hd`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ¬ DRow p → ∀ w, L'.O.quiet w →
    L'.O.quiet (endW mctx mref cctx cref p w)
def MutN3 : Prop := -- frameQ_plus concluding `L.O.quiet`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), FramedA MkRefd p → ¬ DRow p → ∀ w, L'.O.quiet w →
    L.O.quiet (endW mctx mref cctx cref p w)
def MutN4 : Prop := -- cacheSetQ_plus without `hcell`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L'),
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w → L'.O.quiet w'
def MutN5 : Prop := -- frameT_plus dropping the `quiet` conjunct
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, L'.O.quiet w →
    (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW mctx mref cctx cref p w) = sv w ∧
      dv (endW mctx mref cctx cref p w) = dv w)
def MutN6 : Prop := -- frameT_plus dropping the `cv/sv/dv` conjunct
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀)
    (hd : AdmDown L L') (hcell : CellPrem MkRefd mref cref),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Throws p → ∀ w, L'.O.quiet w →
    L'.O.quiet (endW mctx mref cctx cref p w)
def MutN7 : Prop := -- cacheSet_plus dropping the last conjunct
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀) (hd : AdmDown L L'),
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx L'.O.quiet mctx cctx → ∀ v w u w',
    RunsTo (sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → L'.O.quiet w →
    cv w' = v ∧ sv w' = sv w
def MutN8 : Prop := -- envFrameEnd_framedA without `hnd`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {Fresh : (σ : Type) → IO.Ref σ → Prop} (hcell : CellPrem Fresh mref cref)
    {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α} (hp : FramedA Fresh p),
    EnvFrameEnd p mctx mref cctx cref
def MutN9 : Prop := -- envFrameEnd_throws without `hm`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {mctx : Meta.Context} {cctx : Core.Context} {α : Type} {p : MetaM α}
    (hp : Throws p) (hc : ReadWorld cref), EnvFrameEnd p mctx mref cctx cref
def MutN10 : Prop := -- excOk_plus without `hd`
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L L' : Laws mref cref) (env₀ : Environment) (hq : QuietStrength L L' env₀),
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {α : Type}, AdmCtx L'.O.quiet mctx cctx →
    ∀ (p : MetaM α), Op p →
    ∀ w e w', L'.O.quiet w → p mctx mref cctx cref w = .error e w' → OkExc e
def MutCellPrem (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop := -- N11: CellPrem without `SetGet cref`
  CellOK cref sparkleChildCache ∧ CellOK cref sparkleChildSynth ∧ CellOK cref sparkleSynthDepth ∧
  (∀ {σ : Type} (r : IO.Ref σ), SideRef r → CellOK cref r) ∧
  (∀ (σ : Type) (r : IO.Ref σ), Fresh σ r → CellOK cref r) ∧
  ReadWorld mref ∧ SetFrame mref cref ∧ mref.ref ≠ cref.ref ∧ ReadWorld cref
def MutCellOK {σ : Type} (cref : ST.Ref IO.RealWorld Core.State) (r : IO.Ref σ) : Prop := -- N12: CellOK without `r.ref ≠ cref.ref`
  ReadWorld r ∧ SetFrame r cref
def MutN13 : Prop := -- admCtx_down_of_none without `h`
  ∀ {q q' : Void IO.RealWorld → Prop} {mctx : Meta.Context} {cctx : Core.Context},
    AdmCtx q' mctx cctx → AdmCtx q mctx cctx

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)
/-- A constructor's type against an Expected proposition, through the same `cmpTele`. -/
def cmpCtor (c exp : Name) : MetaM Unit := withReducible do
  let ci ← getConstInfo c
  unless ci.isCtor do throwError "ENVFRAME3 CHECK FAILED: {c} is not a constructor"
  let e ← stmtOf exp
  cmpTele s!"{c}" ci.type e
  logInfo m!"ENVFRAME3 CTOR TYPE OK {c} against {exp}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let D := ``DRow
  for (c, e) in [(`ioEnv, ``ExpDRowIoEnv), (`monoMs, ``ExpDRowMonoMs), (`mkExprCache, ``ExpDRowMkExprCache),
      (`localMk, ``ExpDRowLocalMk), (`whnf, ``ExpDRowWhnf), (`inferType, ``ExpDRowInferType), (`isClass?, ``ExpDRowIsClass),
      (`whnfUntil, ``ExpDRowWhnfUntil), (`instantiateForall, ``ExpDRowInstForall), (`mkLambdaFVars, ``ExpDRowMkLam),
      (`mkAppM, ``ExpDRowMkAppM), (`unfoldDefinition?, ``ExpDRowUnfold), (`reduce, ``ExpDRowReduce)] do
    cmpCtor (D ++ c) e
  cmpExp ``CellOK ``ExpCellOK
  cmpExp ``CellPrem ``ExpCellPrem
  cmpExp ``drow_toFramedA ``ExpE1
  cmpExp ``envFrameEnd_framedA ``ExpE2
  cmpExp ``envFrameEnd_throws ``ExpE3
  cmpExp ``admCtx_down_of_none ``ExpE4
  cmpExp ``frameT_plus ``ExpFrameT
  cmpExp ``excOk_plus ``ExpExcOk
  cmpExp ``frameQ_plus ``ExpFrameQ
  cmpExp ``cacheSetQ_plus ``ExpCacheSetQ
  cmpExp ``depthSetQ_plus ``ExpDepthSetQ
  cmpExp ``frame_plus ``ExpFrame
  cmpExp ``cacheSet_plus ``ExpCacheSet
  cmpExp ``depthSet_plus ``ExpDepthSet
  logInfo "ENVFRAME3 TYPE total 27 (13 DRow constructors + 2 definition bodies + 12 theorems), all through the same cmpTele / withReducible"
  cmpMut ``frameQ_plus ``MutN1
  cmpMut ``frameQ_plus ``MutN2
  cmpMut ``frameQ_plus ``MutN3
  cmpMut ``cacheSetQ_plus ``MutN4
  cmpMut ``frameT_plus ``MutN5
  cmpMut ``frameT_plus ``MutN6
  cmpMut ``cacheSet_plus ``MutN7
  cmpMut ``envFrameEnd_framedA ``MutN8
  cmpMut ``envFrameEnd_throws ``MutN9
  cmpMut ``excOk_plus ``MutN10
  cmpMut ``CellPrem ``MutCellPrem
  cmpMut ``CellOK ``MutCellOK
  cmpMut ``admCtx_down_of_none ``MutN13
  logInfo "ENVFRAME3 MUTANT total 13 (N1-N13; N5-N7 drop a conjunct) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

/-! ## 2. Partition (constructor counts read from the environment; no claim of non-overlap or of a `¬ DRow` supplier) -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let some (.inductInfo dr) := env.find? ``DRow | throwError "ENVFRAME3 PARTITION FAILED: DRow"
  let some (.inductInfo fr) := env.find? ``FramedA | throwError "ENVFRAME3 PARTITION FAILED: FramedA"
  unless dr.ctors.length == 13 do throwError "ENVFRAME3 PARTITION FAILED: DRow has {dr.ctors.length} constructors"
  unless fr.ctors.length == 40 do throwError "ENVFRAME3 PARTITION FAILED: FramedA has {fr.ctors.length} constructors"
  let last (n : Name) : Name := Name.mkSimple n.getString!
  let frNames := fr.ctors.map last
  for c in dr.ctors do
    unless frNames.contains (last c) do throwError "ENVFRAME3 PARTITION FAILED: {c} is not a FramedA constructor name"
  let rest := frNames.filter fun n => !(dr.ctors.map last).contains n
  unless rest.length == 27 do throwError "ENVFRAME3 PARTITION FAILED: {rest.length} remaining"
  logInfo m!"ENVFRAME3 PARTITION: DRow {dr.ctors.length} constructors, FramedA {fr.ctors.length}, remaining {rest.length} (constructor counts only)"

/-! ## 3. Closure audit -/
/-- `reach` with `leaf` constants: recorded in `got` and not descended into (they are projection definitions whose bodies are raw projections). -/
structure QReach where
  hit : Option (List Name) := none
  got : NameSet := {}
  visited : Nat := 0

def reachQ (forbid leaf : List Name) (root : Name) (hidden : Option Name := none) (cap : Nat := 3000000) : MetaM QReach := do
  let env ← getEnv
  let lookup (n : Name) : Option ConstantInfo := if hidden == some n then none else env.find? n
  let mut out : QReach := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i : Nat := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "ENVFRAME3 AUDIT INCOMPLETE at {root}"
    if forbid.contains c then return { out with hit := some path }
    if leaf.contains c then
      out := { out with got := out.got.insert c }
      continue
    let some ci := lookup c | throwError "ENVFRAME3 AUDIT UNRESOLVED NAME {c} (path {path})"
    let body := body? ci
    if badProj ci.type || (body.map badProj).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if forbid.contains u then return { out with hit := some (path ++ [u]) }
      unless seen.contains u do
        seen := seen.insert u
        queue := queue.push (u, path ++ [u])
  return out

def opsN : Name := ``Tools.ShippingChildInvA.RefLawsAOps
def allowedQuiet : List Name := [``Tools.ShippingGen2.Laws.O, opsN ++ `quiet]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbid ← mkForbid
  let ops := opsN
  let F := `Tests.Gen5.EnvFrameFixture
  let G := `Tests.Gen5.EnvFrame2Fixture
  let H := `Tests.Gen5.EnvFrame3Fixture
  for s in guarded do
    unless badProj (.proj s 0 (.bvar 0)) do throwError "ENVFRAME3 AUDIT FAILED: misses raw projection of {s}"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "ENVFRAME3 AUDIT FAILED: flags raw Prod projection"
  -- (A) walker agreement: with leaf = [] reachQ equals reach on the U1 / U2 controls
  let std : List (Name × Name) :=
    [(F ++ `dLawsO, ``Tools.ShippingGen2.Laws.O), (F ++ `dOps, ops ++ `frame),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope),
     (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines), (F ++ `dND, ``Tools.ShippingGen2.T1HypND.defines),
     (F ++ `dRec, ops ++ `casesOn), (F ++ `dGetEnvFrame, ``Tools.ShippingEnvSnapshot.GetEnvFrame),
     (F ++ `dSnapshot, ``Tools.ShippingEntryReadsLinked.EnvSnapshot),
     (F ++ `dLemma, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps),
     (G ++ `fGetConstInfo, ``Tools.ShippingEnvSnapshot.GetEnvFrame),
     (F ++ `hOps, ops ++ `frame), (F ++ `hLemma, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps),
     (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines),
     (G ++ `fHelperTyLemma, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps)]
  let mut nAgree : Nat := 0
  for (c, t) in std do
    let a ← reach forbid c
    let b ← reachQ forbid [] c
    unless a.hit.isSome && a.hit == b.hit do throwError "ENVFRAME3 AUDIT FAILED: reachQ disagrees with reach on {c}"
    let b' ← reachQ [t] [] c
    unless b'.hit.map (·.getLast? == some t) == some true do
      throwError "ENVFRAME3 AUDIT FAILED: {c} does not reach its intended {t} (reachQ)"
    nAgree := nAgree + 1
  for c in [F ++ `cUnrelated, F ++ `cBinders, F ++ `cBinders2, F ++ `cHelper, F ++ `hv, F ++ `ht, F ++ `ht2] do
    unless (← reach forbid c).hit.isNone && (← reachQ forbid [] c).hit.isNone do
      throwError "ENVFRAME3 AUDIT FAILED: clean control {c} flagged"
    nAgree := nAgree + 1
  logInfo m!"ENVFRAME3 CONTROL walker agreement: reachQ (leaf = []) equals reach on {nAgree} U1/U2 controls"
  -- (B) LAW-FREE mode: E1-E4 with the U2 walker
  let lawFree : List Name := [``drow_toFramedA, ``envFrameEnd_framedA, ``envFrameEnd_throws, ``admCtx_down_of_none]
  let mut nFree : Nat := 0
  for c in lawFree do
    let r ← reach forbid c
    if let some p := r.hit then throwError "ENVFRAME3 AUDIT FAILED {c}: forbidden use via {p}"
    nFree := nFree + 1
    logInfo m!"ENVFRAME3 REACH law-free {c}: clean, type and value (visited {r.visited})"
  -- (C) QUIET-ONLY mode (E4 at the laws)
  let forbidQ := forbid.filter (!allowedQuiet.contains ·)
  let pos ← reachQ forbidQ allowedQuiet (H ++ `e4AtLaws)
  if let some p := pos.hit then throwError "ENVFRAME3 AUDIT FAILED: e4AtLaws flagged via {p}"
  unless pos.got.toList.toArray.qsort Name.lt == allowedQuiet.toArray.qsort Name.lt do
    throwError "ENVFRAME3 AUDIT FAILED: e4AtLaws reaches {pos.got.toList}, expected exactly {allowedQuiet}"
  logInfo m!"ENVFRAME3 CONTROL quiet-only positive e4AtLaws: clean, reached exactly {pos.got.toList}"
  let qNeg : List (Name × Name) :=
    [(F ++ `dOps, ops ++ `frame), (H ++ `qLawsT, ``Tools.ShippingGen2.Laws.T),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope), (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines),
     (F ++ `dND, ``Tools.ShippingGen2.T1HypND.defines), (F ++ `dRec, ops ++ `casesOn),
     (H ++ `qDiag, ops ++ `diag), (H ++ `qTeleViaL, ``Tools.ShippingGen2.Laws.T),
     (H ++ `qFrameViaL, ops ++ `frame),
     (F ++ `hOps, ops ++ `frame), (H ++ `hQDiag, ops ++ `diag)]
  let mut nQNeg : Nat := 0
  for (c, t) in qNeg do
    unless forbidQ.contains t do throwError "ENVFRAME3 AUDIT FAILED: intended {t} not forbidden in quiet-only mode"
    let r ← reachQ forbidQ allowedQuiet c
    if r.hit.isNone then throwError "ENVFRAME3 AUDIT FAILED: quiet-only misses {c}"
    let rt ← reachQ [t] allowedQuiet c
    unless rt.hit.map (·.getLast? == some t) == some true do
      throwError "ENVFRAME3 AUDIT FAILED: {c} does not reach its intended {t} (quiet-only)"
    nQNeg := nQNeg + 1
  -- the allowed constants are not forbidden, and the other guarded structures stay raw-projection forbidden
  for a in allowedQuiet do
    if forbidQ.contains a then throwError "ENVFRAME3 AUDIT FAILED: allowed {a} is forbidden"
  logInfo m!"ENVFRAME3 CONTROL quiet-only negatives: {nQNeg} flagged with intended constant on the path; raw projections of {guarded.length} guarded structures still flagged"
  -- (D) FIELD ROOTS
  let fieldRoots : List (Name × Name) :=
    [(``frameT_plus, `frameT), (``excOk_plus, `excOk), (``frameQ_plus, `frameQ), (``cacheSetQ_plus, `cacheSetQ),
     (``depthSetQ_plus, `depthSetQ), (``frame_plus, `frame), (``cacheSet_plus, `cacheSet), (``depthSet_plus, `depthSet)]
  let mut nField : Nat := 0
  let mut nFieldNeg : Nat := 0
  for (c, f) in fieldRoots do
    let allowed := allowedQuiet ++ [ops ++ f]
    let fb := forbid.filter (!allowed.contains ·)
    let r ← reachQ fb allowed c
    if let some p := r.hit then throwError "ENVFRAME3 AUDIT FAILED {c}: forbidden use via {p}"
    unless r.got.toList.toArray.qsort Name.lt == allowed.toArray.qsort Name.lt do
      throwError "ENVFRAME3 AUDIT FAILED {c}: reaches {r.got.toList}, expected exactly {allowed}"
    nField := nField + 1
    -- negative 1: shrinking the allowed set by the row's field makes the root flagged on that field (the field is really used)
    let allowed' := allowedQuiet
    let fb' := forbid.filter (!allowed'.contains ·)
    let r' ← reachQ fb' allowed' c
    unless r'.hit.map (·.getLast? == some (ops ++ f)) == some true do
      throwError "ENVFRAME3 AUDIT FAILED {c}: without allowing {ops ++ f} the root is not flagged on it ({toString r'.hit})"
    -- negative 2: fixtures reaching a field that no F row may use, or Laws.T, are flagged in this row's mode
    for (fx, t) in [(H ++ `qDiag, ops ++ `diag), (H ++ `qLawsT, ``Tools.ShippingGen2.Laws.T)] do
      let rx ← reachQ fb allowed fx
      unless rx.hit.map (·.getLast? == some t) == some true do
        throwError "ENVFRAME3 AUDIT FAILED: {fx} not flagged on {t} in the mode of {c}"
    nFieldNeg := nFieldNeg + 3
    logInfo m!"ENVFRAME3 REACH field root {c}: clean, reached exactly {allowed} (visited {r.visited})"
  -- (E) unresolved names (reachQ throws), self-root, clean
  let missing := `Tests.Gen5.EnvFrameFixture.noSuchRoot
  let unres : List (Name × Option Name × Name × List Name) :=
    [(missing, none, missing, []), (F ++ `hv, some (F ++ `helperClean), F ++ `helperClean, []),
     (F ++ `ht, some (F ++ `helperTy), F ++ `helperTy, []),
     (F ++ `ht2, some (F ++ `helperTy), F ++ `helperTy, [F ++ `ht2, F ++ `helperHt])]
  let mut nUnres : Nat := 0
  for (c, hid, nm, via) in unres do
    let ok ← try
        let _ ← reachQ forbid allowedQuiet c hid
        pure false
      catch e =>
        let msg ← e.toMessageData.toString
        let has (n : Name) := (msg.splitOn (toString n)).length > 1
        pure (msg.startsWith s!"ENVFRAME3 AUDIT UNRESOLVED NAME {nm} " && via.all has)
    unless ok do throwError "ENVFRAME3 AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
  let selfRoots : List Name :=
    [``Tools.ShippingEnvSnapshot.GetEnvFrame, ``Tools.ShippingGen2.T1Hyp.defines,
     ``Tools.ShippingGen2.T1HypND.defines, ``Tools.ShippingGen2.Laws.T, ops ++ `frame, ops ++ `casesOn,
     ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps]
  let mut nSelf : Nat := 0
  for t in selfRoots do
    unless forbidQ.contains t do throwError "ENVFRAME3 AUDIT FAILED: self-root {t} not forbidden"
    for fl in [forbidQ, [t]] do
      let r ← reachQ fl allowedQuiet t
      unless r.hit == some [t] do throwError "ENVFRAME3 AUDIT FAILED: forbidden root {t} itself not flagged ({toString r.hit})"
    nSelf := nSelf + 1
  logInfo m!"ENVFRAME3 CLOSURE total: {nFree} law-free roots + {nField} field roots / negatives: std walker agreement {std.length} (10 direct + 4 helper), quiet-only {nQNeg} (9 direct + 2 helper), field-mode {nFieldNeg} (8 roots x 3) + {nUnres} unresolved + {nSelf} self-root / clean: 7 (walker agreement) + 1 (quiet-only positive e4AtLaws)"

/-! ## 4. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``CellOK, ``CellPrem, ``DRow, ``drow_toFramedA, ``envFrameEnd_framedA, ``envFrameEnd_throws, ``admCtx_down_of_none,
      ``frameT_plus, ``excOk_plus, ``frameQ_plus, ``cacheSetQ_plus, ``depthSetQ_plus, ``frame_plus, ``cacheSet_plus,
      ``depthSet_plus] do
    checkAxioms n
  logInfo "ENVFRAME3 AXIOMS total 15 standard (12 theorems + CellOK + CellPrem + DRow)"

end Tests.Gen5.EnvFrame3Check
