import Tools.ShippingFGCircuitS2mReach3
import Tests.Gen5.FGCircuitPilotCheck26
set_option autoImplicit false
-- FG circuit pilot S2m check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §39.

/-! # FGCircuitPilotCheck33 (light: each part is a small `run_cmd`; ONE comparison function `cmp` is used for the positive and for every negative case: both normalise the same constants and use `isDefEq` at DEFAULT transparency; a mutant must be a different expression and not defeq)

1. DEFS: the constructors of `LeafStep` / `Reached`, the strengthened quiet predicate `quietR`, against independently written expected statements, with mutants (arbitrary code as a step, a start at another world, no reach, no `ReadsAt`, another environment, reach from another world).
2. HYPS: the named run-local hypotheses (`DRowEnvR`, `DiagEnvR`, `ProfStepR`, `ProfOffW`, `AdmDownR`, `TeleR`) against independently written types; mutants: the conclusion at the START world, the premise at the END world, no reach premise, no `ReadsAt` premise, another root environment, reach from another world, no admissibility, the class widened, the profile lookup ON instead of off.
3. SIGNATURES: the complete types of `missR`, `jqhr_head` and `hftCoreCloses_of_kidsR` (binder kinds too) against independently written expected types, with the four controls (world not reached from the root, another root environment, end world, profile on) and every premise dropped.
4. STEPS (structural), CONTROLS (kernel-checked consequences), REMAINING, AXIOMS. WHENEVER `hftCoreCloses_of_kidsR` or one of the hypotheses changes, this check must be updated in the same commit. -/
namespace Tests.Gen5.FGCircuitPilotCheck33
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved)
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt profileAct)
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvFrame3 (CellPrem DRow)
open Tools.ShippingFGCircuitS1qLinked (coreHeadOff)
open Tools.ShippingFGCircuitS1zClose (HftCoreCloses)
open Tools.ShippingFGCircuitCover (RootReader)
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 NmHttp NmTlp HttpData TlpData Pre ExpKidsGates tyOf binderNames reach idW idF iteStep)

/-! ## the one comparison -/

def normOnce4 (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let some e' := iteStep e then return .visit e'
    if let .const c _ := e.getAppFn then
      if c == ``DRowEnvR || c == ``DiagEnvR || c == ``ProfStepR || c == ``ProfOffW || c == ``AdmDownR || c == ``TeleR ||
          c == ``JQHR || c == ``KidEv || c == ``MissE || c == ``JQH ||
          (`Tests.Gen5.FGCircuitPilotCheck33).isPrefixOf c || c == ``Tests.Gen5.FGCircuitPilotCheck26.Pre || c == ``Tests.Gen5.FGCircuitPilotCheck26.ExpKidsGates then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm4 (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:6] do
    e ← normOnce4 e
  return e
/-- THE comparison (same function, same transparency, for the positive and for every mutant) -/
def cmp (a b : Lean.Expr) : MetaM Bool := do
  let a ← norm4 a
  let b ← norm4 b
  if a == b then return true
  withDefault (isDefEq a b)
def agree (what : String) (a b : Lean.Expr) : MetaM Unit := do
  unless ← cmp a b do throwError "{what}: NOT the expected statement"
def differ (what : String) (a b : Lean.Expr) : MetaM Unit := do
  if ← cmp a b then throwError "{what}: the MUTANT was accepted"
def binderKinds (e : Lean.Expr) : List BinderInfo :=
  let rec go : Lean.Expr → List BinderInfo
    | .forallE _ _ b bi => bi :: go b
    | _ => []
  go e

/-- the application of a constant to the first `n` free variables of the telescope of an independently written def, plus the extra trailing ones -/
def withApps {α : Type} (real : Name) (pos : Name) (k : Lean.Expr → Lean.Expr → Array Lean.Expr → MetaM α) : MetaM α := do
  let nReal ← forallTelescope (← tyOf real) fun xs _ => pure xs.size
  forallTelescope (← tyOf pos) fun ys _ => do
    k (mkAppN (Lean.mkConst real) (ys.extract 0 nReal)) (mkAppN (Lean.mkConst pos) ys) ys
/-- compare a definition `real` with `pos` and every mutant (same parameters as `real` first, then extra independent ones) -/
def checkDef (what : String) (real : Name) (pos : Name) (muts : List Name) : MetaM Nat := do
  withApps real pos fun r p ys => do
    agree what r p
    let n ← forallTelescope (← tyOf real) fun xs _ => pure xs.size
    let mut c := 0
    for mu in muts do
      let sig ← tyOf mu
      forallTelescope sig fun zs _ => do
        let r' := mkAppN (Lean.mkConst real) (zs.extract 0 n)
        let m := mkAppN (Lean.mkConst mu) zs
        differ s!"{what} vs {mu}" r' m
      c := c + 1
    pure c

/-! ## independently written statements -/

section Exp
variable {mref : Rf1} {cref : Rf2}

/-- the strengthened quiet predicate, written again -/
def ExpQuiet (quiet : W → Prop) (mref : Rf1) (cref : Rf2) (e : Environment) (w₀ : W) : W → Prop :=
  fun w => quiet w ∧ ReadsAt e cref w ∧ Reached quiet mref cref w₀ w
def QNoReach (quiet : W → Prop) (mref : Rf1) (cref : Rf2) (e : Environment) (w₀ : W) : W → Prop :=
  fun w => quiet w ∧ ReadsAt e cref w
def QNoReads (quiet : W → Prop) (mref : Rf1) (cref : Rf2) (e : Environment) (w₀ : W) : W → Prop :=
  fun w => quiet w ∧ Reached quiet mref cref w₀ w
def QNoQuiet (quiet : W → Prop) (mref : Rf1) (cref : Rf2) (e : Environment) (w₀ : W) : W → Prop :=
  fun w => ReadsAt e cref w ∧ Reached quiet mref cref w₀ w
/-- another root environment -/
def QOtherEnv (quiet : W → Prop) (mref : Rf1) (cref : Rf2) (e : Environment) (w₀ : W) (e' : Environment) : W → Prop :=
  fun w => quiet w ∧ ReadsAt e' cref w ∧ Reached quiet mref cref w₀ w
/-- reach from another world -/
def QOtherRoot (quiet : W → Prop) (mref : Rf1) (cref : Rf2) (e : Environment) (w₀ : W) (w₁ : W) : W → Prop :=
  fun w => quiet w ∧ ReadsAt e cref w ∧ Reached quiet mref cref w₁ w
/-- the environment of the reach root's END world (`envAt cref` of another world) -/
def QEnvOfOther (quiet : W → Prop) (mref : Rf1) (cref : Rf2) (e : Environment) (w₀ : W) (w₁ : W) : W → Prop :=
  fun w => quiet w ∧ ReadsAt (envAt cref w₁) cref w ∧ Reached quiet mref cref w₀ w

/-- class-D rows keep `ReadsAt` -/
def ExpD (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → DRow p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w →
      ReadsAt e cref (endW mctx mref cctx cref p w)
/-- conclusion at the START world -/
def DStart (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → DRow p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w → ReadsAt e cref w
/-- premise at the END world, conclusion at the start -/
def DEndPrem (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → DRow p →
    ∀ w : W, O.quiet w → ReadsAt e cref (endW mctx mref cctx cref p w) → Reached O.quiet mref cref w₀ w → ReadsAt e cref w
def DNoReach (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → DRow p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → ReadsAt e cref (endW mctx mref cctx cref p w)
def DNoReads (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → DRow p →
    ∀ w : W, O.quiet w → Reached O.quiet mref cref w₀ w → ReadsAt e cref (endW mctx mref cctx cref p w)
def DNoAdm (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), DRow p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w → ReadsAt e cref (endW mctx mref cctx cref p w)
def DAllFramed (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → FramedA MkRefd p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w → ReadsAt e cref (endW mctx mref cctx cref p w)
def DOtherEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (e' : Environment) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → DRow p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w → ReadsAt e' cref (endW mctx mref cctx cref p w)
def DOtherRoot (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (w₁ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → DRow p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₁ w → ReadsAt e cref (endW mctx mref cctx cref p w)

/-- diagnostics keep `ReadsAt` -/
def ExpG (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → Diag p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w →
      ReadsAt e cref (endW mctx mref cctx cref p w)
def GStart (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → Diag p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w → ReadsAt e cref w
def GNoReach (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → Diag p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → ReadsAt e cref (endW mctx mref cctx cref p w)
def GAsD (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc) {α : Type} (p : MetaM α), AdmCtx O.quiet mctx cctx → DRow p →
    ∀ w : W, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w →
      ReadsAt e cref (endW mctx mref cctx cref p w)

/-- the profile lookup is ON (the environment variable is set) -/
def ProfOnW (mref : Rf1) (cref : Rf2) (w : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), (∀ (o : Option String) (w1 : W), RunsTo profileAct mctx mref cctx cref w o w1 → o = some "1")
def ExpProfOff (mref : Rf1) (cref : Rf2) (w : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), GetEnvProfileAt mctx mref cctx cref w
def ProfOffOnlyOne (mref : Rf1) (cref : Rf2) (w : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), ∀ (o : Option String) (w1 : W), RunsTo profileAct mctx mref cctx cref w o w1 → o = none

/-- a leaf step from a reached world keeps the profile lookup unset -/
def ExpPS (O : RefLawsAOps MkRefd mref cref) (w₀ : W) : Prop :=
  ∀ w w' : W, Reached O.quiet mref cref w₀ w → LeafStep O.quiet mref cref w w' →
    ExpProfOff mref cref w → ExpProfOff mref cref w'
def PSStart (O : RefLawsAOps MkRefd mref cref) (w₀ : W) : Prop :=
  ∀ w w' : W, Reached O.quiet mref cref w₀ w → LeafStep O.quiet mref cref w w' →
    ExpProfOff mref cref w → ExpProfOff mref cref w
def PSEndPrem (O : RefLawsAOps MkRefd mref cref) (w₀ : W) : Prop :=
  ∀ w w' : W, Reached O.quiet mref cref w₀ w → LeafStep O.quiet mref cref w w' →
    ExpProfOff mref cref w' → ExpProfOff mref cref w
def PSNoReach (O : RefLawsAOps MkRefd mref cref) (w₀ : W) : Prop :=
  ∀ w w' : W, LeafStep O.quiet mref cref w w' → ExpProfOff mref cref w → ExpProfOff mref cref w'
def PSAnyStep (O : RefLawsAOps MkRefd mref cref) (w₀ : W) : Prop :=
  ∀ w w' : W, Reached O.quiet mref cref w₀ w → ExpProfOff mref cref w → ExpProfOff mref cref w'
def PSOn (O : RefLawsAOps MkRefd mref cref) (w₀ : W) : Prop :=
  ∀ w w' : W, Reached O.quiet mref cref w₀ w → LeafStep O.quiet mref cref w w' →
    ProfOnW mref cref w → ProfOnW mref cref w'
def PSOtherRoot (O : RefLawsAOps MkRefd mref cref) (w₀ : W) (w₁ : W) : Prop :=
  ∀ w w' : W, Reached O.quiet mref cref w₁ w → LeafStep O.quiet mref cref w w' →
    ExpProfOff mref cref w → ExpProfOff mref cref w'

/-- the contexts -/
def ExpDown (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), AdmCtx (ExpQuiet O.quiet mref cref e w₀) mctx cctx → AdmCtx O.quiet mctx cctx
def DownUp (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), AdmCtx O.quiet mctx cctx → AdmCtx (ExpQuiet O.quiet mref cref e w₀) mctx cctx
def DownId (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), AdmCtx O.quiet mctx cctx → AdmCtx O.quiet mctx cctx
def DownOtherEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (e' : Environment) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), AdmCtx (ExpQuiet O.quiet mref cref e' w₀) mctx cctx → AdmCtx O.quiet mctx cctx

/-- the telescope rows, at the strengthened quiet predicate -/
def ExpT (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  RefLawsATele (ExpQuiet O.quiet mref cref e w₀) mref cref
def TPlain (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  RefLawsATele O.quiet mref cref
def TNoReach (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  RefLawsATele (QNoReach O.quiet mref cref e w₀) mref cref
def TOtherEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (e' : Environment) : Prop :=
  RefLawsATele (ExpQuiet O.quiet mref cref e' w₀) mref cref
end Exp

/-! ## 1. DEFS: leaf steps, reach, the strengthened quiet predicate -/

section Steps
/-- the constructors of `LeafStep` / `Reached`, written again (types of the constructors) -/
def ExpFrame : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {α : Type} (mctx : Cx) (cctx : Cc) (p : MetaM α) (w : W),
    AdmCtx quiet mctx cctx → FramedA MkRefd p → LeafStep quiet mref cref w (endW mctx mref cctx cref p w)
def FrameNoAdm : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {α : Type} (mctx : Cx) (cctx : Cc) (p : MetaM α) (w : W),
    FramedA MkRefd p → LeafStep quiet mref cref w (endW mctx mref cctx cref p w)
def FrameAnyCode : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {α : Type} (mctx : Cx) (cctx : Cc) (p : MetaM α) (w : W),
    AdmCtx quiet mctx cctx → LeafStep quiet mref cref w (endW mctx mref cctx cref p w)
def ExpDiagStep : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {α : Type} (mctx : Cx) (cctx : Cc) (p : MetaM α) (w : W),
    AdmCtx quiet mctx cctx → Diag p → LeafStep quiet mref cref w (endW mctx mref cctx cref p w)
def ExpThrowsStep : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {α : Type} (mctx : Cx) (cctx : Cc) (p : MetaM α) (w : W),
    AdmCtx quiet mctx cctx → Throws p → LeafStep quiet mref cref w (endW mctx mref cctx cref p w)
def ExpCacheSet : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} (mctx : Cx) (cctx : Cc) (v : Std.HashMap Name Res) (w : W) (u : Unit) (w' : W),
    AdmCtx quiet mctx cctx →
    RunsTo (Sparkle.Compiler.Elab.sparkleChildCache.set v : MetaM Unit) mctx mref cctx cref w u w' → LeafStep quiet mref cref w w'
def ExpDepthSet : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} (mctx : Cx) (cctx : Cc) (v : Nat) (w : W) (u : Unit) (w' : W),
    AdmCtx quiet mctx cctx →
    RunsTo (ST.Ref.set Sparkle.Compiler.Elab.sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w' → LeafStep quiet mref cref w w'
def ExpStart : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {w₀ : W}, Reached quiet mref cref w₀ w₀
def StartElsewhere : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {w₀ w : W}, Reached quiet mref cref w₀ w
def ExpReachStep : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {w₀ w w' : W},
    Reached quiet mref cref w₀ w → LeafStep quiet mref cref w w' → Reached quiet mref cref w₀ w'
def ReachStepAny : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {w₀ w w' : W}, Reached quiet mref cref w₀ w → Reached quiet mref cref w₀ w'
def ReachStepNoPre : Prop :=
  ∀ {quiet : W → Prop} {mref : Rf1} {cref : Rf2} {w₀ w w' : W}, LeafStep quiet mref cref w w' → Reached quiet mref cref w₀ w'
end Steps

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2mReach
  let Q := `Tests.Gen5.FGCircuitPilotCheck33
  let C (n : Name) : Lean.Expr := Lean.mkConst n
  let mut nm : Nat := 0
  let chk (what : String) (real : Name) (pos : Name) (muts : List Name) : MetaM Nat := do
    let a ← tyOf real
    agree what a (C pos)
    for mu in muts do differ s!"{what} vs {mu}" a (C mu)
    pure muts.length
  nm := nm + (← chk "LeafStep.frame" (X ++ `LeafStep.frame) (Q ++ `ExpFrame) [Q ++ `FrameNoAdm, Q ++ `FrameAnyCode, Q ++ `ExpDiagStep])
  nm := nm + (← chk "LeafStep.diag" (X ++ `LeafStep.diag) (Q ++ `ExpDiagStep) [Q ++ `ExpFrame, Q ++ `ExpThrowsStep])
  nm := nm + (← chk "LeafStep.throws" (X ++ `LeafStep.throws) (Q ++ `ExpThrowsStep) [Q ++ `ExpFrame, Q ++ `ExpDiagStep])
  nm := nm + (← chk "LeafStep.cacheSet" (X ++ `LeafStep.cacheSet) (Q ++ `ExpCacheSet) [Q ++ `ExpDepthSet])
  nm := nm + (← chk "LeafStep.depthSet" (X ++ `LeafStep.depthSet) (Q ++ `ExpDepthSet) [Q ++ `ExpCacheSet])
  nm := nm + (← chk "Reached.start" (X ++ `Reached.start) (Q ++ `ExpStart) [Q ++ `StartElsewhere])
  nm := nm + (← chk "Reached.step" (X ++ `Reached.step) (Q ++ `ExpReachStep) [Q ++ `ReachStepAny, Q ++ `ReachStepNoPre])
  logInfo m!"FGCIRCUIT33 DEFS-REACH: the five LeafStep constructors (a FramedA row / a diagnostic / a throwError / a write of the child cache / of the depth, each in an admissible context; arbitrary MetaM code is not a leaf step) and Reached.start / Reached.step (reach from the root start world by leaf steps) match the independently written types; {nm} mutants rejected (no admissibility, any code as a step, a diagnostic or throw in the framed constructor, the cache write for the depth write, a start at another world, a step without a leaf step or without the previous reach)"

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2mReach
  let Q := `Tests.Gen5.FGCircuitPilotCheck33
  let n ← checkDef "quietR" (X ++ `quietR) (Q ++ `ExpQuiet)
    [Q ++ `QNoReach, Q ++ `QNoReads, Q ++ `QNoQuiet, Q ++ `QOtherEnv, Q ++ `QOtherRoot, Q ++ `QEnvOfOther]
  logInfo m!"FGCIRCUIT33 DEFS-QUIET: quietR (quiet ∧ the Core environment reads as e (ReadsAt) ∧ reached from the root start world w₀) matches the independently written ExpQuiet; {n} mutants rejected (no reach, no ReadsAt, no quiet, another root environment, reach from another world, the environment of another world)"

/-! ## 2. HYPS -/

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2mReach
  let Q := `Tests.Gen5.FGCircuitPilotCheck33
  let mut nm : Nat := 0
  nm := nm + (← checkDef "DRowEnvR" (X ++ `DRowEnvR) (Q ++ `ExpD)
    [Q ++ `DStart, Q ++ `DEndPrem, Q ++ `DNoReach, Q ++ `DNoReads, Q ++ `DNoAdm, Q ++ `DAllFramed, Q ++ `DOtherEnv, Q ++ `DOtherRoot, Q ++ `ExpG])
  nm := nm + (← checkDef "DiagEnvR" (X ++ `DiagEnvR) (Q ++ `ExpG)
    [Q ++ `GStart, Q ++ `GNoReach, Q ++ `GAsD, Q ++ `ExpD])
  nm := nm + (← checkDef "ProfStepR" (X ++ `ProfStepR) (Q ++ `ExpPS)
    [Q ++ `PSStart, Q ++ `PSEndPrem, Q ++ `PSNoReach, Q ++ `PSAnyStep, Q ++ `PSOn, Q ++ `PSOtherRoot])
  nm := nm + (← checkDef "ProfOffW" (X ++ `ProfOffW) (Q ++ `ExpProfOff) [Q ++ `ProfOnW, Q ++ `ProfOffOnlyOne])
  nm := nm + (← checkDef "AdmDownR" (X ++ `AdmDownR) (Q ++ `ExpDown) [Q ++ `DownUp, Q ++ `DownId, Q ++ `DownOtherEnv])
  nm := nm + (← checkDef "TeleR" (X ++ `TeleR) (Q ++ `ExpT) [Q ++ `TPlain, Q ++ `TNoReach, Q ++ `TOtherEnv])
  logInfo m!"FGCIRCUIT33 HYPS: the six named run-local hypotheses (class-D rows D.T-4m1, diagnostic rows D.T-4m2, telescope rows D.T-4m3, profile along leaf steps D.T-4m4, contexts D.T-4m7; the root profile fact D.T-4m5 is ProfOffW at w) match the independently written types; {nm} mutants rejected (conclusion at the START world, premise at the END world, no reach premise, no ReadsAt premise, no admissibility, the class widened to every framed row or narrowed to diagnostics, another root environment, reach from another world, any step instead of a leaf step, the profile lookup ON instead of off, only one profile conjunct, the context law reversed / trivial / at another environment, the telescope law at the plain / reach-free / other-environment quiet predicate)"

/-! ## 3. SIGNATURES -/

section Sigs
variable {mref : Rf1} {cref : Rf2}

/-- `missR`, complete: from the root profile fact and its step frame, the evidence at every `JQH` world over `ropsR` where a miss occurs. Knobs: the root fact / the step frame premise, the ReadsAt / profile conjuncts, the environment. -/
def ExpMissR (needP needS : Bool) (concl : Nat) : Prop :=
  ∀ {mref : Rf1} {cref : Rf2} {O : RefLawsAOps MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
    {w₀ : W} {hdown : AdmDownR O e w₀} {hD : DRowEnvR O e w₀} {hG : DiagEnvR O e w₀},
    Pre needP (ExpProfOff mref cref w₀) (
    Pre needS (ExpPS O w₀) (
    ∀ (mctx : Cx) (cctx : Cc), AdmCtx (ropsR O hcell e w₀ hdown hD hG).quiet mctx cctx →
      ∀ (D : Nat), 1 ≤ D → ∀ (n : Name) (w : W),
        (JQ (ropsR O hcell e w₀ hdown hD hG).quiet D w ∧
          ∀ c r, (cv w).get? c = some r → RealChildE (ropsR O hcell e w₀ hdown hD hG)
            (fun mctx cctx w => ReadsAt e cref w ∧ GetEnvProfileAt mctx mref cctx cref w) c r) →
        (cv w).get? n = none →
        (if concl == 0 then ReadsAt e cref w ∧ GetEnvProfileAt mctx mref cctx cref w
         else if concl == 1 then ReadsAt e cref w
         else if concl == 2 then GetEnvProfileAt mctx mref cctx cref w
         else ReadsAt e cref w ∧ ProfOnW mref cref w)))
def MissR_real : Prop := ExpMissR true true 0
def MissR_noP : Prop := ExpMissR false true 0
def MissR_noS : Prop := ExpMissR true false 0
def MissR_onlyReads : Prop := ExpMissR true true 1
def MissR_onlyProf : Prop := ExpMissR true true 2
def MissR_profOn : Prop := ExpMissR true true 3
/-- the plain bundle instead of `ropsR`: the S2h miss premise (a world of the history, not tied to the root) -/
def MissR_plain : Prop :=
  ∀ {mref : Rf1} {cref : Rf2} {O : RefLawsAOps MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
    {w₀ : W} {hdown : AdmDownR O e w₀} {hD : DRowEnvR O e w₀} {hG : DiagEnvR O e w₀},
    ExpProfOff mref cref w₀ → ExpPS O w₀ →
    ∀ (mctx : Cx) (cctx : Cc), AdmCtx O.quiet mctx cctx →
      ∀ (D : Nat), 1 ≤ D → ∀ (n : Name) (w : W),
        (JQ O.quiet D w ∧ ∀ c r, (cv w).get? c = some r → RealChildE O
            (fun mctx cctx w => ReadsAt e cref w ∧ GetEnvProfileAt mctx mref cctx cref w) c r) →
        (cv w).get? n = none → ReadsAt e cref w ∧ GetEnvProfileAt mctx mref cctx cref w
/-- the evidence of ANOTHER environment -/
def MissR_otherEnv : Prop :=
  ∀ {mref : Rf1} {cref : Rf2} {O : RefLawsAOps MkRefd mref cref} {hcell : CellPrem MkRefd mref cref} {e : Environment}
    {w₀ : W} {hdown : AdmDownR O e w₀} {hD : DRowEnvR O e w₀} {hG : DiagEnvR O e w₀} {e' : Environment},
    ExpProfOff mref cref w₀ → ExpPS O w₀ →
    ∀ (mctx : Cx) (cctx : Cc), AdmCtx (ropsR O hcell e w₀ hdown hD hG).quiet mctx cctx →
      ∀ (D : Nat), 1 ≤ D → ∀ (n : Name) (w : W),
        (JQ (ropsR O hcell e w₀ hdown hD hG).quiet D w ∧
          ∀ c r, (cv w).get? c = some r → RealChildE (ropsR O hcell e w₀ hdown hD hG)
            (fun mctx cctx w => ReadsAt e cref w ∧ GetEnvProfileAt mctx mref cctx cref w) c r) →
        (cv w).get? n = none → ReadsAt e' cref w ∧ GetEnvProfileAt mctx mref cctx cref w

/-- `jqhr_head`, complete. Knobs: the conclusion's depth, the start depth, the head, the bundle (`ropsR` / the plain one), the environment of the evidence (the root start world / the world after the head). -/
def ExpHeadR (depth d0 : Nat) (off plain envEnd : Bool) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {O : RefLawsAOps MkRefd mref cref} {hcell : CellPrem MkRefd mref cref}
    {w₀ : W} {hdown : AdmDownR O (envAt cref w₀) w₀} {hD : DRowEnvR O (envAt cref w₀) w₀} {hG : DiagEnvR O (envAt cref w₀) w₀},
    AdmCtx (ExpQuiet O.quiet mref cref (envAt cref w₀) w₀) mctx cctx → JQ O.quiet d0 w₀ →
    ∀ {X : Name} {w1 : W} {s : CoreSaved},
      RunsTo (if off then coreHeadOff X else Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w₀ s w1 →
      (if plain then
        JQH O (fun mctx cctx w => ReadsAt (envAt cref (if envEnd then w1 else w₀)) cref w ∧ GetEnvProfileAt mctx mref cctx cref w) depth w1
      else
        JQH (ropsR O hcell (envAt cref w₀) w₀ hdown hD hG)
          (fun mctx cctx w => ReadsAt (envAt cref w₀) cref w ∧ GetEnvProfileAt mctx mref cctx cref w) depth w1)
def Head_real : Prop := ExpHeadR (0 + 1) 0 true false false
def Head_depth0 : Prop := ExpHeadR 0 0 true false false
def Head_start1 : Prop := ExpHeadR (0 + 1) 1 true false false
def Head_diag : Prop := ExpHeadR (0 + 1) 0 false false false
def Head_plain : Prop := ExpHeadR (0 + 1) 0 true true false
def Head_plainEnd : Prop := ExpHeadR (0 + 1) 0 true true true
end Sigs


/-- `hftCoreCloses_of_kidsR`, complete. Knobs: which premises are present; `fEnv` the world whose environment is the root environment (real: `w`), `fRoot` the world the reach starts from (real: `w`), `fProf` the world of the root profile fact (real: `w`), `fW` the conclusion's world; `profOn` replaces the root profile fact by the profile lookup ON. -/
def ExpCoreR (needStart needCell needR needG needAdm needDown needD needGd needT needS need0 concl profOn : Bool)
    (fEnv fRoot fProf fW : W → W) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : Laws mref cref) {w : W},
    Pre needStart (Start L mctx cctx w) (
    Pre needCell (CellPrem MkRefd mref cref) (
    ∀ {lvl : Lean.Expr → Nat},
    Pre needR (RootReader lvl (envAt cref w) NmHttp HttpData) (
    Pre needR (RootReader lvl (envAt cref w) NmTlp TlpData) (
    Pre needG (ExpKidsGates (envAt cref w) NmHttp NmTlp) (
    Pre needAdm (AdmCtx (ExpQuiet L.O.quiet mref cref (envAt cref (fEnv w)) (fRoot w)) mctx cctx) (
    Pre needDown (ExpDown L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needD (ExpD L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needGd (ExpG L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needT (ExpT L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needS (ExpPS L.O (fRoot w)) (
    Pre need0 (if profOn then ProfOnW mref cref (fProf w) else ExpProfOff mref cref (fProf w)) (
    if concl then HftCoreCloses mctx mref cctx cref (fW w) else True))))))))))))
def CR_real : Prop := ExpCoreR true true true true true true true true true true true true false idW idW idW idW
def CR_noStart : Prop := ExpCoreR false true true true true true true true true true true true false idW idW idW idW
def CR_noCell : Prop := ExpCoreR true false true true true true true true true true true true false idW idW idW idW
def CR_noReaders : Prop := ExpCoreR true true false true true true true true true true true true false idW idW idW idW
def CR_noGates : Prop := ExpCoreR true true true false true true true true true true true true false idW idW idW idW
def CR_noAdm : Prop := ExpCoreR true true true true false true true true true true true true false idW idW idW idW
def CR_noDown : Prop := ExpCoreR true true true true true false true true true true true true false idW idW idW idW
def CR_noD : Prop := ExpCoreR true true true true true true false true true true true true false idW idW idW idW
def CR_noG : Prop := ExpCoreR true true true true true true true false true true true true false idW idW idW idW
def CR_noT : Prop := ExpCoreR true true true true true true true true false true true true false idW idW idW idW
def CR_noS : Prop := ExpCoreR true true true true true true true true true false true true false idW idW idW idW
def CR_no0 : Prop := ExpCoreR true true true true true true true true true true false true false idW idW idW idW
def CR_noConcl : Prop := ExpCoreR true true true true true true true true true true true false false idW idW idW idW
/-- control: the profile lookup is ON at the root start world -/
def CR_profOn : Prop := ExpCoreR true true true true true true true true true true true true true idW idW idW idW
/-- control: another root environment (the environment of an independent world `a`) -/
def CR_otherEnv : Prop := ∀ {a : W}, ExpCoreR true true true true true true true true true true true true false (fun _ => a) idW idW idW
/-- control: the world is not reached from the root run's start world (reach from an independent world `a`) -/
def CR_notReached : Prop := ∀ {a : W}, ExpCoreR true true true true true true true true true true true true false idW (fun _ => a) idW idW
/-- control: the root profile fact is about an independent world -/
def CR_profOther : Prop := ∀ {a : W}, ExpCoreR true true true true true true true true true true true true false idW idW (fun _ => a) idW
/-- control: the conclusion about an independent (end) world -/
def CR_endWorld : Prop := ∀ {a : W}, ExpCoreR true true true true true true true true true true true true false idW idW idW (fun _ => a)

set_option maxHeartbeats 16000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2mReach
  let Q := `Tests.Gen5.FGCircuitPilotCheck33
  let q (n : String) : Lean.Expr := Lean.mkConst (Q ++ Name.mkSimple n)
  -- missR
  let missT ← tyOf (X ++ `missR)
  agree "missR" missT (q "MissR_real")
  let mut n1 : Nat := 0
  for mu in ["MissR_noP", "MissR_noS", "MissR_onlyReads", "MissR_onlyProf", "MissR_profOn", "MissR_plain", "MissR_otherEnv"] do
    differ s!"missR vs {mu}" missT (q mu); n1 := n1 + 1
  unless binderKinds (← norm4 missT) == binderKinds (← norm4 (q "MissR_real")) do throwError "missR: binder kinds differ"
  -- jqhr_head
  let headT ← tyOf (X ++ `jqhr_head)
  agree "jqhr_head" headT (q "Head_real")
  let mut n2 : Nat := 0
  for mu in ["Head_depth0", "Head_start1", "Head_diag", "Head_plain", "Head_plainEnd"] do
    differ s!"jqhr_head vs {mu}" headT (q mu); n2 := n2 + 1
  unless binderKinds (← norm4 headT) == binderKinds (← norm4 (q "Head_real")) do throwError "jqhr_head: binder kinds differ"
  logInfo m!"FGCIRCUIT33 SIGNATURES-INV: the complete types of missR (the evidence ReadsAt e ∧ profile-off at every JQH world over the strengthened bundle ropsR where a miss occurs, from the root profile fact and its leaf-step frame) and jqhr_head (the profile-free head of the root run establishes JQHR at depth 1 from JQ at depth 0 and an admissible root context) match the independently written types (binder kinds too); mutants rejected: missR {n1} (no root fact, no step frame, only reads, only profile, profile ON, the plain bundle instead of ropsR, another environment), jqhr_head {n2} (depth 0, start depth 1, the diagnostic head, the plain bundle, the environment of the world after the head)"

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2mReach
  let Q := `Tests.Gen5.FGCircuitPilotCheck33
  let q (n : String) : Lean.Expr := Lean.mkConst (Q ++ Name.mkSimple n)
  let coreT ← tyOf (X ++ `hftCoreCloses_of_kidsR)
  agree "hftCoreCloses_of_kidsR" coreT (q "CR_real")
  unless binderKinds (← norm4 coreT) == binderKinds (← norm4 (q "CR_real")) do throwError "hftCoreCloses_of_kidsR: binder kinds differ"
  let names := binderNames (← instantiateMVars coreT) |>.map (·.toString)
  let exp0 := ["mctx", "mref", "cctx", "cref", "L", "w", "hstart", "hcell", "lvl", "hrH", "hrT", "hg", "hadm", "hdown", "hD", "hG", "hT", "hs", "h0"]
  unless names == exp0 do throwError "hftCoreCloses_of_kidsR binders: {names}"
  let mut n : Nat := 0
  for mu in ["CR_noStart", "CR_noCell", "CR_noReaders", "CR_noGates", "CR_noAdm", "CR_noDown", "CR_noD", "CR_noG", "CR_noT", "CR_noS", "CR_no0", "CR_noConcl",
      "CR_profOn", "CR_otherEnv", "CR_notReached", "CR_profOther", "CR_endWorld"] do
    differ s!"hftCoreCloses_of_kidsR vs {mu}" coreT (q mu); n := n + 1
  logInfo m!"FGCIRCUIT33 SIGNATURES-CORE: the complete type of hftCoreCloses_of_kidsR (hmiss : MissE … of hftCoreCloses_of_kidsH replaced by the seven premises hadm hdown hD hG hT hs h0 about the strengthened quiet predicate of the root start world w; binders {exp0}) matches the independently written type (binder kinds too); {n} mutants rejected: each premise dropped (13), and the four controls — the profile lookup ON at the root, another root environment, a world NOT reached from the root run's start world (reach from an independent world), the root profile fact or the conclusion about an independent (end) world"

/-! ## 4. STEPS (structural), CONTROLS, REMAINING, AXIOMS -/

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2mReach
  let mut nm : Nat := 0
  -- the steps of the induction are the S2h theorems at ropsR: they mention ropsR, KidEv, RealChildE/ChildrenRealE and TeleR, and no plain MissE / KidStartEnv / MachineDefines
  for n in [`jqhr_synthesizeChild, `jqhr_closeInstsM, `jqhr_closeInstsGM, `jqhr_core, `jqhr_childKeeps, `jqhr_bodyStep] do
    let t ← tyOf (X ++ n)
    let uses := t.getUsedConstants
    unless uses.contains ``ropsR do throwError "{n} does not mention ropsR"
    unless uses.contains ``TeleR do throwError "{n} does not take the telescope rows TeleR"
    for bad in [``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine,
        ``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingFGCircuitS2hHist.MissE] do
      if uses.contains bad then throwError "{n} mentions {bad}"
    nm := nm + 9
  -- the core theorem: no MissE, no KidStartEnv, takes the named hypotheses
  let ct ← tyOf (X ++ `hftCoreCloses_of_kidsR)
  let cu := ct.getUsedConstants
  for bad in [``Tools.ShippingFGCircuitS2hHist.MissE, ``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv,
      ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingMachineEntry.MachineCloses] do
    if cu.contains bad then throwError "hftCoreCloses_of_kidsR mentions {bad}"
  nm := nm + 6
  -- the reach walk: MachineDefines and friends are not reachable from the seven hypotheses (within the walk over defnInfo types/values under Tools/Sparkle)
  let env ← getEnv
  let r := reach env [``DRowEnvR, ``DiagEnvR, ``ProfStepR, ``ProfOffW, ``AdmDownR, ``TeleR, ``quietR, ``ropsR, ``JQHR] {}
  for bad in [``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineCloses,
      ``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2hHist.MissE] do
    if r.contains bad then throwError "{bad} is reachable from the new hypotheses within the walk"
  for good in [``Tools.ShippingFGCircuitS1oHead.GetEnvProfileAt, ``Tools.ShippingGen5Env.ReadsAt, ``Tools.ShippingGen5EnvFrame3.DRow, ``Tools.ShippingGen5EnvFrame3.CellPrem] do
    unless r.contains good do throwError "{good} is not reached from the new definitions"
  nm := nm + 9
  logInfo m!"FGCIRCUIT33 STEPS: the preservation lemmas of the induction (jqhr_synthesizeChild: miss and hit, jqhr_closeInstsM / jqhr_closeInstsGM, jqhr_core: the core chain, jqhr_childKeeps, jqhr_bodyStep: the machine body) are stated at ropsR with the telescope rows TeleR and mention none of MissE / KidStartEnv / HftKidsDefine / MachineDefines / MachineCloses; hftCoreCloses_of_kidsR mentions none of them either; {nm} structural checks. Within the reach walk (types and values of defnInfo under Tools/Sparkle; inductive constructors and theorems are not unfolded; reach set {r.size}) MachineDefines, HftKidsDefine, MachineCloses, KidStartEnv and MissE are NOT reachable from the new hypotheses; this is not a claim about the whole dependency closure"

section Ctl
variable {mref : Rf1} {cref : Rf2}
/-- control: a world that is not reached from the root start world is not in the strengthened quiet predicate -/
theorem ctl_notReached {quiet : W → Prop} {e : Environment} {w₀ w : W} (h : ¬ Reached quiet mref cref w₀ w) :
    ¬ quietR quiet mref cref e w₀ w := fun hq => h hq.2.2
/-- control: a world of the strengthened quiet predicate reads the root environment (so a world reading another environment is excluded) -/
theorem ctl_reads {quiet : W → Prop} {e : Environment} {w₀ w : W} (h : quietR quiet mref cref e w₀ w) :
    ReadsAt e cref w := h.2.1
/-- control: the root start world is in the strengthened quiet predicate, with its own environment (`e = envAt cref w₀`), when it is quiet -/
theorem ctl_root {quiet : W → Prop} {w₀ : W} (h : quiet w₀) : quietR quiet mref cref (envAt cref w₀) w₀ w₀ :=
  ⟨h, Tools.ShippingGen5Env.readsAt_self cref w₀, .start⟩
/-- control: one leaf step from a quiet-reached world is reached (the closure used by the field proofs) -/
theorem ctl_step {quiet : W → Prop} {w₀ w w' : W} (h : Reached quiet mref cref w₀ w) (hs : LeafStep quiet mref cref w w') :
    Reached quiet mref cref w₀ w' := .step h hs
/-- control: the profile lookup cannot be both off and on at a world from which the lookup runs (some run exists) -/
theorem ctl_profile {mctx : Cx} {cctx : Cc} {w : W} {o : Option String} {w1 : W}
    (hr : RunsTo profileAct mctx mref cctx cref w o w1) (hoff : ExpProfOff mref cref w) (hon : ProfOnW mref cref w) : False := by
  have h1 := (hoff mctx cctx).unset o w1 hr
  have h2 := hon mctx cctx o w1 hr
  rw [h1] at h2
  cases h2
end Ctl

run_cmd liftTermElabM do
  let X := `Tests.Gen5.FGCircuitPilotCheck33
  for n in [`ctl_notReached, `ctl_reads, `ctl_root, `ctl_step, `ctl_profile] do
    for ax in ← Lean.collectAxioms (X ++ n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{n} uses {ax}"
  logInfo m!"FGCIRCUIT33 CONTROLS: kernel-checked: a world not reached from the root start world is outside the strengthened quiet predicate (ctl_notReached), a world inside it reads the root environment (ctl_reads), the quiet root start world is inside it with its own environment (ctl_root), a leaf step from a reached world is reached (ctl_step), and the profile lookup cannot be both off and on at a world from which the lookup runs (ctl_profile); the four statement-level controls (profile ON, another root environment, a world not reached from the root, an end world) are the mutants CR_profOn / CR_otherEnv / CR_notReached / CR_endWorld / CR_profOther of SIGNATURES-CORE, DStart / DEndPrem / GStart / PSStart / PSEndPrem of HYPS"

run_cmd liftTermElabM do
  let lines := [
    "hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx [FG D.T-4m6] (the root context is admissible for the strengthened quiet predicate)",
    "hdown : AdmDownR L.O (envAt cref w) w [FG D.T-4m7] (a context admissible for the strengthened quiet predicate is admissible for the plain one)",
    "hD : DRowEnvR L.O (envAt cref w) w [FG D.T-4m1] (class-D rows keep ReadsAt on quiet worlds reached from w)",
    "hG : DiagEnvR L.O (envAt cref w) w [FG D.T-4m2] (diagnostic rows keep ReadsAt on quiet worlds reached from w)",
    "hT : TeleR L.O (envAt cref w) w [FG D.T-4m3] (the four telescope rows of RefLawsATele at the strengthened quiet predicate)",
    "hs : ProfStepR L.O w [FG D.T-4m4] (a leaf step from a reached world keeps the profile lookup unset)",
    "h0 : ProfOffW mref cref w [FG D.T-4m5] (the profile lookup is unset at the root start world)"]
  for l in lines do logInfo m!"FGCIRCUIT33 REMAINING {l}"

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2mReach
  let names : List Name := [X ++ `Reached.leafFrame, X ++ `ropsR, X ++ `profOffW_of_reached, X ++ `jqhr_facts, X ++ `missR, X ++ `jqhr_head,
    X ++ `jqhr_bodyStep, X ++ `jqhr_childKeeps, X ++ `jqhr_synthesizeChild, X ++ `jqhr_closeInstsM, X ++ `jqhr_closeInstsGM, X ++ `jqhr_core, X ++ `hftCoreCloses_of_kidsR]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT33 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck33
