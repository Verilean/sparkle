import Tools.ShippingGen5AccReads
import Tests.Gen5.AccCheck
set_option autoImplicit false
-- NOT BUILT (new file; the coder's clean build is pending). No sorry / axiom / native_decide in this source.

/-! # DG-ACC rev2 R1/R2 checks (Tools/ShippingGen5AccReads.lean; scripts/gen5/DG_ACC_FREEZE_REV2.md §B.2, §C.2)

TYPE: every definition and every theorem is compared binder by binder (`checkExpected`) with an independently written `Expected…`
statement (the statements are written from the prose of REV2 §B-§C, not copied from the implementation file); all comparisons use
the same `cmpTele` comparator (syntactic `==` first, `isDefEq` fallback, logged).
MUTANT: one-place, well-typed changes (or a dropped conjunct) rejected by `checkMutant` -- a rejection by signature / defeq, NOT a
semantic counterexample. AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck`, with its negative/clean
controls and the unknown-name controls re-run. -/
namespace Tests.Gen5.AccReadsCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tests.Gen3.ExpectedType
open Tools.ShippingGen2 (Laws LimitStmt Start)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (CoreSaved coreHead)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildVCA (JQ)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildBndCore (dv)
open Tools.ShippingGen5Env (ReadsAt MachineDefinesR)
open Tools.ShippingEnvSnapshot (GetEnvFrame)

section Expected
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

def ExpectedQuietStrengthA (L L' : Laws mref cref) (e : Environment) : Prop :=
  ∀ w, L'.O.quiet w ↔ (L.O.quiet w ∧ ReadsAt e cref w)

def ExpectedAdmDownA (L L' : Laws mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L'.O.quiet mctx cctx → AdmCtx L.O.quiet mctx cctx

def ExpectedChainReadsAt (e : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (X : Name) (w : Void IO.RealWorld) : Prop :=
  ∀ (s : CoreSaved) (w1 w2 w3 w5 : Void IO.RealWorld) (ci : ConstantInfo) (envR envR' : Environment),
    RunsTo (coreHead X) mctx mref cctx cref w s w1 →
    RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
    ReadsAt e cref w1 ∧ ReadsAt e cref w2 ∧ ReadsAt e cref w3

def ExpectedReadsSupplyAt (e : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ X, Reach X → ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld),
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → ChainReadsAt e mctx mref cctx cref X w

/-- The theorem statements, from the prose of REV2 §B.2/§C.2. -/
def ExpectedMachineDefinesAtChain : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {e : Environment}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {shape : MachineShape} {w : Void IO.RealWorld},
    (hD : MachineDefinesR e mctx mref cctx cref X shape) → (hR : ChainReadsAt e mctx mref cctx cref X w) →
    ∀ {s : CoreSaved} {w1 w2 w3 w5 : Void IO.RealWorld} {ci : ConstantInfo} {envR envR' : Environment},
      (h0 : RunsTo (coreHead X) mctx mref cctx cref w s w1) →
      (h1 : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2) →
      (h2 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3) →
      (h3 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5) →
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (instancePredicate envR) = none ∧
      machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') = some shape

def ExpectedReadsSupplyOfQuiet : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {e : Environment}, (hq : QuietStrengthA L L' e) →
    (hg : ∀ (mctx : Meta.Context) (cctx : Core.Context), GetEnvFrame mctx mref cctx cref) →
    ∀ (Reach : Name → Prop), ReadsSupplyAt e L' Reach

def ExpectedAccInvAtReadsAt : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    {L L' : Laws mref cref} {e : Environment}, (hq : QuietStrengthA L L' e) →
    ∀ {Reach : Name → Prop} {D : Nat} {w : Void IO.RealWorld}, (h : AccInvAt K L' Reach D w) → ReadsAt e cref w

def ExpectedAccInvAtDown : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    {L L' : Laws mref cref} {e : Environment}, (hq : QuietStrengthA L L' e) → (hd : AdmDownA L L') →
    ∀ {Reach : Name → Prop} {D : Nat} {w : Void IO.RealWorld}, (h : AccInvAt K L' Reach D w) → AccInvAt K L Reach D w

def ExpectedAccOfEdge : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X c : Name}, (h : Acc (CallRel K) X) → (he : CallEdge K X c) → Acc (CallRel K) c

def ExpectedAccReachOfTop : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {Top : Name → Prop}, (hT : ∀ t, Top t → Acc (CallRel K) t) → ∀ c, ReachEdge K Top c → Acc (CallRel K) c

def ExpectedAccTopOfRun : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop), (hS : AccServed0Stmt K L Reach) → (hI : AccIHAt K L Reach 1) →
    (hKI : AccChildKeeps K L Reach 1) → ∀ {t : Name}, (ht : Reach t) →
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {r : Res},
      (hSt : Start L mctx cctx w) → (hr : RunsTo (synthesizeCombinationalCore t [] false) mctx mref cctx cref w r w') →
      Acc (CallRel K) t

def ExpectedHaccOfTopRuns : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Top : Name → Prop), (hLim : LimitStmt L) → (hS : AccServed0Stmt K L (ReachEdge K Top)) →
    (hKC : AccKeepChildStmt K L (ReachEdge K Top)) →
    (hrun : ∀ t, Top t → ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
      Start L mctx cctx w ∧ RunsTo (synthesizeCombinationalCore t [] false) mctx mref cctx cref w r w') →
    ∀ c, ReachEdge K Top c → Acc (CallRel K) c

-- mutants (each well-typed, one place changed; signature/defeq rejection only)
def MutQuietOr (L L' : Laws mref cref) (e : Environment) : Prop :=
  ∀ w, L'.O.quiet w ↔ (L.O.quiet w ∨ ReadsAt e cref w)

def MutAdmDownReversed (L L' : Laws mref cref) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx → AdmCtx L'.O.quiet mctx cctx

/-- the third conjunct (world `w3`) dropped -/
def MutChainDropW3 (e : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (X : Name) (w : Void IO.RealWorld) : Prop :=
  ∀ (s : CoreSaved) (w1 w2 w3 w5 : Void IO.RealWorld) (ci : ConstantInfo) (envR envR' : Environment),
    RunsTo (coreHead X) mctx mref cctx cref w s w1 →
    RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
    ReadsAt e cref w1 ∧ ReadsAt e cref w2

/-- `ReadsAt` asked at the start world `w` instead of `w1` -/
def MutChainStartWorld (e : Environment) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (X : Name) (w : Void IO.RealWorld) : Prop :=
  ∀ (s : CoreSaved) (w1 w2 w3 w5 : Void IO.RealWorld) (ci : ConstantInfo) (envR envR' : Environment),
    RunsTo (coreHead X) mctx mref cctx cref w s w1 →
    RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
    ReadsAt e cref w ∧ ReadsAt e cref w2 ∧ ReadsAt e cref w3

/-- the admissibility premise dropped from the supply -/
def MutSupplyNoAdm (e : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ X, Reach X → ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld),
    JQC L.O (dv w) w → ChainReadsAt e mctx mref cctx cref X w

/-- the supply at a name that need not be reached -/
def MutSupplyAnyName (e : Environment) (L : Laws mref cref) (_Reach : Name → Prop) : Prop :=
  ∀ X, ∀ (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld),
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → ChainReadsAt e mctx mref cctx cref X w

/-- the conclusion of `machineDefines_at_chain` loses its machine-shape conjunct -/
def MutMachineDefinesDropConj : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {e : Environment}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {shape : MachineShape} {w : Void IO.RealWorld},
    (hD : MachineDefinesR e mctx mref cctx cref X shape) → (hR : ChainReadsAt e mctx mref cctx cref X w) →
    ∀ {s : CoreSaved} {w1 w2 w3 w5 : Void IO.RealWorld} {ci : ConstantInfo} {envR envR' : Environment},
      (h0 : RunsTo (coreHead X) mctx mref cctx cref w s w1) →
      (h1 : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2) →
      (h2 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3) →
      (h3 : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5) →
      certifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) = none ∧
      mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (instancePredicate envR) = none

/-- the `GetEnvFrame` premise dropped from `readsSupply_of_quiet` -/
def MutSupplyOfQuietNoFrame : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {e : Environment}, (hq : QuietStrengthA L L' e) → ∀ (Reach : Name → Prop), ReadsSupplyAt e L' Reach

/-- the supply concluded at `L` instead of the quiet-strengthened `L'` (the thing the freeze says is NOT claimed) -/
def MutSupplyOfQuietAtL : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {L L' : Laws mref cref}
    {e : Environment}, (hq : QuietStrengthA L L' e) →
    (hg : ∀ (mctx : Meta.Context) (cctx : Core.Context), GetEnvFrame mctx mref cctx cref) →
    ∀ (Reach : Name → Prop), ReadsSupplyAt e L Reach

/-- `acc_of_edge` in the wrong direction (from the callee to the caller) -/
def MutAccEdgeReversed : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X c : Name}, (h : Acc (CallRel K) c) → (he : CallEdge K X c) → Acc (CallRel K) X

/-- `hacc_of_top_runs` without `LimitStmt` -/
def MutHaccNoLimit : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Top : Name → Prop), (hS : AccServed0Stmt K L (ReachEdge K Top)) →
    (hKC : AccKeepChildStmt K L (ReachEdge K Top)) →
    (hrun : ∀ t, Top t → ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
      Start L mctx cctx w ∧ RunsTo (synthesizeCombinationalCore t [] false) mctx mref cctx cref w r w') →
    ∀ c, ReachEdge K Top c → Acc (CallRel K) c

/-- `hacc_of_top_runs` without the successful-run premise on the tops -/
def MutHaccNoRun : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Top : Name → Prop), (hLim : LimitStmt L) → (hS : AccServed0Stmt K L (ReachEdge K Top)) →
    (hKC : AccKeepChildStmt K L (ReachEdge K Top)) → ∀ c, ReachEdge K Top c → Acc (CallRel K) c

/-- `hacc_of_top_runs` concluding `Acc` only for the tops themselves -/
def MutHaccOnlyTops : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Top : Name → Prop), (hLim : LimitStmt L) → (hS : AccServed0Stmt K L (ReachEdge K Top)) →
    (hKC : AccKeepChildStmt K L (ReachEdge K Top)) →
    (hrun : ∀ t, Top t → ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
      Start L mctx cctx w ∧ RunsTo (synthesizeCombinationalCore t [] false) mctx mref cctx cref w r w') →
    ∀ c, Top c → Acc (CallRel K) c

/-- `acc_top_of_run` without the run -/
def MutTopOfRunNoRun : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop), (hS : AccServed0Stmt K L Reach) → (hI : AccIHAt K L Reach 1) →
    (hKI : AccChildKeeps K L Reach 1) → ∀ {t : Name}, (ht : Reach t) →
    ∀ {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {r : Res},
      (hSt : Start L mctx cctx w) → Acc (CallRel K) t
end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``QuietStrengthA ``ExpectedQuietStrengthA
  checkExpected ``AdmDownA ``ExpectedAdmDownA
  checkExpected ``ChainReadsAt ``ExpectedChainReadsAt
  checkExpected ``ReadsSupplyAt ``ExpectedReadsSupplyAt
  checkExpected ``machineDefines_at_chain ``ExpectedMachineDefinesAtChain
  checkExpected ``readsSupply_of_quiet ``ExpectedReadsSupplyOfQuiet
  checkExpected ``accInvAt_readsAt ``ExpectedAccInvAtReadsAt
  checkExpected ``accInvAt_down ``ExpectedAccInvAtDown
  checkExpected ``acc_of_edge ``ExpectedAccOfEdge
  checkExpected ``acc_reach_of_top ``ExpectedAccReachOfTop
  checkExpected ``acc_top_of_run ``ExpectedAccTopOfRun
  checkExpected ``hacc_of_top_runs ``ExpectedHaccOfTopRuns
  checkMutant ``QuietStrengthA ``MutQuietOr
  checkMutant ``AdmDownA ``MutAdmDownReversed
  checkMutant ``ChainReadsAt ``MutChainDropW3
  checkMutant ``ChainReadsAt ``MutChainStartWorld
  checkMutant ``ReadsSupplyAt ``MutSupplyNoAdm
  checkMutant ``ReadsSupplyAt ``MutSupplyAnyName
  checkMutant ``machineDefines_at_chain ``MutMachineDefinesDropConj
  checkMutant ``readsSupply_of_quiet ``MutSupplyOfQuietNoFrame
  checkMutant ``readsSupply_of_quiet ``MutSupplyOfQuietAtL
  checkMutant ``acc_of_edge ``MutAccEdgeReversed
  checkMutant ``hacc_of_top_runs ``MutHaccNoLimit
  checkMutant ``hacc_of_top_runs ``MutHaccNoRun
  checkMutant ``hacc_of_top_runs ``MutHaccOnlyTops
  checkMutant ``acc_top_of_run ``MutTopOfRunNoRun

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``QuietStrengthA, ``AdmDownA, ``ChainReadsAt, ``ReadsSupplyAt, ``machineDefines_at_chain, ``accInvAt_readsAt,
      ``jqA_down, ``realChildA_downA, ``jqc_downA, ``accInvAt_down, ``readsSupply_of_quiet, ``acc_of_edge, ``acc_reach_of_top,
      ``acc_top_of_run, ``hacc_of_top_runs] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path (see AccIndCheck): root / helper value / helper type naming an
absent constant MUST be reported; a clean chain MUST NOT. -/
def unknownControls : MetaM Unit := do
  let ghost := `Ghost.Absent.name
  let addU (n : Name) (type value : Expr) : MetaM Unit :=
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl (.thmDecl { name := n, levelParams := [], type := type, value := value })
  let unk (roots : List Name) : MetaM (Array Name) := do
    let (_, u, _) ← Tests.Gen5.AccCheck.closureReport (← getEnv) roots
    pure u
  let u1 ← unk [ghost]
  unless u1 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: unknown root not reported ({u1})"
  let u2 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperVal (mkConst ``True) (mkConst ghost)
    addU `Tests.Gen5.UnkCtl.RootVal (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperVal)
    unk [`Tests.Gen5.UnkCtl.RootVal]
  unless u2 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper value naming an unknown constant not reported ({u2})"
  let u3 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperTy (mkConst ghost) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.RootTy (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperTy)
    unk [`Tests.Gen5.UnkCtl.RootTy]
  unless u3 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper type naming an unknown constant not reported ({u3})"
  let u4 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.CleanHelper (mkConst ``True) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.CleanRoot (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.CleanHelper)
    unk [`Tests.Gen5.UnkCtl.CleanRoot]
  unless u4.isEmpty do throwError "GEN5 UNKNOWN CONTROL FAILED: clean control reported unknown ({u4})"
  logInfo m!"GEN5 UNKNOWN CONTROLS OK: 3 negatives reported unknown (root / helper value / helper type), clean control not reported"

run_cmd Lean.Elab.Command.liftTermElabM unknownControls

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``machineDefines_at_chain, ``accInvAt_readsAt, ``accInvAt_down, ``readsSupply_of_quiet, ``acc_of_edge,
    ``acc_reach_of_top, ``acc_top_of_run, ``hacc_of_top_runs]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (R1/R2): {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, no unknown constant"

end Tests.Gen5.AccReadsCheck
