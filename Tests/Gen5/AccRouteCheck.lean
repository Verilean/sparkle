import Tools.ShippingGen5AccRoute
import Tests.Gen5.AccCheck
-- Built (coder, issue-linked incremental build ac8v-da5a6106, approved at da5a6106): `kjob lake build Tests.Gen5.AccRouteCheck`, exit 0, 724 jobs, source=base=end, dirty=false. TYPE 4 (2 definitions by body + 2 theorems, all syntactic, no isDefEq fallback) / MUTANT 8 (signature/defeq rejection, not semantic: 3 on definitions, 3 on machineRouteAt_of_cover, 2 on accServed0_of_cover_gates) / AXIOMS 4 (standard three; = the 4 TYPE items) / CLOSURE OK 13305 constants (unknown 0) / walker controls 4 negatives / unknown controls 3 negatives + 1 clean. CLOSURE scope: `closureReport` walks `getUsedConstants` of types and values (the constants a declaration mentions); it is NOT an audit specific to raw projections. No sorry / axiom / native_decide in this source; the 6 `sorry` warnings of the build are the intended walker-control negatives: 3 at the walkerControls line of Tests/Gen5/AccCheck.lean (:238) and 3 at the walkerControls line of this file (:137).
-- Built in the Pod (g5ac-r8) at 36376724: `kjob lake build Tests.Gen5.AccRouteCheck`, exit 0, 724 jobs. TYPE 4 (2 definitions by body + 2 theorems, all syntactic, no isDefEq fallback) / MUTANT 8 (signature/defeq rejection, not semantic: 3 on definitions, 3 on machineRouteAt_of_cover, 2 on accServed0_of_cover_gates) / AXIOMS 4 (standard three; = the 4 TYPE items) / CLOSURE OK 13305 constants (unknown 0) / walker controls 4 negatives / unknown controls 3 negatives + 1 clean. Not yet a clean issue-linked build (coder runs it). No sorry / axiom / native_decide in this source (the 3 `sorry` warnings, at the walkerControls line of the Check, come from the intended walker-control negatives of Tests.Gen5.AccCheck).

/-! # DG-ACC unit A6a checks (Tools/ShippingGen5AccRoute.lean; scripts/gen5/DG_ACC_FREEZE_REV4.md §1)

TYPE: the 2 definitions (`GatesNoneAt`, `ClosesOfShape`; the compared statement is the definition BODY) and the 2 theorems
(`machineRouteAt_of_cover`, `accServed0_of_cover_gates`) are each compared binder by binder (`checkExpected`) with an independently written
`Expected…` statement (written from the prose of REV4 §1, not copied from the implementation file).
MUTANT: one-place, well-typed changes (a dropped premise, a dropped conjunct of the conclusion of a definition, a dropped `AdmCtx` premise), all
compared with the same reducible comparator as TYPE and required to be rejected -- a rejection by signature / defeq, NOT a semantic counterexample.
AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck` with its negative/clean controls and the unknown-name controls re-run;
the roots are put in `seen` and judged. -/
namespace Tests.Gen5.AccRouteCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tests.Gen3.ExpectedType
open Tools.ShippingGen2 (Laws)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingGen5Env (ReadsAt MachineDefinesR)

section Expected

def ExpectedGatesNoneAt (env₀ : Environment) (Reach : Name → Prop) : Prop :=
  ∀ c ci, Reach c → env₀.find? c = some ci →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none ∧
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none

def ExpectedClosesOfShape {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c ci shape, Reach c → env₀.find? c = some ci →
    machineShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
      MachineClosesAtA L.O mctx cctx c shape

def ExpectedRouteOfCover : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcov : ReachCover K Reach) → (hG : GatesNoneAt env₀ Reach) → (hC : ClosesOfShape env₀ L Reach) →
    MachineRouteAt env₀ L Reach

def ExpectedServedCoverGates : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) →
    (hcov : ReachCover K Reach) → (hDS : DataOfShape K) → (hG : GatesNoneAt env₀ Reach) →
    (hC : ClosesOfShape env₀ L Reach) → (hRS : ReadsSupplyAt env₀ L Reach) → AccServed0Stmt K L Reach

-- mutants (each well-typed, one place changed; signature/defeq rejection only)
/-- `GatesNoneAt` with the `mixedCertifiedShape?` conjunct dropped -/
def MutGatesNoMixed (env₀ : Environment) (Reach : Name → Prop) : Prop :=
  ∀ c ci, Reach c → env₀.find? c = some ci →
    certifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) = none

/-- `GatesNoneAt` with the `certifiedShape?` conjunct dropped -/
def MutGatesNoFirst (env₀ : Environment) (Reach : Name → Prop) : Prop :=
  ∀ c ci, Reach c → env₀.find? c = some ci →
    mixedCertifiedShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (instancePredicate env₀) = none

/-- `ClosesOfShape` with the `AdmCtx` premise dropped -/
def MutClosesNoAdm {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c ci shape, Reach c → env₀.find? c = some ci →
    machineShape? false [] (entryConst true false [] ci (instancePredicate env₀) (userInliner env₀)
      (structEnv env₀)) (structEnv env₀) = some shape →
    ∀ (mctx : Meta.Context) (cctx : Core.Context),
      MachineClosesAtA L.O mctx cctx c shape

/-- `machineRouteAt_of_cover` without `hG` -/
def MutRouteNoG : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcov : ReachCover K Reach) → (hC : ClosesOfShape env₀ L Reach) → MachineRouteAt env₀ L Reach

/-- `machineRouteAt_of_cover` without `hC` -/
def MutRouteNoC : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcov : ReachCover K Reach) → (hG : GatesNoneAt env₀ Reach) → MachineRouteAt env₀ L Reach

/-- `machineRouteAt_of_cover` without `hcov` -/
def MutRouteNoCov : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hG : GatesNoneAt env₀ Reach) → (hC : ClosesOfShape env₀ L Reach) → MachineRouteAt env₀ L Reach

/-- `accServed0_of_cover_gates` without `hDS` -/
def MutServedNoDS : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) →
    (hcov : ReachCover K Reach) → (hG : GatesNoneAt env₀ Reach) →
    (hC : ClosesOfShape env₀ L Reach) → (hRS : ReadsSupplyAt env₀ L Reach) → AccServed0Stmt K L Reach

/-- `accServed0_of_cover_gates` without `hRS` -/
def MutServedNoRS : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop),
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) →
    (hcov : ReachCover K Reach) → (hDS : DataOfShape K) → (hG : GatesNoneAt env₀ Reach) →
    (hC : ClosesOfShape env₀ L Reach) → AccServed0Stmt K L Reach

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``GatesNoneAt ``ExpectedGatesNoneAt
  checkExpected ``ClosesOfShape ``ExpectedClosesOfShape
  checkExpected ``machineRouteAt_of_cover ``ExpectedRouteOfCover
  checkExpected ``accServed0_of_cover_gates ``ExpectedServedCoverGates
  checkMutant ``GatesNoneAt ``MutGatesNoMixed
  checkMutant ``GatesNoneAt ``MutGatesNoFirst
  checkMutant ``ClosesOfShape ``MutClosesNoAdm
  checkMutant ``machineRouteAt_of_cover ``MutRouteNoG
  checkMutant ``machineRouteAt_of_cover ``MutRouteNoC
  checkMutant ``machineRouteAt_of_cover ``MutRouteNoCov
  checkMutant ``accServed0_of_cover_gates ``MutServedNoDS
  checkMutant ``accServed0_of_cover_gates ``MutServedNoRS

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``GatesNoneAt, ``ClosesOfShape, ``machineRouteAt_of_cover, ``accServed0_of_cover_gates] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path (see AccServedCheck): root / helper value / helper type naming an
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
  let roots := [``GatesNoneAt, ``ClosesOfShape, ``machineRouteAt_of_cover, ``accServed0_of_cover_gates]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A6a): {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, no unknown constant"

end Tests.Gen5.AccRouteCheck
