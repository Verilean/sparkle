import Tools.ShippingGen5AccInd
import Tests.Gen5.AccCheck
set_option autoImplicit false
-- Built in g5ac-r3 at 174b92b3 (Pod `kjob lake build`, exit 0; the build was of the identical uncommitted content; this header is the only later change). Clean build is the coder's. No sorry / axiom / native_decide in this source.

/-! # DG-ACC unit A4 checks (Tools/ShippingGen5AccInd.lean; scripts/gen5/DG_ACC_FREEZE_REV2.md §B)

TYPE: the definitions are compared binder by binder (`checkExpected`, on definition VALUES) with independently written `Expected…`
statements; each theorem is checked by an `example` against the independent statement (kernel defeq, not a syntactic match).
MUTANT: one-place, well-typed changes rejected by `checkMutant` -- a rejection by signature / defeq, NOT a semantic counterexample.
AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck` (negative/clean controls re-run). -/
namespace Tests.Gen5.AccIndCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tests.Gen3.ExpectedType
open Tools.ShippingGen2 (Laws LimitStmt)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res Keeps profLogIO)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildFrontCP (ChildSynthA)

section Expected
open Classical
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

def ExpectedAccInvAt (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) :
    Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w ∧ CacheAcc K Reach (cv w)

def ExpectedAccIHAt (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context) (u u' : Void IO.RealWorld) (r : Res),
    AdmCtx L.O.quiet mctx cctx → AccInvAt K L Reach D u →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' → Acc (CallRel K) c

def ExpectedAccBodyKeeps (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Keeps mctx mref cctx cref (AccInvAt K L Reach D)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)

def ExpectedAccChildKeeps (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ChildSynthA L.O (AccInvAt K L Reach D)

def ExpectedAccKeepBodyStmt (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ D, AccChildKeeps K L Reach D → AccBodyKeeps K L Reach D

def ExpectedAccKeepChildStmt (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → AccBodyKeeps K L Reach (D + 1)) →
    AccIHAt K L Reach D → AccChildKeeps K L Reach D

def ExpectedAccServed0Stmt (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (X : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    Reach X → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → (dv w = 0 ∨ CacheAcc K Reach (cv w)) →
    AccIHAt K L Reach (dv w + 1) → AccChildKeeps K L Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w r w' →
    ∀ c, CallEdge K X c → Acc (CallRel K) c

def ExpectedAccIHAtStepStmt (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  AccServed0Stmt K L Reach → ∀ (D : Nat), AccIHAt K L Reach (D + 1) → AccChildKeeps K L Reach (D + 1) →
    AccIHAt K L Reach D

def ExpectedAccOfRunStmt (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  LimitStmt L → AccServed0Stmt K L Reach → AccKeepChildStmt K L Reach →
    ∀ D, 1 ≤ D → AccIHAt K L Reach D ∧ AccChildKeeps K L Reach D

-- mutants (each well-typed, one place changed)
/-- rev0's form: the start is `AccInvAt (dv w) w` (no cache disjunct) -/
def MutServedAccStart (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (X : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    Reach X → AdmCtx L.O.quiet mctx cctx → AccInvAt K L Reach (dv w) w →
    AccIHAt K L Reach (dv w + 1) → AccChildKeeps K L Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w r w' →
    ∀ c, CallEdge K X c → Acc (CallRel K) c

/-- no cache disjunct -/
def MutServedNoDisjunct (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (X : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    Reach X → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    AccIHAt K L Reach (dv w + 1) → AccChildKeeps K L Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w r w' →
    ∀ c, CallEdge K X c → Acc (CallRel K) c

/-- every instance is a static edge (the `child? = none` test dropped) -/
def MutServedAnyEdge (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ (X : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (r : Res),
    Reach X → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w → (dv w = 0 ∨ CacheAcc K Reach (cv w)) →
    AccIHAt K L Reach (dv w + 1) → AccChildKeeps K L Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w r w' →
    ∀ c, (∃ d, dataOf₀ K X = some d ∧ ∃ k, ∃ hk : k < d.shape.insts.length, (d.shape.insts[k]'hk).1 = c) →
      Acc (CallRel K) c

/-- the invariant without its cache half -/
def MutInvNoCache (_K : AssignKit ι dom env₀) (L : Laws mref cref) (_Reach : Name → Prop) (D : Nat) :
    Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w

/-- `acc_of_run` without `LimitStmt` -/
def MutOfRunNoLimit (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  AccServed0Stmt K L Reach → AccKeepChildStmt K L Reach →
    ∀ D, 1 ≤ D → AccIHAt K L Reach D ∧ AccChildKeeps K L Reach D

/-- the IH concludes nothing about `c` -/
def MutIHTrivial (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context) (u u' : Void IO.RealWorld) (r : Res),
    AdmCtx L.O.quiet mctx cctx → AccInvAt K L Reach D u →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' → True

/-- the step goes up in depth -/
def MutStepWrongDepth (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  AccServed0Stmt K L Reach → ∀ (D : Nat), AccIHAt K L Reach D → AccChildKeeps K L Reach D →
    AccIHAt K L Reach (D + 1)
end Expected

section Examples
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
example (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) :
    Tools.ShippingChildVCA.StableA L.O.quiet (ExpectedAccInvAt K L Reach D) := stableA_accInvAt K L Reach D
example (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) :
    ExpectedAccKeepBodyStmt K L Reach := accKeepBody K L Reach
example (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) (hL : LimitStmt L) {D : Nat}
    (hD : sparkleSynthDepthLimit ≤ D) : ExpectedAccIHAt K L Reach D := accIHAt_limit K L Reach hL hD
example (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) :
    ExpectedAccIHAtStepStmt K L Reach := accIHAt_step K L Reach
example (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) :
    ExpectedAccOfRunStmt K L Reach := acc_of_run K L Reach
end Examples

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``AccInvAt ``ExpectedAccInvAt
  checkExpected ``AccIHAt ``ExpectedAccIHAt
  checkExpected ``AccBodyKeeps ``ExpectedAccBodyKeeps
  checkExpected ``AccChildKeeps ``ExpectedAccChildKeeps
  checkExpected ``AccKeepBodyStmt ``ExpectedAccKeepBodyStmt
  checkExpected ``AccKeepChildStmt ``ExpectedAccKeepChildStmt
  checkExpected ``AccServed0Stmt ``ExpectedAccServed0Stmt
  checkExpected ``AccIHAtStepStmt ``ExpectedAccIHAtStepStmt
  checkExpected ``AccOfRunStmt ``ExpectedAccOfRunStmt
  checkMutant ``AccServed0Stmt ``MutServedAccStart
  checkMutant ``AccServed0Stmt ``MutServedNoDisjunct
  checkMutant ``AccServed0Stmt ``MutServedAnyEdge
  checkMutant ``AccInvAt ``MutInvNoCache
  checkMutant ``AccOfRunStmt ``MutOfRunNoLimit
  checkMutant ``AccIHAt ``MutIHTrivial
  checkMutant ``AccIHAtStepStmt ``MutStepWrongDepth

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``AccInvAt, ``AccIHAt, ``AccBodyKeeps, ``AccChildKeeps, ``AccKeepBodyStmt, ``AccKeepChildStmt, ``AccServed0Stmt,
      ``AccIHAtStepStmt, ``AccOfRunStmt, ``stableA_accInvAt, ``accInvAt_sv, ``translate_keepsAcc_of_tele, ``accKeepBody,
      ``accIHAt_limit, ``accIHAt_step, ``acc_of_run] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path: a root, a helper value and a helper type that mention a name absent
from the environment MUST be reported unknown; a clean chain MUST NOT. (The helpers are added with the kernel type check skipped,
inside `withoutModifyingEnv`.) -/
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
  let roots := [``stableA_accInvAt, ``accInvAt_sv, ``translate_keepsAcc_of_tele, ``accKeepBody, ``accIHAt_limit,
    ``accIHAt_step, ``acc_of_run]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A4): {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, no unknown constant"

end Tests.Gen5.AccIndCheck
