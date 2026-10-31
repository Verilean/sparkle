import Tools.ShippingGen5ReadKindsU5
import Tests.Gen5.ReadKindsCheck
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU5Check exit 0 (756 jobs) in pod on 6e343e997fdbf0ce8cff741ce57f7de45cc68790 (not a clean issue-linked build; that is the coder's). No sorry / axiom / native_decide.
-- Clean issue-linked build: rk5v-4ac00d24 exit 0 (756 jobs), scoped approved at 4ac00d24. Counts (summary lines excluded): TYPE 10 comparisons (7 theorems + 2 definitions + positive control), MUTANT 7.

/-! # DG-READKINDS U5 checks (Tools/ShippingGen5ReadKindsU5.lean; freeze rev3.1)

1. TYPE: each declaration against an independently written `Exp…` statement (same reducible binder-by-binder comparator
   `Tests.Gen3.ExpectedType` as `ReadKindsCheck`); positive control: the comparator accepts a copy.
2. MUTANT: signature/defeq rejections of changed statements, NOT semantic counterexamples.
3. CLOSURE: explicit-value scan (the scanner of `ReadKindsCheck`); unknown constant = fail.
4. AXIOMS: propext / Classical.choice / Quot.sound only.
Log: `RootFactsAt` is supplied by the peel; `RootFactsTie` at an externally fixed body, `hentry`, `hq` are NOT supplied. -/

namespace Tests.Gen5.ReadKindsU5Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts)

/-! ## 1. Expected statements, written independently -/

def ExpRootFactsAt (E : Lean.ConstantInfo) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ entryBody : Lean.Expr),
    E.value? = some entryV ∧ RootFacts entryV bsIn entryBody₀ entryBody

def ExpRootFactsTie (E : Lean.ConstantInfo) (entryBody : Lean.Expr) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ : Lean.Expr),
    E.value? = some entryV ∧ RootFacts entryV bsIn entryBody₀ entryBody

def ExpPeel : Prop :=
  ∀ {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp),
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      ci = .defnInfo d ∧ ci.value? = some d.value ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e)

def ExpOfPeel : Prop :=
  ∀ {entryV : Lean.Expr} {bsIn : List (Lean.Name × MixedGateBinder)} {entryBody₀ : Lean.Expr}
    (h : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)),
    RootFacts entryV bsIn entryBody₀ (Sparkle.Compiler.MachRawSurface.rootFloat entryBody₀)

def ExpAtShape : Prop :=
  ∀ {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp),
    ExpRootFactsAt ci

def ExpAtRun : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {X : Lean.Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {b : Bool} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    {w5 w6 : Void IO.RealWorld}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    ExpRootFactsAt (Sparkle.Compiler.Elab.entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
      (Sparkle.Compiler.Elab.userInliner envR) (Sparkle.Compiler.Elab.structEnv envR))

def ExpUnique : Prop :=
  ∀ {entryV : Lean.Expr} {bsIn bsIn' : List (Lean.Name × MixedGateBinder)} {b₀ b₀' b b' : Lean.Expr}
    (h : RootFacts entryV bsIn b₀ b) (h' : RootFacts entryV bsIn' b₀' b'), bsIn = bsIn' ∧ b₀ = b₀' ∧ b = b'

def ExpTieUnique : Prop :=
  ∀ {E : Lean.ConstantInfo} {b b' : Lean.Expr} (h : ExpRootFactsTie E b) (h' : ExpRootFactsTie E b'), b = b'

def ExpIff : Prop :=
  ∀ {E : Lean.ConstantInfo}, ExpRootFactsAt E ↔ ∃ body : Lean.Expr, ExpRootFactsTie E body

/-- the comparator is not vacuous: it accepts a separately written copy of a statement (positive control) -/
def CopyOfPeel : Prop :=
  ∀ {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp),
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      ci = .defnInfo d ∧ ci.value? = some d.value ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e)

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``peel_of_machineShape ``ExpPeel
  checkExpected ``rootFacts_of_peel ``ExpOfPeel
  checkExpected ``rootFactsAt_of_machineShape ``ExpAtShape
  checkExpected ``rootFactsAt_of_runReads ``ExpAtRun
  checkExpected ``rootFacts_unique ``ExpUnique
  checkExpected ``rootFactsTie_unique ``ExpTieUnique
  checkExpected ``rootFactsAt_iff_tie ``ExpIff
  checkExpected ``CopyOfPeel ``ExpPeel
  -- the two definitions: bodies against independent copies
  checkExpected ``RootFactsAt ``ExpRootFactsAt
  checkExpected ``RootFactsTie ``ExpRootFactsTie
  logInfo "RK-U5 TYPE OK: 7 theorems + RootFactsAt + RootFactsTie against independent statements; comparator positive control accepted"

/-! ## 2. Mutants (signature / defeq rejections, not semantic counterexamples) -/

/-- `envR'` for `envR` in `structEnv` of the conclusion -/
def MutAtRunEnv : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {X : Lean.Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {b : Bool} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    {w5 w6 : Void IO.RealWorld}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    ExpRootFactsAt (Sparkle.Compiler.Elab.entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
      (Sparkle.Compiler.Elab.userInliner envR) (Sparkle.Compiler.Elab.structEnv envR'))

/-- uniqueness without the second hypothesis -/
def MutTieUniqueNoH : Prop :=
  ∀ {E : Lean.ConstantInfo} {b b' : Lean.Expr} (h : ExpRootFactsTie E b) (h' : True), b = b'

/-- float of `entryBody₀` itself instead of `rootFloat entryBody₀` -/
def MutOfPeelNoFloat : Prop :=
  ∀ {entryV : Lean.Expr} {bsIn : List (Lean.Name × MixedGateBinder)} {entryBody₀ : Lean.Expr}
    (h : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)),
    RootFacts entryV bsIn entryBody₀ entryBody₀

/-- peel applied to the wrong expression (`d.value` replaced by `d.type`) -/
def MutPeelType : Prop :=
  ∀ {sym : Bool} {params : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : Sparkle.Compiler.Elab.StructEnv} {allow : Bool} {sp : MachineShape}
    (h : Sparkle.Compiler.Elab.machineShape? sym params ci senv allow = some sp),
    ∃ (d : Lean.DefinitionVal) (bs : List (Lean.Name × MixedGateBinder)) (e : Lean.Expr),
      ci = .defnInfo d ∧ ci.value? = some d.value ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.type) = some (bs, e)

/-- conclusion for every body (∀ in place of ∃ for the externally fixed body) -/
def MutIffForall : Prop :=
  ∀ {E : Lean.ConstantInfo}, ExpRootFactsAt E ↔ ∀ body : Lean.Expr, ExpRootFactsTie E body

/-- the tie definition with entryBody₀ and entryBody swapped in `RootFacts` -/
def MutTieSwap (E : Lean.ConstantInfo) (entryBody : Lean.Expr) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ : Lean.Expr),
    E.value? = some entryV ∧ RootFacts entryV bsIn entryBody entryBody₀

/-- existence version with `entryBody` universally quantified -/
def MutAtForall (E : Lean.ConstantInfo) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (entryBody₀ : Lean.Expr),
    E.value? = some entryV ∧ ∀ entryBody : Lean.Expr, RootFacts entryV bsIn entryBody₀ entryBody

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``rootFactsAt_of_runReads ``MutAtRunEnv
  checkMutant ``rootFactsTie_unique ``MutTieUniqueNoH
  checkMutant ``rootFacts_of_peel ``MutOfPeelNoFloat
  checkMutant ``peel_of_machineShape ``MutPeelType
  checkMutant ``rootFactsAt_iff_tie ``MutIffForall
  checkMutant ``RootFactsTie ``MutTieSwap
  checkMutant ``RootFactsAt ``MutAtForall
  logInfo "RK-U5 MUTANT REJECTED 7 (signature/defeq rejection, not semantic counterexamples)"

/-! ## 3. Closure -/

/-- `Expr.equal` / `Expr.eqv` are reached through the PROGRAM `machineShape?` (its `Expr` `BEq`), which the
theorems talk about; they are not a law the proofs use. So the forbid set here drops those two and keeps
T1Hyp / T1HypND (name, raw proj, rec) / Laws; the full-set path is logged below as a fact. -/
def forbidU5 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (c, req) in [(``peel_of_machineShape, [``Tools.ShippingShapeDecomp.machineShape?_decomp]),
      (``rootFacts_of_peel, []), (``rootFactsAt_of_machineShape, [``peel_of_machineShape, ``rootFacts_of_peel]),
      (``rootFactsAt_of_runReads, [``rootFactsAt_of_machineShape]),
      (``rootFacts_unique, []), (``rootFactsTie_unique, [``rootFacts_unique]), (``rootFactsAt_iff_tie, [])] do
    let r ← reach c (forbid := forbidU5)
    if let some p := r.hit then throwError "RK-U5 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK-U5 AUDIT FAILED {c}: {t} not reached"
    if !r.unknown.isEmpty then throwError "RK-U5 AUDIT FAILED {c}: unknown constants {r.unknown}"
    logInfo m!"RK-U5 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown {r.unknown.size}, opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
  for c in [``peel_of_machineShape, ``rootFactsAt_of_runReads, ``rootFacts_unique] do
    let r ← reach c
    logInfo m!"RK-U5 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString r.hit}"
  -- negative control of the scanner on this module's own context
  let r ← reach `Tests.Gen5.ReadKindsFixtureOther.viaHelper2
  if r.hit.isNone then throwError "RK-U5 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach `Tests.Gen5.ReadKindsFixtureOther.cleanHelper
  if r.hit.isSome then throwError "RK-U5 AUDIT FAILED: scanner control flags the clean helper"
  logInfo "RK-U5 CONTROL: fixture detected, clean helper not flagged"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``peel_of_machineShape, ``rootFacts_of_peel, ``rootFactsAt_of_machineShape, ``rootFactsAt_of_runReads,
      ``rootFacts_unique, ``rootFactsTie_unique, ``rootFactsAt_iff_tie] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U5 STATUS: RootFactsAt supplied by the peel (rootFactsAt_of_machineShape / _of_runReads). NOT supplied: RootFactsTie at an externally fixed body (readMachine entryBody / Read result), hentry, hq. No real-run tie, coverage, or FG."

end Tests.Gen5.ReadKindsU5Check
