import Tools.ShippingGen5ReadKindsU6
import Tests.Gen5.ReadKindsCheck
import Tests.Gen5.ReadKindsU5Check
set_option autoImplicit false
-- NOT BUILT (freeze: scripts/gen5/DG_READKINDS_U6_FREEZE.md). No sorry / axiom / native_decide.

/-! # DG-READKINDS U6 checks (Tools/ShippingGen5ReadKindsU6.lean; freeze scripts/gen5/DG_READKINDS_U6_FREEZE.md)

1. TYPE: each declaration against an independently written `Exp…` statement (same reducible comparator `Tests.Gen3.ExpectedType`);
   positive control: the comparator accepts a copy.
2. MUTANT: signature/defeq rejections of changed statements, NOT semantic counterexamples.
3. CLOSURE: explicit-value scan (the scanner of `ReadKindsCheck`); unknown constant = fail.
4. AXIOMS: propext / Classical.choice / Quot.sound only.
Log: `hentry` is only CONDITIONAL (`GetEnvFrame`, `hw`, `declName = X`); hq, `Read` fields beyond the root, real-run tie, coverage, FG are NOT supplied. -/

namespace Tests.Gen5.ReadKindsU6Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.Prototype.DGenProv
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5 Tools.ShippingGen5ReadKindsU6
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEnvSnapshot (GetEnvFrame)
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts)

/-! ## 1. Expected statements, written independently -/

def ExpReadRoot (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ReadConcl ci env r ∧
  ∃ body : Lean.Expr, RootFactsTie (GenEntry ci env) body ∧
    r.rootLets = (machRoot (structEnv env).proj body []).1.length ∧
    r.sel? = (machRoot (structEnv env).proj body []).2.1 ∧
    r.hasOuter = (machRoot (structEnv env).proj body []).2.2.1.isSome

def ExpAt : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    RootFactsAt r.entry

def ExpRoot : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadRoot ci env r

def ExpAgrees : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {w1 w2 w3 w5 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    {shape : MachineShape}
    (hget : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5)
    (hshape : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape)
    (hX : declName = X) (hg : GetEnvFrame mctx mref cctx cref) (hw : envAt cref w = envAt cref w1),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- the comparator is not vacuous: it accepts a separately written copy (positive control) -/
def CopyOfAt : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    RootFactsAt r.entry

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``readMachine_rootFactsAt ``ExpAt
  checkExpected ``readMachine_root ``ExpRoot
  checkExpected ``readMachine_agrees_runReads ``ExpAgrees
  checkExpected ``CopyOfAt ``ExpAt
  checkExpected ``ReadRoot ``ExpReadRoot
  logInfo "RK-U6 TYPE OK: 5 comparisons (3 theorems + 1 definition ReadRoot + 1 comparator positive control)"

/-! ## 2. Mutants (signature / defeq rejections, not semantic counterexamples) -/

def MutAtForall : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∀ body : Lean.Expr, RootFactsTie r.entry body

def MutReadRootNIn (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ReadConcl ci env r ∧
  ∃ body : Lean.Expr, RootFactsTie (GenEntry ci env) body ∧
    r.nIn = (machRoot (structEnv env).proj body []).1.length ∧
    r.sel? = (machRoot (structEnv env).proj body []).2.1 ∧
    r.hasOuter = (machRoot (structEnv env).proj body []).2.2.1.isSome

def MutReadRootThm : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ MutReadRootNIn ci env r

/-- U6b without the `GetEnvFrame` premise -/
def MutAgreesNoHg : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {w1 w2 w3 w5 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    {shape : MachineShape}
    (hget : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5)
    (hshape : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape)
    (hX : declName = X) (hw : envAt cref w = envAt cref w1),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U6b without the world-agreement premise -/
def MutAgreesNoHw : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {w1 w2 w3 w5 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    {shape : MachineShape}
    (hget : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5)
    (hshape : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape)
    (hX : declName = X) (hg : GetEnvFrame mctx mref cctx cref),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- U6b with `envR'` in the entry -/
def MutAgreesEnv : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {w1 w2 w3 w5 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    {shape : MachineShape}
    (hget : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5)
    (hshape : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape)
    (hX : declName = X) (hg : GetEnvFrame mctx mref cctx cref) (hw : envAt cref w = envAt cref w1),
    r.entry = entryConst true false [] ci (instancePredicate envR') (userInliner envR') (structEnv envR') ∧
      r.shape = shape

/-- U6b without the shape conjunct -/
def MutAgreesNoShape : Prop :=
  ∀ {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {w1 w2 w3 w5 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    {shape : MachineShape}
    (hget : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5)
    (hshape : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape)
    (hX : declName = X) (hg : GetEnvFrame mctx mref cctx cref) (hw : envAt cref w = envAt cref w1),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``readMachine_rootFactsAt ``MutAtForall
  checkMutant ``readMachine_root ``MutReadRootThm
  checkMutant ``readMachine_agrees_runReads ``MutAgreesNoHg
  checkMutant ``readMachine_agrees_runReads ``MutAgreesNoHw
  checkMutant ``readMachine_agrees_runReads ``MutAgreesEnv
  checkMutant ``readMachine_agrees_runReads ``MutAgreesNoShape
  logInfo "RK-U6 MUTANT REJECTED 6 (signature/defeq rejection, not semantic counterexamples)"

/-! ## 3. Closure (Expr.equal / Expr.eqv reached only through the programs `readMachine` / `machineShape?`; logged as a fact) -/

def forbidU6 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (c, req) in [(``readMachine_rootFactsAt, [``Tools.Prototype.DGenProv.readMachine_run, ``rootFactsAt_of_machineShape]),
      (``readMachine_root, []), (``readMachine_agrees_runReads, [``Tools.Prototype.DGenProv.readMachine_run])] do
    let r ← reach c (forbid := forbidU6)
    if let some p := r.hit then throwError "RK-U6 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK-U6 AUDIT FAILED {c}: {t} not reached"
    if !r.unknown.isEmpty then throwError "RK-U6 AUDIT FAILED {c}: unknown constants {r.unknown}"
    logInfo m!"RK-U6 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown {r.unknown.size}, opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
  for c in [``readMachine_rootFactsAt, ``readMachine_root, ``readMachine_agrees_runReads] do
    let r ← reach c
    logInfo m!"RK-U6 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString r.hit}"
  let r ← reach `Tests.Gen5.ReadKindsFixtureOther.viaHelper2
  if r.hit.isNone then throwError "RK-U6 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach `Tests.Gen5.ReadKindsFixtureOther.cleanHelper
  if r.hit.isSome then throwError "RK-U6 AUDIT FAILED: scanner control flags the clean helper"
  logInfo "RK-U6 CONTROL: fixture detected, clean helper not flagged"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``readMachine_rootFactsAt, ``readMachine_root, ``readMachine_agrees_runReads] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U6 STATUS: readMachine_rootFactsAt / readMachine_root closed from a readMachine run `hrun`; readMachine_agrees_runReads is CONDITIONAL (GetEnvFrame, world agreement, declName = X). NOT supplied: hentry unconditional, hq (Expr.equal / unq), Read fields beyond root, real-run tie, coverage, FG."
