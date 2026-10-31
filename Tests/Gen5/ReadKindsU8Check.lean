import Tools.ShippingGen5ReadKindsU8
import Tests.Gen5.ReadKindsCheck
import Tests.Gen5.ReadKindsU5Check
import Tests.Gen5.ReadKindsU7Check
set_option autoImplicit false
-- NOT BUILT: (header to be synced by a comment-only commit after a successful build). Freeze: scripts/gen5/DG_READKINDS_U8_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U8 checks (Tools/ShippingGen5ReadKindsU8.lean)

1. TYPE: each declaration against an independently written `Exp…` statement (written from freeze §1-§3, not copied from the Lean; same reducible comparator `Tests.Gen3.ExpectedType`); positive control: the comparator accepts a copy.
2. MUTANT: signature/defeq rejections of well-typed single-change statements, NOT semantic counterexamples. A mutant that fails to typecheck is not counted.
3. COUNT: conjunct counts (auxiliary, necessary condition only).
4. CLOSURE: explicit-value scan; unknown constant = fail. 5. AXIOMS: propext / Classical.choice / Quot.sound only. -/

namespace Tests.Gen5.ReadKindsU8Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.Prototype.DGenProv
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5 Tools.ShippingGen5ReadKindsU6 Tools.ShippingGen5ReadKindsU7
open Tools.ShippingGen5ReadKindsU8
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts)
open Tests.Gen5.ReadKindsU7Check (ExpReadConcl ExpReadFields conjCount)

/-! ## 1. Expected statements (freeze §1-§3) -/

/-- freeze §1: `ReadRoot` is `ReadConcl` plus the root-body facts (U6 freeze §3) -/
def ExpReadRoot (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ExpReadConcl ci env r ∧
  ∃ body : Lean.Expr, RootFactsTie (GenEntry ci env) body ∧
    r.rootLets = (machRoot (structEnv env).proj body []).1.length ∧
    r.sel? = (machRoot (structEnv env).proj body []).2.1 ∧
    r.hasOuter = (machRoot (structEnv env).proj body []).2.2.1.isSome

def ExpDet : Prop :=
  ∀ {α : Type} {m : MetaM α} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {a b : α} {w' w'' : Void IO.RealWorld}
    (h1 : RunsTo m mctx mref cctx cref w a w') (h2 : RunsTo m mctx mref cctx cref w b w''),
    a = b ∧ w' = w''
def ExpRootFields : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadRoot ci env r ∧ ExpReadFields ci env r
def ExpGates : Prop :=
  ∀ {declName : Lean.Name} 
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName false) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ certifiedShape? false [] (GenEntry ci env) = none ∧
      mixedCertifiedShape? false [] (GenEntry ci env) (instancePredicate env) = none
def ExpMD : Prop :=
  ∀ {declName : Lean.Name} 
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName false) mctx mref cctx cref w r w')
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u),
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName r.shape

/-- positive control: a separately written copy of the rootFields statement is accepted -/
def CopyOfRootFields : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadRoot ci env r ∧ ExpReadFields ci env r

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``runsTo_det ``ExpDet
  checkExpected ``readMachine_rootFields ``ExpRootFields
  checkExpected ``readMachine_gates ``ExpGates
  checkExpected ``machineDefines_of_readMachine ``ExpMD
  checkExpected ``CopyOfRootFields ``ExpRootFields
  logInfo "RK-U8 TYPE OK: 5 comparisons (4 theorems + 1 comparator positive control)"

/-! ## 2. Mutants (signature / defeq rejections of well-typed single changes, not semantic counterexamples) -/

def MutRFNoRoot : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadFields ci env r
def MutRFNoFields : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadRoot ci env r
def MutRFTwoTuples : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    (∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadRoot ci env r) ∧
    (∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadFields ci env r)
def MutGatesAllowGate : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ certifiedShape? false [] (GenEntry ci env) = none ∧
      mixedCertifiedShape? false [] (GenEntry ci env) (instancePredicate env) = none
def MutGatesIsSome : Prop :=
  ∀ {declName : Lean.Name} 
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName false) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ (certifiedShape? false [] (GenEntry ci env)).isSome = true ∧
      mixedCertifiedShape? false [] (GenEntry ci env) (instancePredicate env) = none
def MutGatesNoMixed : Prop :=
  ∀ {declName : Lean.Name} 
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName false) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ certifiedShape? false [] (GenEntry ci env) = none
def MutMDNoHall : Prop :=
  ∀ {declName : Lean.Name} 
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName false) mctx mref cctx cref w r w')
    ,
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName r.shape
def MutMDAllowGate : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u),
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName r.shape
def MutMDArbShape : Prop :=
  ∀ {declName : Lean.Name} {shape : MachineShape}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName false) mctx mref cctx cref w r w')
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u),
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName shape
def MutDetNoWorld : Prop :=
  ∀ {α : Type} {m : MetaM α} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {a b : α} {w' w'' : Void IO.RealWorld}
    (h1 : RunsTo m mctx mref cctx cref w a w') (h2 : RunsTo m mctx mref cctx cref w b w''),
    a = b

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``readMachine_rootFields ``MutRFNoRoot
  checkMutant ``readMachine_rootFields ``MutRFNoFields
  checkMutant ``readMachine_rootFields ``MutRFTwoTuples
  checkMutant ``readMachine_gates ``MutGatesAllowGate
  checkMutant ``readMachine_gates ``MutGatesIsSome
  checkMutant ``readMachine_gates ``MutGatesNoMixed
  checkMutant ``machineDefines_of_readMachine ``MutMDNoHall
  checkMutant ``machineDefines_of_readMachine ``MutMDAllowGate
  checkMutant ``machineDefines_of_readMachine ``MutMDArbShape
  checkMutant ``runsTo_det ``MutDetNoWorld
  logInfo "RK-U8 MUTANT REJECTED 10 (rootFields 3, gates 3, machineDefines 3, runsTo_det 1; signature/defeq rejection, not semantic counterexamples)"

/-! ### 2b. Conjunct-count auxiliary check (necessary condition only, not proof of a single change) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let unf : List Name := [``ExpReadConcl, ``ExpReadFields, ``ExpReadRoot]
  let cnt (n : Name) : Lean.Elab.TermElabM Nat := do
    let some ci := env.find? n | throwError "RK-U8 COUNT: {n} missing"
    let some v := ci.value? | throwError "RK-U8 COUNT: {n} has no value"
    return conjCount env unf v
  let rf ← cnt ``ExpRootFields
  let nr ← cnt ``MutRFNoRoot
  let nf ← cnt ``MutRFNoFields
  let tt ← cnt ``MutRFTwoTuples
  let root ← cnt ``MutRFNoFields
  let fields ← cnt ``MutRFNoRoot
  if rf != root + fields - 2 || nr != fields || nf != root then
    throwError "RK-U8 COUNT FAILED rootFields: Expected {rf}, NoRoot {nr}, NoFields {nf}"
  let g ← cnt ``ExpGates
  let ga ← cnt ``MutGatesAllowGate
  let gi ← cnt ``MutGatesIsSome
  let gn ← cnt ``MutGatesNoMixed
  if ga != g || gi != g || gn + 1 != g then
    throwError "RK-U8 COUNT FAILED gates: Expected {g}, allowGate {ga}, isSome {gi}, noMixed {gn}"
  let d ← cnt ``ExpDet
  let dn ← cnt ``MutDetNoWorld
  if dn + 1 != d then throwError "RK-U8 COUNT FAILED det: Expected {d}, mutant {dn}"
  logInfo m!"RK-U8 COUNT OK: rootFields Expected {rf} leaves (NoRoot {nr}, NoFields {nf}, TwoTuples {tt}, informational); gates Expected {g} (allowGate {ga}, isSome {gi} equal; noMixed {gn} = -1); det Expected {d} (mutant {dn} = -1)"

/-! ## 3. Closure -/

def forbidU8 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (c, req) in [(``readMachine_rootFields, [``Tools.ShippingGen5ReadKindsU6.readMachine_root, ``Tools.ShippingGen5ReadKindsU7.readMachine_fields, ``Tools.ShippingGen5ReadKindsU8.runsTo_det]),
      (``readMachine_gates, []),
      (``machineDefines_of_readMachine, [``Tools.ShippingGen5ReadKindsU8.readMachine_gates, ``Tools.Prototype.DGenProv.readMachine_run, ``Tools.ShippingGen5Env.machineDefines_of_readsAll, ``Tools.ShippingGen5Env.ci_of_readsAt, ``Tools.ShippingGen5Env.envR_of_readsAt, ``Tools.ShippingStRefCorrespondence.runsTo_det]),
      (``runsTo_det, [``Tools.ShippingStRefCorrespondence.runsTo_det])] do
    let r ← reach c (forbid := forbidU8)
    if let some p := r.hit then throwError "RK-U8 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK-U8 AUDIT FAILED {c}: {t} not reached"
    if !r.unknown.isEmpty then throwError "RK-U8 AUDIT FAILED {c}: unknown constants {r.unknown}"
    logInfo m!"RK-U8 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown {r.unknown.size}, opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
  for c in [``readMachine_rootFields, ``readMachine_gates, ``machineDefines_of_readMachine] do
    let r ← reach c
    logInfo m!"RK-U8 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString r.hit}"
  let r ← reach `Tests.Gen5.ReadKindsFixtureOther.viaHelper2
  if r.hit.isNone then throwError "RK-U8 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach `Tests.Gen5.ReadKindsFixtureOther.cleanHelper
  if r.hit.isSome then throwError "RK-U8 AUDIT FAILED: scanner control flags the clean helper"
  logInfo "RK-U8 CONTROL: fixture detected, clean helper not flagged"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``runsTo_det, ``readMachine_rootFields, ``readMachine_gates, ``machineDefines_of_readMachine] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U8 STATUS: runsTo_det (alias), readMachine_rootFields (one tuple), readMachine_gates closed from a readMachine run; machineDefines_of_readMachine is CONDITIONAL on hall : ∀ u, ReadsAt env₀ cref u (intermediate). NOT supplied: hall / DG-ENV C0, GetEnvFrame, real-run tie (hrun; hX for RunReadsAt), hstore, GateDefines, srcDom, ls/outs/nexts, hq (Expr.equal_sound not added; Q2; Q3), coverage, FG."

end Tests.Gen5.ReadKindsU8Check
