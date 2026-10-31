import Tools.ShippingGen5ReadKindsU7
import Tests.Gen5.ReadKindsCheck
import Tests.Gen5.ReadKindsU5Check
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU7Check exit 0 in pod on 819617491c4fac6d1b17ca03ef595fbfd970d252 (not a clean issue-linked build; that is the coder's). Freeze: scripts/gen5/DG_READKINDS_U7_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U7 checks (Tools/ShippingGen5ReadKindsU7.lean)

1. TYPE: each declaration against an independently written `Exp…` statement (same reducible comparator `Tests.Gen3.ExpectedType`); positive control: the comparator accepts a copy.
2. MUTANT: signature/defeq rejections of changed statements, NOT semantic counterexamples.
3. CLOSURE: explicit-value scan; unknown constant = fail.
4. AXIOMS: propext / Classical.choice / Quot.sound only.
Log: `hq`, `Expr.equal_sound`, `srcDom`, `ls/outs/nexts`, `GetEnvFrame`/`hX`/`hall` supply, real-run tie, coverage, FG are NOT supplied. -/

namespace Tests.Gen5.ReadKindsU7Check
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineCommand Tools.Prototype.DGenProv
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5 Tools.ShippingGen5ReadKindsU7
open Tests.Gen3.ExpectedType
open Tests.Gen5.ReadKindsCheck (reach forbidConsts)

/-! ## 1. Expected statements, written independently from the freeze -/

def ExpReadFields (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (b0 : Lean.Expr),
    (GenEntry ci env).value? = some entryV ∧
    mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, b0) ∧
    r.nDecl = bsIn.length ∧
    r.nIn = r.nDecl + r.shape.insts.length ∧
    r.shape.binders.length = r.nIn + r.shape.layout.slots.length + r.shape.layout.lets ∧
    r.tuple = machTupleKinds? (GenEntry ci env).type ∧
    (∃ outKinds : List (String × MixedGateBinder),
      (match machTupleKinds? (GenEntry ci env).type with
        | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
        | none => machOuts? (structEnv env) (GenEntry ci env).type) = some (r.ctor?, outKinds) ∧
      r.outNames = outKinds.map (·.1)) ∧
    r.bposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => if k == .bool then some p else none) ∧
    r.vposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => match k with | .bits _ => some p | _ => none) ∧
    r.vwL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (_, k) => match k with | .bits w => some w | _ => none) ∧
    ∃ (srcDom' : Lean.Expr) (snd : Sparkle.IR.Type.ResetKind),
      machDom? (r.shape.insts.length + r.shape.layout.slots.length + r.shape.layout.lets) srcDom' = some (r.dom, snd)

/-- written from freeze §1 (`ReadConcl`): the entry and the shape of the run -/
def ExpReadConcl (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  r.entry = GenEntry ci env ∧ machineShape? false [] (GenEntry ci env) (structEnv env) = some r.shape

def ExpFields : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadConcl ci env r ∧ ExpReadFields ci env r

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
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u) (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

/-- the comparator is not vacuous: it accepts a separately written copy (positive control) -/
def CopyOfFields : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadConcl ci env r ∧ ExpReadFields ci env r

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``readMachine_fields ``ExpFields
  checkExpected ``readMachine_agrees_runReads_of_readsAt ``ExpAgrees
  checkExpected ``ReadFields ``ExpReadFields
  checkExpected ``CopyOfFields ``ExpFields
  logInfo "RK-U7 TYPE OK: 4 comparisons (2 theorems + 1 definition ReadFields + 1 comparator positive control)"

/-! ## 2. Mutants (signature / defeq rejections, not semantic counterexamples) -/

def MutReadFieldsNIn (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (b0 : Lean.Expr),
    (GenEntry ci env).value? = some entryV ∧
    mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, b0) ∧
    r.nDecl = bsIn.length ∧
    r.nIn = r.nDecl ∧
    r.shape.binders.length = r.nIn + r.shape.layout.slots.length + r.shape.layout.lets ∧
    r.tuple = machTupleKinds? (GenEntry ci env).type ∧
    (∃ outKinds : List (String × MixedGateBinder),
      (match machTupleKinds? (GenEntry ci env).type with
        | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
        | none => machOuts? (structEnv env) (GenEntry ci env).type) = some (r.ctor?, outKinds) ∧
      r.outNames = outKinds.map (·.1)) ∧
    r.bposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => if k == .bool then some p else none) ∧
    r.vposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => match k with | .bits _ => some p | _ => none) ∧
    r.vwL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (_, k) => match k with | .bits w => some w | _ => none) ∧
    ∃ (srcDom' : Lean.Expr) (snd : Sparkle.IR.Type.ResetKind),
      machDom? (r.shape.insts.length + r.shape.layout.slots.length + r.shape.layout.lets) srcDom' = some (r.dom, snd)

def MutReadFieldsTuple (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (b0 : Lean.Expr),
    (GenEntry ci env).value? = some entryV ∧
    mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, b0) ∧
    r.nDecl = bsIn.length ∧
    r.nIn = r.nDecl + r.shape.insts.length ∧
    r.shape.binders.length = r.nIn + r.shape.layout.slots.length + r.shape.layout.lets ∧
    r.tuple = none ∧
    (∃ outKinds : List (String × MixedGateBinder),
      (match machTupleKinds? (GenEntry ci env).type with
        | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
        | none => machOuts? (structEnv env) (GenEntry ci env).type) = some (r.ctor?, outKinds) ∧
      r.outNames = outKinds.map (·.1)) ∧
    r.bposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => if k == .bool then some p else none) ∧
    r.vposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => match k with | .bits _ => some p | _ => none) ∧
    r.vwL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (_, k) => match k with | .bits w => some w | _ => none) ∧
    ∃ (srcDom' : Lean.Expr) (snd : Sparkle.IR.Type.ResetKind),
      machDom? (r.shape.insts.length + r.shape.layout.slots.length + r.shape.layout.lets) srcDom' = some (r.dom, snd)

def MutReadFieldsSwap (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (b0 : Lean.Expr),
    (GenEntry ci env).value? = some entryV ∧
    mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, b0) ∧
    r.nDecl = bsIn.length ∧
    r.nIn = r.nDecl + r.shape.insts.length ∧
    r.shape.binders.length = r.nIn + r.shape.layout.slots.length + r.shape.layout.lets ∧
    r.tuple = machTupleKinds? (GenEntry ci env).type ∧
    (∃ outKinds : List (String × MixedGateBinder),
      (match machTupleKinds? (GenEntry ci env).type with
        | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
        | none => machOuts? (structEnv env) (GenEntry ci env).type) = some (r.ctor?, outKinds) ∧
      r.outNames = outKinds.map (·.1)) ∧
    r.vposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => if k == .bool then some p else none) ∧
    r.bposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => match k with | .bits _ => some p | _ => none) ∧
    r.vwL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (_, k) => match k with | .bits w => some w | _ => none) ∧
    ∃ (srcDom' : Lean.Expr) (snd : Sparkle.IR.Type.ResetKind),
      machDom? (r.shape.insts.length + r.shape.layout.slots.length + r.shape.layout.lets) srcDom' = some (r.dom, snd)

def MutFieldsNIn : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ MutReadFieldsNIn ci env r

def MutFieldsTuple : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ MutReadFieldsTuple ci env r

def MutFieldsSwap : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ MutReadFieldsSwap ci env r

/-- ReadConcl dropped (the R1 weakening) -/
def MutFieldsNoConcl : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ExpReadFields ci env r

/-- ReadConcl kept but without the shape conjunct -/
def MutFieldsNoShape : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ r.entry = GenEntry ci env ∧ ExpReadFields ci env r

/-- ReadConcl kept but without the entry conjunct -/
def MutFieldsNoEntry : Prop :=
  ∀ {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'),
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ machineShape? false [] (GenEntry ci env) (structEnv env) = some r.shape ∧ ExpReadFields ci env r

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
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u) (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR') (userInliner envR') (structEnv envR') ∧
      r.shape = shape

def MutAgreesNoHx : Prop :=
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
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutAgreesNoHall : Prop :=
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
    (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

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
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u) (hX : declName = X),
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``readMachine_fields ``MutFieldsNIn
  checkMutant ``readMachine_fields ``MutFieldsTuple
  checkMutant ``readMachine_fields ``MutFieldsSwap
  checkMutant ``readMachine_fields ``MutFieldsNoConcl
  checkMutant ``readMachine_fields ``MutFieldsNoShape
  checkMutant ``readMachine_fields ``MutFieldsNoEntry
  checkMutant ``readMachine_agrees_runReads_of_readsAt ``MutAgreesEnv
  checkMutant ``readMachine_agrees_runReads_of_readsAt ``MutAgreesNoHx
  checkMutant ``readMachine_agrees_runReads_of_readsAt ``MutAgreesNoHall
  checkMutant ``readMachine_agrees_runReads_of_readsAt ``MutAgreesNoShape
  logInfo "RK-U7 MUTANT REJECTED 10 (signature/defeq rejection, not semantic counterexamples)"

/-! ## 3. Closure (Expr.equal / Expr.eqv reached only through the programs `readMachine` / `machineShape?`; logged as a fact) -/

def forbidU7 : List Name := forbidConsts.filter fun n => n != ``Lean.Expr.equal && n != ``Lean.Expr.eqv

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (c, req) in [(``readMachine_fields, []),
      (``readMachine_agrees_runReads_of_readsAt, [``Tools.Prototype.DGenProv.readMachine_run, ``Tools.ShippingGen5Env.ci_of_readsAt, ``Tools.ShippingGen5Env.envR_of_readsAt])] do
    let r ← reach c (forbid := forbidU7)
    if let some p := r.hit then throwError "RK-U7 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK-U7 AUDIT FAILED {c}: {t} not reached"
    if !r.unknown.isEmpty then throwError "RK-U7 AUDIT FAILED {c}: unknown constants {r.unknown}"
    logInfo m!"RK-U7 REACH {c}: no T1Hyp / T1HypND (name, raw proj, rec) / Laws; reaches {req} (visited {r.visited}, unknown {r.unknown.size}, opaque {r.opaqueNames}, no-value count {r.noBodyNames.size})"
  for c in [``readMachine_fields, ``readMachine_agrees_runReads_of_readsAt] do
    let r ← reach c
    logInfo m!"RK-U7 FACT full forbid set (incl. Expr.equal/eqv) on {c}: {toString r.hit}"
  let r ← reach `Tests.Gen5.ReadKindsFixtureOther.viaHelper2
  if r.hit.isNone then throwError "RK-U7 AUDIT FAILED: scanner control misses the fixture"
  let r ← reach `Tests.Gen5.ReadKindsFixtureOther.cleanHelper
  if r.hit.isSome then throwError "RK-U7 AUDIT FAILED: scanner control flags the clean helper"
  logInfo "RK-U7 CONTROL: fixture detected, clean helper not flagged"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``readMachine_fields, ``readMachine_agrees_runReads_of_readsAt] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo "RK-U7 STATUS: readMachine_fields (ReadConcl ∧ ReadFields from the same ci/env/w1/w2 walk) closed from a readMachine run `h`; readMachine_agrees_runReads_of_readsAt is CONDITIONAL (hall : ∀ u, ReadsAt env₀ cref u, declName = X). NOT supplied: hall, hX, GetEnvFrame, hq (Expr.equal_sound not added; Q2; Q3), srcDom, ls/outs/nexts, real-run tie, coverage, FG."
