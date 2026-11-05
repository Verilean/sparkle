import Tools.ShippingGen5Flow1Reads
import Tests.Gen5.ClosingRun2Check
import Tests.Gen5.Flow1TieCheck
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT as a clean issue-linked build yet (build is the coder's). No sorry / axiom / native_decide.

/-! # FG flow 1 U2 checks (Tools/ShippingGen5Flow1Reads.lean; scripts/gen5/FLOW1_FREEZE.md section 3)

The Expected statement is written from the frozen type of FLOW1_FREEZE.md section 3, not derived from the implementation's
signature. The single comparator is `Tests.Gen5.ClosingRun2Check.cmpTeleR` (binder-by-binder, REDUCIBLE defeq fallback).
Mutants are one-point, well-typed variants; they are rejected by signature / defeq, NOT by a semantic counterexample.
Negative control: the `R : RunReadsAt ..` form (U13 `readMachine_agrees_runReads_of_head_self`) is not accepted as the run-side form.
Closure: value + type walk, root judged, unresolved names fail (controls are in Flow1TieCheck and re-run here on the same walker).
Not claimed: `hk`, `hHead`, `h0s`, env tie / DG-ENV C0, existence of the runs, `envR = envR'`, T1/FG. -/

namespace Tests.Gen5.Flow1ReadsCheck
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC
open Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA
open Tools.ShippingChildRunAMain
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingMachineCommand
open Tools.ShippingGen5ReadKinds
open Tests.Gen3.ExpectedType
open Tests.Gen5.ClosingRun2Check (cmpTeleR)
open Tests.Gen5.Flow1TieCheck (checkExp rejected auditRoot auditFails)

def ExpAgree : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoHk : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoHHead : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoH0s : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2H0sSwap : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref ws) cref w)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2H0sWs1 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws')
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoHX : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    ,
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoEntry : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoCloses : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoHc : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0)
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2HcWrongWorld : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2HwWrongWorld : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2HwDepth0 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet 0 ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoHA : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2HrWorldSwap : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws' (raw, D) ws)
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2HrIsReadMachine : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] true) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2HrunWs : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w)
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2RunReadsWsSwap : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws' ws raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2RunReadsEnvSwap : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR' envR shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2NoEntryEq : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.shape = shape

def MutU2EntryEnvR1 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR') (userInliner envR') (structEnv envR') ∧
      r.shape = shape

def MutU2NoShapeEq : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)

def MutU2NoRunReads : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape

def MutU2HXSwap : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : X = declName),
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape


set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let muts : List Name := [``MutU2NoHk, ``MutU2NoHHead, ``MutU2NoH0s, ``MutU2H0sSwap, ``MutU2H0sWs1, ``MutU2NoHX, ``MutU2NoEntry, ``MutU2NoCloses, ``MutU2NoHc, ``MutU2HcWrongWorld, ``MutU2HwWrongWorld, ``MutU2HwDepth0, ``MutU2NoHA, ``MutU2HrWorldSwap, ``MutU2HrIsReadMachine, ``MutU2HrunWs, ``MutU2RunReadsWsSwap, ``MutU2RunReadsEnvSwap, ``MutU2NoEntryEq, ``MutU2EntryEnvR1, ``MutU2NoShapeEq, ``MutU2NoRunReads, ``MutU2HXSwap]
  checkExp ``Tools.ShippingGen5Flow1Reads.readMachine_agrees_of_run ``ExpAgree
  let mut nMut : Nat := 0
  for m in muts do
    unless ← rejected ``Tools.ShippingGen5Flow1Reads.readMachine_agrees_of_run m do throwError "FLOW1 MUTANT ACCEPTED: {m}"
    nMut := nMut + 1
  let mut nNeg : Nat := 0
  for o in [``Tools.ShippingGen5ReadKindsU13.readMachine_agrees_runReads_of_head_self,
      ``Tools.ShippingGen5RunReads.runReads_of_run] do
    unless ← rejected ``Tools.ShippingGen5Flow1Reads.readMachine_agrees_of_run o do
      throwError "FLOW1 NEGATIVE CONTROL ACCEPTED: {o}"
    nNeg := nNeg + 1
  -- CONTROL: the shared walker still flags the root itself and unresolved names (same function as Flow1TieCheck)
  let env ← getEnv
  let F := `Tests.Gen5.Flow1TieFixture
  let mut nCtl : Nat := 0
  unless ← auditFails env.find? ``Tools.ShippingGen2.core_reads_invAt0 do throwError "FLOW1 CONTROL FAILED: root itself not judged"
  nCtl := nCtl + 1
  unless ← auditFails env.find? (F ++ `rootBad) do throwError "FLOW1 CONTROL FAILED: bad use not flagged"
  nCtl := nCtl + 1
  let hideV := fun n => if n == F ++ `helperV then none else env.find? n
  let hideT := fun n => if n == F ++ `helperT then none else env.find? n
  unless ← auditFails hideV (F ++ `useV) do throwError "FLOW1 CONTROL FAILED: unknown helper VALUE skipped"
  nCtl := nCtl + 1
  unless ← auditFails hideT (F ++ `useT) do throwError "FLOW1 CONTROL FAILED: unknown helper TYPE skipped"
  nCtl := nCtl + 1
  let v ← auditRoot env.find? ``Tools.ShippingGen5Flow1Reads.readMachine_agrees_of_run
    [``Tools.ShippingGen5RunReads.runReads_of_run, ``Tools.ShippingGen5ReadKindsU13.readMachine_agrees_runReads_of_head_self]
  checkAxioms ``Tools.ShippingGen5Flow1Reads.readMachine_agrees_of_run
  logInfo m!"FLOW1 READS SUMMARY: TYPE 1, MUTANT {nMut} + NEGATIVE {nNeg}, CONTROL {nCtl}, REACH 1 (visited {v}), AXIOMS 1 standard-only"

end Tests.Gen5.Flow1ReadsCheck
