import Tools.ShippingGen5ClosingRun
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in the Pod (kjob lake build Tests.Gen5.ClosingRunCheck, exit 0: STRUCT 1 + 6 mutants, TYPE 8, MUTANT 13, controls 11, REACH 5, AXIOMS 8) on the tree of 0bdad261; NOT a clean issue-linked build (the coder runs that).
-- No sorry / axiom / native_decide.

/-! # DG-CLOSINGRUN checks (Tools/ShippingGen5ClosingRun.lean; scripts/gen5/DG_CLOSINGRUN_FREEZE.md)

1. `ClosingRun`: its constructor telescope against an independently written `ExpClosingRun` (field names, order,
   `binderInfo`, types at REDUCIBLE `isDefEq`, no extra field). One-point mutants (each a well-typed structure that
   elaborates; rejection is by the SAME comparison; they are signature / defeq rejections, NOT semantic counterexamples).
2. Expected TYPES (independent `def … : Prop := ∀ …`, fully bound) of CR0, CR1 (`coreHead_invAt0` and
   `invAt_w5_of_runReadsAt`), CR2, CR3, CR4 and `closingRun_of_run`; `PortsServed` against its independent value.
   One-point theorem mutants (well-typed; same comparator; not semantic counterexamples).
3. Closure audit (full reachable closure, explicit constant bodies, value + type): forbidden are `T1Hyp` fields
   (named projection, raw `.proj`, recursor, incl. `dec`), `BodyStepC`, `core_reads_invAt0`, `soundX_ships_ran`,
   `servedShips0_proved`, `TopShips`, `ofReduceBool`. Controls: direct, through a helper in ANOTHER namespace, raw
   projection, recursor; clean controls (not flagged).
4. Axioms.

Not checked / not claimed: non-vacuity (no concrete `Pkg` and run satisfying the premises is available: `hrow` and
`hGen` are unsupplied). -/

/-! ## 0. Fixtures -/
namespace Tests.Gen5.ClosingRunHelperA
theorem helperA : True := (fun _ => trivial) @Tools.ShippingGen2.core_reads_invAt0
end Tests.Gen5.ClosingRunHelperA
namespace Tests.Gen5.ClosingRunHelperB
theorem helperB : True := Tests.Gen5.ClosingRunHelperA.helperA
end Tests.Gen5.ClosingRunHelperB
namespace Tests.Gen5.ClosingRunHelperC
theorem helperC : True := (fun _ => trivial) @Tools.ShippingChildDepthC.BodyStepC
end Tests.Gen5.ClosingRunHelperC
namespace Tests.Gen5.ClosingRunHelperD
theorem helperD : True := Tests.Gen5.ClosingRunHelperC.helperC
end Tests.Gen5.ClosingRunHelperD
namespace Tests.Gen5.ClosingRunFixture
theorem badCoreReads : True := (fun _ => trivial) @Tools.ShippingGen2.core_reads_invAt0
theorem badCoreReadsHelper : True := Tests.Gen5.ClosingRunHelperB.helperB
theorem badBodyStep : True := Tests.Gen5.ClosingRunHelperD.helperD
theorem badDec : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
theorem badHypCases : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.casesOn.{0}
theorem badSoundXRan : True := (fun _ => trivial) @Tools.ShippingGen2.soundX_ships_ran
theorem badServed0 : True := (fun _ => trivial) @Tools.ShippingGen2.servedShips0_proved
theorem badTopShips : True := (fun _ => trivial) @Tools.ShippingGen2.TopShips
theorem badReduceBool : True := (fun _ => trivial) @Lean.ofReduceBool
theorem unrelated : True := trivial
theorem cleanND : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.pkg
end Tests.Gen5.ClosingRunFixture

namespace Tests.Gen5.ClosingRunCheck
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun
open Tests.Gen3.ExpectedType

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## 1. `ClosingRun` and its mutants -/

structure ExpClosingRun (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w) w'
  shared : ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc
structure MutClosingSplit (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w) w'
  shared : (∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children))) ∧
    ∃ t2 : Sparkle.IR.AST.Module, Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t2 raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc
structure MutClosingHideChildren (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w) w'
  shared : ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ ∃ children : List Res, CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc
structure MutClosingW5Dv (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w) w'
  shared : ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc
structure MutClosingW5Jqc (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w) w'
  shared : ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    JQC L.O (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc
structure MutClosingStopSucc (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w + 1) w'
  shared : ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc
structure MutClosingEnvSwap (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w) w'
  shared : ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR' e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc

/-- Constructor telescope comparison of two structures on the same parameter fvars (field types at REDUCIBLE
transparency, stricter than default). -/
def structPair (a b : Name) : MetaM Nat := do
  let env ← getEnv
  let some (.inductInfo i1) := env.find? a | throwError "no {a}"
  let some (.inductInfo i2) := env.find? b | throwError "no {b}"
  unless i1.numParams == i2.numParams do throwError "CR STRUCT FAILED: numParams"
  let c1 ← getConstInfo (a ++ `mk)
  let c2 ← getConstInfo (b ++ `mk)
  forallTelescope c1.type fun xs _ => do
    let ps := xs[:i1.numParams].toArray
    let mut t2 ← instantiateForall c2.type ps
    let mut j : Nat := 0
    for x in xs[i1.numParams:].toArray do
      let ld ← x.fvarId!.getDecl
      match t2 with
      | .forallE n ty bd bi =>
        unless n == ld.userName do throwError "CR STRUCT FAILED: field {j}: {n} ≠ {ld.userName}"
        unless bi == ld.binderInfo do throwError "CR STRUCT FAILED: binderInfo of {n}"
        unless ← withReducible (isDefEq ty ld.type) do throwError "CR STRUCT FAILED: type of {n}"
        t2 := bd.instantiate1 x
        j := j + 1
      | _ => throwError "CR STRUCT FAILED: {b}.mk has fewer fields (at {ld.userName})"
    if t2.isForall then throwError "CR STRUCT FAILED: {b}.mk has an EXTRA field"
    return j

run_cmd Lean.Elab.Command.liftTermElabM do
  let j ← structPair ``ClosingRun ``Tests.Gen5.ClosingRunCheck.ExpClosingRun
  logInfo m!"CR STRUCT OK ClosingRun: {j} fields = ExpClosingRun (names, order, binderInfo, types), no extra field"
  for mu in [``Tests.Gen5.ClosingRunCheck.MutClosingSplit, ``Tests.Gen5.ClosingRunCheck.MutClosingHideChildren,
      ``Tests.Gen5.ClosingRunCheck.MutClosingW5Dv, ``Tests.Gen5.ClosingRunCheck.MutClosingW5Jqc,
      ``Tests.Gen5.ClosingRunCheck.MutClosingStopSucc, ``Tests.Gen5.ClosingRunCheck.MutClosingEnvSwap] do
    let acc ← try
        let _ ← structPair ``ClosingRun mu
        pure true
      catch e => do
        logInfo m!"CR STRUCT MUTANT REJECTED {mu}: {e.toMessageData}"
        pure false
    if acc then throwError "CR STRUCT MUTANT ACCEPTED: {mu}"

/-! ## 2. Expected types and mutants -/

/-- `PortsServed`, independent value. -/
noncomputable def ExpPortsServed : {ι : Type} → {dom : ι → Sparkle.Core.Domain.DomainConfig} →
    {mref : ST.Ref IO.RealWorld Meta.State} → {cref : ST.Ref IO.RealWorld Core.State} →
    Laws mref cref → Pkgs ι dom → Name → MachineShape → Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Design →
    List FVarId → IO.Ref (ExprStructMap String) → Prop :=
  fun {ι} {dom} {mref} {cref} L P X shape t raw D ids cache =>
    machPorts X ids cache shape.binders = t.inputs ∧ ServedP (ShipsRes L P) X shape raw D ids cache

noncomputable def MutPortsNoMach : {ι : Type} → {dom : ι → Sparkle.Core.Domain.DomainConfig} →
    {mref : ST.Ref IO.RealWorld Meta.State} → {cref : ST.Ref IO.RealWorld Core.State} →
    Laws mref cref → Pkgs ι dom → Name → MachineShape → Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Design →
    List FVarId → IO.Ref (ExprStructMap String) → Prop :=
  fun {ι} {dom} {mref} {cref} L P X shape t raw D ids cache =>
    ServedP (ShipsRes L P) X shape raw D ids cache

def ExpCR0 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool} {ci : ConstantInfo} {envR envR' : Environment}
    {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (h : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR e hint top named)
      (profLogIO b) X shape) mctx mref cctx cref w5 (some (raw, D)) w6

def ExpCR1h : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx) {X : Name} {D : Nat}
    {w w1 : Void IO.RealWorld} {s : Tools.ShippingEntryReadsLinked.CoreSaved}
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheShips L P Reach (cv w))
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1),
    InvAt L P Reach (D + 1) w1

def ExpCR1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hst : InvAt L P Reach (dv w) w)
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    InvAt L P Reach (dv w + 1) w5

def ExpCR2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {tenv : Environment} {b : Bool} {X : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    {t t' : Sparkle.IR.AST.Module} {d₀ : Design} {children : List Res}
    (hmix : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) X shape.binders shape.body)
      (t, d₀))
    (hcl : closeLets shape.layout.lets t = some t')
    (hmt : (shape.insts = [] ∧ children = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ CloseCalls shape t (closeMachine shape.layout t') d₀ children m d ∧
        ChildrenShipsI L P Reach shape children))
    (hreach : ∀ k (hk : k < shape.insts.length),
      (shape.instOrigins.getD k .ord).child? = none → Reach (shape.insts[k]).1)
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none),
    SoundXAt (PortsServed L P X shape t m d) X shape m d

def ExpCR3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {t m : Sparkle.IR.AST.Module} {d : Design}
    (hX : SoundXAt (PortsServed L P p.decl p.d.shape t m d) p.decl p.d.shape m d),
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P p.decl p.d.shape t m d) p.decl p.d m d dom
      p.src p.extS p.extBS p.lsrc

def ExpCR4 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h1 : 1 ≤ dv w) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hst : InvAt L P Reach (dv w) w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'),
    InvAt L P Reach (dv w) w'

def ExpConn : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D

def MutCR0EnvSwap : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {w w' : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool} {ci : ConstantInfo} {envR envR' : Environment}
    {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (h : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR' e hint top named)
      (profLogIO b) X shape) mctx mref cctx cref w5 (some (raw, D)) w6

def MutCR1Dv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hst : InvAt L P Reach (dv w) w)
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    InvAt L P Reach (dv w) w5

def MutCR1Jqc : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hst : InvAt L P Reach (dv w) w)
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    JQC L.O (dv w + 1) w5

def MutCR1W3 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hst : InvAt L P Reach (dv w) w)
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    ∃ w3 : Void IO.RealWorld, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 ∧
      InvAt L P Reach (dv w + 1) w3

def MutCR2NoReach : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {tenv : Environment} {b : Bool} {X : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    {t t' : Sparkle.IR.AST.Module} {d₀ : Design} {children : List Res}
    (hmix : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) X shape.binders shape.body)
      (t, d₀))
    (hcl : closeLets shape.layout.lets t = some t')
    (hmt : (shape.insts = [] ∧ children = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ CloseCalls shape t (closeMachine shape.layout t') d₀ children m d ∧
        ChildrenShipsI L P Reach shape children))
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none),
    SoundXAt (PortsServed L P X shape t m d) X shape m d

def MutCR2ChildrenFree : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {tenv : Environment} {b : Bool} {X : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    {t t' : Sparkle.IR.AST.Module} {d₀ : Design} {children : List Res}
    (hmix : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) X shape.binders shape.body)
      (t, d₀))
    (hcl : closeLets shape.layout.lets t = some t')
    (hmt : (shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ CloseCalls shape t (closeMachine shape.layout t') d₀ children m d ∧
        ChildrenShipsI L P Reach shape children))
    (hreach : ∀ k (hk : k < shape.insts.length),
      (shape.instOrigins.getD k .ord).child? = none → Reach (shape.insts[k]).1)
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none),
    SoundXAt (PortsServed L P X shape t m d) X shape m d

def MutCR4StopSucc : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h1 : 1 ≤ dv w) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hst : InvAt L P Reach (dv w) w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'),
    InvAt L P Reach (dv w + 1) w'

def MutCR4NoH1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hst : InvAt L P Reach (dv w) w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'),
    InvAt L P Reach (dv w) w'

def MutConnNoRow : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D

def MutConnNoGen : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop),
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D

def MutConnT1Hyp : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1Hyp L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D

def MutConnNoH1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D


/-! ## 2a. Mutant comparator at REDUCIBLE transparency
(the default `isDefEq` fallback of `cmpEq` unfolds `translateExprToWire` and exceeds the recursion limit, a runtime
exception; the mutants are rejected by the same binder-by-binder comparison with a reducible fallback). -/

def cmpEqR (what : String) (a e : Lean.Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let e ← instantiateMVars e
  if a == e then return
  unless (← withReducible (isDefEq a e)) do
    throwError "CR CHECK FAILED {what}"

partial def cmpTeleR (what : String) (a e : Lean.Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | .forallE na ta ba bia, .forallE ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "CR CHECK FAILED {what}: binder {i} name"
    unless bia == bie do throwError "CR CHECK FAILED {what}: binder {i} info"
    cmpEqR s!"{what} binder {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpTeleR what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .forallE na .., _ => throwError "CR CHECK FAILED {what}: extra binder {i} ({na})"
  | _, .forallE ne .. => throwError "CR CHECK FAILED {what}: missing binder {i} ({ne})"
  | _, _ => cmpEqR s!"{what} conclusion" a e

def checkMutantR (thm mt : Name) : MetaM Unit := do
  let a ← stmtOf thm
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTeleR s!"{thm} vs mutant {mt}" a e
      pure true
    catch _ => pure false
  if accepted then throwError "CR MUTANT ACCEPTED: {mt} matches {thm}"
  logInfo m!"CR MUTANT REJECTED {mt} (against {thm}; binder-by-binder, reducible fallback)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``PortsServed ``ExpPortsServed
  checkMutant ``PortsServed ``MutPortsNoMach
  checkExpected ``RunReadsAt.machineRun ``ExpCR0
  checkExpected ``coreHead_invAt0 ``ExpCR1h
  checkExpected ``invAt_w5_of_runReadsAt ``ExpCR1
  checkExpected ``soundX_ships_at ``ExpCR2
  checkExpected ``trace_of_soundX_at ``ExpCR3
  checkExpected ``stop_of_run ``ExpCR4
  checkExpected ``closingRun_of_run ``ExpConn
  checkMutantR ``RunReadsAt.machineRun ``Tests.Gen5.ClosingRunCheck.MutCR0EnvSwap
  checkMutantR ``invAt_w5_of_runReadsAt ``Tests.Gen5.ClosingRunCheck.MutCR1Dv
  checkMutantR ``invAt_w5_of_runReadsAt ``Tests.Gen5.ClosingRunCheck.MutCR1Jqc
  checkMutantR ``invAt_w5_of_runReadsAt ``Tests.Gen5.ClosingRunCheck.MutCR1W3
  checkMutantR ``soundX_ships_at ``Tests.Gen5.ClosingRunCheck.MutCR2NoReach
  checkMutantR ``soundX_ships_at ``Tests.Gen5.ClosingRunCheck.MutCR2ChildrenFree
  checkMutantR ``stop_of_run ``Tests.Gen5.ClosingRunCheck.MutCR4StopSucc
  checkMutantR ``stop_of_run ``Tests.Gen5.ClosingRunCheck.MutCR4NoH1
  checkMutantR ``closingRun_of_run ``Tests.Gen5.ClosingRunCheck.MutConnNoRow
  checkMutantR ``closingRun_of_run ``Tests.Gen5.ClosingRunCheck.MutConnNoGen
  checkMutantR ``closingRun_of_run ``Tests.Gen5.ClosingRunCheck.MutConnT1Hyp
  checkMutantR ``closingRun_of_run ``Tests.Gen5.ClosingRunCheck.MutConnNoH1

/-! ## 3. Closure audit -/

def forbidConsts : List Name :=
  [``Tools.ShippingChildDepthC.BodyStepC, ``Tools.ShippingGen2.core_reads_invAt0, ``Tools.ShippingGen2.soundX_ships_ran,
   ``Tools.ShippingGen2.servedShips0_proved, ``Tools.ShippingGen2.TopShips, ``Lean.ofReduceBool,
   ``Tools.ShippingGen2.T1Hyp.rec, ``Tools.ShippingGen2.T1Hyp.casesOn, ``Tools.ShippingGen2.T1Hyp.recOn] ++
  (["pkg", "defines", "closes", "dec", "closed"].map fun f => (``Tools.ShippingGen2.T1Hyp).str f)

def badProj (e : Lean.Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s _ _ => s == ``Tools.ShippingGen2.T1Hyp
    | _ => false).isSome

def body? : ConstantInfo → Option Lean.Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure AReach where
  hit : Option (List Name) := none
  seen : NameSet := {}
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Nat := 0

def reach (root : Name) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "CR AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | continue
    let body := body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques + 1 }
    if badProj ci.type || (body.map badProj).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if forbidConsts.contains u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  unless badProj (.proj ``Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do throwError "CR AUDIT FAILED: raw T1Hyp proj missed"
  if badProj (.proj ``Tools.ShippingGen2.T1HypND 1 (.bvar 0)) then throwError "CR AUDIT FAILED: T1HypND proj flagged"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "CR AUDIT FAILED: unrelated raw proj flagged"
  logInfo "CR CONTROL rawProj: T1Hyp flagged, T1HypND and Prod not flagged"
  let F := `Tests.Gen5.ClosingRunFixture
  for (c, bad) in [(F ++ `badCoreReads, true), (F ++ `badCoreReadsHelper, true), (F ++ `badBodyStep, true),
      (F ++ `badDec, true), (F ++ `badHypCases, true), (F ++ `badSoundXRan, true), (F ++ `badServed0, true),
      (F ++ `badTopShips, true), (F ++ `badReduceBool, true), (F ++ `unrelated, false), (F ++ `cleanND, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "CR AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "CR AUDIT FAILED: detector flags {c}"
    logInfo m!"CR CONTROL {c}: {toString r.hit}"
  let base := [``Tools.ShippingChildVCA.keepsA_framed]
  for (c, req) in [(``coreHead_invAt0, base), (``invAt_w5_of_runReadsAt, base ++ [``coreHead_invAt0]),
      (``soundX_ships_at, [``Tools.ShippingMachineEntry.synthesizeMachineCertified_soundX]),
      (``stop_of_run, [``Tools.ShippingGen2.keepBody, ``Tools.ShippingGen2.core_tripleAInv]),
      (``closingRun_of_run, base ++ [``Tools.ShippingGen5RunReads.runReads_of_run, ``coreHead_invAt0,
        ``Tools.ShippingGen2.synthesizeMachineCertified_runsS, ``Tools.ShippingGen2.keepBody,
        ``Tools.ShippingGen2.core_tripleAInv, ``Tools.ShippingGen2.Pkg.traceX,
        ``Tools.ShippingGen2DataBridge.hord_of_row, ``Tools.ShippingGen2.T1HypND.closed])] do
    let r ← reach c
    if let some p := r.hit then throwError "CR AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "CR AUDIT FAILED {c}: {t} not reached"
    logInfo m!"CR REACH {c}: no BodyStepC / core_reads_invAt0 / soundX_ships_ran / servedShips0_proved / TopShips / ofReduceBool / T1Hyp field (named, raw proj, recursor); reaches {req} (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques})"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``RunReadsAt.machineRun, ``coreHead_invAt0, ``invAt_w5_of_runReadsAt, ``soundX_ships_at,
      ``trace_of_soundX_at, ``stop_of_run, ``closingRun_of_run, ``PortsServed] do
    checkAxioms n

end Tests.Gen5.ClosingRunCheck
