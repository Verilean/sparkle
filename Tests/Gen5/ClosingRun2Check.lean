import Tools.ShippingGen5ClosingRun2
import Tests.Gen5.ClosingRunCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in the Pod (kjob lake build Tests.Gen5.ClosingRun2Check, exit 0: TYPE 12, MUTANT 28, STRUCT 3 + 10 mutants, controls 12, REACH 8, AXIOMS 11) on the tree of 018ff69a; clean issue-linked build is run by the coder (not yet done).
-- No sorry / axiom / native_decide.

/-! # DG-CLOSINGRUN2 checks (Tools/ShippingGen5ClosingRun2.lean; scripts/gen5/DG_CLOSINGRUN_FREEZE_R4.md)

Every Expected statement below is written from the frozen types of freeze r4 §1 (not derived from the implementation's
signature, and the Lean text of the implementation is not imported into this file's Expected definitions).
ONE comparator is used for everything: `cmpTeleR` = binder-by-binder (`∀`/`fun`), names with macro scopes erased, binder
info, types by `==` with a REDUCIBLE `isDefEq` fallback. Structures use the REDUCIBLE field-by-field `structPair`.
Positive controls run first with the SAME comparator: each Expected statement is accepted, and the existing
`ClosingRun`, `stop_of_run`, `closingRun_of_run` Expected statements of `ClosingRunCheck` are re-accepted
(that file is not edited). Mutants are one-point, well-typed variants of an Expected statement produced from the same text;
they are rejected by this comparator (a rejection by signature / defeq of a changed statement, NOT a semantic counterexample).
Then: explicit value+type closure audit with negative / clean controls, and AXIOMS.

Not checked / not claimed: non-vacuity, `hord`/`hrow`, `hGen`/`GeneratedAt`, depth-0 `stop`, T1/FG. -/

namespace Tests.Gen5.ClosingRun2Helper
theorem helperA : True := (fun _ => trivial) @Tools.ShippingGen2.core_reads_invAt0
end Tests.Gen5.ClosingRun2Helper
namespace Tests.Gen5.ClosingRun2Helper2
theorem helperB : True := Tests.Gen5.ClosingRun2Helper.helperA
end Tests.Gen5.ClosingRun2Helper2
namespace Tests.Gen5.ClosingRun2Fixture
theorem badCoreReads : True := (fun _ => trivial) @Tools.ShippingGen2.core_reads_invAt0
theorem badCoreReadsHelper : True := Tests.Gen5.ClosingRun2Helper2.helperB
theorem badBodyStep : True := (fun _ => trivial) @Tools.ShippingChildDepthC.BodyStepC
theorem badDec : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
theorem badHypCases : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.casesOn.{0}
theorem badSoundXRan : True := (fun _ => trivial) @Tools.ShippingGen2.soundX_ships_ran
theorem badServed0 : True := (fun _ => trivial) @Tools.ShippingGen2.servedShips0_proved
theorem badTopShips : True := (fun _ => trivial) @Tools.ShippingGen2.TopShips
theorem badReduceBool : True := (fun _ => trivial) @Lean.ofReduceBool
theorem unrelated : True := trivial
theorem cleanND : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.pkg
end Tests.Gen5.ClosingRun2Fixture

namespace Tests.Gen5.ClosingRun2Check
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun Tools.ShippingGen5ClosingRun2
open Tests.Gen3.ExpectedType

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## 1. Independent Expected values -/
noncomputable def ExpClosingShared :
    {ι : Type} → {dom : ι → Sparkle.Core.Domain.DomainConfig} → {mref : ST.Ref IO.RealWorld Meta.State} →
    {cref : ST.Ref IO.RealWorld Core.State} → (L : Laws mref cref) → (P : Pkgs ι dom) → (Reach : Name → Prop) →
    (mctx : Meta.Context) → (cctx : Core.Context) → (X : Name) → (p : Pkg ι dom) →
    (Gen : ConstantInfo → Environment → Environment → Prop) →
    (w w' : Void IO.RealWorld) → (raw : Sparkle.IR.AST.Module) → (D : Design) → Prop :=
  fun {ι} {dom} {mref} {cref} L P Reach mctx cctx X p Gen w w' raw D =>
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
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
noncomputable def MutCSNoGen :
    {ι : Type} → {dom : ι → Sparkle.Core.Domain.DomainConfig} → {mref : ST.Ref IO.RealWorld Meta.State} →
    {cref : ST.Ref IO.RealWorld Core.State} → (L : Laws mref cref) → (P : Pkgs ι dom) → (Reach : Name → Prop) →
    (mctx : Meta.Context) → (cctx : Core.Context) → (X : Name) → (p : Pkg ι dom) →
    (Gen : ConstantInfo → Environment → Environment → Prop) →
    (w w' : Void IO.RealWorld) → (raw : Sparkle.IR.AST.Module) → (D : Design) → Prop :=
  fun {ι} {dom} {mref} {cref} L P Reach mctx cctx X p Gen w w' raw D =>
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
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
noncomputable def MutCSw5Dv :
    {ι : Type} → {dom : ι → Sparkle.Core.Domain.DomainConfig} → {mref : ST.Ref IO.RealWorld Meta.State} →
    {cref : ST.Ref IO.RealWorld Core.State} → (L : Laws mref cref) → (P : Pkgs ι dom) → (Reach : Name → Prop) →
    (mctx : Meta.Context) → (cctx : Core.Context) → (X : Name) → (p : Pkg ι dom) →
    (Gen : ConstantInfo → Environment → Environment → Prop) →
    (w w' : Void IO.RealWorld) → (raw : Sparkle.IR.AST.Module) → (D : Design) → Prop :=
  fun {ι} {dom} {mref} {cref} L P Reach mctx cctx X p Gen w w' raw D =>
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
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
noncomputable def MutCSEnvSwap :
    {ι : Type} → {dom : ι → Sparkle.Core.Domain.DomainConfig} → {mref : ST.Ref IO.RealWorld Meta.State} →
    {cref : ST.Ref IO.RealWorld Core.State} → (L : Laws mref cref) → (P : Pkgs ι dom) → (Reach : Name → Prop) →
    (mctx : Meta.Context) → (cctx : Core.Context) → (X : Name) → (p : Pkg ι dom) →
    (Gen : ConstantInfo → Environment → Environment → Prop) →
    (w w' : Void IO.RealWorld) → (raw : Sparkle.IR.AST.Module) → (D : Design) → Prop :=
  fun {ι} {dom} {mref} {cref} L P Reach mctx cctx X p Gen w w' raw D =>
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
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
noncomputable def MutCSDropTrace :
    {ι : Type} → {dom : ι → Sparkle.Core.Domain.DomainConfig} → {mref : ST.Ref IO.RealWorld Meta.State} →
    {cref : ST.Ref IO.RealWorld Core.State} → (L : Laws mref cref) → (P : Pkgs ι dom) → (Reach : Name → Prop) →
    (mctx : Meta.Context) → (cctx : Core.Context) → (X : Name) → (p : Pkg ι dom) →
    (Gen : ConstantInfo → Environment → Environment → Prop) →
    (w w' : Void IO.RealWorld) → (raw : Sparkle.IR.AST.Module) → (D : Design) → Prop :=
  fun {ι} {dom} {mref} {cref} L P Reach mctx cctx X p Gen w w' raw D =>
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
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
      ChildrenShipsI L P Reach p.d.shape children))
def ExpClosingRunShared : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingRun L P Reach mctx cctx X p Gen w w' raw D),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def ExpInvAtW5JQC : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    InvAt L P Reach (dv w + 1) w5
def ExpSharedOfRun : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def ExpRun0OfRun : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def ExpGA : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') p),
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') p) w w' raw D
def ExpNonempty : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {DataOk : Pkg ι dom → Prop} {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    (h : ClosingPremises L P Reach DataOk mctx cctx X p w w' raw D Gen),
    Nonempty (ClosingRun L P Reach mctx cctx X p Gen w w' raw D)
def ExpGenOf : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingShared L P Reach mctx cctx X p Gen w w' raw D),
    ∃ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧ Gen ci envR envR'
def ExpNotFalse : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingShared L P Reach mctx cctx X p (fun _ _ _ => False) w w' raw D),
    False
def MutHordNoBound : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutHordFieldsNe : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields ≠ [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutSharedNoHc : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutSharedJqc0 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O 0 w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutSharedHIHdv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutSharedHKIdv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutSharedT1Hyp : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1Hyp L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutSharedNoGen : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
,
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D
def MutW5Dv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    InvAt L P Reach (dv w) w5
def MutW5Jqc0 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hw : JQC L.O 0 w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    InvAt L P Reach (dv w + 1) w5
def MutW5NoHc : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hw : JQC L.O (dv w) w)
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    InvAt L P Reach (dv w + 1) w5
def MutW5W6 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6),
    InvAt L P Reach (dv w + 1) w6
def MutRun0HIHdv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach (dv w)) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def MutRun0HIH2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 2) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def MutRun0HKI2 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 2)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def MutRun0NoHd0 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def MutRun0Hd1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 1)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'),
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D
def MutGAEnvR : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR) p),
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') p) w w' raw D
def MutGAEntryFalse : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst false false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') p),
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') p) w w' raw D
def MutGANoH1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') p),
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') p) w w' raw D
def MutGAT1Hyp : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1Hyp L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') p),
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') p) w w' raw D
def MutGenOfNoGen : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingShared L P Reach mctx cctx X p Gen w w' raw D),
    ∃ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6
def MutNotFalseTrue : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingShared L P Reach mctx cctx X p (fun _ _ _ => True) w w' raw D),
    False
def MutShOfRunNotShared : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingRun L P Reach mctx cctx X p Gen w w' raw D),
    ClosingShared L P Reach mctx cctx X p (fun _ _ _ => True) w w' raw D
/-! ## 2. Structures: Expected and mutants -/
structure ExpClosingRun0 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  start0 : Start L mctx cctx w
  depth0 : dv w = 0
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D
structure MutRun0Stop (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  start0 : Start L mctx cctx w
  depth0 : dv w = 0
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D
  stop   : InvAt L P Reach (dv w) w'
structure MutRun0Depth1 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  start0 : Start L mctx cctx w
  depth0 : dv w = 1
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D
structure MutRun0NoStart (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  depth0 : dv w = 0
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D
structure MutRun0Swap (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  depth0 : dv w = 0
  start0 : Start L mctx cctx w
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D
structure MutRun0Jqc (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  start0 : JQC L.O 0 w
  depth0 : dv w = 0
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D
structure ExpClosingPremises (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
  hT   : T1HypND L P Reach DataOk
  hA   : AdmCtx L.O.quiet mctx cctx
  hR   : Reach X
  hP   : P X = some p
  hst  : InvAt L P Reach (dv w) w
  hIH  : IHAt L P Reach (dv w + 1)
  hKI  : ChildKeepsInv L P Reach (dv w + 1)
  h1   : 1 ≤ dv w
  hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  hGen : ∀ b ci envR envR' w5 w6,
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'
structure MutPremNoH1 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
  hT   : T1HypND L P Reach DataOk
  hA   : AdmCtx L.O.quiet mctx cctx
  hR   : Reach X
  hP   : P X = some p
  hst  : InvAt L P Reach (dv w) w
  hIH  : IHAt L P Reach (dv w + 1)
  hKI  : ChildKeepsInv L P Reach (dv w + 1)
  hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  hGen : ∀ b ci envR envR' w5 w6,
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'
structure MutPremT1Hyp (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
  hT   : T1Hyp L P Reach DataOk
  hA   : AdmCtx L.O.quiet mctx cctx
  hR   : Reach X
  hP   : P X = some p
  hst  : InvAt L P Reach (dv w) w
  hIH  : IHAt L P Reach (dv w + 1)
  hKI  : ChildKeepsInv L P Reach (dv w + 1)
  h1   : 1 ≤ dv w
  hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  hGen : ∀ b ci envR envR' w5 w6,
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'
structure MutPremGenTrue (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
  hT   : T1HypND L P Reach DataOk
  hA   : AdmCtx L.O.quiet mctx cctx
  hR   : Reach X
  hP   : P X = some p
  hst  : InvAt L P Reach (dv w) w
  hIH  : IHAt L P Reach (dv w + 1)
  hKI  : ChildKeepsInv L P Reach (dv w + 1)
  h1   : 1 ≤ dv w
  hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  hGen : ∀ b ci envR envR' w5 w6,
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → True
structure MutPremHIH0 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
  hT   : T1HypND L P Reach DataOk
  hA   : AdmCtx L.O.quiet mctx cctx
  hR   : Reach X
  hP   : P X = some p
  hst  : InvAt L P Reach (dv w) w
  hIH  : IHAt L P Reach (dv w)
  hKI  : ChildKeepsInv L P Reach (dv w + 1)
  h1   : 1 ≤ dv w
  hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  hGen : ∀ b ci envR envR' w5 w6,
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'
structure MutPremNoHrow (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hT   : T1HypND L P Reach DataOk
  hA   : AdmCtx L.O.quiet mctx cctx
  hR   : Reach X
  hP   : P X = some p
  hst  : InvAt L P Reach (dv w) w
  hIH  : IHAt L P Reach (dv w + 1)
  hKI  : ChildKeepsInv L P Reach (dv w + 1)
  h1   : 1 ≤ dv w
  hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  hGen : ∀ b ci envR envR' w5 w6,
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'
/-! ## 3. The single comparator -/

def cmpEqR (what : String) (a e : Lean.Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let e ← instantiateMVars e
  if a == e then return
  unless (← withReducible (isDefEq a e)) do
    throwError "CR2 CHECK FAILED {what}"

partial def cmpTeleR (what : String) (a e : Lean.Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | .forallE na ta ba bia, .forallE ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "CR2 CHECK FAILED {what}: binder {i} name {na} vs {ne}"
    unless bia == bie do throwError "CR2 CHECK FAILED {what}: binder {i} info"
    cmpEqR s!"{what} binder {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpTeleR what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .lam na ta ba bia, .lam ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "CR2 CHECK FAILED {what}: parameter {i} name {na} vs {ne}"
    unless bia == bie do throwError "CR2 CHECK FAILED {what}: parameter {i} info"
    cmpEqR s!"{what} parameter {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpTeleR what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .forallE na .., _ => throwError "CR2 CHECK FAILED {what}: extra binder {i} ({na})"
  | _, .forallE ne .. => throwError "CR2 CHECK FAILED {what}: missing binder {i} ({ne})"
  | .lam na .., _ => throwError "CR2 CHECK FAILED {what}: extra parameter {i} ({na})"
  | _, .lam ne .. => throwError "CR2 CHECK FAILED {what}: missing parameter {i} ({ne})"
  | _, _ => cmpEqR s!"{what} conclusion" a e

def checkExpectedR (thm exp : Name) : MetaM Unit := do
  let ciT ← getConstInfo thm
  let ciE ← getConstInfo exp
  unless ciT.levelParams.length == ciE.levelParams.length do
    throwError "CR2 CHECK FAILED {thm}: universe parameters"
  let a ← stmtOf thm
  let e ← stmtOf exp
  let e := e.instantiateLevelParams ciE.levelParams (ciT.levelParams.map mkLevelParam)
  cmpTeleR s!"{thm}" a e
  logInfo m!"CR2 TYPE OK {thm} against {exp} (reducible comparator)"

def checkMutantR (thm mt : Name) : MetaM Unit := do
  let a ← stmtOf thm
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try
      cmpTeleR s!"{thm} vs mutant {mt}" a e
      pure true
    catch _ => pure false
  if accepted then throwError "CR2 MUTANT ACCEPTED: {mt} matches {thm}"
  logInfo m!"CR2 MUTANT REJECTED {mt} (against {thm}; same comparator)"

/-- Constructor telescope comparison of two structures on the same parameter fvars (REDUCIBLE field types). -/
def structPair (a b : Name) : MetaM Nat := do
  let env ← getEnv
  let some (.inductInfo i1) := env.find? a | throwError "no {a}"
  let some (.inductInfo i2) := env.find? b | throwError "no {b}"
  unless i1.numParams == i2.numParams do throwError "CR2 STRUCT FAILED: numParams"
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
        unless n == ld.userName do throwError "CR2 STRUCT FAILED: field {j}: {n} ≠ {ld.userName}"
        unless bi == ld.binderInfo do throwError "CR2 STRUCT FAILED: binderInfo of {n}"
        unless ← withReducible (isDefEq ty ld.type) do throwError "CR2 STRUCT FAILED: type of {n}"
        t2 := bd.instantiate1 x
        j := j + 1
      | _ => throwError "CR2 STRUCT FAILED: {b}.mk has fewer fields (at {ld.userName})"
    if t2.isForall then throwError "CR2 STRUCT FAILED: {b}.mk has an EXTRA field"
    return j

def checkStructMutant (a mu : Name) : MetaM Unit := do
  let acc ← try
      let _ ← structPair a mu
      pure true
    catch e => do
      logInfo m!"CR2 STRUCT MUTANT REJECTED {mu}: {e.toMessageData}"
      pure false
  if acc then throwError "CR2 STRUCT MUTANT ACCEPTED: {mu}"

/-! ## 4. Positive controls, then mutants -/

run_cmd Lean.Elab.Command.liftTermElabM do
  -- positive controls on the EXISTING (accepted) statements, same comparator
  checkExpectedR ``ClosingRun.closingShared ``ExpClosingRunShared
  checkExpectedR ``stop_of_run ``Tests.Gen5.ClosingRunCheck.ExpCR4
  checkExpectedR ``closingRun_of_run ``Tests.Gen5.ClosingRunCheck.ExpConn
  checkExpectedR ``invAt_w5_of_runReadsAt ``Tests.Gen5.ClosingRunCheck.ExpCR1
  let j ← structPair ``ClosingRun ``Tests.Gen5.ClosingRunCheck.ExpClosingRun
  logInfo m!"CR2 STRUCT OK ClosingRun: {j} fields (positive control, same structure comparator)"
  -- the new statements
  checkExpectedR ``ClosingShared ``ExpClosingShared
  checkExpectedR ``invAt_w5_of_runReadsAt_JQC ``ExpInvAtW5JQC
  checkExpectedR ``closingShared_of_run ``ExpSharedOfRun
  checkExpectedR ``closingRun0_of_run ``ExpRun0OfRun
  checkExpectedR ``closingRun_of_run_ga ``ExpGA
  checkExpectedR ``closingRun_nonempty_of_premises ``ExpNonempty
  checkExpectedR ``gen_of_closingShared ``ExpGenOf
  checkExpectedR ``not_closingShared_false ``ExpNotFalse
  let j0 ← structPair ``ClosingRun0 ``ExpClosingRun0
  logInfo m!"CR2 STRUCT OK ClosingRun0: {j0} fields = ExpClosingRun0 (run, start0, depth0, shared; no stop)"
  let jp ← structPair ``ClosingPremises ``ExpClosingPremises
  logInfo m!"CR2 STRUCT OK ClosingPremises: {jp} fields = ExpClosingPremises"
  -- mutants (signature / defeq rejection)
  checkMutantR ``ClosingShared ``Tests.Gen5.ClosingRun2Check.MutCSNoGen
  checkMutantR ``ClosingShared ``Tests.Gen5.ClosingRun2Check.MutCSw5Dv
  checkMutantR ``ClosingShared ``Tests.Gen5.ClosingRun2Check.MutCSEnvSwap
  checkMutantR ``ClosingShared ``Tests.Gen5.ClosingRun2Check.MutCSDropTrace
  checkMutantR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.MutHordNoBound
  checkMutantR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.MutHordFieldsNe
  checkMutantR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.MutSharedNoHc
  checkMutantR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.MutSharedJqc0
  checkMutantR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.MutSharedHIHdv
  checkMutantR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.MutSharedHKIdv
  checkMutantR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.MutSharedT1Hyp
  checkMutantR ``closingShared_of_run ``Tests.Gen5.ClosingRun2Check.MutSharedNoGen
  checkMutantR ``invAt_w5_of_runReadsAt_JQC ``Tests.Gen5.ClosingRun2Check.MutW5Dv
  checkMutantR ``invAt_w5_of_runReadsAt_JQC ``Tests.Gen5.ClosingRun2Check.MutW5Jqc0
  checkMutantR ``invAt_w5_of_runReadsAt_JQC ``Tests.Gen5.ClosingRun2Check.MutW5NoHc
  checkMutantR ``invAt_w5_of_runReadsAt_JQC ``Tests.Gen5.ClosingRun2Check.MutW5W6
  checkMutantR ``closingRun0_of_run ``Tests.Gen5.ClosingRun2Check.MutRun0HIHdv
  checkMutantR ``closingRun0_of_run ``Tests.Gen5.ClosingRun2Check.MutRun0HIH2
  checkMutantR ``closingRun0_of_run ``Tests.Gen5.ClosingRun2Check.MutRun0HKI2
  checkMutantR ``closingRun0_of_run ``Tests.Gen5.ClosingRun2Check.MutRun0NoHd0
  checkMutantR ``closingRun0_of_run ``Tests.Gen5.ClosingRun2Check.MutRun0Hd1
  checkMutantR ``closingRun_of_run_ga ``Tests.Gen5.ClosingRun2Check.MutGAEnvR
  checkMutantR ``closingRun_of_run_ga ``Tests.Gen5.ClosingRun2Check.MutGAEntryFalse
  checkMutantR ``closingRun_of_run_ga ``Tests.Gen5.ClosingRun2Check.MutGANoH1
  checkMutantR ``closingRun_of_run_ga ``Tests.Gen5.ClosingRun2Check.MutGAT1Hyp
  checkMutantR ``gen_of_closingShared ``Tests.Gen5.ClosingRun2Check.MutGenOfNoGen
  checkMutantR ``not_closingShared_false ``Tests.Gen5.ClosingRun2Check.MutNotFalseTrue
  checkMutantR ``ClosingRun.closingShared ``Tests.Gen5.ClosingRun2Check.MutShOfRunNotShared
  checkStructMutant ``ClosingRun0 ``Tests.Gen5.ClosingRun2Check.MutRun0Stop
  checkStructMutant ``ClosingRun0 ``Tests.Gen5.ClosingRun2Check.MutRun0Depth1
  checkStructMutant ``ClosingRun0 ``Tests.Gen5.ClosingRun2Check.MutRun0NoStart
  checkStructMutant ``ClosingRun0 ``Tests.Gen5.ClosingRun2Check.MutRun0Swap
  checkStructMutant ``ClosingRun0 ``Tests.Gen5.ClosingRun2Check.MutRun0Jqc
  checkStructMutant ``ClosingPremises ``Tests.Gen5.ClosingRun2Check.MutPremNoH1
  checkStructMutant ``ClosingPremises ``Tests.Gen5.ClosingRun2Check.MutPremT1Hyp
  checkStructMutant ``ClosingPremises ``Tests.Gen5.ClosingRun2Check.MutPremGenTrue
  checkStructMutant ``ClosingPremises ``Tests.Gen5.ClosingRun2Check.MutPremHIH0
  checkStructMutant ``ClosingPremises ``Tests.Gen5.ClosingRun2Check.MutPremNoHrow

/-! ## 5. Closure audit (explicit value + type; negative and clean controls) -/

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
    if out.visited > cap then throwError "CR2 AUDIT INCOMPLETE at {root}"
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
  unless badProj (.proj ``Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do throwError "CR2 AUDIT FAILED: raw T1Hyp proj missed"
  if badProj (.proj ``Tools.ShippingGen2.T1HypND 1 (.bvar 0)) then throwError "CR2 AUDIT FAILED: T1HypND proj flagged"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "CR2 AUDIT FAILED: unrelated raw proj flagged"
  logInfo "CR2 CONTROL rawProj: T1Hyp flagged, T1HypND and Prod not flagged"
  let F := `Tests.Gen5.ClosingRun2Fixture
  for (c, bad) in [(F ++ `badCoreReads, true), (F ++ `badCoreReadsHelper, true), (F ++ `badBodyStep, true),
      (F ++ `badDec, true), (F ++ `badHypCases, true), (F ++ `badSoundXRan, true), (F ++ `badServed0, true),
      (F ++ `badTopShips, true), (F ++ `badReduceBool, true), (F ++ `unrelated, false), (F ++ `cleanND, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "CR2 AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "CR2 AUDIT FAILED: detector flags {c}"
    logInfo m!"CR2 CONTROL {c}: {toString r.hit}"
  let base := [``Tools.ShippingChildVCA.keepsA_framed, ``Tools.ShippingGen5ClosingRun.coreHead_invAt0]
  let shared := base ++ [``invAt_w5_of_runReadsAt_JQC, ``Tools.ShippingGen5RunReads.runReads_of_run,
        ``Tools.ShippingGen2.synthesizeMachineCertified_runsS, ``Tools.ShippingGen5ClosingRun.soundX_ships_at,
        ``Tools.ShippingGen5ClosingRun.trace_of_soundX_at, ``Tools.ShippingGen2.Pkg.traceX,
        ``Tools.ShippingGen2.T1HypND.closed]
  for (c, req) in [(``invAt_w5_of_runReadsAt_JQC, base), (``closingShared_of_run, shared),
      (``closingRun0_of_run, shared ++ [``closingShared_of_run]),
      (``closingRun_of_run_ga, [``Tools.ShippingGen5ClosingRun.closingRun_of_run]),
      (``closingRun_nonempty_of_premises, [``Tools.ShippingGen5ClosingRun.closingRun_of_run]),
      (``ClosingRun.closingShared, []), (``gen_of_closingShared, []), (``not_closingShared_false, [])] do
    let r ← reach c
    if let some p := r.hit then throwError "CR2 AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "CR2 AUDIT FAILED {c}: {t} not reached"
    logInfo m!"CR2 REACH {c}: no BodyStepC / core_reads_invAt0 / soundX_ships_ran / servedShips0_proved / TopShips / ofReduceBool / T1Hyp field (named, raw proj, recursor); reaches {req} (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques})"

/-! ## 6. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``ClosingShared, ``ClosingRun.closingShared, ``invAt_w5_of_runReadsAt_JQC, ``closingShared_of_run,
      ``ClosingRun0, ``closingRun0_of_run, ``closingRun_of_run_ga, ``ClosingPremises,
      ``closingRun_nonempty_of_premises, ``gen_of_closingShared, ``not_closingShared_false] do
    checkAxioms n

end Tests.Gen5.ClosingRun2Check
