import Tests.Compiler.SharedLeafMemKidIfaceTest
import Tools.ShippingKidsChildIfaceM
-- BUILT (unit SRM3): b15 exit 0 (dev run); the final-SHA rebuild is in REPORT-SRM3.md.
-- SCOPE (SRM3, audits): (1) for each of the EIGHT `*_derived` theorems of `Tests/Compiler/SharedLeafMemKidIfaceTest.lean` and for the eight component theorems (`leafM_closesA`, `leafM_ifaceP`, `wrapM_closesA`, `wrapM3_closesA`,
-- `wrapM_ifaceP`, `wrapM3_ifaceP`, `wrapQ_closesA`, `wrapQ_ifaceP`) the FULL forall-type is compared with `isDefEq` at DEFAULT transparency against a hand-written statement, and type-correct MUTATIONS of the hand-written
-- statement (wrong parent / interface name, names without the memory module, callees in the other order, no `CacheCoh`, wrong shared entry, a reflection / start-world premise dropped, ...) are REJECTED (the mutation check runs at
-- REDUCIBLE transparency: at default transparency it unfolds `machineData` of the parent and exhausts the heartbeat budget); (2) a closure audit: standard axioms only, no old `RefLaws` boundary, and NO old-form
-- `RealChild` / `InvW` / `MachineRan` / `MachineClosesAt` / `Kid` / `kidsChild_of_realM` / `ChildBnd` / `StartV` / `GenKid` / `KidFacts` / `MachineRunNC` / `CacheClosed` in the closure of the derived theorems, and the A-form memory lemmas
-- (`deepChild_ifaceP_M`, `memCallee_closesA`, `memCallee_ifaceP`, `core_kids_facts_ranAM`) ARE in it.  The examples do not make the class complete.
set_option Elab.async false
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
namespace Tests.Compiler.SharedLeafMemKidIfaceAuditTest
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingMemLeafRun Tools.ShippingMemLeafCache Tools.ShippingNmGroup Tools.ShippingNmEntry
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh
open Tools.ShippingSharedLeafHit Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingSharedLeafNL
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Sparkle.Compiler.MachMemory (memModule memChild?)
open Tools.ShippingMemCloses Tools.ShippingTopShareRun Tools.ShippingTopShareNoParent

/-- expected full type of `leafM_closesA` -/
@[reducible] def CLMFull : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``leafM leafM.machineData.shape

/-- MUTATION (wrong declaration) -/
@[reducible] def CLMName : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM leafM.machineData.shape

/-- MUTATION (RefLawsATele premise dropped) -/
@[reducible] def CLMNoT : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : True) (_hA : AdmCtx O.quiet mctx cctx),
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``leafM leafM.machineData.shape

/-- expected full type of `wrapM_closesA` -/
@[reducible] def CWMFull : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape

/-- MUTATION (wrong declaration) -/
@[reducible] def CWMName : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``leafM wrapM.machineData.shape

/-- MUTATION (reflection of the memory leaf dropped) -/
@[reducible] def CWMNoL : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape

/-- expected full type of `wrapM3_closesA` -/
@[reducible] def CW3Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape

/-- MUTATION (wrong declaration) -/
@[reducible] def CW3Name : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``leafM wrapM3.machineData.shape

/-- MUTATION (reflection of the memory leaf dropped) -/
@[reducible] def CW3NoL : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape

/-- expected full type of `wrapQ_closesA` -/
@[reducible] def CWQFull : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape

/-- MUTATION (wrong declaration) -/
@[reducible] def CWQName : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapP wrapQ.machineData.shape

/-- MUTATION (MachineCloses of the plain leaf dropped) -/
@[reducible] def CWQNoCl : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    True →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape

/-- expected full type of `leafM_ifaceP` -/
@[reducible] def ILMFull : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    ∀ {y : Res}, RealChildA O ``leafM y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``leafM) (machNIn leafM.machineData.shape) (leafM.machineData.shape.layout.outs.map (·.name)) [(memModule false 4 8).1.name] y.1 y.2

/-- MUTATION (names without the memory module) -/
@[reducible] def ILMNoMem : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    ∀ {y : Res}, RealChildA O ``leafM y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``leafM) (machNIn leafM.machineData.shape) (leafM.machineData.shape.layout.outs.map (·.name)) ([] : List String) y.1 y.2

/-- MUTATION (wrong interface name) -/
@[reducible] def ILMName : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    ∀ {y : Res}, RealChildA O ``leafM y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn leafM.machineData.shape) (leafM.machineData.shape.layout.outs.map (·.name)) [(memModule false 4 8).1.name] y.1 y.2

/-- MUTATION (wrong argument count) -/
@[reducible] def ILMNin : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    ∀ {y : Res}, RealChildA O ``leafM y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``leafM) (4) (leafM.machineData.shape.layout.outs.map (·.name)) [(memModule false 4 8).1.name] y.1 y.2

/-- expected full type of `wrapM_ifaceP` -/
@[reducible] def IWMFull : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapM y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2

/-- MUTATION (names without the memory module) -/
@[reducible] def IWMNoMem : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapM y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``leafM] y.1 y.2

/-- MUTATION (wrong interface name) -/
@[reducible] def IWMName : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapM y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``leafM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2

/-- MUTATION (reflection of the memory leaf dropped) -/
@[reducible] def IWMNoL : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    True →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapM y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2

/-- expected full type of `wrapM3_ifaceP` -/
@[reducible] def IW3Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapM3 y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2

/-- MUTATION (names without the memory module) -/
@[reducible] def IW3NoMem : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapM3 y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``leafM] y.1 y.2

/-- MUTATION (wrong interface name) -/
@[reducible] def IW3Name : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapM3 y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``leafM) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2

/-- MUTATION (reflection of the memory leaf dropped) -/
@[reducible] def IW3NoL : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    True →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapM3 y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2

/-- expected full type of `wrapQ_ifaceP` -/
@[reducible] def IWQFull : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapQ y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2

/-- MUTATION (names without the memory module) -/
@[reducible] def IWQNoMem : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapQ y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``leafP] y.1 y.2

/-- MUTATION (wrong interface name) -/
@[reducible] def IWQName : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapQ y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``leafP) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2

/-- MUTATION (MachineCloses of the plain leaf dropped) -/
@[reducible] def IWQNoCl : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    True →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    ∀ {y : Res}, RealChildA O ``wrapQ y →
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2

/-- expected full type (derived version) of `topshareM_closes0` -/
@[reducible] def DM0Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape

/-- MUTATION (parent name wrapM) -/
@[reducible] def DM0Name : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``wrapM topshareM.machineData.shape

/-- expected full type (derived version) of `topshareM_machineRun` -/
@[reducible] def DM1Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design

/-- MUTATION (machine run at depth 0) -/
@[reducible] def DM1D : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 0 ``topshareM topshareM.machineData.shape m design

/-- MUTATION (start world at depth 1) -/
@[reducible] def DM1W : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 1 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design

/-- MUTATION (entry premise of wrapM) -/
@[reducible] def DM1EP : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design

/-- expected full type (derived version) of `topshareM_entry_run` -/
@[reducible] def DM2Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 0 w → RunsTo (synthesizeCombinational ``topshareM) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length ∧
      closeLets topshareM.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
        topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
        topshareM.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareM.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

/-- MUTATION (no CacheCoh) -/
@[reducible] def DM2Coh : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 0 w → RunsTo (synthesizeCombinational ``topshareM) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length ∧
      closeLets topshareM.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
        topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
        topshareM.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareM.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ (fun _ : Std.HashMap Lean.Name Res => True) (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

/-- MUTATION (callees in the other order) -/
@[reducible] def DM2Rev : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 0 w → RunsTo (synthesizeCombinational ``topshareM) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length ∧
      closeLets topshareM.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
        topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
        topshareM.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareM.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

/-- MUTATION (start world at depth 1) -/
@[reducible] def DM2W : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 1 w → RunsTo (synthesizeCombinational ``topshareM) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length ∧
      closeLets topshareM.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
        topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
        topshareM.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareM.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

/-- expected full type (derived version) of `topshareM_shared_leaf` -/
@[reducible] def DM3Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (second callee not absent at the start) -/
@[reducible] def DM3NoAbs : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → True → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (the shared entry is wrapM) -/
@[reducible] def DM3Leaf : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``wrapM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (no CacheCoh) -/
@[reducible] def DM3Coh : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ (fun _ : Std.HashMap Lean.Name Res => True) (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (closing of topshareQ) -/
@[reducible] def DM3Run : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- expected full type (derived version) of `topshareQ_closes0` -/
@[reducible] def DQ0Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape

/-- MUTATION (parent name wrapQ) -/
@[reducible] def DQ0Name : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``wrapQ topshareQ.machineData.shape

/-- MUTATION (reflection of the plain leaf dropped) -/
@[reducible] def DQ0NoLeaf : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape

/-- expected full type (derived version) of `topshareQ_machineRun` -/
@[reducible] def DQ1Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design

/-- MUTATION (machine run at depth 0) -/
@[reducible] def DQ1D : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 0 ``topshareQ topshareQ.machineData.shape m design

/-- MUTATION (start world at depth 1) -/
@[reducible] def DQ1W : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 1 w → RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design

/-- expected full type (derived version) of `topshareQ_entry_run` -/
@[reducible] def DQ2Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 0 w → RunsTo (synthesizeCombinational ``topshareQ) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length ∧
      closeLets topshareQ.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareQ.machineData.shape) topshareQ.machineData.shape.insts.length
        topshareQ.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareQ.machineData.shape.insts.map (·.2.1))
        topshareQ.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareQ.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts.length),
          (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

/-- MUTATION (no CacheCoh) -/
@[reducible] def DQ2Coh : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 0 w → RunsTo (synthesizeCombinational ``topshareQ) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length ∧
      closeLets topshareQ.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareQ.machineData.shape) topshareQ.machineData.shape.insts.length
        topshareQ.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareQ.machineData.shape.insts.map (·.2.1))
        topshareQ.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareQ.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ (fun _ : Std.HashMap Lean.Name Res => True) (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts.length),
          (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

/-- MUTATION (start world at depth 1) -/
@[reducible] def DQ2W : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 1 w → RunsTo (synthesizeCombinational ``topshareQ) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length ∧
      closeLets topshareQ.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareQ.machineData.shape) topshareQ.machineData.shape.insts.length
        topshareQ.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareQ.machineData.shape.insts.map (·.2.1))
        topshareQ.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareQ.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts.length),
          (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

/-- expected full type (derived version) of `topshareQ_shared_leaf` -/
@[reducible] def DQ3Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapP = none → (cv w).get? ``wrapQ = none → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (the shared entry is wrapP) -/
@[reducible] def DQ3Leaf : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapP = none → (cv w).get? ``wrapQ = none → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``wrapP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (no CacheCoh) -/
@[reducible] def DQ3Coh : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapP = none → (cv w).get? ``wrapQ = none → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ (fun _ : Std.HashMap Lean.Name Res => True) (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (second callee not absent at the start) -/
@[reducible] def DQ3NoAbs : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapP = none → True → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (reflection of the memory leaf dropped) -/
@[reducible] def DM0NoL : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape

/-- MUTATION (reflection of the memory leaf dropped) -/
@[reducible] def DM1NoL : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design

/-- MUTATION (reflection of the memory leaf dropped) -/
@[reducible] def DM2NoL : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 0 w → RunsTo (synthesizeCombinational ``topshareM) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length ∧
      closeLets topshareM.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareM.machineData.shape) topshareM.machineData.shape.insts.length
        topshareM.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareM.machineData.shape.insts.map (·.2.1))
        topshareM.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareM.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) j (hj : j < [(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts.length),
          (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapM, wrapM.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩ : NCal), ⟨``wrapM3, wrapM3.machineData, leafM.machineData.shape.insts.map (·.1), namesM⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

/-- MUTATION (reflection of the memory leaf dropped) -/
@[reducible] def DM3NoL : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (reflection of the plain leaf dropped) -/
@[reducible] def DQ1NoLeaf : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design

/-- MUTATION (reflection of the plain leaf dropped) -/
@[reducible] def DQ2NoLeaf : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {y : Res}, JQC O 0 w → RunsTo (synthesizeCombinational ``topshareQ) mctx mref cctx cref w y w' → ∃ (Y : List Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      Y.length = [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length ∧
      closeLets topshareQ.machineData.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn topshareQ.machineData.shape) topshareQ.machineData.shape.insts.length
        topshareQ.machineData.shape.layout.slots.length (t.inputs.map (·.name)) (topshareQ.machineData.shape.insts.map (·.2.1))
        topshareQ.machineData.shape.instFields (Y.flatMap fun y => [y, y]) (closeMachine topshareQ.machineData.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosedNM (cv w10) ∧ KeyTop (cv w10) ∧ MemDet (cv w10) ∧ CacheCoh (cv w10) ∧
      (∀ j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length), ∃ y, Y[j]? = some y ∧ (cv w10).get? ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).c = some y) ∧
      (∀ i (hi : i < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts.length),
          (∃ md, (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w10).get? (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) j (hj : j < [(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩].length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts.length) k₂ (hk₂ : k₂ < ([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts.length),
          (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1 = (([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w10).get? ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? ((([(⟨``wrapP, wrapP.machineData, [], namesP⟩ : NCal), ⟨``wrapQ, wrapQ.machineData, [], namesQ⟩][i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name)

end Tests.Compiler.SharedLeafMemKidIfaceAuditTest

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let NT := `Tests.Compiler.SharedLeafMemKidIfaceTest
  let NA := `Tests.Compiler.SharedLeafMemKidIfaceAuditTest
  let pairs : List (Name × Name × List Name) :=
    [(NT ++ `leafM_closesA, NA ++ `CLMFull, [NA ++ `CLMName, NA ++ `CLMNoT]),
     (NT ++ `wrapM_closesA, NA ++ `CWMFull, [NA ++ `CWMName, NA ++ `CWMNoL]),
     (NT ++ `wrapM3_closesA, NA ++ `CW3Full, [NA ++ `CW3Name, NA ++ `CW3NoL]),
     (NT ++ `wrapQ_closesA, NA ++ `CWQFull, [NA ++ `CWQName, NA ++ `CWQNoCl]),
     (NT ++ `leafM_ifaceP, NA ++ `ILMFull, [NA ++ `ILMNoMem, NA ++ `ILMName, NA ++ `ILMNin]),
     (NT ++ `wrapM_ifaceP, NA ++ `IWMFull, [NA ++ `IWMNoMem, NA ++ `IWMName, NA ++ `IWMNoL]),
     (NT ++ `wrapM3_ifaceP, NA ++ `IW3Full, [NA ++ `IW3NoMem, NA ++ `IW3Name, NA ++ `IW3NoL]),
     (NT ++ `wrapQ_ifaceP, NA ++ `IWQFull, [NA ++ `IWQNoMem, NA ++ `IWQName, NA ++ `IWQNoCl]),
     (NT ++ `topshareM_closes0_derived, NA ++ `DM0Full, [NA ++ `DM0Name, NA ++ `DM0NoL]),
     (NT ++ `topshareM_machineRun_derived, NA ++ `DM1Full, [NA ++ `DM1D, NA ++ `DM1W, NA ++ `DM1EP, NA ++ `DM1NoL]),
     (NT ++ `topshareM_entry_run_derived, NA ++ `DM2Full, [NA ++ `DM2Coh, NA ++ `DM2Rev, NA ++ `DM2W, NA ++ `DM2NoL]),
     (NT ++ `topshareM_shared_leaf_derived, NA ++ `DM3Full, [NA ++ `DM3NoAbs, NA ++ `DM3Leaf, NA ++ `DM3Coh, NA ++ `DM3Run, NA ++ `DM3NoL]),
     (NT ++ `topshareQ_closes0_derived, NA ++ `DQ0Full, [NA ++ `DQ0Name, NA ++ `DQ0NoLeaf]),
     (NT ++ `topshareQ_machineRun_derived, NA ++ `DQ1Full, [NA ++ `DQ1D, NA ++ `DQ1W, NA ++ `DQ1NoLeaf]),
     (NT ++ `topshareQ_entry_run_derived, NA ++ `DQ2Full, [NA ++ `DQ2Coh, NA ++ `DQ2W, NA ++ `DQ2NoLeaf]),
     (NT ++ `topshareQ_shared_leaf_derived, NA ++ `DQ3Full, [NA ++ `DQ3Leaf, NA ++ `DQ3Coh, NA ++ `DQ3NoAbs])]
  for (thm, full, muts) in pairs do
    let gt ← instantiateMVars (← getConstInfo thm).type
    for (e, what) in [(gt, "the theorem's type"), (mkConst full, "the expected full type")] ++ muts.map fun c => (mkConst c, s!"mutation {c}") do
      if e.hasMVar || e.hasFVar then throwError "SRM3 AUDIT FAILED: metavariables / free variables in {what}"
      Meta.check e
    let pos ← withCurrHeartbeats (withTransparency .default (isDefEq gt (mkConst full)))
    unless pos do
      throwError "SRM3 AUDIT FAILED: the FULL type of {thm} is not definitionally the hand-written {full}"
    for c in muts do
      if (← withCurrHeartbeats (withReducible (isDefEq gt (mkConst c)))) then throwError "SRM3 AUDIT FAILED: the mutated full type of {thm} ({c}) was ACCEPTED"
    stdAxioms thm
    logInfo m!"SRM3 AUDIT: the full forall-type of {thm} is isDefEq (default transparency) to {full}; {muts.length} type-correct mutations are REJECTED (at reducible transparency); standard axioms only"

/-! ## closure audit -/

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let NT := `Tests.Compiler.SharedLeafMemKidIfaceTest
  let thms : List Name := ([`leafM_closesA, `leafM_ifaceP, `wrapM_closesA, `wrapM3_closesA, `wrapM_ifaceP, `wrapM3_ifaceP, `wrapQ_closesA, `wrapQ_ifaceP,
    `topshareM_closes0_derived, `topshareM_machineRun_derived, `topshareM_entry_run_derived, `topshareM_shared_leaf_derived,
    `topshareQ_closes0_derived, `topshareQ_machineRun_derived, `topshareQ_entry_run_derived, `topshareQ_shared_leaf_derived]).map (NT ++ ·)
  -- CONTROL: every forbidden root names a constant that EXISTS (a misspelled root would make the audit vacuous)
  let forbiddenRoots : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbiddenRoots do
    unless (← getEnv).contains f do throwError "SRM3 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  -- CONTROL: the old-form memory-kid theorem IS caught by the same walk
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbiddenRoots.any (·.isPrefixOf c)).length > 0 do throwError "SRM3 AUDIT FAILED: control walk found no old-form constant"
  for thm in thms do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM3 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    -- old-form boundary: `RealChild` (not `RealChildA`), `InvW`, `MachineRan` (not `MachineRanA`), `MachineClosesAt` (not `MachineClosesAtA` / `...Start0`), the memory-kid `Kid` and `kidsChild_of_realM`, and the SRM2 list
    let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM3 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    -- the old-form memory-kid chain: any `core_*` / `kids*` theorem of `Tools.ShippingMemKid*` namespaces
    let bad3 := cl.toList.filter fun c => (c.getPrefix.toString.startsWith "Tools.ShippingMemKid" || c.getPrefix.toString.startsWith "Tools.ShippingKidsChildIfaceM") && (c.getString!.startsWith "core_" || c.getString!.startsWith "kids")
    unless bad3.isEmpty do throwError "SRM3 AUDIT FAILED: old-form memory-kid chain in the closure of {thm}: {bad3}"
    let has (x : String) : Bool := (thm.toString.splitOn x).length > 1
    let must : List Name :=
      (if has "closesA" || has "derived" then [``Tools.ShippingSrm3Callee.memCallee_closesA, ``Tools.ShippingMemCloses.memIface] else []) ++
      (if has "ifaceP" || (has "derived" && !has "shared_leaf") then
        [``Tools.ShippingSrm3Callee.memCallee_ifaceP, ``Tools.ShippingSrm3Iface.deepChild_ifaceP_M, ``Tools.ShippingSrm3Iface.core_kids_facts_ranAM] else []) ++
      (if has "derived" && !has "shared_leaf" then [``Tools.ShippingNmEntry.nm_closes0] else [])
    for m in must do
      unless cl.contains m do throwError "SRM3 AUDIT FAILED: {m} not in the closure of {thm}"
    stdAxioms thm
    logInfo m!"SRM3 CLOSURE AUDIT: {thm}: standard axioms; closure {cl.size} constants; no old-form RealChild / InvW / MachineRan / MachineClosesAt / Kid / kidsChild_of_realM / ChildBnd / GenKid / KidFacts / CacheClosed; the A-form memory lemmas are in it"

end
