import Tests.Compiler.SharedLeafMemKidEntryTest
-- UNBUILT (unit SRM2): the run names and exits are recorded in REPORT-SRM2.md.
-- SCOPE (SRM2, step 2, audits): for each of the eight hand-applied theorems of `Tests/Compiler/SharedLeafMemKidEntryTest.lean` (`topshareM_*`, `topshareQ_*`: `closes0`, `machineRun`, `entry_run`, `shared_leaf`) the FULL
-- forall-type of the theorem is compared with `isDefEq` at DEFAULT transparency against a hand-written statement, and type-correct MUTATIONS of the hand-written statement (checked with `withReducible`: at default transparency that check exhausts the heartbeat budget) (parent name, depth, start world,
-- dropped interface / closing / reflection premise, wrong interface names, callees in the other order, no `CacheCoh`, wrong shared entry, callee not absent at the start) are REJECTED.  Then a closure audit: standard axioms
-- only, no old `RefLaws` boundary, no `ChildBnd` / `StartV` / `GenKid` / `KidFacts` / `MachineRunNC`, no `CacheClosed` clause, and the memory-aware lemmas are in the closure.  The examples do not make the class complete.
set_option Elab.async false
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
namespace Tests.Compiler.SharedLeafMemKidEntryAuditTest
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingMemLeafRun Tools.ShippingMemLeafCache Tools.ShippingNmGroup Tools.ShippingNmEntry
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh
open Tools.ShippingSharedLeafHit Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine Tools.ShippingSharedLeafNL
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Sparkle.Compiler.MachMemory (memModule memChild?)
open Tools.ShippingMemCloses Tools.ShippingTopShareRun Tools.ShippingTopShareNoParent

/-- expected full type of `topshareM_closes0` -/
@[reducible] def M0Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape

/-- MUTATION (parent name wrapM) -/
@[reducible] def M0Name : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``wrapM topshareM.machineData.shape

/-- MUTATION (interface premise of wrapM3 dropped) -/
@[reducible] def M0NoI3 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    True →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape

/-- MUTATION (interface premise of wrapM3 about wrapM results) -/
@[reducible] def M0I3rc : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape

/-- MUTATION (interface names without the memory module) -/
@[reducible] def M0I3ns : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``leafM] y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape

/-- MUTATION (closing premise of wrapM for wrapM3) -/
@[reducible] def M0C3 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape

/-- expected full type of `topshareM_machineRun` -/
@[reducible] def M1Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design

/-- MUTATION (machine run at depth 0) -/
@[reducible] def M1D : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 0 ``topshareM topshareM.machineData.shape m design

/-- MUTATION (start world at depth 1) -/
@[reducible] def M1W : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 1 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design

/-- MUTATION (entry premise of wrapM) -/
@[reducible] def M1EP : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineDefines mctx mref cctx cref ``wrapM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design

/-- MUTATION (interface premise of wrapM dropped) -/
@[reducible] def M1NoI1 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    True →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design

/-- expected full type of `topshareM_entry_run` -/
@[reducible] def M2Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
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
@[reducible] def M2Coh : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
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
@[reducible] def M2Rev : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
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
@[reducible] def M2W : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    (∀ y : Res, RealChildA O ``wrapM3 y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM3) (machNIn wrapM3.machineData.shape) (wrapM3.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
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

/-- MUTATION (interface premise of wrapM3 dropped) -/
@[reducible] def M2NoI3 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapM y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapM) (machNIn wrapM.machineData.shape) (wrapM.machineData.shape.layout.outs.map (·.name)) namesM y.1 y.2) →
    True →
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

/-- expected full type of `topshareM_shared_leaf` -/
@[reducible] def M3Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (second callee not absent at the start) -/
@[reducible] def M3NoAbs : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → True → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (the shared entry is wrapM) -/
@[reducible] def M3Leaf : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``wrapM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (no CacheCoh) -/
@[reducible] def M3Coh : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareM.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ (fun _ : Std.HashMap Lean.Name Res => True) (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (closing of topshareQ) -/
@[reducible] def M3Run : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM wrapM.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapM3 wrapM3.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapM = none → (cv w).get? ``wrapM3 = none → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapM = some y ∧ (cv w').get? ``wrapM3 = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafM = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- expected full type of `topshareQ_closes0` -/
@[reducible] def Q0Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape

/-- MUTATION (parent name wrapQ) -/
@[reducible] def Q0Name : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``wrapQ topshareQ.machineData.shape

/-- MUTATION (interface premise of wrapQ dropped) -/
@[reducible] def Q0NoIQ : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    True →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape

/-- MUTATION (interface names without the memory module) -/
@[reducible] def Q0IQns : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesP y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape

/-- MUTATION (closing premise of wrapQ dropped) -/
@[reducible] def Q0NoC2 : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    True →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape

/-- MUTATION (reflection of the plain leaf dropped) -/
@[reducible] def Q0NoLeaf : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    True →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareQ topshareQ.machineData.shape

/-- expected full type of `topshareQ_machineRun` -/
@[reducible] def Q1Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design

/-- MUTATION (machine run at depth 0) -/
@[reducible] def Q1D : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 0 ``topshareQ topshareQ.machineData.shape m design

/-- MUTATION (start world at depth 1) -/
@[reducible] def Q1W : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 1 w → RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design

/-- MUTATION (interface premise of wrapQ dropped) -/
@[reducible] def Q1NoIQ : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    True →
    MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape →
    ∀ {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}, JQC O 0 w → RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (m, design) w' → Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareQ topshareQ.machineData.shape m design

/-- expected full type of `topshareQ_entry_run` -/
@[reducible] def Q2Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
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
@[reducible] def Q2Coh : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
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
@[reducible] def Q2W : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    (∀ y : Res, RealChildA O ``wrapQ y → ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``wrapQ) (machNIn wrapQ.machineData.shape) (wrapQ.machineData.shape.layout.outs.map (·.name)) namesQ y.1 y.2) →
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

/-- MUTATION (interface premise of wrapQ dropped) -/
@[reducible] def Q2NoIQ : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    True →
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

/-- expected full type of `topshareQ_shared_leaf` -/
@[reducible] def Q3Full : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapP = none → (cv w).get? ``wrapQ = none → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (the shared entry is wrapP) -/
@[reducible] def Q3Leaf : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapP = none → (cv w).get? ``wrapQ = none → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``wrapP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (no CacheCoh) -/
@[reducible] def Q3Coh : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapP = none → (cv w).get? ``wrapQ = none → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ (fun _ : Std.HashMap Lean.Name Res => True) (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

/-- MUTATION (second callee not absent at the start) -/
@[reducible] def Q3NoAbs : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (_T : RefLawsATele O.quiet mref cref) (_hA : AdmCtx O.quiet mctx cctx),
    MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape →
    (∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape) →
    MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape →
    MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape →
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx ``wrapQ wrapQ.machineData.shape →
    ∀ {D : Nat}, D ≠ 0 → ∀ {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design} {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}, JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (cv w).get? ``wrapP = none → True → RunsTo (closeInstsGM topshareQ.machineData.shape t m₀ d₀) mctx mref cctx cref w r w' → ∃ (Y : List Res) (y y' : Res), Y[0]? = some y ∧ Y[1]? = some y' ∧
      (cv w').get? ``wrapP = some y ∧ (cv w').get? ``wrapQ = some y' ∧
      CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      ∃ e : Res, (cv w').get? ``leafP = some e ∧ e.1 ∈ y.2.modules ∧ e.1 ∈ y'.2.modules

end Tests.Compiler.SharedLeafMemKidEntryAuditTest

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let NT := `Tests.Compiler.SharedLeafMemKidEntryTest
  let NA := `Tests.Compiler.SharedLeafMemKidEntryAuditTest
  let pairs : List (Name × Name × List (Name × String)) :=
    [(NT ++ `topshareM_closes0, NA ++ `M0Full, [(NA ++ `M0Name, "parent name wrapM"), (NA ++ `M0NoI3, "interface premise of wrapM3 dropped"), (NA ++ `M0I3rc, "interface premise of wrapM3 about wrapM results"), (NA ++ `M0I3ns, "interface names without the memory module"), (NA ++ `M0C3, "closing premise of wrapM for wrapM3")]),
     (NT ++ `topshareM_machineRun, NA ++ `M1Full, [(NA ++ `M1D, "machine run at depth 0"), (NA ++ `M1W, "start world at depth 1"), (NA ++ `M1EP, "entry premise of wrapM"), (NA ++ `M1NoI1, "interface premise of wrapM dropped")]),
     (NT ++ `topshareM_entry_run, NA ++ `M2Full, [(NA ++ `M2Coh, "no CacheCoh"), (NA ++ `M2Rev, "callees in the other order"), (NA ++ `M2W, "start world at depth 1"), (NA ++ `M2NoI3, "interface premise of wrapM3 dropped")]),
     (NT ++ `topshareM_shared_leaf, NA ++ `M3Full, [(NA ++ `M3NoAbs, "second callee not absent at the start"), (NA ++ `M3Leaf, "the shared entry is wrapM"), (NA ++ `M3Coh, "no CacheCoh"), (NA ++ `M3Run, "closing of topshareQ")]),
     (NT ++ `topshareQ_closes0, NA ++ `Q0Full, [(NA ++ `Q0Name, "parent name wrapQ"), (NA ++ `Q0NoIQ, "interface premise of wrapQ dropped"), (NA ++ `Q0IQns, "interface names without the memory module"), (NA ++ `Q0NoC2, "closing premise of wrapQ dropped"), (NA ++ `Q0NoLeaf, "reflection of the plain leaf dropped")]),
     (NT ++ `topshareQ_machineRun, NA ++ `Q1Full, [(NA ++ `Q1D, "machine run at depth 0"), (NA ++ `Q1W, "start world at depth 1"), (NA ++ `Q1NoIQ, "interface premise of wrapQ dropped")]),
     (NT ++ `topshareQ_entry_run, NA ++ `Q2Full, [(NA ++ `Q2Coh, "no CacheCoh"), (NA ++ `Q2W, "start world at depth 1"), (NA ++ `Q2NoIQ, "interface premise of wrapQ dropped")]),
     (NT ++ `topshareQ_shared_leaf, NA ++ `Q3Full, [(NA ++ `Q3Leaf, "the shared entry is wrapP"), (NA ++ `Q3Coh, "no CacheCoh"), (NA ++ `Q3NoAbs, "second callee not absent at the start")])]
  for (thm, full, muts) in pairs do
    let gt ← instantiateMVars (← getConstInfo thm).type
    for (e, what) in [(gt, "the theorem's type"), (mkConst full, "the expected full type")] ++ muts.map fun (c, w) => (mkConst c, s!"mutation {w}") do
      if e.hasMVar || e.hasFVar then throwError "SRM2 AUDIT FAILED: metavariables / free variables in {what}"
      Meta.check e
    let pos ← withCurrHeartbeats (withTransparency .default (isDefEq gt (mkConst full)))
    unless pos do
      throwError "SRM2 AUDIT FAILED: the FULL type of {thm} is not definitionally the hand-written {full}"
    -- the mutations are checked at REDUCIBLE transparency (at default transparency the check unfolds `machineData` of the parent and exhausts the heartbeat budget)
    for (c, w) in muts do
      if (← withCurrHeartbeats (withReducible (isDefEq gt (mkConst c)))) then throwError "SRM2 AUDIT FAILED: the mutated full type of {thm} ({w}) was ACCEPTED"
    stdAxioms thm
    logInfo m!"SRM2 AUDIT: the full forall-type of {thm} is isDefEq (default transparency) to {full}; {muts.length} type-correct mutations are REJECTED (at reducible transparency); standard axioms only"

/-! ## closure audit -/

open Tests.Compiler.ChildVertAuditTest in
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let NT := `Tests.Compiler.SharedLeafMemKidEntryTest
  for thm in [NT ++ `topshareM_closes0, NT ++ `topshareM_machineRun, NT ++ `topshareM_entry_run, NT ++ `topshareM_shared_leaf,
      NT ++ `topshareQ_closes0, NT ++ `topshareQ_machineRun, NT ++ `topshareQ_entry_run, NT ++ `topshareQ_shared_leaf] do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM2 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM2 AUDIT FAILED: old boundary / CacheClosed in the closure of {thm}: {bad2}"
    let isEntry := (thm.toString.splitOn "closes0").length > 1 || (thm.toString.splitOn "machineRun").length > 1 || (thm.toString.splitOn "entry_run").length > 1
    let must : List Name := [``Tools.ShippingNmGroup.nm_group, ``Tools.ShippingNmGroup.nm_loop, ``Tools.ShippingNmGroup.nm_closing,
      ``Tools.ShippingMemLeafRun.synthesizeChild_miss_nm, ``Tools.ShippingMemLeafCache.cacheCoh_of_nm, ``Tools.ShippingMemLeafCache.MemDet,
      ``Tools.ShippingLeafMissCoh.CacheClosedNM] ++
      (if isEntry then [``Tools.ShippingNmEntry.nm_machineSynth_ne_none, ``Tools.ShippingNmEntry.nm_closes0] else []) ++
      (if (thm.toString.splitOn "entry_run").length > 1 then [``Tools.ShippingNmEntry.nm_entry_run_ret_np, ``Tools.ShippingNmEntry.noParent_nm] else [])
    for m in must do
      unless cl.contains m do throwError "SRM2 AUDIT FAILED: {m} not in the closure of {thm}"
    logInfo m!"SRM2 CLOSURE AUDIT: {thm}: standard axioms; closure {cl.size} constants; no old RefLaws boundary, no `CacheClosed`, no ChildBnd / GenKid / KidFacts; the NM lemmas are in it"

end
