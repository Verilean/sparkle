import Tests.Compiler.CDefTest
import Tests.Compiler.Srm4ParentTest
import Tests.Compiler.SharedLeafMemKidIfaceTest
-- C4 G-CLOSES / G-RAN / G-RUN (issue sparkle-gen-c4-gcloses): generic over `P : MemSharedLeafParent` (AMENDMENT 3 + 4).
-- Binders are the C4 contract binders only (O T hA entryL entryW entry hw hcore). No new premise, no sorry / axiom / native_decide.
set_option Elab.async false
-- Closure audit added by the integrator before review (walks every Tests.* constant reached from the four generic theorems).
set_option autoImplicit false
namespace Tests.Compiler.C4Closes
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine
open Tests.Compiler.CDef Tools.ShippingMachineSource Tools.ShippingTopShareRun Tests.Compiler.Srm9ComposedTest
open Tools.ShippingMemLeafRun Tools.ShippingNmGroup Tools.ShippingNmEntry
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingMemCloses
open Tools.ShippingQuadComposed (genTrace)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- `ChildIfaceP` of a `RealChildA` of the class's leaf (generalises `leafM_ifaceP`). -/
theorem leaf_ifaceP_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) {y : Res} (h : RealChildA O P.leaf.decl y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl P.leaf.decl) (machNIn P.leaf.d.shape)
      (P.leaf.d.shape.layout.outs.map (·.name)) P.lNames y.1 y.2 :=
  memCallee_ifaceP O T P.leafMem (fun _ _ _ k hk y hn _ => by
    have := P.leafAllMem k hk
    rw [hn] at this
    exact absurd this (by decide)) entryL h

/-- `ChildIfaceP` of a `RealChildA` of a wrapper (generalises `wrapM_ifaceP`). -/
theorem wrapper_ifaceP_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers)
    (entry : MachineDefines mctx mref cctx cref w.decl w.d.shape) {y : Res} (h : RealChildA O w.decl y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl w.decl) (machNIn w.d.shape)
      (w.d.shape.layout.outs.map (·.name)) (Sparkle.IR.ModuleName.ofDecl P.leaf.decl :: P.lNames) y.1 y.2 :=
  memCallee_ifaceP O T (P.wMem w hw) (fun m' c' _ k hk y _ hre => by
    rw [(P.wKids w hw k hk).1] at hre
    exact leaf_ifaceP_of_class P (mctx := m') (cctx := c') O T (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre) entry h

/-- `MachineClosesAtA` of a wrapper (generalises `wrapM_closesA`). -/
theorem wrapper_closesA_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx w.decl w.d.shape :=
  memCallee_closesA O T hA (P.wMem w hw) (fun k hk y _ hre => by
    rw [(P.wKids w hw k hk).1] at hre
    exact leaf_ifaceP_of_class P O T entryL hre)

/-- the leaf's step contract (generalises `leafM_step`) -/
theorem leaf_step_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) :
    ∀ D, D ≠ 0 → StepNM (mref := mref) (cref := cref) O mctx cctx D P.leaf.decl (P.leaf.d.shape.insts.map (·.1)) :=
  memLeaf_stepNM O T hA P.leafMemOnly P.leafCloseData P.leafCne entryL

/-- `CalleeNM` of a wrapper (generalises `wrapM_calleeNM`). -/
theorem wrapper_calleeNM_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers)
    (entry : MachineDefines mctx mref cctx cref w.decl w.d.shape) :
    CalleeNM O mctx cctx (⟨w.decl, w.d, P.leaf.d.shape.insts.map (·.1), Sparkle.IR.ModuleName.ofDecl P.leaf.decl :: P.lNames⟩ : NCal) :=
  ⟨(P.wMem w hw).ok, (P.wMem w hw).body, ⟨P.nDecl, (P.wMem w hw).callsOk, (P.wMem w hw).domB⟩, (P.wMem w hw).slots,
    (P.wMem w hw).insts_ne, (P.wMem w hw).fne,
    fun D' hD' x hx => Or.inr ⟨(P.wTags w hw x hx).1, by
      have e := (P.wTags w hw x hx).2
      rw [e]
      exact leaf_step_of_class P O T hA entryL D' hD'⟩,
    fun k hk => Tools.ShippingInstTagged.agree_at (P.wAgree w hw) hk, P.wCne w hw, P.wNotin w hw, entry,
    wrapper_closesA_of_class P O T hA entryL hw⟩

theorem callees_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) :
    NmCallees O mctx cctx P.top.decl P.cs :=
  ⟨fun e he => by
    rw [P.tieCs] at he
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
    exact wrapper_calleeNM_of_class P O T hA entryL hw (entryW w hw), P.csNc, P.csCd⟩

theorem iface_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) :
    CalleeIface O P.cs := by
  intro e he y hy
  rw [P.tieCs] at he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
  exact wrapper_ifaceP_of_class P O T entryL hw (entryW w hw) hy

/-- **G-CLOSES**: `MachineClosesAtStart0` of the class's top, from the class fields and the contract binders only. -/
theorem closes0_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx P.top.decl P.top.d.shape :=
  nm_closes0 O hA P.pdata (callees_of_class P O T hA entryL entryW) (iface_of_class P O T entryL entryW)

/-- **G-RAN** -/
theorem ranA_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (raw, D) w1) (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx P.top.decl P.top.d.shape raw D :=
  Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry (closes0_of_class P O T hA entryL entryW) hw

/-- **G-RUN** -/
theorem machineRun_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 P.top.decl P.top.d.shape m design :=
  nm_machineRun O hA P.pdata (callees_of_class P O T hA entryL entryW) (iface_of_class P O T entryL entryW) entry hw hcore

/-- **soundLA for the class** -/
theorem soundLA_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape)
    (entry : MachineDefines mctx mref cctx cref P.top.decl P.top.d.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore P.top.decl [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineAuto.MachineTraceLB P.top.decl P.top.d m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      P.top.src P.top.extS P.top.extBS P.top.lsrc := by
  letI := P.top.inh
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    genTrace O T hA P.top.d (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) P.top.gen (D₀ := 0)
      (machineRun_of_class P O T hA entryL entryW entry hw hcore)
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

/-! ## corollaries for `P_M` (statements of the `topshareM_*` theorems) -/
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidEntryTest

theorem topshareM_closes0_of_class (hgrp : TmGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx ``topshareM topshareM.machineData.shape :=
  closes0_of_class (P_M hgrp) O T hA entryL (by
    intro wp hwp
    simp only [P_M, List.mem_cons, List.not_mem_nil, or_false] at hwp
    rcases hwp with rfl | rfl
    · exact entry₁
    · exact entry₂)

theorem topshareM_machineRun_of_class (hgrp : TmGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 ``topshareM topshareM.machineData.shape m design :=
  machineRun_of_class (P_M hgrp) O T hA entryL (by
    intro wp hwp
    simp only [P_M, List.mem_cons, List.not_mem_nil, or_false] at hwp
    rcases hwp with rfl | rfl
    · exact entry₁
    · exact entry₂) entryP hw hcore

theorem topshareM_ranA_of_class (hgrp : TmGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1) (hw : JQC O 0 w) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx ``topshareM topshareM.machineData.shape raw D :=
  ranA_of_class (P_M hgrp) O T hA entryL (by
    intro wp hwp
    simp only [P_M, List.mem_cons, List.not_mem_nil, or_false] at hwp
    rcases hwp with rfl | rfl
    · exact entry₁
    · exact entry₂) entry hcore hw

theorem topshareM_soundLA_of_class (hgrp : TmGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entryP : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingMachineAuto.MachineTraceLB ``topshareM topshareM.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineSource
      (fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshareM.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineInits
        topshareM.machineBody topshareM.machineExt topshareM.machineExtB) :=
  soundLA_of_class (P_M hgrp) O T hA entryL (by
    intro wp hwp
    simp only [P_M, List.mem_cons, List.not_mem_nil, or_false] at hwp
    rcases hwp with rfl | rfl
    · exact entry₁
    · exact entry₂) entryP hw hcore


/-! ## isDefEq type audit: each corollary's type (hgrp binder dropped) is defeq to the original `topshareM_*` statement -/
open Lean Meta in
#eval show MetaM Unit from do
  let pairs : List (Name × Name) :=
    [(``topshareM_closes0_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_closes0_derived),
     (``topshareM_machineRun_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_machineRun_derived),
     (``topshareM_ranA_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_ranA),
     (``topshareM_soundLA_of_class, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_soundLA)]
  for (n, o) in pairs do
    let ci ← getConstInfo n
    let oi ← getConstInfo o
    let ok ← forallTelescope ci.type fun xs body => do
      let mut keep := #[]
      for x in xs do
        let t ← inferType x
        unless t.isConstOf ``Tests.Compiler.Srm9ComposedTest.TmGrp || (← whnfR t).isAppOf ``Tools.ShippingQuadComposed.QuadGroupFacts do
          keep := keep.push x
      isDefEq (← mkForallFVars keep body) oi.type
    unless ok do throwError "C4 AUDIT FAILED: {n} vs {o}"
  logInfo m!"C4|ok|4 corollary types defeq to topshareM_* statements"

/-! ## closure audit: the generic theorems reach only the class definition and this file's generic helpers -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``closes0_of_class, ``ranA_of_class, ``machineRun_of_class, ``soundLA_of_class]
  let generic := [``leaf_ifaceP_of_class, ``wrapper_ifaceP_of_class, ``wrapper_closesA_of_class, ``leaf_step_of_class,
    ``wrapper_calleeNM_of_class, ``callees_of_class, ``iface_of_class] ++ roots
  for r in roots do
    let mut seen : NameSet := {}
    let mut work : List Name := [r]
    let mut reached : Array Name := #[]
    while !work.isEmpty do
      let n := work.head!
      work := work.tail!
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throwError "C4CLOSES CLOSURE FAILED: {n} not found"
      -- bodies read from thmInfo / defnInfo (`value?` does not return theorem bodies here)
      let body? : Option Lean.Expr := match ci with
        | .thmInfo t => some t.value
        | .defnInfo v => some v.value
        | .opaqueInfo v => some v.value
        | _ => none
      let cs := ci.type.getUsedConstants ++ (body?.map Lean.Expr.getUsedConstants).getD #[]
      for c in cs do
        if (c.toString.splitOn "Tests.").length > 1 && !seen.contains c then
          reached := reached.push c
          work := c :: work
    for c in reached do
      let cdef := (c.toString.splitOn "Tests.Compiler.CDef.").length > 1
      let own := (c.toString.splitOn "Tests.Compiler.C4Closes.").length > 1
      unless cdef || own do throwError "C4CLOSES CLOSURE FAILED: {r} reaches {c} (outside the class definition and this file)"
      if own then
        unless generic.any (fun g => (c.toString.splitOn g.toString).length > 1) do
          throwError "C4CLOSES CLOSURE FAILED: {r} reaches the non-generic own constant {c}"
      for comp in c.components.map (·.toString) do
        if ["P_M", "P_Q", "TmGrp", "wrapM", "wrapM3", "leafM", "leafP", "wrapP", "wrapQ", "csM"].contains comp
            || comp.startsWith "topshare" then
          throwError "C4CLOSES CLOSURE FAILED: {r} reaches {c} (instance component {comp})"
    logInfo m!"C4CLOSES|closure ok|{r}: {reached.size} Tests constants, all class / generic-helper constants"

end Tests.Compiler.C4Closes

open Tests.Compiler.C4Closes in
#print axioms closes0_of_class
open Tests.Compiler.C4Closes in
#print axioms ranA_of_class
open Tests.Compiler.C4Closes in
#print axioms machineRun_of_class
open Tests.Compiler.C4Closes in
#print axioms soundLA_of_class
open Tests.Compiler.C4Closes in
#print axioms topshareM_closes0_of_class
open Tests.Compiler.C4Closes in
#print axioms topshareM_machineRun_of_class
open Tests.Compiler.C4Closes in
#print axioms topshareM_ranA_of_class
open Tests.Compiler.C4Closes in
#print axioms topshareM_soundLA_of_class
