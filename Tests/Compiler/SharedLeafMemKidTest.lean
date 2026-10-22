import Tests.Compiler.MemDepthProbeTest
import Tests.Compiler.SharedLeafGenTopshareTest
import Tools.ShippingQuadLeafGeneric
import Tools.ShippingQuadComposed
import Tests.Compiler.KaryThreeTest
-- BUILT (unit SRM1): s7 exit 0 (dev run; log-only probes, no theorem is claimed beyond the decided data equations); final-SHA rebuild in REPORT-SRM1.md.
-- SCOPE (SRM1, step 1 = EVIDENCE): the smallest shared-leaf example whose SHARED LEAF has a MEMORY child: `topshareM` calls the callees `wrapM` and `wrapM3`, both call the SAME leaf
-- `leafM`, whose one call is the synchronous 4/8 memory (`Signal.memory`, an instance of the memory-only submodule).  The existing machine-route commands are run on it as LOG-ONLY steps
-- (`#mem_depth_try`), and the existing data classes (`LeafData`, `LeafKidData`, `LeafCalleeData`, `QuadParentData`-style) are evaluated FIELD BY FIELD to record which one fails first.
-- Not a statement about an endpoint; an example does not make a class complete.
set_option Elab.async false
section
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
namespace Tests.Compiler.SharedLeafMemKidTest
open Tests.Compiler.MemDepthProbeTest

structure MOut (dom : DomainConfig) where
  s : Signal dom (BitVec 8)
  odd : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (MOut dom) dom := ⟨⟩

/-- the shared leaf: a register and ONE synchronous memory (read address = the argument's low bits) -/
@[hardware_module] def leafM {dom : DomainConfig} (we : Signal dom Bool) (wa : Signal dom (BitVec 4))
    (wd : Signal dom (BitVec 8)) : MOut dom :=
  circuit do
    let a ← Signal.reg 0#8
    let as := (a : Signal dom (BitVec 8))
    let rd := Signal.memory wa wd we wa
    a <~ as + rd
    return ({ s := as, odd := as === (Signal.pure 5#8 : Signal dom (BitVec 8)) } : MOut dom)

@[hardware_module] def wrapM {dom : DomainConfig} (we : Signal dom Bool) (wa : Signal dom (BitVec 4))
    (wd : Signal dom (BitVec 8)) : MOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := leafM we wa wd
    r <~ a.s + wd
    return ({ s := rs, odd := a.odd } : MOut dom)

@[hardware_module] def wrapM3 {dom : DomainConfig} (we : Signal dom Bool) (wa : Signal dom (BitVec 4))
    (wd : Signal dom (BitVec 8)) : MOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := leafM we wa wd
    r <~ a.s + wd + wd
    return ({ s := rs, odd := a.odd } : MOut dom)

def topshareM (en : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4)) (v w : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrapM en wa v
    let m2 := wrapM3 en wa w
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint leafM
#machine_endpoint wrapM
#machine_endpoint wrapM3
#machine_endpoint topshareM

/-- the call structure is ASSERTED by kernel-checked equations (the leaf's one entry is the memory placeholder) -/
theorem topshareM_callees : topshareM.machineData.shape.insts.map (·.1) = [``wrapM, ``wrapM, ``wrapM3, ``wrapM3] := by decide
theorem wrapM_leaf : wrapM.machineData.shape.insts.map (·.1) = [``leafM, ``leafM] := by decide
theorem wrapM3_leaf : wrapM3.machineData.shape.insts.map (·.1) = [``leafM, ``leafM] := by decide
theorem leafM_mem : leafM.machineData.shape.insts.map (·.1) = [Sparkle.Compiler.MachMemory.memChildName false 4 8] := by decide

/-! ## data of the leaf (decided) -/
theorem leafM_insts_ne : leafM.machineData.shape.insts ≠ [] := by decide
theorem leafM_fne : leafM.machineData.shape.instFields ≠ [] := by decide
theorem leafM_slotsNe : leafM.machineData.shape.layout.slots ≠ [] := by decide
/-- `LeafData.insts` is FALSE for the memory leaf -/
theorem leafM_not_leafData : ¬ (leafM.machineData.shape.insts = []) := leafM_insts_ne

/-! ## the existing machine-route commands (LOG ONLY) -/
#mem_depth_try "M0 #machine_composedTS leafM" in
  #machine_composedTS Tests.Compiler.SharedLeafMemKidTest.leafM
#mem_depth_try "M0b #machine_ships_hier leafM (after composedTS)" in
  #machine_ships_hier Tests.Compiler.SharedLeafMemKidTest.leafM
#mem_depth_try "M0c #machine_closes_at leafM" in
  #machine_closes_at Tests.Compiler.SharedLeafMemKidTest.leafM
#mem_depth_try "M1 #machine_composedT leafM" in
  #machine_composedT Tests.Compiler.SharedLeafMemKidTest.leafM
#mem_depth_try "M2 #machine_ships_hier leafM" in
  #machine_ships_hier Tests.Compiler.SharedLeafMemKidTest.leafM
#mem_depth_try "M3 #machine_design_svR0 leafM" in
  #machine_design_svR0 Tests.Compiler.SharedLeafMemKidTest.leafM
#mem_depth_try "M4 #machine_no_ports_mem leafM" in
  #machine_no_ports_mem Tests.Compiler.SharedLeafMemKidTest.leafM
#mem_depth_try "M5 #machine_closes_at wrapM" in
  #machine_closes_at Tests.Compiler.SharedLeafMemKidTest.wrapM
#mem_depth_try "M6 #machine_no_ports_kids wrapM 1" in
  #machine_no_ports_kids Tests.Compiler.SharedLeafMemKidTest.wrapM 1
#mem_depth_try "M7 #machine_design_svNR topshareM 2" in
  #machine_design_svNR Tests.Compiler.SharedLeafMemKidTest.topshareM 2
#mem_depth_try "M8 #machine_seq_parent_endpoint topshareM (shared-leaf candidate on)" in
  set_option sparkle.sharedLeafCandidate true in
  #machine_seq_parent_endpoint Tests.Compiler.SharedLeafMemKidTest.topshareM


/-! ## the data classes of the K-ary / QUAD chain, field by field (the goals that `decide` does NOT close are reported) -/
open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadComposed in
#mem_depth_try "F1 LeafData leafM (leaf WITH memory child)" in
  example : LeafData leafM.machineData := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> try first | exact leafM.machine_ok | exact leafM.machine_body | decide | decide +kernel
    run_tac show Lean.Elab.Tactic.TacticM Unit from do
      let gs ← Lean.Elab.Tactic.getGoals
      throwError "FIELDS NOT CLOSED: {← gs.mapM fun g => do ppExpr (← g.getType)}"

open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadComposed in
#mem_depth_try "F2 LeafKidData leafM (callsOk at nIn, as the class states it)" in
  example : LeafKidData leafM.machineData := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try first | decide | decide +kernel
    run_tac show Lean.Elab.Tactic.TacticM Unit from do
      let gs ← Lean.Elab.Tactic.getGoals
      throwError "FIELDS NOT CLOSED: {← gs.mapM fun g => do ppExpr (← g.getType)}"

open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadComposed in
#mem_depth_try "F3 LeafCalleeData wrapM leafM (callee of the memory leaf)" in
  example : LeafCalleeData wrapM.machineData leafM.machineData ``wrapM ``leafM 4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      try first | exact wrapM.machine_ok | exact wrapM.machine_body | decide | decide +kernel
    run_tac show Lean.Elab.Tactic.TacticM Unit from do
      let gs ← Lean.Elab.Tactic.getGoals
      throwError "FIELDS NOT CLOSED: {← gs.mapM fun g => do ppExpr (← g.getType)}"

/-! ## variant B: the leaf has NO memory, one CALLEE has a memory child next to its leaf call -/

@[hardware_module] def leafP {dom : DomainConfig} (x : Signal dom (BitVec 8)) : MOut dom :=
  circuit do
    let a ← Signal.reg 0#8
    let as := (a : Signal dom (BitVec 8))
    a <~ as + x
    return ({ s := as, odd := as === (Signal.pure 5#8 : Signal dom (BitVec 8)) } : MOut dom)

@[hardware_module] def wrapP {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : MOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := leafP x
    r <~ a.s + y
    return ({ s := rs, odd := a.odd } : MOut dom)

/-- a callee with a memory child NEXT TO its call of the leaf -/
@[hardware_module] def wrapQ {dom : DomainConfig} (we : Signal dom Bool) (wa : Signal dom (BitVec 4))
    (x y : Signal dom (BitVec 8)) : MOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let a := leafP x
    let rd := Signal.memory wa y we wa
    r <~ a.s + rd
    return ({ s := rs, odd := a.odd } : MOut dom)

def topshareQ (en : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4)) (v w : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := wrapP v w
    let m2 := wrapQ en wa w v
    r <~ Signal.mux (m.odd &&& m2.odd &&& en) (rs + v) rs
    return rs

#machine_endpoint leafP
#machine_endpoint wrapP
#machine_endpoint wrapQ
#machine_endpoint topshareQ

theorem topshareQ_callees : topshareQ.machineData.shape.insts.map (·.1) = [``wrapP, ``wrapP, ``wrapQ, ``wrapQ] := by decide
theorem wrapQ_kids : wrapQ.machineData.shape.insts.map (·.1) = [``leafP, ``leafP, Sparkle.Compiler.MachMemory.memChildName false 4 8] := by decide

open Tools.ShippingQuadLeafGeneric Tools.ShippingQuadComposed in
#mem_depth_try "G1 LeafCalleeData wrapQ leafP (callee WITH a memory child)" in
  example : LeafCalleeData wrapQ.machineData leafP.machineData ``wrapQ ``leafP 5 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      try first | exact wrapQ.machine_ok | exact wrapQ.machine_body | decide | decide +kernel
    run_tac show Lean.Elab.Tactic.TacticM Unit from do
      let gs ← Lean.Elab.Tactic.getGoals
      throwError "FIELDS NOT CLOSED: {← gs.mapM fun g => do ppExpr (← g.getType)}"
#mem_depth_try "G2 #machine_closes_at wrapQ" in
  #machine_closes_at Tests.Compiler.SharedLeafMemKidTest.wrapQ
#mem_depth_try "G3 #machine_design_svNR topshareQ 2" in
  #machine_design_svNR Tests.Compiler.SharedLeafMemKidTest.topshareQ 2
#mem_depth_try "G4 #machine_seq_parent_endpoint topshareQ (shared-leaf candidate on)" in
  set_option sparkle.sharedLeafCandidate true in
  #machine_seq_parent_endpoint Tests.Compiler.SharedLeafMemKidTest.topshareQ


-- `callsOk n` for `n = 0..7`, to read the right `n` of each machine (read: leafM true at 4 only, wrapM at 4, wrapQ at 5; nIn = 5, 6, 8)
#reduce ((List.range 8).map fun n => (n, leafM.machineData.callsOk n, wrapM.machineData.callsOk n, wrapQ.machineData.callsOk n))
#reduce (leafM.machineData.nIn, wrapM.machineData.nIn, wrapQ.machineData.nIn, leafP.machineData.nIn, wrapP.machineData.nIn)

end Tests.Compiler.SharedLeafMemKidTest
end
