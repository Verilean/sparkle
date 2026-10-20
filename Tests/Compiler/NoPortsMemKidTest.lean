import Lean.Elab.Command
import Sparkle
import Tools.ShippingMachineCommand
import Tools.ShippingMachineMemCommand
import Tools.ShippingMachineShipsHierCommand
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingMachineSeqCommandR
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingNoPortsMemCommand
import Tools.ShippingMachineLoopCausalCommand
import Tools.ShippingMachineDepthMemKidCommand
import Tools.ShippingMachineDepthMemKidRunCommand
import Tools.ShippingBndOnly
import Tools.ShippingNoPortsMemKidCommand
import Tools.ShippingNoPortsMemKidSweep
import Tools.ShippingLeafSweepCommand

/-! # `#machine_no_ports_memkid`: a parent of memory machines, check-free at the design level, GENERATED (round par/e-1)

WRITTEN, NOT BUILT. ASSERTING, and written to be suitable for
`Tests/AllTests.lean`: every declaration below is this file's own (no import
of the never-failing probe `Tests/Compiler/MemDepthProbeTest.lean`, none of
`Tests/Compiler/ShippingMachineSeqTest.lean`), so every generated constant is
under a name of this file's namespace.

## The declarations

* `kcnt` — a leaf register machine with a structure result (`cnt` of
  `ShippingMachineSeqTest` 20, copied): the callee that puts a parent under
  the GENERAL closing;
* `mkH` — a memory machine: two registers and a combinational-read memory,
  address width 4, data width 8 (`memCounterH` of the probe, copied);
* `mkW` — the same with address width 5 (another memory module:
  `ofMem true 5 8`);
* `mkParent` — a register parent of `kcnt` and `mkH` (`memParent` of the
  probe, copied): call entries `[kcnt, kcnt, mkH]` (ASSUMED BY READING, as
  for `memParent`; the generator reads them, nothing here is indexed by
  hand);
* `mkParent2` — a register parent of `kcnt`, `mkH` AND `mkW`: two different
  memory-machine callees over two different memory modules; call entries
  `[kcnt, kcnt, mkH, mkW]` by the analogy with `memParent` (a structure call
  is one entry per field of the structure — NOT measured for this
  declaration; the generator reads the entries and does not depend on the
  guess). It shows that the generator is not specialised to one declaration:
  another entry table, two tagged entries, the sibling separation decided on
  two different tags;
* `mkGrand` — a parent of `mkParent` and of `kcnt` (`memGrand`, copied): NO
  command is run on it; it is swept only, to be REFUSED from its source
  shape (`kcnt` is a callee and a descendant of the callee `mkParent`).

## What is asserted

1. the command chains (errors of the file where one fails);
2. `#machine_no_ports_memkid mkParent`: the generator, its statement check
   (the census's `recheck`, 4 proposition binders, 1 antecedent) and its
   axiom audit — an error otherwise;
3. the generated closed statement against a HAND statement written as in
   `Tests/Compiler/MemParentFreeTest.lean` (`#noports_open_as` of the built
   `endpointTermX`, then `bnd_only%`, proved by the hand file's `refine` —
   which spells the boundary's shape out, independently of the generator's
   `memkid_boundary`): `Meta.isDefEq` of the two statements, and the
   GENERATED proof accepted by the KERNEL at the HAND statement
   (`addTheorem`; the constant is then removed);
4. the sweep of `mkParent2`, `mkParent`, `mkH`, `mkGrand` with the PREDICTED
   classes (`docs/parallel/E-memkid-generator.md`; the integrator corrects
   them from the measurement): GENERATED, REBUILT, REFUSED ("a memory entry
   of"), REFUSED ("is also a descendant of the callee").

SCOPE of each generated endpoint: ONE declaration, depth 1, data conditions
decided per declaration, the runtime boundary a premise, `DesignSV` of the
module list — not the SV string, not `#sim`. -/
namespace Sparkle.Tests.Compiler.NoPortsMemKidTest

section Leaf
open Sparkle.Core.Domain Sparkle.Core.Signal

structure KOut (dom : DomainConfig) where
  n : Signal dom (BitVec 8)
  hit : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (KOut dom) dom := ⟨⟩

/-- A counter with two outputs: a leaf sequential child. -/
@[hardware_module] def kcnt {dom : DomainConfig} (en : Signal dom Bool) : KOut dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 1#8 : Signal dom (BitVec 8))) cs
    return ({ n := cs, hit := cs === (Signal.pure 7#8 : Signal dom (BitVec 8)) } : KOut dom)

end Leaf

section Machines
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

/-- A write port from the inputs, a read at a counter: a machine with two
registers and one memory (address width 4, data width 8), as a hardware
module. -/
@[hardware_module]
def mkH (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 4 × BitVec 8)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead wa wd we addr
    bundle2 (Signal.register 0#4 (addr + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))))
      (Signal.register 0#8 rd)
  Signal.snd st

/-- The same with address width 5: another memory module. -/
@[hardware_module]
def mkW (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 5))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 5 × BitVec 8)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead wa wd we addr
    bundle2 (Signal.register 0#5 (addr + (Signal.pure 1#5 : Signal defaultDomain (BitVec 5))))
      (Signal.register 0#8 rd)
  Signal.snd st

/-- A register parent of the memory machine and of the structure-result leaf
(the general closing). -/
@[hardware_module]
def mkParent (en we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let k := kcnt en
    let y := mkH we wa wd
    acc <~ Signal.mux k.hit y accS
    return accS

/-- A register parent of TWO different memory machines (two different memory
modules) and of the structure-result leaf. -/
def mkParent2 (en we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wb : Signal defaultDomain (BitVec 5)) (wd : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let k := kcnt en
    let y := mkH we wa wd
    let z := mkW we wb wd
    acc <~ Signal.mux k.hit (y + z) accS
    return accS

/-- Two levels: a register parent of `mkParent` and of `kcnt` (swept only:
refused from its source shape). -/
def mkGrand (en we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal defaultDomain (BitVec 8))
    let k := kcnt en
    let y := mkParent en we wa wd
    acc <~ Signal.mux k.hit y accS
    return accS

end Machines

end Sparkle.Tests.Compiler.NoPortsMemKidTest

/-! ## The memory machines as entries, and as sequential children at depth 0

The order measured on the probe (`docs/parallel/C-mem-depth-ships.md`, build
records): the entry chain (C1, C2, C3, C5), the joint causality (J1), the
composed theorem and the run theorem of the memory-only kid (K1, K2). -/

#machine_endpoint Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH
#machine_composedT Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH
#machine_ships_hier Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH
#machine_no_ports_mem Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH
#machine_ext_joint Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH
#machine_composed_memNR Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH 0
#machine_seq_child_memNR Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH 0

#machine_endpoint Sparkle.Tests.Compiler.NoPortsMemKidTest.mkW
#machine_composedT Sparkle.Tests.Compiler.NoPortsMemKidTest.mkW
#machine_ships_hier Sparkle.Tests.Compiler.NoPortsMemKidTest.mkW
#machine_no_ports_mem Sparkle.Tests.Compiler.NoPortsMemKidTest.mkW
#machine_ext_joint Sparkle.Tests.Compiler.NoPortsMemKidTest.mkW
#machine_composed_memNR Sparkle.Tests.Compiler.NoPortsMemKidTest.mkW 0
#machine_seq_child_memNR Sparkle.Tests.Compiler.NoPortsMemKidTest.mkW 0

/-! ## `mkParent`: the depth endpoint, then the generator (asserting) -/

#machine_endpoint Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent
#machine_depth_core Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent 1
#machine_depth_ships Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent 1
#machine_design_svNR Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent 1

set_option maxHeartbeats 0 in
#machine_no_ports_memkid Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent

/-! ## The generated closed statement against a hand statement

As `Tests/Compiler/MemParentFreeTest.lean` 402-426: the open endpoint by the
BUILT `endpointTermX` (`#noports_open_as`) under a name of this test, its
closed statement by `bnd_only%`, proved by the hand file's `refine` — the
boundary of the depth endpoint spelled out,

    ChildBnd mref cref w ∧ MachineDefines … kcnt … ∧
      (MachineDefines … mkH … ∧
        ∀ mctx' cctx', ChildRanIn mref cref mkH mctx' cctx' →
          MachineClosesAt mctx' mref cctx' cref mkH … ∧
            ∀ wc raw D, ChildBnd mref cref wc → ChildBnd mref cref wc)

— not by the generator's `memkid_boundary`. The four run theorems and the
closing of `mkParent` are the generated ones. -/
namespace Tests.Compiler.NoPortsMemKidTest
open Sparkle.Tests.Compiler.NoPortsMemKidTest

#noports_open_as mkParent_open_hand := mkParent 1 mkParent.machine_runFactsT1
  mkParent.machine_outsGT1 mkParent.machine_maskedGT1 mkParent.machine_designPT1 [ ]

set_option maxHeartbeats 4000000 in
/-- The hand statement (`bnd_only%` of the hand-named open endpoint) and the
hand proof of `MemParentFreeTest`, at this file's declarations. -/
theorem mkParent_closed_hand : bnd_only% mkParent_open_hand [kcnt, mkH] := by
  intro mctx mref cctx cref w w' b design hr hP hRc hRm
  obtain ⟨raw, D, hpost, h⟩ :=
    mkParent_open_hand hr hP (mkParent.machine_closes_at_memkid hRc hRm)
  refine ⟨raw, D, hpost, fun hB => h ⟨hB, ?_, hRm, fun _ _ _ =>
    ⟨mkH.noPortsMem_closes, fun _ _ _ hb => hb⟩⟩⟩
  first
    | exact hRc
    | exact ⟨hRc, fun mc cc _ => kcnt.machine_closes mc _ cc _⟩

end Tests.Compiler.NoPortsMemKidTest

-- the comparison: `Meta.isDefEq` of the two statements, then the GENERATED
-- proof at the HAND statement through the kernel (standard axioms); the
-- constant is removed again
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent
  let gen := f ++ `machine_design_noPortsNR1_closed
  let hand := ``Tests.Compiler.NoPortsMemKidTest.mkParent_closed_hand
  let atHand := hand ++ `by_the_generated_proof
  let env0 ← Lean.getEnv
  let genTy ← match env0.find? gen with
    | some (Lean.ConstantInfo.thmInfo ti) => pure ti.type
    | _ => throwError "{gen}: not a theorem (#machine_no_ports_memkid did not add it)"
  let handTy ← match env0.find? hand with
    | some (Lean.ConstantInfo.thmInfo ti) => pure ti.type
    | _ => throwError "{hand}: not a theorem"
  if env0.contains atHand then throwError "{atHand}: exists already"
  let sameTerm : Bool := genTy == handTy
  let defEq ← Lean.Meta.isDefEq genTy handTy
  unless defEq do
    throwError "MEMKID COMPARE: the generated statement of {gen} is NOT isDefEq the hand statement of {hand}. Generated:{Lean.indentExpr genTy}\nhand:{Lean.indentExpr handTy}"
  Lean.withOptions (fun o => Lean.Elab.async.set o false) <|
    Tools.ShippingMachineLinkedCommand.addTheorem atHand handTy (Lean.mkConst gen)
  Lean.setEnv env0
  Lean.logInfo m!"MEMKID COMPARE: the statement of {gen} isDefEq the hand statement of {hand} (the same term: {sameTerm}); the generated proof was accepted by the kernel AT the hand statement, standard axioms (as {atHand}, then removed: no constant is kept)"

-- the census's own re-check on the generated statement (an error unless it
-- passes), and the axioms
#assert_check_free Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent.machine_design_noPortsNR1_closed

#print axioms Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH.kid_factsT
#print axioms Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent.machine_closes_at_memkid
#print axioms Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent.machine_design_noPortsNR1_closed

/-! ## `mkParent2`: two different memory-machine callees — the depth endpoint, then the sweep -/

#machine_endpoint Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent2
#machine_depth_core Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent2 1
#machine_depth_ships Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent2 1
#machine_design_svNR Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent2 1

set_option maxHeartbeats 0 in
#machine_no_ports_memkid_sweep Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent2

-- `mkParent` again: its endpoint exists — the compare path (REBUILT)
set_option maxHeartbeats 0 in
#machine_no_ports_memkid_sweep Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent

-- a memory-only parent: a memory entry of its own
set_option maxHeartbeats 0 in
#machine_no_ports_memkid_sweep Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH

-- a callee that is also a descendant of another callee
set_option maxHeartbeats 0 in
#machine_no_ports_memkid_sweep Sparkle.Tests.Compiler.NoPortsMemKidTest.mkGrand

#machine_no_ports_memkid_summary

/-! ## The classes, asserted (PREDICTED by reading — WRITTEN, NOT BUILT)

The integrator corrects these lines from the measurement
(`docs/parallel/E-memkid-generator.md`, the build record). -/

#machine_no_ports_memkid_expect Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent2 "GENERATED"
#machine_no_ports_memkid_expect Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent "REBUILT"
#machine_no_ports_memkid_expect Sparkle.Tests.Compiler.NoPortsMemKidTest.mkH "REFUSED"
  "a memory entry of"
#machine_no_ports_memkid_expect Sparkle.Tests.Compiler.NoPortsMemKidTest.mkGrand "REFUSED"
  "is also a descendant of the callee"

#assert_check_free Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent2.machine_design_noPortsNR1_closed
#print axioms Sparkle.Tests.Compiler.NoPortsMemKidTest.mkParent2.machine_design_noPortsNR1_closed

/-! ## `kcnt` as an entry: LOG ONLY (for the census)

`#leaf_sweep` (BUILT, `Tools/ShippingLeafSweepCommand.lean`) is an error in
NO case and nothing of its outcome is asserted here. `kcnt` gets
`kcnt.machineData` as a child of `mkParent`; without a design-level endpoint
of its own it is one more `OPEN register-leaf` row of `#design_coverage`
once this file is in `Tests.AllTests`. If the line below logs
`LEAFSWEEP RESULT … GENERATED`, `kcnt.machine_design_leaf0` exists and the
row is `COVERED`; if it logs REFUSED / FAILED, the reason names what the
leaf chain of `kcnt` lacks. NOT predicted. -/

set_option maxHeartbeats 0 in
#leaf_sweep Sparkle.Tests.Compiler.NoPortsMemKidTest.kcnt
