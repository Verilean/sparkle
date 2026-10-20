import Tests.Compiler.ShippingDesignSVTest
import Tools.ShippingDesignSVMem

/-! Memory leaves of a design's emitted texts.

The built memory module `memModule cb aw dw` is a checked leaf for every read
kind and widths (`leafCheck_memModule`, `outsLeaf_memModule`), so a memory
parent's design endpoint (`#machine_design_sv0`: existence of the closed
emitted run ∧ every closed run shows the source) applies on the real compile:
`designCheck` and `outsCheck` are evaluated on the shipped module and must
hold before the evaluator reports `SVCHILD:SOURCE` / `CLOSED:AT-MOST-ONE`.
Covered: combinational reads (`memCounter`, `twoMems`, `memWide` aw 6 / dw 16),
synchronous reads (`syncNarrow` aw 3 / dw 5), both kinds in one parent
(`mixedMems`); a multi-cycle read/write run of the memory module's IR and of
its emitted text against an independent reference model; and the shapes the
leaf checks keep rejecting. -/
namespace Sparkle.Tests.Compiler.ShippingDesignSVMemTest
open Lean
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.AST Sparkle.IR.Semantics

/-- A combinational read, wider address and data. -/
def memWide (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 6))
    (wd : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 16) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 6 × BitVec 16)) =>
    let addr := Signal.fst st
    let rd := Signal.memoryComboRead wa wd we addr
    bundle2 (Signal.register 0#6 (addr + (Signal.pure 1#6 : Signal defaultDomain (BitVec 6))))
      (Signal.register 0#16 rd)
  Signal.snd st

/-- A synchronous read, narrow address and data. -/
def syncNarrow (we : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 3))
    (wd : Signal defaultDomain (BitVec 5)) : Signal defaultDomain (BitVec 5) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 3 × BitVec 5)) =>
    let addr := Signal.fst st
    let rd := Signal.memory wa wd we addr
    bundle2 (Signal.register 0#3 (addr + (Signal.pure 1#3 : Signal defaultDomain (BitVec 3))))
      (Signal.register 0#5 rd)
  Signal.snd st

#machine_endpoint memWide
#machine_composedT memWide
#machine_endpoint syncNarrow
#machine_composedT syncNarrow
#machine_ships_hier memWide
#machine_ships_hier syncNarrow

set_option maxHeartbeats 0 in
#machine_design_sv0 Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems
set_option maxHeartbeats 0 in
#machine_design_sv0 Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems
set_option maxHeartbeats 0 in
#machine_design_sv0 memWide
set_option maxHeartbeats 0 in
#machine_design_sv0 syncNarrow

/-- The memory parents (endpoint, depth-0 memory route). -/
def memParents : List Name :=
  [``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter,
   ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems,
   ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems, ``memWide, ``syncNarrow]

/-! ### On the real compile: the premises hold, the endpoint applies -/

open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in memParents do
    let v ← evalShipsHierSeq n none
    unless v.applies && v.svTag == "SV:PARENT" && v.svChildTag == "SVCHILD:SOURCE" &&
        v.uniqTag == "CLOSED:AT-MOST-ONE" do
      throwError "{n}: {v.tag}\n{v.report}"
    -- the premises the endpoint states, evaluated on the shipped module itself
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
    let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let C := Tools.ShippingMachineLinked.childMap D.modules
    unless Tools.ShippingDesignSV.designCheck C 0 o && Tools.ShippingDesignSVBack.outsCheck C 0 o do
      throwError "{n}: designCheck / outsCheck false on the shipped module"
    -- and `designCheck_memKids` derives both from the parent's own text check
    -- plus "every instance is a built memory module" (`MemKids`)
    unless Tools.ShippingDesignSV.textCheckI C o do throwError "{n}: textCheckI false"
    -- every memory child is the built memory module; both read kinds occur
    for st in o.body do
      if let .inst mn _ _ := st then
        let some (m, _) := C mn | throwError "{n}: {mn} unresolved"
        let some (cb, aw, dw) := Sparkle.Compiler.MachMemory.memParams? m
          | throwError "{n}: {mn} is not a memory module"
        unless m == (Sparkle.Compiler.MachMemory.memModule cb aw dw).1 do
          throwError "{n}: {mn} is not the built memory module"
  -- the read kinds and widths actually instantiated
  let kinds ← memParents.mapM fun n => do
    let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
    return D.modules.filterMap Sparkle.Compiler.MachMemory.memParams?
  let all := kinds.flatten
  for want in [(true, 4, 8), (false, 4, 8), (true, 6, 16), (false, 3, 5)] do
    unless all.contains want do throwError "memory module {want} not instantiated"
  Lean.logInfo m!"MEM DESIGNS: SOURCE + AT-MOST-ONE on {memParents.length} memory parents; instantiated {all.eraseDups}"

-- A generated endpoint whose premise is false is not counted: the
-- evaluator's `SVCHILD` is derived from `designCheck` on the shipped module,
-- not from the endpoint's existence.
open Tools.ShippingPremiseEval in
run_cmd Lean.Elab.Command.liftTermElabM do
  let v ← evalShipsHierSeq ``memWide none
  let v' := { v with svChildren := .fails "designCheck 0 rejects the shipped design" }
  unless v'.designEndpoint.isSome && v'.svChildTag != "SVCHILD:SOURCE" do
    throwError "an endpoint with a false designCheck counted as SOURCE: {v'.tag}"
  let v'' := { v with uniqueCheck := .fails "a child does not write all its outputs" }
  unless v''.uniqTag != "CLOSED:AT-MOST-ONE" do throwError "outsCheck false counted: {v''.tag}"

/-! ### Multi-cycle read/write: the leaf's IR run, its emitted text, a reference model -/

/-- The input schedule at cycle `t`: write `t*37+5` at `t`, read `t-1`. -/
def sched (aw dw t : Nat) (n : String) : Option Nat :=
  if n == "wa" then some (t % 2 ^ aw)
  else if n == "wd" then some ((t * 37 + 5) % 2 ^ dw)
  else if n == "we" then some 1
  else if n == "ra" then some ((t + 2 ^ aw - 1) % 2 ^ aw)
  else none

/-- The seeding: cycle `t = T-1-k` (`runModule` counts down). -/
def seedOf (aw dw T : Nat) : Nat → (String → Nat) → Env :=
  fun k st n => (sched aw dw (T - 1 - k) n).getD (st n)

/-- An independent reference: read-old combinational reads, a one-cycle
read latch for synchronous reads, memory and latch from zero. -/
def refOuts (cb : Bool) (aw dw T : Nat) : List Nat := Id.run do
  let mut mem : Nat → Nat := fun _ => 0
  let mut latch := 0
  let mut outs := #[]
  for t in [0:T] do
    let ra := (t + 2 ^ aw - 1) % 2 ^ aw
    let rdata := mem ra % 2 ^ dw
    outs := outs.push (if cb then rdata else latch)
    latch := rdata
    let wa := t % 2 ^ aw
    let wd := (t * 37 + 5) % 2 ^ dw
    mem := fun a => if a = wa then wd else mem a
  return outs.toList

/-- The output, cycle by cycle, of the memory module's IR run and of its
emitted text's run (`LeafRun`'s two kinds). -/
def runOuts (cb : Bool) (aw dw T : Nat) : Option (List Nat × List Nat) := do
  let m := (Sparkle.Compiler.MachMemory.memModule cb aw dw).1
  let wof := Tools.ShippingDesignSV.wofOf m
  let seed := seedOf aw dw T
  let ir ← runModule (Sparkle.IR.RegDedup.declWidth m) m.body seed T (fun _ => 0) (fun _ _ => 0)
  let pairs ← Tools.SVParser.EmitSem.emitAssigns wof m.body
  let mprog ← Tools.SVParser.EmitSem.emitMemWrites wof m.body
  let sv ← if Tools.ShippingDesignSV.hasSyncMem m.body then do
      let seqs ← Tools.ShippingMemSVSoundness.emitSeqNexts wof m.body
      Tools.ShippingMemSVSoundness.runModuleSVM wof pairs seqs mprog seed T (fun _ => 0) (fun _ _ => 0)
    else do
      let regs ← Tools.SVParser.EmitSem.emitRegs wof m.body
      Tools.SVParser.EmitSem.runModuleSV wof pairs regs mprog seed T (fun _ => 0) (fun _ _ => 0)
  return (ir.map (· "out"), sv.map (· "out"))

run_cmd Lean.Elab.Command.liftTermElabM do
  for (cb, aw, dw) in [(true, 4, 8), (false, 4, 8), (true, 6, 16), (false, 3, 5), (true, 1, 1),
      (false, 2, 32), (true, 2, 3)] do
    let T := min 12 (2 ^ aw + 3)   -- past one wrap of the address where it fits
    let some (ir, sv) := runOuts cb aw dw T | throwError "{(cb, aw, dw)}: a run failed"
    let r := refOuts cb aw dw T
    unless ir == r && sv == r do
      throwError "{(cb, aw, dw)}: IR {ir} / text {sv} / reference {r}"
    -- data really goes through the memory (a written word is read back)
    unless r.any (· != 0) do throwError "{(cb, aw, dw)}: no data read back"
    unless Tools.ShippingDesignSV.leafCheck (Sparkle.Compiler.MachMemory.memModule cb aw dw).1 do
      throwError "{(cb, aw, dw)}: leafCheck"
  Lean.logInfo m!"MEM LEAF RUNS: IR = emitted text = reference, comb and sync, 7 width pairs, multi-cycle"

/-! ### Shapes kept rejected -/

/-- The memory module with its fields replaced. -/
def memWith (body : List Sparkle.IR.AST.Stmt) (outs : List Sparkle.IR.AST.Port := [{ name := "out", ty := .bitVector 8 }]) : Sparkle.IR.AST.Module :=
  { (Sparkle.Compiler.MachMemory.memModule true 4 8).1 with body := body, outputs := outs }

run_cmd Lean.Elab.Command.liftTermElabM do
  let mem (cr : Bool) (ra : Sparkle.IR.AST.Expr) (rd : String) (wd : Sparkle.IR.AST.Expr := .ref "wd")
      (er : List (Sparkle.IR.AST.Expr × String) := []) :=
    Stmt.memory "mem" 4 8 "clk" (.ref "wa") wd (.ref "we") ra rd cr [] er
  let cases : List (String × Sparkle.IR.AST.Module × Bool × Bool) :=
    [ -- (what, module, leafCheck expected, outsLeaf expected)
      ("comb read into an output directly", memWith [mem true (.ref "ra") "out"], true, true),
      ("sync read latch driving an output directly", memWith [mem false (.ref "ra") "out"], true, false),
      ("non-reference write data", memWith [mem true (.ref "ra") "out_rdata" (wd := .op .not [.ref "wd"]),
        .assign "out" (.ref "out_rdata")], false, true),
      ("read target narrower than the data", { memWith [mem true (.ref "ra") "out_rdata",
        .assign "out" (.ref "out_rdata")] with wires := [{ name := "out_rdata", ty := .bitVector 4 }] },
        false, true),
      ("comb and sync reads in one leaf", { memWith [mem true (.ref "ra") "out_rdata",
        Stmt.memory "m2" 4 8 "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra") "r2" false [] [],
        .assign "out" (.ref "out_rdata")] with
          wires := [{ name := "out_rdata", ty := .bitVector 8 }, { name := "r2", ty := .bitVector 8 }] },
        false, true),
      ("an instance in a leaf", memWith [.inst "X" "u" [], .assign "out" (.ref "wd")], false, true),
      ("an output not written", memWith [mem true (.ref "ra") "out_rdata"], true, false) ]
  for (what, m, lc, ol) in cases do
    let a := Tools.ShippingDesignSV.leafCheck m
    let b := Tools.ShippingDesignSV.outsLeaf m
    unless a == lc && b == ol do
      throwError "{what}: leafCheck {a} (want {lc}), outsLeaf {b} (want {ol})"
  Lean.logInfo m!"MEM REJECTIONS: {cases.length} shapes as expected"

-- every memory endpoint states the existence AND the all-runs part, with outsCheck explicit
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in memParents do
    let e := n ++ `machine_design_sv0
    let ty ← Lean.Meta.inferType (Lean.mkConst e)
    unless (ty.find? (·.isConstOf ``Tools.ShippingDesignSVBack.outsCheck)).isSome &&
        (ty.find? (·.isConstOf ``Tools.ShippingDesignSV.designCheck)).isSome do
      throwError "{e}: designCheck / outsCheck premise missing"
    let rec occ (x : Lean.Expr) : Nat :=
      (if x.isAppOf ``Tools.ShippingDesignSV.DesignSV then 1 else 0) +
      match x with
      | .app f a => occ f + occ a
      | .lam _ t b _ => occ t + occ b
      | .forallE _ t b _ => occ t + occ b
      | .letE _ t v b _ => occ t + occ v + occ b
      | .mdata _ b => occ b
      | _ => 0
    unless occ ty ≥ 2 do throwError "{e}: the all-runs part is missing"

/-! ### Axioms -/

run_cmd do
  for name in [``Tools.ShippingDesignSV.leafCheck_memModule, ``Tools.ShippingDesignSV.outsLeaf_memModule,
      ``Tools.ShippingDesignSV.leaf_forward, ``Tools.ShippingDesignSV.leaf_backward,
      ``Tools.ShippingDesignSV.leaf_stepBound, ``Tools.ShippingDesignSV.leaf_outs,
      ``Tools.ShippingDesignSV.evalAssignsSV_written, ``Tools.ShippingDesignSV.designCheck_memKids, ``Tools.ShippingDesignSV.emitAssigns_readsOK,
      ``Tools.ShippingDesignSV.design_sv_runN, ``Tools.ShippingDesignSVBounds.svBounds_of_checks,
      ``Tools.ShippingDesignSVBack.design_sv_backN, ``Tools.ShippingDesignSVBack.design_sv_all,
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter.machine_design_sv0,
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems.machine_design_sv0,
      ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems.machine_design_sv0,
      ``memWide.machine_design_sv0, ``syncNarrow.machine_design_sv0] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"MEM AXIOMS: standard only"

end Sparkle.Tests.Compiler.ShippingDesignSVMemTest
