import Tests.Compiler.ShippingCallsCloseTest
import Tests.Compiler.ShippingMachineSeqLoopTest
import Tests.Compiler.ShippingDesignSVMemTest
import Tools.ShippingPremiseEval

/-! # A census of `hierBinds` on the real instance-bearing declarations (G1)

Compiled evidence, LOGS ONLY — nothing here throws and nothing is a theorem.

`Sparkle.IR.OptCheck.checkedOptimize` on a module with an instance statement
(not `simpleBody`, not all `seqStmtOk`) keeps the optimizer's output only as
checked by `hierRefineCheck` WHEN `hierBinds` holds; when `hierBinds` is
false it returns the optimizer's output UNCHECKED (its last `else o`). The
endpoints' premise `shipsHierCheck` has `hierBinds b` as its conjunct 1 and
two facts of the optimized module as conjuncts 2 and 4.

For every candidate declaration (the instance-bearing declarations of the
shipping tests; a name that is absent or does not compile is logged as
such), with `(raw, D)` the core run, `b` the full entry's module,
`o = optimizeModule b`, `o' = deinline b o`, `C = childMap D.modules`, one
line:

    HIERBINDS <decl>: branch=<simple|seq|hier-kept|hier-rejected|ELSE-O>
      gate=.. flatSelf=.. binds=.. hrc=.. same=.. wfB=.. ndB=.. wfO=.. ndO=..
      self=.. outs=.. rst=.. wid=.. ships=..

* `gate` `hierGate b`; `flatSelf` `refineCheck flat flat`; `binds`
  `hierBinds b`; `hrc` `hierRefineCheck b o'`;
* `same` `checkedOptimize b == b`;
* `wfB` / `ndB` `linkedWF C b.body`, `(instNames b.body).Nodup` (derived
  from the run: `core_linkedWF`, `core_raw_facts`);
* `wfO` / `ndO` the same of `(checkedOptimize b).body` — conjuncts 2, 4;
* `self` `outs` `rst` `wid` conjuncts 5 (on `b`), 6, 7, 8; `ships`
  `shipsHierCheck C b`.

Then the totals line `HIERBINDS CENSUS: …`. -/
namespace Tests.Compiler.HierBindsCensusTest
open Lean Meta

def bs (b : Bool) : String := if b then "T" else "F"

/-- The candidates, by name (no elaboration-time resolution: an absent name
is logged, not an error). -/
def candidates : List Name := [
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained,
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid,
  `Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand,
  `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
  `Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
  `Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2,
  `Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2,
  `Sparkle.Tests.Compiler.ShippingDesignSVTest.mixD1,
  `Sparkle.Tests.Compiler.ShippingDesignSVMemTest.memWide,
  `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter,
  `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.twoMems,
  `Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.mixedMems,
  `Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory,
  `Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent,
  `Sparkle.Tests.Compiler.MultiInstance.engineOnce,
  `Sparkle.Tests.Compiler.MultiInstance.twinCalls,
  `Sparkle.Tests.Compiler.MultiInstance.mesh2x2,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.caller,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerTwice,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerNested,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerD,
  `Sparkle.Tests.Compiler.ShippingMachineInstTest.callerInner,
  `Sparkle.Tests.Compiler.ShippingPremiseEvalTest.callerMix,
  `Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerL,
  `Sparkle.Tests.Compiler.ShippingMachineLinkedTest.callerLN,
  `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte,
  `Sparkle.Tests.Compiler.ShippingMachineTeleTest.divInLoop,
  `callerRep,
  `callerABA]

/-- One declaration's record. -/
structure Row where
  branch : String
  gate : Bool
  flatSelf : Bool
  binds : Bool
  hrc : Bool
  same : Bool
  wfB : Bool
  ndB : Bool
  wfO : Bool
  ndO : Bool
  self : Bool
  outs : Bool
  rst : Bool
  wid : Bool
  ships : Bool

def Row.str (r : Row) : String :=
  s!"branch={r.branch} gate={bs r.gate} flatSelf={bs r.flatSelf} binds={bs r.binds} " ++
  s!"hrc={bs r.hrc} same={bs r.same} wfB={bs r.wfB} ndB={bs r.ndB} wfO={bs r.wfO} " ++
  s!"ndO={bs r.ndO} self={bs r.self} outs={bs r.outs} rst={bs r.rst} wid={bs r.wid} " ++
  s!"ships={bs r.ships}"

/-- The record of a declaration; `none` when its module has no instance. -/
def census (n : Name) : MetaM (Option Row) := do
  let (_, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCore n [] false
  let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
  unless b.body.any Sparkle.IR.Machine.isInst do return none
  let C := Tools.ShippingMachineLinked.childMap D.modules
  let o := Sparkle.IR.Optimize.optimizeModule b
  let o' := Sparkle.IR.HierCheck.deinline b o
  let co := Sparkle.IR.OptCheck.checkedOptimize b
  let flat := Sparkle.IR.HierCheck.openFlat b (Sparkle.IR.HierCheck.openIns b)
    (Sparkle.IR.HierCheck.openOuts b)
  let binds := Sparkle.IR.RefineCheck.hierBinds b
  let hrc := Sparkle.IR.RefineCheck.hierRefineCheck b o'
  -- the branch of `checkedOptimize`, read off its definition
  let branch :=
    if Sparkle.IR.OptCheck.simpleBody b then "simple"
    else if b.body.all Sparkle.IR.OptCheck.seqStmtOk then "seq"
    else if binds then (if hrc then "hier-kept" else "hier-rejected")
    else "ELSE-O"
  return some {
    branch := branch
    gate := Sparkle.IR.RefineCheck.hierGate b
    flatSelf := Sparkle.IR.RefineCheck.refineCheck flat flat
    binds := binds
    hrc := hrc
    same := co == b
    wfB := Tools.ShippingHierOpen.linkedWF C b.body
    ndB := decide (Tools.ShippingHierState.instNames b.body).Nodup
    wfO := Tools.ShippingHierOpen.linkedWF C co.body
    ndO := decide (Tools.ShippingHierState.instNames co.body).Nodup
    self := Tools.ShippingHierPremisesBase.noSelfRead C b.body
    outs := Tools.ShippingHierPremisesBase.outsExtracted C b
    rst := (b.inputs.map (·.name)).contains "rst"
    wid := Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body
    ships := Tools.ShippingHierPremisesBase.shipsHierCheck C b }

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut rows : List (Name × Row) := []
  let mut absent : List Name := []
  let mut noInst : List Name := []
  let mut failed : List Name := []
  for n in candidates do
    if !env.contains n then
      absent := absent ++ [n]
      logInfo m!"HIERBINDS {n}: ABSENT (no such declaration in this build)"
    else
      try
        match ← census n with
        | some r =>
          rows := rows ++ [(n, r)]
          logInfo m!"HIERBINDS {n}: {r.str}"
        | none =>
          noInst := noInst ++ [n]
          logInfo m!"HIERBINDS {n}: no instance statement in the full entry's module"
      catch e =>
        failed := failed ++ [n]
        logInfo m!"HIERBINDS {n}: COMPILE FAILED: {e.toMessageData}"
  let cnt (p : Row → Bool) : Nat := (rows.filter fun x => p x.2).length
  let names (p : Row → Bool) : List Name := (rows.filter fun x => p x.2).map (·.1)
  let isElse (r : Row) : Bool := r.branch == "ELSE-O"
  let isKept (r : Row) : Bool := r.branch == "hier-kept"
  let isRej (r : Row) : Bool := r.branch == "hier-rejected"
  let line : String :=
    s!"HIERBINDS CENSUS: {rows.length} parents with an instance " ++
    s!"({absent.length} absent, {noInst.length} without instance, {failed.length} failed); " ++
    s!"hierGate true {cnt (fun r => r.gate)}; hierBinds true {cnt (fun r => r.binds)}; " ++
    s!"else-o branch taken {cnt isElse} {names isElse}; " ++
    s!"hier-kept {cnt isKept}; hier-rejected {cnt isRej} {names isRej}; " ++
    s!"checkedOptimize b == b {cnt (fun r => r.same)}; " ++
    s!"raw linkedWF false {names (fun r => !r.wfB)}; " ++
    s!"raw instNames Nodup false {names (fun r => !r.ndB)}; " ++
    s!"conjunct 2 (linkedWF of the optimized body) false {names (fun r => !r.wfO)}; " ++
    s!"conjunct 4 (instNames Nodup of the optimized body) false {names (fun r => !r.ndO)}; " ++
    s!"conjunct 5 (on b) false {names (fun r => !r.self)}; " ++
    s!"conjunct 6 false {names (fun r => !r.outs)}; " ++
    s!"conjunct 7 false {names (fun r => !r.rst)}; " ++
    s!"conjunct 8 false {names (fun r => !r.wid)}; " ++
    s!"shipsHierCheck true {cnt (fun r => r.ships)}, false {names (fun r => !r.ships)}"
  logInfo m!"{line}"

end Tests.Compiler.HierBindsCensusTest
