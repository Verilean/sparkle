import Tests.Compiler.ShippingChildBoundaryTest
import Tests.Compiler.NoPortsTwoTest
import Tests.Compiler.ShippingMachineMemLinkedTest
import Tools.ShippingNoPortsMemSeqCommand

/-! # `#machine_no_ports_memseq` on a NEW declaration: two different leaf register children and two memories of different widths and read kinds (round par/b-21)

`seqMem` is the only declaration of the mixed pattern in the repository, and
its endpoints exist by hand (the compare path:
`NoPortsMemSeqGenCompareTest`). This file adds ONE new real declaration,

    def seqTwoMem (en : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
        (wd : Signal defaultDomain (BitVec 8)) (wb : Signal defaultDomain (BitVec 3)) :
        Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal defaultDomain (BitVec 8))
        let k := cnt en                               -- leaf register machine (CntOut: n, hit)
        let a := acc rs                               -- a second, different one (AccOut: s, odd)
        let rd := Signal.memoryComboRead wa wd en wa  -- SparkleMem.combo.4.8
        let rq := Signal.memory wb wd en wb           -- SparkleMem.sync.3.8: other kind, other aw
        r <~ Signal.mux k.hit (rd + rq + a.s + k.n) rs
        return rs

runs the BUILT base commands on it in the order `seqMem`'s defining test
ran them (`Tests/Compiler/ShippingChildBoundaryTest.lean` 62, 71:
`#machine_endpoint`, then `#machine_design_svR0` — which leaves
`f.machine_ships_hierR` and `f.machine_design_svR0`; `#machine_composedTS` /
`#machine_ships_hier` there are the OLD route, for comparison only, and are
not run here), then `#machine_no_ports_memseq`, `#machine_goal_gap_of`, the
audit, and four refusals.

## READ vs NOT READ (nothing was run)

READ: the source above; `cnt` (`ShippingMachineSeqTest` 20) and `acc`
(`ShippingChildBoundaryTest` 34) are the leaf register machines of `two`,
whose `machine_leafKid` are in the imports (`NoPortsTwoTest`, BUILT); the
call forms `cnt en`, `acc rs`, `Signal.memoryComboRead wa wd en wa` are those
of `two` / `seqMem` (BUILT on the base commands, separately); a synchronous
`Signal.memory` is built on the base commands only inside a `Signal.loop`
(`mixedMems`, `syncNarrow`).

NOT READ — LOGGED by the first `run_cmd` (`NOPORTS MEMSEQ NEW DATA`), not
asserted, nothing predicted: `nDecl`, the binders, the NUMBER and ORDER of
the call entries (one per projected field: by the source `k.hit`, `k.n`,
`a.s`, `rd`, `rq`), their argument `let`s, `instFields`, the slots, the
`let` count, the output names. NOT KNOWN: whether `#machine_endpoint` and
`#machine_design_svR0` accept (i) two leaf children next to memories,
(ii) a synchronous memory in a `circuit do`, (iii) two memories of different
`(aw, dw)` in the sequential route — each is new for the base commands; a
failure there is a base-command finding, before the generator runs.

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise | predicted state |
|---|---|---|
| `seqTwoMem.machine_design_svR0` (base, IF it is generated) | `shipsHierCheck`, `kidsMixed`, `designCheck 0`, `outsCheck 0`, `MachineClosesAt seqTwoMem` | present (asserted: the inventory) |
| `seqTwoMem.machine_design_noPortsR0` | `shipsHierCheck (childMap D.modules) b` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `kidsMixed (childMap D.modules) b.body` | predicted absent, pending build |
| | `designCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `outsCheck (childMap D.modules) 0 (checkedOptimize b)` | predicted absent, pending build |
| | `MachineClosesAt seqTwoMem` | still a binder, the one NOT ALLOWED |
| | the boundary antecedent, the run, `MachineDefines seqTwoMem` | stay; the boundary's printed form is LOGGED, not predicted |
| `seqTwoMem.machine_design_noPortsR0_closed` | `MachineClosesAt seqTwoMem` | predicted ABSENT, pending build |
| | binders ADDED: `MachineDefines cnt`, `MachineDefines acc` (allowed) | predicted present (the SET; their order is the entries') |
| | 0 NOT ALLOWED | asserted |
| `…_closed_gap` | gap hypotheses | predicted NONE |

## SCOPE (binding for any report)

ONE declaration, `seqTwoMem`: a parent WITH a register, the general closing,
two leaf register machine children and two memory placeholders of different
read kinds and address widths, depth 0. Data conditions decided per
declaration by the kernel are conditions, not reductions. The result depends
on the compiler's guards with fallback. The conclusion is about `DesignSV
(childMap D.modules) 0 (checkedOptimize b)` — the module list, not the SV
string, not `#sim`. The run, the reflections of `seqTwoMem`, `cnt`, `acc`
and `ChildBnd` at the start world stay premises.

This file may be in `Tests/AllTests.lean` once built (every name it adds is
under the new `seqTwoMem`); the first build should be target-only.

WRITTEN, NOT BUILT (par/b-21). -/
namespace Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingChildBoundaryTest (acc)

/-- Two different sequential children next to two memories of different
read kinds and address widths. -/
def seqTwoMem (en : Signal defaultDomain Bool) (wa : Signal defaultDomain (BitVec 4))
    (wd : Signal defaultDomain (BitVec 8)) (wb : Signal defaultDomain (BitVec 3)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let a := acc rs
    let rd := Signal.memoryComboRead wa wd en wa
    let rq := Signal.memory wb wd en wb
    r <~ Signal.mux k.hit (rd + rq + a.s + k.n) rs
    return rs

#machine_endpoint seqTwoMem

end Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest

/-! ## The reader data: LOGGED first, nothing asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem
  let rf ← Tools.ShippingMachineCommand.readMachine f
  Lean.logInfo m!"NOPORTS MEMSEQ NEW DATA {f}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {rf.shape.insts.map (·.1)}, argument lets {rf.shape.insts.map (·.2.1)}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {rf.shape.layout.outs.map (·.name)}"
  for c in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc] do
    let rc ← Tools.ShippingMachineCommand.readMachine c
    Lean.logInfo m!"NOPORTS MEMSEQ NEW DATA {c}: nDecl={rc.nDecl}, binders={rc.shape.binders.length}, call entries {rc.shape.insts.map (·.1)}, slots={rc.shape.layout.slots.length}, lets={rc.shape.layout.lets}, outputs {rc.shape.layout.outs.map (·.name)}; machine_leafKid in the imports: {(← Lean.getEnv).contains (c ++ `machine_leafKid)}; machine_closes: {(← Lean.getEnv).contains (c ++ `machine_closes)}"

/-! ## The base endpoint, by the built command -/

set_option maxHeartbeats 0 in
#machine_design_svR0 Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem

/-! ## The generator -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_memseq_try Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem "GENERATED"

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem.machine_design_noPortsR0_closed

namespace Tests.Compiler.NoPortsMemSeqGenNewTest
open Lean Meta Elab Command

/-- The `gap_…` hypotheses of a goal-gap theorem. -/
def gapsOf (thm : Name) : MetaM (List String) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut out : List String := []
    for x in xs do
      let nm := (← x.fvarId!.getUserName).toString
      if nm.startsWith "gap_" then out := out ++ [nm]
    return out

/-- The proposition binders of a statement. -/
def propTypes (t : Lean.Expr) : MetaM (Array Lean.Expr) :=
  forallTelescope t fun xs _ => do
    let mut out : Array Lean.Expr := #[]
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then out := out.push ty
    return out

def mentions (e : Lean.Expr) (c : Name) : Bool := (e.find? (·.isConstOf c)).isSome

end Tests.Compiler.NoPortsMemSeqGenNewTest

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.NoPortsMemSeqGenNewTest.seqTwoMem
  let leaves : List Lean.Name := [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
    ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc]
  let old := f ++ `machine_design_svR0
  let openN := f ++ `machine_design_noPortsR0
  let closed := f ++ `machine_design_noPortsR0_closed
  let gap := f ++ `machine_design_noPortsR0_closed_gap
  let cl := f ++ `noPortsMemSeq_closes
  let env ← Lean.getEnv
  -- (a) standard axioms: the endpoints, the gap theorem, the lemmas the file names
  let lemmas : List String :=
    ["outsOf", "insOf", "nameOf", "nkOf", "outsNOf", "namesOf", "entry", "calls", "slots",
     "domB", "callWidths", "callArgs", "outChars", "kids", "runFacts",
     "outsG0", "mixedG", "designP0", "alias", "argsN", "fieldOut", "fieldsNd", "outHead",
     "notinP0", "notinP1", "leafNotin0_0", "leafNotin0_1", "leafNotin1_0", "leafNotin1_1",
     "leafNeParent0", "leafNeParent1", "leafNe0_1", "memNe0_1", "iface0", "iface1",
     "kidsP", "sep", "parent", "parentD", "disj", "closes"]
  -- par/r-5: the two output facts come from the reader (outTy_of_core / outScalar_of_core)
  for s in ["outTy", "outScalar"] do
    let n := f ++ Lean.Name.mkSimple ("noPortsMemSeq_" ++ s)
    if env.contains n then
      throwError "{n}: generated — the default path takes it from the reader (par/r-5), it must not decide it"
  for n in [openN, closed, gap] ++ lemmas.map (fun s => f ++ Lean.Name.mkSimple ("noPortsMemSeq_" ++ s)) do
    unless env.contains n do throwError "{n}: missing"
    Tests.Compiler.NoPortsTest.stdAxioms n
  for sfx in ["_regen"] do
    for s in ["machine_design_noPortsR0", "machine_design_noPortsR0_closed"] do
      if env.contains (f ++ Lean.Name.mkSimple (s ++ sfx)) then
        throwError "{f}.{s}{sfx}: exists — the endpoint was there before the command ran"
  -- (b) the inventory: the base endpoint asks the four check premises and the closing
  let oldT := (← Lean.getConstInfo old).type
  for k in [``Tools.ShippingHierPremisesBase.shipsHierCheck,
      ``Tools.ShippingMachineShipsHier.kidsMixed, ``Tools.ShippingDesignSV.designCheck,
      ``Tools.ShippingDesignSVBack.outsCheck, ``Tools.ShippingChildInv.MachineClosesAt] do
    unless Tests.Compiler.NoPortsMemSeqGenNewTest.mentions oldT k do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (c) the statements: no checker constant; the closed ones no closing premise
  let openT := (← Lean.getConstInfo openN).type
  let closedT := (← Lean.getConstInfo closed).type
  let gapT := (← Lean.getConstInfo gap).type
  for (n, t) in [(openN, openT), (closed, closedT), (gap, gapT)] do
    for k in Tests.Compiler.NoPortsTest.checkers ++ Tools.ShippingNoPortsMemCommand.forbiddenMem do
      if Tests.Compiler.NoPortsMemSeqGenNewTest.mentions t k then
        throwError "{n}: the statement mentions {k}"
  unless Tests.Compiler.NoPortsMemSeqGenNewTest.mentions openT ``Tools.ShippingChildInv.MachineClosesAt do
    throwError "{openN}: does not ask MachineClosesAt (the report says it stays a premise of the open form)"
  for (n, t) in [(closed, closedT), (gap, gapT)] do
    for k in [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingChildInv.ChildRanIn,
        ``Tools.ShippingMachineEntry.MachineCloses] do
      if Tests.Compiler.NoPortsMemSeqGenNewTest.mentions t k then
        throwError "{n}: the statement mentions {k}"
  for k in [``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingDesignSV.DesignSV] do
    unless Tests.Compiler.NoPortsMemSeqGenNewTest.mentions closedT k do
      throwError "{closed}: does not mention {k}"
  -- (d) the closing theorem: its proposition premises are the reflections of cnt and acc, no other
  let clP ← Tests.Compiler.NoPortsMemSeqGenNewTest.propTypes (← Lean.getConstInfo cl).type
  unless clP.size == leaves.length do
    throwError "{cl}: {clP.size} proposition premises, expected {leaves.length} (MachineDefines of {leaves})"
  for p in clP do
    unless p.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 do
      throwError "{cl}: a premise is not a reflection:{Lean.indentExpr p}"
  for c in leaves do
    let mut found : Bool := false
    for p in clP do
      if p.isAppOfArity ``Tools.ShippingMachineEntry.MachineDefines 6 then
        if ← Lean.Meta.isDefEq (p.getArg! 4) (Lean.toExpr c) then found := true
    unless found do throwError "{cl}: no premise MachineDefines of {c}"
  -- (e) the binders: open = the base's; closed = the open's without the closing, plus the two reflections
  let pOld ← Tests.Compiler.NoPortsMemSeqGenNewTest.propTypes oldT
  let pOpen ← Tests.Compiler.NoPortsMemSeqGenNewTest.propTypes openT
  let pClosed ← Tests.Compiler.NoPortsMemSeqGenNewTest.propTypes closedT
  unless pOpen.size == 3 && pOld.size == 3 do
    throwError "{openN}: {pOpen.size} proposition binders ({old}: {pOld.size}), expected 3 and 3 (the run, MachineDefines, MachineClosesAt)"
  unless pClosed.size == 2 + leaves.length do
    throwError "{closed}: {pClosed.size} proposition binders, expected {2 + leaves.length} (the run, MachineDefines {f}, MachineDefines of {leaves})"
  for p in pClosed do
    unless p.isAppOf ``Tools.ShippingEntrySoundness.RunsTo ||
        p.isAppOf ``Tools.ShippingMachineEntry.MachineDefines do
      throwError "{closed}: a proposition binder is neither the run nor a reflection:{Lean.indentExpr p}"
  -- (f) the premise lists (the goal-gap classifier's verdicts)
  let (linesO, badO) ← Tests.Compiler.NoPortsTest.premiseLines openN
  let (linesC, badC) ← Tests.Compiler.NoPortsTest.premiseLines closed
  Lean.logInfo m!"{String.intercalate "\n" linesO.toList}"
  Lean.logInfo m!"{String.intercalate "\n" linesC.toList}"
  unless badO.size == 1 do
    throwError "{openN}: {badO.size} premises NOT ALLOWED, expected exactly 1 (MachineClosesAt {f}):\n{String.intercalate "\n" badO.toList}"
  unless badC.isEmpty do
    throwError "{closed}: {badC.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" badC.toList}"
  let innerOld ← Lean.Meta.forallTelescope oldT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  let innerC ← Lean.Meta.forallTelescope closedT fun _ body =>
    Tests.Compiler.NoPortsTest.innerAntecedents body
  Lean.logInfo m!"NOPORTS MEMSEQ NEW ANTECEDENTS {old}: {innerOld.size} — {innerOld.map (·.1)}"
  Lean.logInfo m!"NOPORTS MEMSEQ NEW ANTECEDENTS {closed}: {innerC.size} — {innerC.map (·.1)}"
  unless innerC.size == 1 && innerC[0]!.2 do
    throwError "{closed}: expected ONE allowed antecedent under the existentials (the boundary): {innerC.map (·.1)}"
  -- (g) the gap theorem: no gap hypothesis
  let gaps ← Tests.Compiler.NoPortsMemSeqGenNewTest.gapsOf gap
  unless gaps.isEmpty do throwError "{gap}: the gap hypotheses are {gaps}, expected none"
  Lean.logInfo m!"NOPORTS MEMSEQ NEW AUDIT {f}: GENERATED by #machine_no_ports_memseq; {openN}, {closed}, {gap} and {lemmas.length} named lemmas {f}.noPortsMemSeq_* on standard axioms. {old} mentions shipsHierCheck, kidsMixed, designCheck, outsCheck and MachineClosesAt ({innerOld.size} antecedents under its existentials); none of the three generated statements mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN, hierCheck, kidsMixed, kidsMem or kidsMasked. {openN}: {linesO.size} premises listed, 1 NOT ALLOWED (MachineClosesAt {f}). {closed}: {linesC.size} premises listed, 0 NOT ALLOWED — the run, MachineDefines {f}, MachineDefines of {leaves}, and ONE antecedent under the existentials (the boundary, allowed); no MachineClosesAt, MachineCloses, ChildRanIn. {cl}: its only proposition premises are the reflections of {leaves}. {gap}: NO gap hypothesis. SCOPE: one declaration, a register parent under the general closing, two leaf register machine children and two memory placeholders (combinational aw 4 dw 8, synchronous aw 3 dw 8), depth 0; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim. The run, the reflections and ChildBnd remain premises."

/-! ## Refusals (class asserted; the reason is LOGGED by the command) -/

set_option maxHeartbeats 0 in
#machine_no_ports_memseq_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt "REFUSED"

set_option maxHeartbeats 0 in
#machine_no_ports_memseq_try Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent "REFUSED"

set_option maxHeartbeats 0 in
#machine_no_ports_memseq_try Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two "REFUSED"

set_option maxHeartbeats 0 in
#machine_no_ports_memseq_try Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter "REFUSED"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let refused : List Lean.Name :=
    [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
     ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
     ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.two,
     ``Sparkle.Tests.Compiler.ShippingMachineMemLinkedTest.memCounter]
  let env ← Lean.getEnv
  for g in refused do
    for s in ["noPortsMemSeq_entry", "noPortsMemSeq_outsOf", "noPortsMemSeq_closes"] do
      if env.contains (g ++ Lean.Name.mkSimple s) then
        throwError "{g}: REFUSED, yet {g}.{s} is in the environment"
  Lean.logInfo m!"NOPORTS MEMSEQ NEW REFUSED: {refused} — nothing of the command's left in the environment (expected reasons, by reading: cnt — no call; parent, two — no memory entry: use #machine_no_ports / _kids; memCounter — memory-only: use #machine_no_ports_mem; the lines above say which)"
