import Tests.Compiler.ShippingChildBoundaryTest
import Tests.Compiler.NoPortsTwoTest
import Tools.ShippingNoPortsMemSeqCommand

/-! # `#machine_no_ports_memseq` on a NEW declaration inside the BUILT base scope: two different leaf register children and ONE synchronous memory (round par/b-25)

`NoPortsMemSeqGenNewTest` (`seqTwoMem`: two leaf children, TWO memories)
failed in the BASE command `#machine_design_svR0`, before the generator ran
(integrator's build of db9d0b84). By READING (not verified by a build):
`Tools.ShippingMachineSeqCommand.memTactic`
(`Tools/ShippingMachineSeqCommand.lean` 127–137) names its synthetic holes
`?A ?D ?E ?R ?h0 ?h1 ?h2 ?h3` WITHOUT the call index and closes them by
`all_goals rfl` (only `?hx` goes through `case`, which clears the tag), so
the SECOND memory call of one command finds the first call's holes. The
built base scope of the sequential route is therefore: any number of leaf
callees / entries, AT MOST ONE memory entry (`docs/parallel/B-memseqgen2.md`).

This declaration stays inside it and is new for the generator against
`seqMem` in three ways: TWO different leaf callees (three keys: the tables'
`if` chains, the three-way `Or.elim`, `leafNe0_1`, two reflections in the
closing), a SYNCHRONOUS read, and another address width (3):

    def seqAccSync (en : Signal defaultDomain Bool) (wd : Signal defaultDomain (BitVec 8))
        (wb : Signal defaultDomain (BitVec 3)) : Signal defaultDomain (BitVec 8) :=
      circuit do
        let r ← Signal.reg 0#8
        let rs := (r : Signal defaultDomain (BitVec 8))
        let k := cnt en
        let a := acc rs
        let rq := Signal.memory wb wd en wb
        r <~ Signal.mux k.hit (rq + a.s + k.n) rs
        return rs

## READ vs NOT READ (nothing was run by the worker)

READ: the source; the BUILT log of `seqTwoMem` (this source plus one
combinational memory): `#machine_endpoint` accepted it (a synchronous
`Signal.memory` in a `circuit do` next to `cnt` and `acc`), entries
`[cnt, cnt, acc, acc, combo, sync]`, fields `[n, hit, s, odd, out, out]`
(one entry per OUTPUT of a callee, `odd` included), `slots=1`, output
`[out]`. `two` (the same two leaf callees, no memory) and `seqMem` (one
leaf, one combinational memory) are BUILT on `#machine_design_svR0`.
INFERRED for `seqAccSync`, NOT asserted (LOGGED first, `NOPORTS MEMSEQ NEW2
DATA`): `nDecl=3`, entries `[cnt, cnt, acc, acc, SparkleMem.sync.3.8]`.
NOT KNOWN: `memTactic` with `cb = false` in the sequential route (its
`?hx` step is `intro j; rfl`; the memory-only route's same step is built for
a synchronous read on `mixedMems` / `syncNarrow`).

## EXPECTED (stated before the build; the audit THROWS otherwise)

| endpoint | premise | predicted state |
|---|---|---|
| `seqAccSync.machine_design_svR0` (base) | `shipsHierCheck`, `kidsMixed`, `designCheck 0`, `outsCheck 0`, `MachineClosesAt seqAccSync` | present (asserted: the inventory) |
| `seqAccSync.machine_design_noPortsR0` | `shipsHierCheck`, `kidsMixed`, `designCheck 0`, `outsCheck 0` | WRITTEN, NOT BUILT — predicted absent, pending build |
| | `MachineClosesAt seqAccSync` | still a binder, the one NOT ALLOWED |
| | the boundary antecedent, the run, `MachineDefines seqAccSync` | stay |
| `seqAccSync.machine_design_noPortsR0_closed` | `MachineClosesAt seqAccSync` | predicted ABSENT, pending build |
| | binders ADDED: `MachineDefines cnt`, `MachineDefines acc` (allowed) | predicted present |
| | NOT ALLOWED premises | 0 (asserted) |
| `…_closed_gap` | gap hypotheses | predicted NONE |

NOT exercised by this file: per-entry widths (two placeholders) — outside
the built base scope until `memTactic` is changed.

SCOPE: one declaration, depth 0, data conditions decided per declaration
(conditions, not reductions), compiler guards with fallback, `DesignSV` of
the module list — not the SV string, not `#sim`; the run, the reflections of
`seqAccSync`, `cnt`, `acc` and `ChildBnd` stay premises.

WRITTEN, NOT BUILT (par/b-25). -/
namespace Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingChildBoundaryTest (acc)

/-- Two different sequential children next to ONE synchronous-read memory
(aw 3, dw 8). -/
def seqAccSync (en : Signal defaultDomain Bool) (wd : Signal defaultDomain (BitVec 8))
    (wb : Signal defaultDomain (BitVec 3)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let a := acc rs
    let rq := Signal.memory wb wd en wb
    r <~ Signal.mux k.hit (rq + a.s + k.n) rs
    return rs

#machine_endpoint seqAccSync

end Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test

/-! ## The reader data: LOGGED first, nothing asserted -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync
  let rf ← Tools.ShippingMachineCommand.readMachine f
  Lean.logInfo m!"NOPORTS MEMSEQ NEW2 DATA {f}: nDecl={rf.nDecl}, binders={rf.shape.binders.length}, call entries {rf.shape.insts.map (·.1)}, argument lets {rf.shape.insts.map (·.2.1)}, instFields={rf.shape.instFields}, slots={rf.shape.layout.slots.length}, lets={rf.shape.layout.lets}, outputs {rf.shape.layout.outs.map (·.name)}"
  for c in [``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt,
      ``Sparkle.Tests.Compiler.ShippingChildBoundaryTest.acc] do
    let rc ← Tools.ShippingMachineCommand.readMachine c
    Lean.logInfo m!"NOPORTS MEMSEQ NEW2 DATA {c}: nDecl={rc.nDecl}, binders={rc.shape.binders.length}, call entries {rc.shape.insts.map (·.1)}, slots={rc.shape.layout.slots.length}, lets={rc.shape.layout.lets}, outputs {rc.shape.layout.outs.map (·.name)}; machine_leafKid in the imports: {(← Lean.getEnv).contains (c ++ `machine_leafKid)}; machine_closes: {(← Lean.getEnv).contains (c ++ `machine_closes)}"

/-! ## The base endpoint, by the built command -/

set_option maxHeartbeats 0 in
#machine_design_svR0 Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync

/-! ## The generator -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#machine_no_ports_memseq_try Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync "GENERATED"

set_option maxHeartbeats 0 in
#machine_goal_gap_of
  Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync.machine_design_noPortsR0_closed

namespace Tests.Compiler.NoPortsMemSeqGenNew2Test
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

end Tests.Compiler.NoPortsMemSeqGenNew2Test

/-! ## The audit (an error on any failure) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.NoPortsMemSeqGenNew2Test.seqAccSync
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
     "domB", "outTy", "callWidths", "callArgs", "outChars", "outScalar", "kids", "runFacts",
     "outsG0", "mixedG", "designP0", "alias", "argsN", "fieldOut", "fieldsNd", "outHead",
     "notinP0", "leafNotin0_0", "leafNotin1_0",
     "leafNeParent0", "leafNeParent1", "leafNe0_1", "iface0", "iface1",
     "kidsP", "sep", "parent", "parentD", "disj", "closes"]
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
    unless Tests.Compiler.NoPortsMemSeqGenNew2Test.mentions oldT k do
      throwError "{old}: does not mention {k} (the inventory is wrong)"
  -- (c) the statements: no checker constant; the closed ones no closing premise
  let openT := (← Lean.getConstInfo openN).type
  let closedT := (← Lean.getConstInfo closed).type
  let gapT := (← Lean.getConstInfo gap).type
  for (n, t) in [(openN, openT), (closed, closedT), (gap, gapT)] do
    for k in Tests.Compiler.NoPortsTest.checkers ++ Tools.ShippingNoPortsMemCommand.forbiddenMem do
      if Tests.Compiler.NoPortsMemSeqGenNew2Test.mentions t k then
        throwError "{n}: the statement mentions {k}"
  unless Tests.Compiler.NoPortsMemSeqGenNew2Test.mentions openT ``Tools.ShippingChildInv.MachineClosesAt do
    throwError "{openN}: does not ask MachineClosesAt (the report says it stays a premise of the open form)"
  for (n, t) in [(closed, closedT), (gap, gapT)] do
    for k in [``Tools.ShippingChildInv.MachineClosesAt, ``Tools.ShippingChildInv.ChildRanIn,
        ``Tools.ShippingMachineEntry.MachineCloses] do
      if Tests.Compiler.NoPortsMemSeqGenNew2Test.mentions t k then
        throwError "{n}: the statement mentions {k}"
  for k in [``Tools.ShippingChildInv.ChildBnd, ``Tools.ShippingDesignSV.DesignSV] do
    unless Tests.Compiler.NoPortsMemSeqGenNew2Test.mentions closedT k do
      throwError "{closed}: does not mention {k}"
  -- (d) the closing theorem: its proposition premises are the reflections of cnt and acc, no other
  let clP ← Tests.Compiler.NoPortsMemSeqGenNew2Test.propTypes (← Lean.getConstInfo cl).type
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
  let pOld ← Tests.Compiler.NoPortsMemSeqGenNew2Test.propTypes oldT
  let pOpen ← Tests.Compiler.NoPortsMemSeqGenNew2Test.propTypes openT
  let pClosed ← Tests.Compiler.NoPortsMemSeqGenNew2Test.propTypes closedT
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
  Lean.logInfo m!"NOPORTS MEMSEQ NEW2 ANTECEDENTS {old}: {innerOld.size} — {innerOld.map (·.1)}"
  Lean.logInfo m!"NOPORTS MEMSEQ NEW2 ANTECEDENTS {closed}: {innerC.size} — {innerC.map (·.1)}"
  unless innerC.size == 1 && innerC[0]!.2 do
    throwError "{closed}: expected ONE allowed antecedent under the existentials (the boundary): {innerC.map (·.1)}"
  -- (g) the gap theorem: no gap hypothesis
  let gaps ← Tests.Compiler.NoPortsMemSeqGenNew2Test.gapsOf gap
  unless gaps.isEmpty do throwError "{gap}: the gap hypotheses are {gaps}, expected none"
  Lean.logInfo m!"NOPORTS MEMSEQ NEW2 AUDIT {f}: GENERATED by #machine_no_ports_memseq; {openN}, {closed}, {gap} and {lemmas.length} named lemmas {f}.noPortsMemSeq_* on standard axioms. {old} mentions shipsHierCheck, kidsMixed, designCheck, outsCheck and MachineClosesAt ({innerOld.size} antecedents under its existentials); none of the three generated statements mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck, kidsMaskedN, hierCheck, kidsMixed, kidsMem or kidsMasked. {openN}: {linesO.size} premises listed, 1 NOT ALLOWED (MachineClosesAt {f}). {closed}: {linesC.size} premises listed, 0 NOT ALLOWED — the run, MachineDefines {f}, MachineDefines of {leaves}, and ONE antecedent under the existentials (the boundary, allowed); no MachineClosesAt, MachineCloses, ChildRanIn. {cl}: its only proposition premises are the reflections of {leaves}. {gap}: NO gap hypothesis. SCOPE: one declaration, a register parent under the general closing, two leaf register machine children and ONE memory placeholder (synchronous read, aw 3, dw 8), depth 0; data conditions decided per declaration (conditions, not reductions); compiler guards with fallback; DesignSV of the module list — not the SV string, not #sim. The run, the reflections and ChildBnd remain premises."
