import Lean.Elab.Command
import Tools.ShippingMachineCommand
import Tools.ShippingMachineDepthCommandR
import Tools.ShippingMachineClosesAtGen
import Tools.ShippingNoPortsSlotlessCommand
import Tools.ShippingFinalGoalCommand
import Tests.Compiler.ShippingMachineSeqTest
import Tests.Compiler.NoPortsTest

/-! # A bare-register child at depth: the `machine_trace_of_regs` branch of `generateSeqChildN` (rounds par/b-28, par/b-29)

WRITTEN, NOT BUILT in this form (the first form was built and FAILED at step 1, see below). TARGET-ONLY for its first build.

Reviewer ruling 2026-10-13, item 6: "The `_of_regs` branch is untested: add
ONE small existing example." `seqChildNProof`
(`Tools/ShippingMachineDepthCommand.lean` 46–63) maps a child whose
`machine_sound` is built from `Tools.ShippingMachineLoop.machine_trace_of_regs`
to the wired twin `Tools.ShippingMachineLoopL.machine_traceL_of_regs`; no test
reached that line (`docs/parallel/depth-switch-evidence.md` §3).

## The example (corrected after the first build, round par/b-29)

FIRST BUILD (integrator, on par/b-28): the child was the existing
`ShippingHierarchySoundnessTest.childSeq` (`Signal.register 0#8 x`, any
domain) and `#machine_endpoint childSeq` REFUSED it — "a combinational gate
takes it, not the machine route". The reading had missed the first test of
`readMachine` (`Tools/ShippingMachineCommand.lean` 426–428): a declaration
that `certifiedShape?` or `mixedCertifiedShape?` accepts never reaches the
machine reader. `unifiedRegisterRoot` (`Sparkle/Compiler/Elab.lean`
2641–2652) accepts a canonical register (`canonicalRegister?` 1565–1574: a
`BitVec` register with a literal initial value over a POLYMORPHIC domain
binder) over a gate cone, or ONE more such register stage — a chain of depth
one or two. So the two existing bare-register `@[hardware_module]`s
(`childSeq`, `childSeq2`) are GATE children, with no machine endpoint at
all.

A declaration gets the `machine_trace_of_regs` head when (a) both gates miss
it, (b) the machine reader takes it with at least one slot, and (c) it has
no `circuit do` run, no `Signal.loop`, no `runCircuitH`
(`ShippingMachineCommand.lean` 2520–2523). For bare registers (a) holds for:
a chain of THREE or more registers; a register over a CONCRETE domain (the
corpus's `synth_reg`, `shift4Loop`: `defaultDomain`); a `Bool` register; a
structure / tuple of registers. No existing `@[hardware_module]` is of that
kind (every `@[hardware_module]` whose body has `register` and neither
`loop` nor `circuit` was read: `childSeq`, `childSeq2` only; `pe`, `twoHW`,
`cnt`, `acc` are `circuit do`s, head `machine_trace_of_data`). So the child
is declared HERE, the smallest of the first kind:

    @[hardware_module] def shift3 {dom : DomainConfig}
        (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
      Signal.register 0#8 (Signal.register 0#8 (Signal.register 0#8 x))

(`shift4Loop`'s shape, one stage shorter, over any domain as the built
sequential children are.) Step 2 THROWS unless its head is
`machine_trace_of_regs`.

The NEW parent, declared here:

    def regsParent (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain Bool) :
        Signal defaultDomain (BitVec 8) :=
      let k := cnt en          -- ShippingMachineSeqTest.cnt: a `circuit do` child, structure result
      let d := shift3 x        -- the bare-register child
      Signal.mux k.hit d k.n

BUILT in the first build with `childSeq` in `shift3`'s place:
`regsParent.machine_sound` was generated (the mixed parent's endpoint).

Why it has this form (by READING, except the line above):

* **no register of its own.** A parent WITH registers gets its endpoint from
  `causalProof`, whose per-call fact (`causalFactE`,
  `Tools/ShippingMachineCommand.lean` 1440–1450) REFUSES a sequential child
  whose endpoint is not `machine_trace_of_data(_ext/_causal)` or `_of_loop`:
  there is no `src_causal_of_regs`. So `#machine_endpoint` of a register
  parent of `shift3` fails before any depth generator runs, and the
  `_of_regs` branch is reachable by the command path only under a parent
  WITHOUT a register (`combCallsProof`, head `machine_trace_of_comb_calls`,
  which does not read the children's endpoints) — the class of `engineOnce`,
  `twinCalls`, `mesh2x2`.
* **a second call, of a structure-result child.** `shift3` has ONE
  `BitVec` output; a parent whose only calls are of that kind is read under
  the one-output closing (`instFields = []`, `Sparkle/Compiler/Elab.lean`
  4048–4052, 5180), which `generateCoreNR` refuses ("one-output combinational
  calls") and, without a register, the reader does not take at all (5134).
  The call of `cnt` (structure result) puts the parent under the general
  closing; `shift3`'s call is then an entry with the field `out`.
* `cnt` first: the generators that take "call entry 0" (the optional part
  below) then meet the child that built tests already cover.

NOT built anywhere before: a parent mixing a one-output `BitVec` sequential
call with a structure call under the general closing. If step 3 or 4 fails
on THAT (the message names `regsParent`, a `machine_*` check of the parent,
or `call 0/1/2 (group …)`) and not on `seq child …shift3`, the failure is
about the mixed parent, not about the `_of_regs` branch.

## The steps

| step | what | a failure means |
|---|---|---|
| 0 | names this file must be the first to add: absent (THROWS otherwise) | a NAME CLASH: another file generates `shift3.*` |
| 1 | `#machine_endpoint shift3` | the reader does not take `shift3` on the machine route, or a `rfl` of `regsProof` fails |
| 2 | ASSERT: `shift3.machine_sound` is built from `machine_trace_of_regs`; reader data of both declarations LOGGED; ASSERT the parent has no slot, `instFields ≠ []`, calls `cnt` and `shift3` | this file would not test the branch (the head is printed), or the reading of the header is wrong |
| 3 | `#machine_endpoint regsParent` | the mixed parent's endpoint (`combCallsProof`) |
| 4 | `#machine_design_svNR regsParent 1` | `seq child …shift3: …` = the `_of_regs` branch (a decided condition of `seqChildRunN_full`, or the twin's arguments); anything else = the grouped loop / ships / design on the mixed parent |
| 5 | ASSERT: `shift3.seq_child_runN` is a theorem GENERATED by the command, proof head `seqChildRunN_full`, proof mentions `machine_traceL_of_regs`, statement mentions `SeqChildRunN`, standard axioms; the parent's three `…NR1` theorems exist on standard axioms; fingerprints LOGGED | — |
| 6 | OPTIONAL, LOG-ONLY (`#drc_try`: a failure is logged, the environment put back, the file goes on): `#machine_closes_at regsParent`, `#machine_no_ports_seq regsParent 1`, `#machine_goal_gap_of_try` | nothing for the `_of_regs` branch; the log says how far the check-free chain goes on a bare-register leaf (`leafKidTheorem shift3`, `shift3.machine_closes`) |
| 7 | the audit of what step 6 left: for each theorem PRESENT — standard axioms, no checker constant in the check-free statements, the closed form's premises listed with 0 NOT ALLOWED (THROWS otherwise); each ABSENT one is named in the log line | a generated check-free theorem that does not pass the usual audit |

EXPECTED (prediction by reading; nothing here was elaborated): steps 0–2
pass; steps 3–5 pass if the mixed parent is within what `combCallsProof` and
the depth generator already do for `engineOnce` / `mesh2x2` (the per-entry
facts do not depend on the child's head; the child's theorem is the only new
term); step 6 is NOT predicted — `#machine_no_ports_seq` asks
`shift3.machine_closes` and `LeafKid` of a bare-register leaf, neither
ever generated.

NAME CLASH: this file generates `shift3.machineData`, `.machine_sound`,
`.seq_child_runN`, … (declared in this file) and `regsParent.*`; it REUSES `cnt.*` from the
imports (`cnt.seq_child_runN`, `cnt.machine_leafKid` exist there and the
generators return an existing constant). It imports only files of
`Tests/AllTests.lean`'s closure, so it could be added there after its first
target build.

SCOPE (binding for any report): ONE bare-register child (`shift3`: three
8-bit registers in a chain, any domain) under ONE new parent without a register, depth
1; the base depth endpoint WITH its check premises. Says nothing about a
register parent of a bare-register child (refused at `#machine_endpoint`,
see above), about `shift4Loop` / `synth_reg`, about the SV string or `#sim`.

    lake build Tests.Compiler.DepthRegsChildTest
-/

namespace Sparkle.Tests.Compiler.DepthRegsChildTest
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- Three bare registers in a chain: one stage more than the certified gate's
register root takes, so the machine reader reads it (three slots). -/
@[hardware_module] def shift3 {dom : DomainConfig}
    (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.register 0#8 (Signal.register 0#8 (Signal.register 0#8 x))

/-- A parent WITHOUT a register: a structure-result `circuit do` child and
the bare-register child, both sequential. -/
def regsParent (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  let k := Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt en
  let d := Sparkle.Tests.Compiler.DepthRegsChildTest.shift3 x
  Signal.mux k.hit d k.n

end Sparkle.Tests.Compiler.DepthRegsChildTest

namespace Tests.Compiler.DepthRegsChildTest
open Lean Elab Command

/-- The number of leading binders of a statement. -/
partial def binderCount : Lean.Expr → Nat
  | Lean.Expr.forallE _ _ b _ => binderCount b + 1
  | Lean.Expr.mdata _ e => binderCount e
  | _ => 0

/-- The head constant of a theorem's proof, as text. -/
def headText (v : Lean.Expr) : String :=
  match v.getAppFn with
  | Lean.Expr.const n _ => toString n
  | _ => "(not a constant application)"

/-- `#drc_try "label" in cmd`: a command as an OPTIONAL, LOG-ONLY step (the
wrapper of `NoPortsKeccakSpongeTest.runStep` with `must = false`): a thrown
or logged error is reported in ONE information line, the environment and the
message log are put back, and the file goes on. Never silent: `OK` or
`FAILED` is logged. -/
elab "#drc_try " tag:str " in " c:command : command => do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let before := savedMsgs.toList.length
  let res : Option String ← try
      elabCommand c
      pure none
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure (some msg)
  let msgs := (← get).messages.toList.drop before
  let errs ← (msgs.filter (·.severity == .error)).mapM fun m => m.data.toString
  let failure : Option String := match res with
    | some msg => some msg
    | none => if errs.isEmpty then none else some (String.intercalate " | " (errs.take 2))
  match failure with
  | some msg =>
    setEnv savedEnv
    modify fun s => { s with messages := savedMsgs }
    logInfo m!"DEPTH REGS CHILD OPTIONAL {tag.getString}: FAILED (log only, the environment put back) — {msg}"
  | none =>
    logInfo m!"DEPTH REGS CHILD OPTIONAL {tag.getString}: OK"

end Tests.Compiler.DepthRegsChildTest

/-! ## Step 0: the names this file must be the first to add -/

run_cmd Lean.Elab.Command.liftCoreM do
  let f := ``Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent
  let c := ``Sparkle.Tests.Compiler.DepthRegsChildTest.shift3
  let env ← Lean.getEnv
  for n in [c ++ `machineData, c ++ `machine_sound, c ++ `seq_child_runN,
      f ++ `machineData, f ++ `machine_sound, f ++ `machine_composedNR1] do
    if env.contains n then
      throwError "{n}: exists already — another imported file generates it (NAME CLASH, see the header)"

/-! ## Step 1: the child's endpoint -/

set_option maxHeartbeats 0 in
#machine_endpoint Sparkle.Tests.Compiler.DepthRegsChildTest.shift3

/-! ## Step 2: its head is `machine_trace_of_regs`; the reader's data -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent
  let c := ``Sparkle.Tests.Compiler.DepthRegsChildTest.shift3
  let k := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
  let env ← Lean.getEnv
  match env.find? (c ++ `machine_sound) with
  | some (Lean.ConstantInfo.thmInfo ti) =>
    let head : String := Tests.Compiler.DepthRegsChildTest.headText ti.value
    unless ti.value.isAppOf ``Tools.ShippingMachineLoop.machine_trace_of_regs do
      throwError "{c}.machine_sound is built from {head}, not from machine_trace_of_regs: this file would not test the branch"
    Lean.logInfo m!"DEPTH REGS CHILD: before the command — {c}.seq_child_runN absent, {c}.machine_sound built from {head}"
  | _ => throwError "{c}.machine_sound: not generated as a theorem by #machine_endpoint"
  if env.contains (c ++ `seq_child_runN) then
    throwError "{c}.seq_child_runN: exists before the depth command (the endpoint generator added it?) — the command path would not be tested"
  unless env.contains (k ++ `machine_sound) do
    throwError "{k}.machine_sound: not in the imports"
  let rc ← Tools.ShippingMachineCommand.readMachine c
  let cKids : List Lean.Name := rc.shape.insts.map (·.1)
  Lean.logInfo m!"DEPTH REGS CHILD DATA {c}: nDecl {rc.nDecl}, {rc.shape.layout.slots.length} slot(s), callees {cKids}, outputs {rc.shape.layout.outs.map (·.name)}"
  if rc.shape.layout.slots.isEmpty then throwError "{c}: no slot — not a register machine"
  unless rc.shape.insts.isEmpty do throwError "{c}: it has calls — not a leaf"
  let rf ← Tools.ShippingMachineCommand.readMachine f
  let fKids : List Lean.Name := rf.shape.insts.map (·.1)
  Lean.logInfo m!"DEPTH REGS CHILD DATA {f}: nDecl {rf.nDecl}, {rf.shape.layout.slots.length} slot(s), call entries' callees {fKids}, instFields {rf.shape.instFields}"
  unless rf.shape.layout.slots.isEmpty do
    throwError "{f}: {rf.shape.layout.slots.length} slot(s) — expected a parent without a register"
  if rf.shape.instFields.isEmpty then
    throwError "{f}: instFields = [] — the one-output closing; the depth generator refuses it (the structure call did not put the parent under the general closing)"
  unless fKids.contains c && fKids.contains k do
    throwError "{f}: the callees are {fKids}, expected both {k} and {c}"

/-! ## Step 3: the parent's endpoint -/

set_option maxHeartbeats 0 in
#machine_endpoint Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent

/-! ## Step 4: the depth endpoint — `generateSeqChildN shift3` takes the `_of_regs` branch -/

set_option maxHeartbeats 0 in
#machine_design_svNR Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent 1

/-! ## Step 5: what the command generated (every line THROWS where it fails) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent
  let c := ``Sparkle.Tests.Compiler.DepthRegsChildTest.shift3
  let env ← Lean.getEnv
  let name := c ++ `seq_child_runN
  let mut lines : List String := []
  match env.find? name with
  | some (Lean.ConstantInfo.thmInfo ti) =>
    unless ti.value.getAppFn.isConstOf ``Tools.ShippingMachineDepthRun.seqChildRunN_full do
      throwError "{name}: its proof is an application of {Tests.Compiler.DepthRegsChildTest.headText ti.value}, not of seqChildRunN_full"
    unless (ti.value.find? (fun e => e.isConstOf ``Tools.ShippingMachineLoopL.machine_traceL_of_regs)).isSome do
      throwError "{name}: its proof does not mention machine_traceL_of_regs (the wired twin of the bare-register head)"
    unless (ti.type.find? (fun e => e.isConstOf ``Tools.ShippingMachineDepth.SeqChildRunN)).isSome do
      throwError "{name}: its statement does not mention SeqChildRunN"
    lines := lines ++ [s!"{name}: hash {ti.type.hash.toNat}, {Tests.Compiler.DepthRegsChildTest.binderCount ti.type} binders"]
  | _ => throwError "{name}: not generated as a theorem by #machine_design_svNR"
  Tests.Compiler.NoPortsTest.stdAxioms name
  for n in [f ++ `machine_composedNR1, f ++ `machine_ships_hierNR1, f ++ `machine_design_svNR1] do
    match env.find? n with
    | some (Lean.ConstantInfo.thmInfo ti) =>
      lines := lines ++ [s!"{n}: hash {ti.type.hash.toNat}, {Tests.Compiler.DepthRegsChildTest.binderCount ti.type} binders"]
    | _ => throwError "{n}: not generated as a theorem"
    Tests.Compiler.NoPortsTest.stdAxioms n
  Lean.logInfo m!"DEPTH REGS CHILD: {name} GENERATED by generateSeqChildN inside #machine_design_svNR {f} 1 (no hand-written theorem; the constant was absent before the command): seqChildRunN_full at machine_traceL_of_regs, the wired twin of a machine_trace_of_regs endpoint, standard axioms; {f}.machine_composedNR1, machine_ships_hierNR1, machine_design_svNR1 kernel-checked on standard axioms. Fingerprints: {lines}. SCOPE: one bare-register child (three 8-bit registers in a chain) under one parent WITHOUT a register that also calls a circuit-do child, depth 1, the base endpoint with its check premises; a register parent of a bare-register child is refused at #machine_endpoint and is not covered"

/-! ## Step 6 (OPTIONAL, LOG-ONLY): the check-free chain of a parent of leaf register machines -/

set_option maxHeartbeats 0 in
#drc_try "6a #machine_closes_at regsParent" in
  #machine_closes_at Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
#drc_try "6b #machine_no_ports_seq regsParent 1" in
  #machine_no_ports_seq Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent 1

set_option maxHeartbeats 0 in
#machine_goal_gap_of_try
  Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent.machine_design_noPortsNR1_closed

/-! ## Step 7: the audit of what step 6 left (present ⇒ audited, THROWS on a failed audit; absent ⇒ named) -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let f := ``Sparkle.Tests.Compiler.DepthRegsChildTest.regsParent
  let c := ``Sparkle.Tests.Compiler.DepthRegsChildTest.shift3
  let closesAt := f ++ `machine_closes_at
  let openN := f ++ `machine_design_noPortsNR1
  let closed := f ++ `machine_design_noPortsNR1_closed
  let gap := f ++ `machine_design_noPortsNR1_closed_gap
  let mut present : List Lean.Name := []
  let mut absent : List Lean.Name := []
  for n in [c ++ `machine_closes, c ++ `machine_ships_wired, c ++ `machine_leafKid, closesAt,
      f ++ `machine_kidsK1, f ++ `machine_seqKidS, f ++ `machine_runFactsK1,
      f ++ `machine_designPK1, f ++ `machine_outsGK1, f ++ `machine_maskedGK1,
      openN, closed, gap] do
    if (← Lean.getEnv).contains n then
      Tests.Compiler.NoPortsTest.stdAxioms n
      present := present ++ [n]
    else absent := absent ++ [n]
  for n in [openN, closed, gap] do
    if (← Lean.getEnv).contains n then
      let ci ← Lean.getConstInfo n
      for chk in Tests.Compiler.NoPortsTest.checkers do
        if (ci.type.find? (fun e => e.isConstOf chk)).isSome then
          throwError "{n}: the statement mentions {chk}"
  let mut closedWord : String := s!"{closed}: ABSENT"
  if (← Lean.getEnv).contains closed then
    let closedT := (← Lean.getConstInfo closed).type
    if (closedT.find? (fun e => e.isConstOf ``Tools.ShippingChildInv.MachineClosesAt)).isSome then
      throwError "{closed}: still asks MachineClosesAt"
    let (plines, bad) ← Tests.Compiler.NoPortsTest.premiseLines closed
    Lean.logInfo m!"DEPTH REGS CHILD LISTING {closed}:\n{String.intercalate "\n" plines.toList}"
    unless bad.isEmpty do
      throwError "{closed}: {bad.size} premise(s) NOT ALLOWED:\n{String.intercalate "\n" bad.toList}"
    closedWord := s!"{closed}: GENERATED, no checker constant, {plines.size} premise lines, 0 NOT ALLOWED"
  Lean.logInfo m!"DEPTH REGS CHILD CHECK-FREE (optional part, by the built #machine_closes_at / #machine_no_ports_seq; see the OPTIONAL lines above for each command's outcome): PRESENT on standard axioms: {present}; ABSENT: {absent}. {closedWord}. SCOPE: one declaration, depth 1, data conditions decided per declaration, DesignSV of the module list — not the SV string, not #sim. An ABSENT name is a generator's refusal or failure on this declaration, not a refutation"
