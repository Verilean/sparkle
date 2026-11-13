import Tools.VedU1PackedEntry

/-!
# Checks for the packed result with registers (`#ved_u1_packed` on a `Signal.loop` body)

A product result is ONE port `out` (docs/VED-U1-PACKED.md); when the body has registers the contract also
carries the clock/reset names and the register initial values (docs/VED-U1-MULTISEQ.md), read from the returned
module like `contractOf` does for a single port, and the statement is the same `PackedStmt`.

Positives: the registered theorem has EXACTLY the type `PackedStmt <ved_contract> <ved_mod> <decl>`; the
contract's slice map, clock/reset, register names and initial values equal ones written out by hand here
(the initial values are literals in this file, not read back from the declaration); standard three axioms.
Controls (each refused at the stage named; no `ved_*` constant the checker registered is left): a missing /
swapped / wrongly sized slice, a missing projection (the module of a two-leaf declaration against a
three-leaf one), outputs swapped inside the module (same widths), a same-width different value in one
output, one output altered through its register's update, a register initial value changed (module and
declaration disagree), a register initial value changed in the returned module itself.
-/

namespace Tests.Ved.U1MultiSeqCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Packed Tools.VedU1PackedEntry

/-! ## Declarations (a loop of two registers, result a product in ONE port) -/

/-- 8-bit accumulator and a sticky flag: result `(acc : 8) × (flag : 1)` -/
def msCnt (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

/-- the same with the flag never set (one output altered, through its register's update) -/
def msCntFlag (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 254#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

/-- the same with a non-zero initial value -/
def msCntInit (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 1#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

/-- two 8-bit accumulators (equal widths), three variants -/
def msPair (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × BitVec 8) :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (a + d) a), Signal.register 0#8 (Signal.mux en (b - d) b)]
  bundle2 (projN! st 2 0) (projN! st 2 1)

def msPairSwap (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × BitVec 8) :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (a + d) a), Signal.register 0#8 (Signal.mux en (b - d) b)]
  bundle2 (projN! st 2 1) (projN! st 2 0)

def msPairVal (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × BitVec 8) :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (a + d) a), Signal.register 0#8 (Signal.mux en (b - d) b)]
  bundle2 (projN! st 2 0) (projN! st 2 1 + 1#8)

/-- three leaves (nested right), with a plain wire next to the registers -/
def msTri (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × (BitVec 8 × Bool)) :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (a + d) a), Signal.register 0#8 (Signal.mux en (b - d) b)]
  bundle2 (projN! st 2 0) (bundle2 (projN! st 2 1) (en &&& (projN! st 2 0 === 0#8)))

/-- control targets: never run through the entry themselves -/
def msCntCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) := msCnt en d
def msPairCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × BitVec 8) := msPair en d
def msTriCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × (BitVec 8 × Bool)) := msTri en d

/-! ## Positives -/

def modOf (decl : Name) : TermElabM Sparkle.IR.AST.Module := do
  return (← Sparkle.Compiler.Elab.synthesizeCombinational decl).1

/-- `slices`, the clock/reset and the registers' initial values are written out by hand
(`inits`: one value per register, in body order; the register NAMES are the module's). -/
def checkPackedSeq (decl : Name) (stmtStx : Term) (slices : List (Nat × Nat)) (W : Nat)
    (inits : List Int) (wrap : TermElabM (Sparkle.IR.AST.Module × Name × Nat) →
      TermElabM (Sparkle.IR.AST.Module × Name × Nat) := id) : CommandElabM Unit := liftTermElabM do
  let (m, thm, nDom) ← wrap (vedU1PackedS decl)
  let nm := Names.ofBase decl
  unless m.outputs == [⟨"out", .bitVector W⟩] do throwError "{decl}: outputs {repr m.outputs}"
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``PackedStmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not the expected PackedStmt\n{ti.type}\n{expected}"
  let some (.defnInfo ci) := (← getEnv).find? nm.contract | throwError "no contract"
  let tbl ← readTableOfType decl (← inferType stmt)
  let regNames := (regsOf m.body).map (·.1)
  unless regNames.length == inits.length do throwError "{decl}: {regNames.length} registers"
  let hand : PContract :=
    { modName := m.name, tbl, port := "out", slices,
      inNames := tbl.binders.map ("_gen_" ++ ·), wires := m.wires,
      clkRst := some ("clk", "rst"), inits := regNames.zip inits }
  unless ci.value == toExpr hand do throwError "{decl}: the contract is not the hand-written one"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"packed+registers OK {thm} {slices} {inits} {nDom}"

/-- info: packed+registers OK Tests.Ved.U1MultiSeqCheck.msCnt.ved_u1 [(1, 8), (0, 1)] [0, 0] 0 -/
#guard_msgs in
run_cmd checkPackedSeq ``msCnt (← `(msCnt)) [(1, 8), (0, 1)] 9 [0, 0]

/-- info: packed+registers OK Tests.Ved.U1MultiSeqCheck.msPair.ved_u1 [(8, 8), (0, 8)] [0, 0] 0 -/
#guard_msgs in
run_cmd checkPackedSeq ``msPair (← `(msPair)) [(8, 8), (0, 8)] 16 [0, 0]

/-- info: packed+registers OK Tests.Ved.U1MultiSeqCheck.msTri.ved_u1 [(9, 8), (1, 8), (0, 1)] [0, 0] 0 -/
#guard_msgs in
run_cmd checkPackedSeq ``msTri (← `(msTri)) [(9, 8), (1, 8), (0, 1)] 17 [0, 0]

-- a non-zero initial value is part of the contract, as the hand-written one says
/-- info: packed+registers OK Tests.Ved.U1MultiSeqCheck.msCntInit.ved_u1 [(1, 8), (0, 1)] [1, 0] 0 -/
#guard_msgs in
run_cmd checkPackedSeq ``msCntInit (← `(msCntInit)) [(1, 8), (0, 1)] 9 [1, 0]

/-! ## Controls: refused, no `ved_*` constant registered by the checker left -/

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

def expectRefused (stage : String) (base : Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  for n in checkerNames base do
    if (← getEnv).contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

/-- the checker on `decl` (its own statement and table) with a substituted slice map / module -/
def onMap (decl : Name) (slices : List (Nat × Nat)) (m : Sparkle.IR.AST.Module) : TermElabM Unit := do
  let (stmt, _, tbl) ← packedStmtOf decl
  discard <| checkPackedE decl stmt tbl slices m .generated

-- slice maps (module of a register body)
/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``msPairCtl do onMap ``msPairCtl [(0, 8), (8, 8)] (← modOf ``msPair)  -- swapped

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``msCntCtl do onMap ``msCntCtl [(0, 1), (1, 8)] (← modOf ``msCnt)  -- exchanged

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``msCntCtl do onMap ``msCntCtl [(2, 8), (0, 1)] (← modOf ``msCnt)  -- wrong offset

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``msCntCtl do onMap ``msCntCtl [(1, 7), (0, 1)] (← modOf ``msCnt)  -- wrong width

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``msTriCtl do onMap ``msTriCtl [(9, 8), (1, 8)] (← modOf ``msTri)  -- missing slice

-- the module's registers / outputs
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``msPairCtl do onMap ``msPairCtl [(8, 8), (0, 8)] (← modOf ``msPairSwap)  -- outputs swapped

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``msPairCtl do onMap ``msPairCtl [(8, 8), (0, 8)] (← modOf ``msPairVal)  -- same width, other value

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``msCntCtl do onMap ``msCntCtl [(1, 8), (0, 1)] (← modOf ``msCntFlag)  -- one output altered

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``msCntCtl do onMap ``msCntCtl [(1, 8), (0, 1)] (← modOf ``msCntInit)  -- initial value

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``msTriCtl do onMap ``msTriCtl [(9, 8), (1, 8), (0, 1)] (← modOf ``msPair)  -- missing projection

-- the returned module itself changed: a register initial value
def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r d _ => .register o c r d 7
      | s => s }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``msCntCtl do onMap ``msCntCtl [(1, 8), (0, 1)] (mutInit (← modOf ``msCnt))

/-! ## Heartbeat budget of the loop script (no fixed floor: `ved.u1.seqProofHeartbeats`)

A packed body with registers is elaborated under `withProofBudget`, plus the extra floor
`ved.u1.seqProofHeartbeats` (default 0 = none).  (N) `ved.u1.proofHeartbeats 0` and `ved.u1.seqProofHeartbeats 0`
with a small context budget: the low budget is respected, refused at `[proof]`.  (P) the same context budget with
`ved.u1.seqProofHeartbeats 24000000`: the option raises the floor, the registered theorem has the exact
`PackedStmt` type.  (D) the positives above run at the default options (no extra floor). -/

/-- Local heartbeat budget of `n` thousand (the context field), the proof budget switched off
(as in `Tests/Ved/U1StageCheck.lean`), and the extra floor `seq` (thousands). -/
def withLowBudget (n seq : Nat) (act : TermElabM α) : TermElabM α :=
  withOptions (fun o => ((o.set `ved.u1.proofRecDepth (0 : Nat)).set `ved.u1.proofHeartbeats (0 : Nat)).set
      `ved.u1.seqProofHeartbeats seq) <|
    Core.withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := n * 1000 }) act

def msCntLow (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) := msCnt en d

-- (N) the low budget is respected
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``msCntLow do
  discard <| withLowBudget 2000 0 (vedU1PackedS ``msCntLow)

-- (P) the option raises the floor: accepted, exact type, standard axioms
/-- info: packed+registers OK Tests.Ved.U1MultiSeqCheck.msCntLow.ved_u1 [(1, 8), (0, 1)] [0, 0] 0 -/
#guard_msgs in
run_cmd checkPackedSeq ``msCntLow (← `(msCntLow)) [(1, 8), (0, 1)] 9 [0, 0] (withLowBudget 2000 24000000)

end Tests.Ved.U1MultiSeqCheck
