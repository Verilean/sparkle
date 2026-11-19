import Tools.VedU1PackedEntry

/-!
# Checks for the per-statement script of a packed result with registers (`sparkle-ved-packed-seq2`)

`#ved_u1_packed` on a `Signal.loop` body first runs `Tools.VedU1PackedSeq2.packedSeqScript` (one `step_seq`, one equation per
statement, `Bool` state components split per goal) and falls back to the flat loop script of `Tools/VedU1MultiSeq.lean`.  The
statement is the unchanged `PackedStmt <ved_contract> <ved_mod> <decl>`.

Positives (each: the stored type `==` the expected `PackedStmt`, the contract equal to one written out by hand here, the standard
three axioms, and the proof uses `Tools.VedU1ScriptSeq.step_seq`, which only the new script does): a two-register counter with a
flag, an fsm with a 3-bit state and two `Bool` registers, a three-leaf result, a wide body with `|||` / `&&&` / `~~~`.
Controls (each refused at the stage named, no `ved_*` constant left): a swapped / wrongly sized slice, an output altered by a
constant, an output altered through its register's update, a register initial value changed in the declaration / in the
returned module.
-/

namespace Tests.Ved.U1PackedSeq2Check

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Packed Tools.VedU1PackedEntry

/-! ## Declarations -/

def psCnt (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

/-- a 3-bit state and two `Bool` registers -/
def psFsm (go done : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 3 × Bool × Bool) :=
  let st := Signal.loop fun state =>
    let s := projN! state 3 0
    let a := projN! state 3 1
    let b := projN! state 3 2
    let sNext := Signal.mux (go &&& (s === 0#3)) (Signal.pure 1#3)
      (Signal.mux (done &&& (s === 1#3)) (Signal.pure 2#3)
        (Signal.mux (s === 2#3) (Signal.pure 0#3) s))
    let aNext := Signal.mux (s === 1#3) (Signal.pure true) (Signal.mux (s === 2#3) (Signal.pure false) a)
    let bNext := (a &&& go) ||| b
    bundleAll! [Signal.register 0#3 sNext, Signal.register false aNext, Signal.register false bNext]
  bundle2 (projN! st 3 0) (bundle2 (projN! st 3 1) (projN! st 3 2))

/-- three leaves, two registers, a plain wire -/
def psTri (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × (BitVec 8 × Bool)) :=
  let st := Signal.loop fun state =>
    let a := projN! state 2 0
    let b := projN! state 2 1
    bundleAll! [Signal.register 0#8 (Signal.mux en (a + d) a), Signal.register 0#8 (Signal.mux en (b - d) b)]
  bundle2 (projN! st 2 0) (bundle2 (projN! st 2 1) (en &&& (projN! st 2 0 === 0#8)))

/-- wide: set / clear / write of a 32-bit register (`|||`, `&&&`, `~~~`), a masked second register -/
def psWide (wd : Signal defaultDomain (BitVec 32)) (op : Signal defaultDomain (BitVec 2))
    (we : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 32 × BitVec 32 × Bool) :=
  let st := Signal.loop fun state =>
    let r := projN! state 2 0
    let m := projN! state 2 1
    let rNext := Signal.mux (we &&& (op === 1#2)) wd
      (Signal.mux (we &&& (op === 2#2)) (r ||| wd)
        (Signal.mux (we &&& (op === 3#2)) (r &&& (~~~wd)) r))
    let mNext := Signal.mux we ((m ||| 0x80#32) &&& 0xFFFFFFF7#32) m
    bundleAll! [Signal.register 0#32 rNext, Signal.register 0#32 mNext]
  bundle2 (projN! st 2 0) (bundle2 (projN! st 2 1) (we &&& (projN! st 2 0 === 0#32)))

-- variants for the controls (never run through the entry themselves, except as modules)
def psCntFlag (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 254#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

def psCntConst (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0 + 1#8) (projN! st 2 1)

def psCntInit (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 1#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

def psCntCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) := psCnt en d
def psTriCtl (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × (BitVec 8 × Bool)) := psTri en d

/-! ## Positives -/

def modOf (decl : Name) : TermElabM Sparkle.IR.AST.Module := do
  return (← Sparkle.Compiler.Elab.synthesizeCombinational decl).1

/-- the proof term uses `step_seq` (the per-statement script), looked through the auxiliary theorems -/
def usesStepSeq (thm : Name) : CoreM Bool := do
  let env ← getEnv
  let mut todo := [thm]
  let mut seen : Std.HashSet Name := {}
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if n == ``Tools.VedU1ScriptSeq.step_seq then return true
      if let some (.thmInfo ti) := env.find? n then
        todo := ti.value.getUsedConstants.toList ++ todo
  return false

def checkPk (decl : Name) (stmtStx : Term) (slices : List (Nat × Nat)) (W : Nat) (inits : List Int) :
    CommandElabM Unit := liftTermElabM do
  let (m, thm, nDom) ← vedU1PackedS decl
  let nm := Names.ofBase decl
  unless m.outputs == [⟨"out", .bitVector W⟩] do throwError "{decl}: outputs {repr m.outputs}"
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``PackedStmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not the expected PackedStmt"
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
  unless ← usesStepSeq thm do throwError "{thm}: the proof does not come from the per-statement script"
  logInfo m!"packed seq2 OK {thm} {slices} {inits} {nDom}"

/-- info: packed seq2 OK Tests.Ved.U1PackedSeq2Check.psCnt.ved_u1 [(1, 8), (0, 1)] [0, 0] 0 -/
#guard_msgs in
run_cmd checkPk ``psCnt (← `(psCnt)) [(1, 8), (0, 1)] 9 [0, 0]

/-- info: packed seq2 OK Tests.Ved.U1PackedSeq2Check.psFsm.ved_u1 [(2, 3), (1, 1), (0, 1)] [0, 0, 0] 0 -/
#guard_msgs in
run_cmd checkPk ``psFsm (← `(psFsm)) [(2, 3), (1, 1), (0, 1)] 5 [0, 0, 0]

/-- info: packed seq2 OK Tests.Ved.U1PackedSeq2Check.psTri.ved_u1 [(9, 8), (1, 8), (0, 1)] [0, 0] 0 -/
#guard_msgs in
run_cmd checkPk ``psTri (← `(psTri)) [(9, 8), (1, 8), (0, 1)] 17 [0, 0]

/-- info: packed seq2 OK Tests.Ved.U1PackedSeq2Check.psWide.ved_u1 [(33, 32), (1, 32), (0, 1)] [0, 0] 0 -/
#guard_msgs in
run_cmd checkPk ``psWide (← `(psWide)) [(33, 32), (1, 32), (0, 1)] 65 [0, 0]

/-! ## Controls -/

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

def onMap (decl : Name) (slices : List (Nat × Nat)) (m : Sparkle.IR.AST.Module) : TermElabM Unit := do
  let (stmt, _, tbl) ← packedStmtOf decl
  discard <| checkPackedE decl stmt tbl slices m .generated

-- slices
/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``psCntCtl do onMap ``psCntCtl [(0, 1), (1, 8)] (← modOf ``psCnt)  -- exchanged

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``psCntCtl do onMap ``psCntCtl [(1, 7), (0, 1)] (← modOf ``psCnt)  -- wrong width

/-- info: refused [packed], clean -/
#guard_msgs in
run_cmd expectRefused "packed" ``psTriCtl do onMap ``psTriCtl [(9, 8), (1, 8)] (← modOf ``psTri)  -- missing slice

-- the module
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``psCntCtl do onMap ``psCntCtl [(1, 8), (0, 1)] (← modOf ``psCntFlag)  -- register update

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``psCntCtl do onMap ``psCntCtl [(1, 8), (0, 1)] (← modOf ``psCntConst)  -- output + 1

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``psCntCtl do onMap ``psCntCtl [(1, 8), (0, 1)] (← modOf ``psCntInit)  -- initial value

def mutInit (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .register o c r d _ => .register o c r d 7
      | s => s }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``psCntCtl do onMap ``psCntCtl [(1, 8), (0, 1)] (mutInit (← modOf ``psCnt))

end Tests.Ved.U1PackedSeq2Check
