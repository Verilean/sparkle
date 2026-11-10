import Tools.VedU1Entry

/-!
# Checks for the multi-output U1 entry (register-free, product of signals)

A result `Signal d A × Signal d B × …` (a `×`-tree whose leaves are `Signal
defaultDomain _`) is read from the declaration's TYPE.  The synthesizer names
the output ports `out_0`, `out_1`, nested `out_0_1`, … (`splitReturnLeaves`),
left-first; the entry derives that list from the declaration, requires it to be
EXACTLY the returned module's output names, and proves
`U1Stmt c m (fun xs => bundle2 (decl xs).1 (decl xs).2)` with the contract's
output ports in that order: every projection's port is checked against the
declaration's own projection.

A `Signal d (A × B)` result is ONE packed port (`out`) and stays refused; a
structure result is not supported (refused at `[table]`).
-/

namespace Tests.Ved.U1MultiOutCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

/-! ## Declarations -/

/-- two outputs of different widths -/
def mo2 (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 4) :=
  (a + b, (fun x => x.extractLsb' 0 4) <$> a)

/-- three outputs, right-nested -/
def mo3r (a : Signal defaultDomain (BitVec 8)) (b c : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) × (Signal defaultDomain Bool × Signal defaultDomain (BitVec 16)) :=
  (~~~a, (b, (fun x y => x ++ y) <$> a <*> a))

/-- three outputs, left-nested -/
def mo3l {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    (Signal dom (BitVec 8) × Signal dom (BitVec 8)) × Signal dom (BitVec 8) :=
  ((a &&& b, a ||| b), a ^^^ b)

/-- two outputs of the same width, and variants of them -/
def mw (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 8) := (a &&& b, a ||| b)
def mwSwap (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 8) := (a ||| b, a &&& b)
def mwVal (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 8) := (a &&& b, a ^^^ b)

/-- control targets: never run through the entry themselves, so that their
checker constants must not exist afterwards -/
def mwCtl (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 8) := (a &&& b, a ||| b)

/-- one packed port -/
def packed (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × BitVec 8) := bundle2 a b

/-- a register in a multi-output body -/
def moReg (a : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 8) :=
  (Signal.register 0#8 a, a)

structure PO where
  x : Signal defaultDomain (BitVec 8)
  y : Signal defaultDomain (BitVec 8)

def moRec (a b : Signal defaultDomain (BitVec 8)) : PO := { x := a &&& b, y := a ||| b }

/-! ## Positives: exact theorem type, ports in order, std3 axioms -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

/-- the statement term written out by hand (elaborated, not built by the entry) -/
def checkMulti (decl : Name) (stmtStx : Term) (ports : List String) : CommandElabM Unit := liftTermElabM do
  let (m, _, thm, nDom) ← vedU1EntryS decl
  let nm := Names.ofBase decl
  unless m.outputs.map (·.name) == ports do throwError "{decl}: ports {m.outputs.map (·.name)}"
  let stmt ← instantiateMVars (← Term.elabTerm stmtStx none)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not the expected U1Stmt\n{ti.type}\n{expected}"
  -- the contract's output list is the module's, in order
  let some (.defnInfo ci) := (← getEnv).find? nm.outs | throwError "no outs"
  unless ci.value == toExpr (m.outputs) do throwError "{decl}: ved_outs is not m.outputs"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  logInfo m!"multi OK {thm} {m.outputs.map (·.name)} {nDom}"

/-- info: multi OK Tests.Ved.U1MultiOutCheck.mo2.ved_u1 [out_0, out_1] 0 -/
#guard_msgs in
run_cmd checkMulti ``mo2
  (← `(fun a b => bundle2 (mo2 a b).1 (mo2 a b).2)) ["out_0", "out_1"]

/-- info: multi OK Tests.Ved.U1MultiOutCheck.mo3r.ved_u1 [out_0, out_1_0, out_1_1] 0 -/
#guard_msgs in
run_cmd checkMulti ``mo3r
  (← `(fun a b c => bundle2 (mo3r a b c).1 (bundle2 (mo3r a b c).2.1 (mo3r a b c).2.2)))
  ["out_0", "out_1_0", "out_1_1"]

/-- info: multi OK Tests.Ved.U1MultiOutCheck.mo3l.ved_u1 [out_0_0, out_0_1, out_1] 1 -/
#guard_msgs in
run_cmd checkMulti ``mo3l
  (← `(fun a b => bundle2 (bundle2 (mo3l defaultDomain a b).1.1 (mo3l defaultDomain a b).1.2) (mo3l defaultDomain a b).2))
  ["out_0_0", "out_0_1", "out_1"]

/-- info: multi OK Tests.Ved.U1MultiOutCheck.mw.ved_u1 [out_0, out_1] 0 -/
#guard_msgs in
run_cmd checkMulti ``mw
  (← `(fun a b => bundle2 (mw a b).1 (mw a b).2)) ["out_0", "out_1"]

/-! ## Controls: refused, no `ved_*` constant left -/

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

/-- the entry's checker on `decl` with a substituted module -/
def onModule (decl : Name) (m : Sparkle.IR.AST.Module) : TermElabM Unit := do
  let (stmt, nDom, names) ← stmtOf decl
  discard <| vedU1EntryOn decl stmt nDom names m

/-- entry-level refusals (the declaration itself) -/
def expectEntry (stage : String) (decl : Name) : CommandElabM Unit :=
  expectRefused stage decl (discard <| vedU1Entry decl)

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectEntry "multi-output" ``packed

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectEntry "multi-output" ``moReg

/-- info: refused [table], clean -/
#guard_msgs in
run_cmd expectEntry "table" ``moRec

-- one output dropped (port list and its assignment)
def mutDrop (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with outputs := m.outputs.dropLast
           body := m.body.filter fun s => match s with
             | .assign "out_1" _ => false
             | _ => true }

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``mwCtl do onModule ``mwCtl (mutDrop (← modOf ``mw))

-- the two same-width outputs swapped: the drivers exchange their ports
def mutSwap (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign "out_0" e => .assign "out_1" e
      | .assign "out_1" e => .assign "out_0" e
      | s => s }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``mwCtl do onModule ``mwCtl (mutSwap (← modOf ``mw))

-- the module of the declaration with the same widths but another value
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``mwCtl do onModule ``mwCtl (← modOf ``mwVal)

-- the swapped declaration's module (same widths, outputs exchanged)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``mwCtl do onModule ``mwCtl (← modOf ``mwSwap)

-- one output's value changed (same width): only the second driver is replaced
def mutValue (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with body := m.body.map fun s => match s with
      | .assign o (.op .or a) => if o == "out_1" then .assign o (.op .xor a) else s
      | s => s }

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``mwCtl do onModule ``mwCtl (mutValue (← modOf ``mw))

-- the module of another declaration (other port list)
/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``mwCtl do onModule ``mwCtl (← modOf ``mo3r)

-- a port-name mismatch: out_1 renamed
def mutRename (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with outputs := m.outputs.map fun p => if p.name == "out_1" then { p with name := "out_x" } else p
           body := m.body.map fun s => match s with
             | .assign "out_1" e => .assign "out_x" e
             | s => s }

/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``mwCtl do onModule ``mwCtl (mutRename (← modOf ``mw))

-- the checker itself, with a wrong port-name list for the right module
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefused "proof" ``mwCtl do
  let (stmt, _, _) ← stmtOf ``mwCtl
  discard <| checkU1E ``mwCtl ``mwCtl stmt (← modOf ``mw) .generated ["out_0", "out_x"]

-- the checker with ONE port name for two projections
/-- info: refused [multi-output], clean -/
#guard_msgs in
run_cmd expectRefused "multi-output" ``mwCtl do
  let (stmt, _, _) ← stmtOf ``mwCtl
  discard <| checkU1E ``mwCtl ``mwCtl stmt (← modOf ``mw) .generated

end Tests.Ved.U1MultiOutCheck
