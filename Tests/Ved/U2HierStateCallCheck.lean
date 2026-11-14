import Tools.VedU2HierRegEntry
import Tests.IP.Net.HTTPTest
import Tests.Ved.U2HierWireCheck
import IP.Net.HTTP
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for H2c-state: a child call whose argument is the parent's REGISTER state

R223 `synth_httpGetByte` (`Tests/IP/Net/HTTPTest.lean`): `(httpGetEmitter trigger).byte` is `httpGetByte cnt`
where `cnt` is the emitter's counter register (`burstEmit`: the child is passed as a function and applied to
the register inside `circuit do`).  `synth_httpGetByte` is PRIVATE to its module, so the entry cannot be run
on it from another module; `getByteCopy` below is the same declaration, and a check compares the two
definitions' VALUES as `Expr`s (`==`).  The run on the original declaration itself is the same command
appended to that module (see `docs/VED-HIER-H2C-STATE.md`).

After `#ved_u2_hier` the facts are checked independently of the entry: the stored type of the theorem is, as an
`Expr` compared with `==`, `U2HRStmt <decl>.ved_contract <decl>.ved_mod <decl>.ved_design <decl>` (the H2b
statement, UNCHANGED, no binder added), its axioms are within `propext`, `Classical.choice`, `Quot.sound`,
and the kernel equation `decl xs = g a` of the declaration with its call is a theorem with standard axioms.

`stFam` is a small family with three parent registers (`a`, `b = a` delayed, `c` feeding `a`) and a child with
two data ports reading `a` and `b`.  The CONTROLS run the checker on the real synthesis `(m, d)` of `stFam`
with ONE piece altered; each is refused at a named stage and leaves nothing behind.
-/

namespace Tests.Ved.U2HierStateCallCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry Tests.Ved.U2HierWireCheck

/-! ## Declarations -/

@[hardware_module]
def diff2 (x y : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := x - y

@[hardware_module]
def sum2 (x y : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) := x + y

/-- The child reads two registers: `a` and `b` (`a` one cycle late); `a`'s next value reads `c`. -/
def stFam (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let a ← Signal.reg 0#4
    let b ← Signal.reg 0#4
    let c ← Signal.reg 1#4
    let aS := (a : Signal defaultDomain (BitVec 4))
    let cS := (c : Signal defaultDomain (BitVec 4))
    a <~ Signal.mux trigger (aS + cS) aS
    b <~ aS
    c <~ cS + 1#4
    return diff2 aS (b : Signal defaultDomain (BitVec 4))

/-- The declaration the CONTROLS alter (never accepted itself, so nothing is left under its name). -/
def stRef (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let a ← Signal.reg 0#4
    let b ← Signal.reg 0#4
    let c ← Signal.reg 1#4
    let aS := (a : Signal defaultDomain (BitVec 4))
    let cS := (c : Signal defaultDomain (BitVec 4))
    a <~ Signal.mux trigger (aS + cS) aS
    b <~ aS
    c <~ cS + 1#4
    return diff2 aS (b : Signal defaultDomain (BitVec 4))

open Sparkle.IP.Net.HTTP in
/-- R223, as in `Tests/IP/Net/HTTPTest.lean`. -/
def getByteCopy (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  (httpGetEmitter trigger).byte

/-! ## Helpers -/

def privateNamed (user : Name) : CoreM Name := do
  let env ← getEnv
  let r := env.constants.fold (init := (none : Option Name)) fun acc n _ =>
    if acc.isNone && privateToUserName? n == some user then some n else acc
  match r with
  | some n => pure n
  | none => throwError "no private declaration {user}"

/-- Run the stateful hierarchical entry on `decl` and check the result independently of the entry. -/
def checkRow (decl : Name) : CommandElabM Unit := do
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    unless !(regsOf m.body).isEmpty do throwError "{decl}: the parent has no register"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    let openSuf := "ved_open_" ++ "_".intercalate (decl.components.map toString)
    let n := decl ++ Name.mkSimple (openSuf ++ "_ceq")
    let some (.thmInfo _) := (← getEnv).find? n | throwError "{n} is not a theorem"
    std3Only n
    logInfo m!"u2 hier state OK: {(regsOf m.body).length} parent registers, children {", ".intercalate (d.modules.map (·.name))}"

/-! ## Positives -/

/-- info: u2 hier state OK: 3 parent registers, children Tests.Ved.U2HierStateCallCheck.diff2 -/
#guard_msgs in
run_cmd checkRow ``stFam

/-- info: u2 hier state OK: 1 parent registers, children Sparkle.IP.Net.HTTP.httpGetByte -/
#guard_msgs in
run_cmd checkRow ``getByteCopy

/-- info: getByteCopy is the value of synth_httpGetByte -/
#guard_msgs in
run_cmd do
  let orig ← liftCoreM (privateNamed `synth_httpGetByte)
  let some (.defnInfo a) := (← getEnv).find? orig | throwError "no original"
  let some (.defnInfo b) := (← getEnv).find? ``getByteCopy | throwError "no copy"
  unless a.value == b.value && a.type == b.type do throwError "the copy differs from the original declaration"
  logInfo m!"getByteCopy is the value of synth_httpGetByte"

/-! ## The closed run equals the declaration (concrete trigger, the child inside the run) -/

def trigS (t : Nat) (n : String) : Nat :=
  if n == "_gen_trigger" then [1, 0, 1, 1, 0, 0, 1, 0, 0, 0].getD t 0 else if n == "clk" then t % 2 else 0

def trigSig : Signal defaultDomain Bool := ⟨fun t => [1, 0, 1, 1, 0, 0, 1, 0, 0, 0].getD t 0 == 1⟩

/-- info: closed run = declaration: stFam [0, 1, 0, 3, 4, 0, 0, 7, 0, 0] -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``stFam
  let a := outsOf d m trigS 10
  let e := (List.range 10).map fun t => ((stFam trigSig).val t).toNat
  unless a == some e do throwError "closed run of stFam: {a}, declaration {e}"
  logInfo m!"closed run = declaration: stFam {e}"

/-! ## Controls: ONE piece altered, refused at a named stage, nothing left -/

/- Names in the synthesised `stFam`: registers `_tmp_a_7` (a), `_tmp_a_9` (b), `_tmp_a_12` (c); the register
bundle is sliced into `_tmp_op_a_2` (a) and `_tmp_arg1_19` (b); the child's instance (`diff2`, ports `_gen_x`,
`_gen_y`, output `_gen_out`); `_tmp_reg_input_6` is `a`'s input net. -/

def controls : CommandElabM Unit := do
  let (m, d) ← synthOf ``stRef
  let name := ``stRef
  -- ANOTHER REGISTER: the child's first port reads `c`
  expectRefused name "kernel" "let-declaration type mismatch" { m with body := setConnAt 0 "_gen_x" (.ref "_tmp_a_12") m.body } d
  -- THE POST-UPDATE STATE: the first port reads the register `a`'s input net (its value one cycle later)
  expectRefused name "proof" "errors were logged while elaborating the proof" { m with body := setConnAt 0 "_gen_x" (.ref "_tmp_reg_input_6") m.body } d
  -- A ONE-CYCLE SHIFT: the first port reads `b` (`a` one cycle late), the second reads `a` (`b` one cycle early)
  expectRefused name "kernel" "let-declaration type mismatch" { m with body := setConnAt 0 "_gen_x" (.ref "_tmp_a_9") m.body } d
  expectRefused name "kernel" "let-declaration type mismatch" { m with body := setConnAt 0 "_gen_y" (.ref "_tmp_op_a_2") m.body } d
  -- THE CALL'S ARGUMENTS EXCHANGED
  expectRefused name "kernel" "let-declaration type mismatch"
    { m with body := setConnAt 0 "_gen_y" (.ref "_tmp_op_a_2") (setConnAt 0 "_gen_x" (.ref "_tmp_arg1_19") m.body) } d
  -- A CYCLE through the instance: its own output feeds its input
  expectRefused name "order" "combinational cycle"
    { m with body := setConnAt 0 "_gen_x" (.ref "_gen_out") m.body } d
  -- THE CHILD MODULE (and its theorem) EXCHANGED: the design holds `sum2` where the declaration calls `diff2`
  let (ms, _) ← synthOf ``sum2
  expectRefused name "open" "does not reduce to a call of"
    { m with body := m.body.map fun s => match s with
        | .inst _ i cs => .inst ms.name i cs
        | s => s } { d with modules := [ms] }

/-- info: u2 hier state controls: 7 refused -/
#guard_msgs in
run_cmd do
  controls
  logInfo m!"u2 hier state controls: 7 refused"

end Tests.Ved.U2HierStateCallCheck
