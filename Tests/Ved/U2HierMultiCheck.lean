import Tools.VedU2HierRegEntry
import Tests.Ved.U2HierWireCheck
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for H3-open: SEVERAL child instances whose data inputs are computed from the parent's register state, the
child outputs feeding the registers

`sha512BlockHW` (R193 `synth_sha512Block_out0`, R194 `synth_sha512Block_done`): the child `kMux` is called inside the
`circuit do` on the round counter, twice (two instances), and its output feeds the working registers' next values.  The
declaration is not one call of the child, so the H2c-state method (the declaration IS the call; the call is dead in the
loop) does not apply.  H3-open (`Tools/VedU2HierMultiGen.lean`, notes/ved/VED-HIER-H3OPEN.md) builds the open parent with every
call replaced by an oracle and proves, in the kernel, that the declaration IS that open parent at the oracle the real
children give along the declaration's own loop (`ved_open_…_eq`, from `Tools.VedU2HierMulti.loop_knot`).  The statement
`U2HRStmt` is unchanged.

After `#ved_u2_hier` the facts are checked independently of the entry: the stored type of the theorem is, as an `Expr`
compared with `==`, `U2HRStmt <decl>.ved_contract <decl>.ved_mod <decl>.ved_design <decl>`, its axioms are within
`propext`, `Classical.choice`, `Quot.sound`, and the equation and the loop knot are theorems with standard axioms.

* `multiTwo`: the SAME child on two different state nets (`cnt` and `cnt - 1`), both outputs feed a register;
* `multiShared`: the same child on ONE net, in the next values of two registers (two instances, one class: the shape of
  sha512's `kMux`);
* `multiKids`: two DIFFERENT children, each on its own register.

The CONTROLS run the checker on the real synthesis `(m, d)` of a copy with ONE piece altered; each is refused at a named
stage and leaves nothing behind.
-/

namespace Tests.Ved.U2HierMultiCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry Tests.Ved.U2HierWireCheck

/-! ## Declarations -/

@[hardware_module]
def mkA (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 3#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

@[hardware_module]
def mkB (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 5#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

/-- The same child on two different state nets; both outputs feed `acc`. -/
def multiTwo (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let cnt ← Signal.reg 0#4
    let acc ← Signal.reg 0#4
    let cntS := (cnt : Signal defaultDomain (BitVec 4))
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let k1 := mkA cntS
    let k2 := mkA (cntS - (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    cnt <~ (cntS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    acc <~ Signal.mux start inp (accS + k1 + k2 : Signal defaultDomain (BitVec 4))
    return accS

/-- A copy for the controls (never accepted itself, so nothing is left under its name). -/
def multiTwoRef (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let cnt ← Signal.reg 0#4
    let acc ← Signal.reg 0#4
    let cntS := (cnt : Signal defaultDomain (BitVec 4))
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let k1 := mkA cntS
    let k2 := mkA (cntS - (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    cnt <~ (cntS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    acc <~ Signal.mux start inp (accS + k1 + k2 : Signal defaultDomain (BitVec 4))
    return accS

/-- One net, two uses (two registers): the shape of sha512's `kMux`. -/
def multiShared (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let cnt ← Signal.reg 0#4
    let a ← Signal.reg 0#4
    let b ← Signal.reg 0#4
    let cntS := (cnt : Signal defaultDomain (BitVec 4))
    let aS := (a : Signal defaultDomain (BitVec 4))
    let bS := (b : Signal defaultDomain (BitVec 4))
    let k := mkA cntS
    cnt <~ (cntS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    a <~ Signal.mux start inp (aS + k : Signal defaultDomain (BitVec 4))
    b <~ Signal.mux start inp (bS + aS + k : Signal defaultDomain (BitVec 4))
    return bS

/-- Two different children, each on its own register. -/
def multiKids (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let cnt ← Signal.reg 0#4
    let acc ← Signal.reg 0#4
    let cntS := (cnt : Signal defaultDomain (BitVec 4))
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let k1 := mkA cntS
    let k2 := mkB accS
    cnt <~ (cntS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    acc <~ Signal.mux start inp (k1 + k2 : Signal defaultDomain (BitVec 4))
    return accS

/-- A copy for the controls. -/
def multiKidsRef (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let cnt ← Signal.reg 0#4
    let acc ← Signal.reg 0#4
    let cntS := (cnt : Signal defaultDomain (BitVec 4))
    let accS := (acc : Signal defaultDomain (BitVec 4))
    let k1 := mkA cntS
    let k2 := mkB accS
    cnt <~ (cntS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    acc <~ Signal.mux start inp (k1 + k2 : Signal defaultDomain (BitVec 4))
    return accS

/-! ## Helpers -/

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
    for sfx in ["_eq", "_knot"] do
      let n := decl ++ Name.mkSimple (openSuf ++ sfx)
      let some (.thmInfo _) := (← getEnv).find? n | throwError "{n} is not a theorem"
      std3Only n
    logInfo m!"u2 hier multi OK: {(regsOf m.body).length} parent registers, {(m.body.filter fun s => match s with | .inst .. => true | _ => false).length} instances, children {", ".intercalate (d.modules.map (·.name))}"

/-! ## Positives -/

/-- info: u2 hier multi OK: 2 parent registers, 4 instances, children Tests.Ved.U2HierMultiCheck.mkA -/
#guard_msgs in
run_cmd checkRow ``multiTwo

/-- info: u2 hier multi OK: 3 parent registers, 2 instances, children Tests.Ved.U2HierMultiCheck.mkA -/
#guard_msgs in
run_cmd checkRow ``multiShared

/-- info: u2 hier multi OK: 2 parent registers, 4 instances, children Tests.Ved.U2HierMultiCheck.mkA, Tests.Ved.U2HierMultiCheck.mkB -/
#guard_msgs in
run_cmd checkRow ``multiKids

/-! ## The closed run equals the declaration (concrete inputs, the children inside the run) -/

def inS (t : Nat) (n : String) : Nat :=
  if n == "_gen_start" then [1, 0, 0, 1, 0, 0, 0, 1, 0, 0].getD t 0
  else if n == "_gen_inp" then [5, 0, 0, 9, 0, 0, 0, 3, 0, 0].getD t 0
  else if n == "clk" then t % 2 else 0

def startSig : Signal defaultDomain Bool := ⟨fun t => [1, 0, 0, 1, 0, 0, 0, 1, 0, 0].getD t 0 == 1⟩
def inpSig : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 ([5, 0, 0, 9, 0, 0, 0, 3, 0, 0].getD t 0)⟩

def closedEq (decl : Name) (f : Signal defaultDomain Bool → Signal defaultDomain (BitVec 4) → Signal defaultDomain (BitVec 4)) :
    CommandElabM Unit := do
  let (m, d) ← synthOf decl
  let a := outsOf d m inS 10
  let e := (List.range 10).map fun t => ((f startSig inpSig).val t).toNat
  unless a == some e do throwError "closed run of {decl}: {a}, declaration {e}"
  logInfo m!"closed run = declaration: {e}"

/-- info: closed run = declaration: [0, 5, 12, 5, 9, 6, 5, 6, 3, 8] -/
#guard_msgs in
run_cmd closedEq ``multiTwo multiTwo

/-- info: closed run = declaration: [0, 5, 12, 5, 9, 6, 5, 6, 3, 8] -/
#guard_msgs in
run_cmd closedEq ``multiTwoRef multiTwoRef

/-! ## Controls: ONE piece altered, refused at a named stage, nothing left -/

/- Names in the synthesised `multiTwoRef`: parent registers `_tmp_a_4` (cnt) and `_tmp_a_15` (acc), their input nets
`_tmp_reg_input_3` (cnt + 1) and `_tmp_reg_input_14`; the nets `_tmp_arg1_1` (cnt), `_tmp_arg0_11` (cnt - 1) and
`_tmp_s_7` (acc) feed the four instances of `mkA` (instance numbers 0..3: reading cnt, cnt - 1, cnt, cnt - 1; output
wire of instance 0: `_tmp_op_b_9`).  In `multiKidsRef`: instances 0 (`mkA` on cnt, `_tmp_arg1_1`), 1 (`mkB` on acc,
`_tmp_arg0_9`), 2, 3 their copies. -/

def mkAName : String := "Tests.Ved.U2HierMultiCheck.mkA"
def mkBName : String := "Tests.Ved.U2HierMultiCheck.mkB"

def controls : CommandElabM Unit := do
  let (m, d) ← synthOf ``multiTwoRef
  let name := ``multiTwoRef
  let set (ks : List Nat) (net : String) (b : List Stmt) : List Stmt :=
    ks.foldl (fun b k => setConnAt k "_gen_x" (.ref net) b) b
  -- TWO INSTANCES' ARGUMENTS EXCHANGED: the instance on `cnt` reads `cnt - 1` and the other way round
  expectRefused name "proof" "unsolved goals" { m with body := set [1, 3] "_tmp_arg1_1" (set [0, 2] "_tmp_arg0_11" m.body) } d
  -- ONE ARGUMENT CHANGED: all four instances read `cnt`, the body has two distinct calls
  expectRefused name "open" "cannot be paired" { m with body := set [1, 3] "_tmp_arg1_1" m.body } d
  -- ANOTHER REGISTER: the instances that read `cnt` read `acc`
  expectRefused name "kernel" "let-declaration type mismatch" { m with body := set [0, 2] "_tmp_op_a_8" m.body } d
  -- THE POST-UPDATE STATE: the instances that read `cnt` read its input net (its value one cycle later)
  expectRefused name "proof" "unsolved goals" { m with body := set [0, 2] "_tmp_reg_input_3" m.body } d
  -- A CONSTANT: the instances that read `cnt` read a constant
  expectRefused name "proof" "unsolved goals" { m with body := set [0, 2] "_tmp_arg2_2" m.body } d
  -- A CYCLE through an instance: its own output feeds its input
  expectRefused name "order" "combinational cycle" { m with body := set [0] "_tmp_op_b_9" m.body } d
  -- THE CHILD MODULES EXCHANGED: the instance on `cnt` is the child the declaration calls on `acc`, and the other way round
  let (m2, d2) ← synthOf ``multiKidsRef
  let swapMods : List Stmt → List Stmt := List.map fun s => match s with
    | .inst mn i cs => .inst (if mn == mkAName then mkBName else if mn == mkBName then mkAName else mn) i cs
    | s => s
  expectRefused ``multiKidsRef "kernel" "let-declaration type mismatch" { m2 with body := swapMods m2.body } d2

/-- info: u2 hier multi controls: 7 refused -/
#guard_msgs in
run_cmd do
  controls
  logInfo m!"u2 hier multi controls: 7 refused"

end Tests.Ved.U2HierMultiCheck
