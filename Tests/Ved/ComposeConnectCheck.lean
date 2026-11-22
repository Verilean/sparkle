import Tools.VedU2HierRegEntry
import Tools.VedComposeConnectGen
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for the cone connection (option `ved.compose.connect`, `Tools/VedComposeConnect*.lean`)

`multiTwo` (one child, two instance classes, four instances) and `multiShared` (one child on ONE net, three registers, a
right-nested register bundle) are accepted by `#ved_u2_hier` with the option on.  There is no old fallback in that mode: the
parent's `hloc` goal is closed by `reg_connect` / `out_connect` only (the generator returns before the per-cone `simp`
closers).  After the entry the facts are checked independently of it:

* the stored type is, as an `Expr` compared with `==`, `U2HRStmt <decl>.ved_contract <decl>.ved_mod <decl>.ved_design <decl>`;
* the module constant is the declaration's own synthesis (`synthesizeCombinational` run a second time, `==`), the design too;
* the axioms are within `propext`, `Classical.choice`, `Quot.sound`; the kernel accepted the theorem (it is in the environment);
* the child's real theorem constant occurs in the proof; the connection lemmas occur once per register and once for the port,
  and the same number of `VED COMPOSE CONNECT` log lines was emitted (the new path is observable).

CONTROLS: ONE piece altered, refused (entry level), and two kernel-evaluated refusals of the connection equation itself.
-/

namespace Tests.Ved.ComposeConnectCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

/-! ## Declarations (the same as `Tests/Ved/U2HierMultiCheck.lean`, copied: that module is a ~470 s import) -/

@[hardware_module]
def mkA (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 3#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

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

/-- A copy for the controls (never accepted itself). -/
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

/-- A copy for the controls. -/
def multiSharedRef (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
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

/-! ## Helpers -/

/-- How many distinct (maximal) application sites of the constant `c` the term has. -/
def countApps (e : Lean.Expr) (c : Name) : Nat := Id.run do
  let mut seen : Std.HashSet Lean.Expr := {}
  let mut todo : Array Lean.Expr := #[e]
  let mut n := 0
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .app f a =>
      if x.getAppFn.isConstOf c then
        n := n + 1
        for y in x.getAppArgs do todo := todo.push y
      else todo := todo.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return n

/-- Run the entry with the option on and check the result independently of the entry. -/
def checkRow (decl : Name) (kidThm : Name) (nRegs : Nat) : CommandElabM Unit := do
  unless Tools.VedComposeConnect.ved.compose.connect.get (← getOptions) do throwError "the option ved.compose.connect is not on"
  let nMsg0 := (← get).messages.toList.length
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  -- the new path is observable: one log line per connection
  let logs := ((← get).messages.toList.drop nMsg0).filter fun msg => msg.severity == .information
  let logTxt ← logs.mapM fun msg => msg.data.toString
  let conn := logTxt.filter fun s => (s.splitOn "VED COMPOSE CONNECT").length > 1
  modify fun s => { s with messages := (s.messages.toList.take nMsg0).foldl (fun l msg => l.add msg) {} }
  unless conn.length == nRegs + 1 do throwError "{decl}: {conn.length} connection log lines, expected {nRegs + 1}: {conn}"
  let (m2, d2) ← synthOf decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    -- the same artifact as the declaration's own synthesis
    unless decide (m = m2) && d.topModule == d2.topModule && decide (d.modules = d2.modules) do
      throwError "{decl}: the returned module/design differ from the declaration's own synthesis"
    let nm := HNames.ofBase decl
    let some ci := (← getEnv).find? nm.mod | throwError "{nm.mod} missing"
    unless ci.value! == toExpr m2 do throwError "{nm.mod} is not the declaration's own module"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    -- the child's REAL theorem is in the proof
    unless ti.value.getUsedConstants.contains kidThm do throwError "{thm}: the child theorem {kidThm} does not occur"
    let nr := countApps ti.value ``Tools.VedComposeConnect.reg_connect
    let no := countApps ti.value ``Tools.VedComposeConnect.out_connect
    unless nr == nRegs && no == 1 do throwError "{decl}: reg_connect sites {nr} (expected {nRegs}), out_connect sites {no} (expected 1)"
    logInfo m!"compose connect OK: {nRegs} registers by reg_connect, 1 port by out_connect, child theorem {kidThm}, std3, type ==, same artifact"

/-! ## Positives -/

/-- info: compose connect OK: 2 registers by reg_connect, 1 port by out_connect, child theorem Tests.Ved.ComposeConnectCheck.multiTwo.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd checkRow ``multiTwo `Tests.Ved.ComposeConnectCheck.multiTwo.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1 2

/-- info: compose connect OK: 3 registers by reg_connect, 1 port by out_connect, child theorem Tests.Ved.ComposeConnectCheck.multiShared.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd checkRow ``multiShared `Tests.Ved.ComposeConnectCheck.multiShared.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1 3

/-! ## Controls (entry level): ONE piece altered, refused at a named stage, nothing left -/

/- Names in the synthesised `multiTwoRef`: parent registers `_tmp_a_4` (cnt) and `_tmp_a_15` (acc), their input nets
`_tmp_reg_input_3` (cnt + 1) and `_tmp_reg_input_14`; the nets `_tmp_arg1_1` (cnt), `_tmp_arg0_11` (cnt - 1) feed the four
instances of `mkA` (numbers 0..3: reading cnt, cnt - 1, cnt, cnt - 1; output wire of instance 0: `_tmp_op_b_9`). -/

def mapRegs (f : String → Stmt → Stmt) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
  | .register o .. => f o s
  | s => s

def setInit (v : Int) : Stmt → Stmt
  | .register o k r e _ => .register o k r e v
  | s => s

def expectRefusedT (decl : Name) (stage : String) (needle : String) (m : Sparkle.IR.AST.Module) (d : Design)
    (tamper : Phase1 → CommandElabM Phase1) : CommandElabM Unit := do
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let r ← try
      discard <| checkU2HR decl stmt nDom m d none tamper
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  let pre := s!"VED U1 REFUSED {decl} [{stage}]"
  match r with
  | none => throwError "{decl}: expected a refusal at [{stage}], the checker ACCEPTED"
  | some msg =>
    if stage == "?" then logInfo m!"{msg.take 420}"
    else unless msg.startsWith pre do throwError "expected {pre} (needle `{needle}`), got: {msg}"
    if needle == "?" then pure ()
    else unless (msg.splitOn needle).length > 1 do throwError "the refusal does not name `{needle}`: {msg}"
  let after ← localConsts
  let added := after.toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"

def controls : CommandElabM Unit := do
  let (m, d) ← synthOf ``multiTwoRef
  let name := ``multiTwoRef
  let set (ks : List Nat) (net : String) (b : List Stmt) : List Stmt :=
    ks.foldl (fun b k => setConnAt k "_gen_x" (.ref net) b) b
  let noT : Phase1 → CommandElabM Phase1 := fun p => pure p
  -- WRONG WIRING: two instances' arguments exchanged (the instance on `cnt` reads `cnt - 1` and the other way round)
  expectRefusedT name "proof" "unsolved goals" { m with body := set [1, 3] "_tmp_arg1_1" (set [0, 2] "_tmp_arg0_11" m.body) } d noT
  -- INSTANCE CORRESPONDENCE SWAPPED: every instance is paired with the other call
  expectRefusedT name "proof" "unsolved goals" m d fun p => pure { p with insts := p.insts.map fun ii => { ii with call := 1 - ii.call } }
  -- WIDTH MISMATCH (port): the declared width of an instance output wire is not its port's
  expectRefusedT name "hier-shape" "width mismatch" { m with wires := m.wires.map fun w =>
    if w.name == "_tmp_op_b_9" then { w with ty := .bitVector 5 } else w } d noT
  -- WIDTH MISMATCH (cone): an internal wire's declared width is not the width of its right-hand side (`WOKb` fails, so the
  -- connection's width side condition is refused)
  expectRefusedT name "proof" "?" { m with wires := m.wires.map fun w =>
    if w.name == "_tmp_mux_else_5" then { w with ty := .bitVector 5 } else w } d noT
  -- MUTATED INITIAL VALUE: a register starts at 5, the declaration's loop at 0
  expectRefusedT name "proof" "unsolved goals" { m with body := mapRegs (fun o s => if o == "_tmp_a_15" then setInit 5 s else s) m.body } d noT
  -- TIME SHIFT: the instances that read `cnt` read its input net (its value one cycle later)
  expectRefusedT name "proof" "unsolved goals" { m with body := set [0, 2] "_tmp_reg_input_3" m.body } d noT
  -- RESET SHIFT: a register's reset port is another input
  expectRefusedT name "hier-shape" "clock/reset" { m with body := mapRegs (fun o s => if o == "_tmp_a_15" then
      (match s with | .register o' k (_, rk) e i => .register o' k ("_gen_start", rk) e i | s => s) else s) m.body } d noT

/-- info: compose connect controls (entry level): 7 refused -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd do
  controls
  logInfo m!"compose connect controls (entry level): 7 refused"

/-! ## Controls of the connection equation itself, evaluated by the KERNEL on the accepted `multiTwo` -/

def elabText (txt : String) : TermElabM Lean.Expr := do
  match Lean.Parser.runParserCategory (← getEnv) `term txt "<check>" with
  | .ok stx =>
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | .error err => throwError err

def kernelEqual (a b : Lean.Expr) : TermElabM Bool := do
  match Lean.Kernel.isDefEq (← getEnv) {} a b with
  | .ok r => pure r
  | .error _ => throwError "kernel error"

def eqnControls : CommandElabM Unit := liftTermElabM do
  let M := "Tests.Ved.ComposeConnectCheck.multiTwo"
  let nm := s!"{M}.ved_open_Tests_Ved_ComposeConnectCheck_multiTwo_nm"
  let fid1 := Lean.mkConst (`Tests.Ved.ComposeConnectCheck.multiTwo ++ `ved_open_Tests_Ved_ComposeConnectCheck_multiTwo_deep_fidelity_r1)
  -- the literal is read from the TYPE of the fidelity theorem
  let L := (← inferType fid1).appArg!
  let tabTxt (o0 o1 : Nat) :=
    s!"([(\"_tmp_a_4\", 0), (\"_tmp_a_15\", 1), (\"_gen_start\", 2), (\"_gen_inp\", 3), (\"_tmp_op_b_9\", {o0}), (\"_tmp_op_b_12\", {o1}), (\"_gen_k1\", {o0}), (\"_gen_k2\", {o1})] : List (String × Nat))"
  let cone := s!"(Tools.VedComposeResearch.bn (Tools.VedU1Contract.declWidth {M}.ved_mod) 28 (Tools.VedComposeConnect.flat 28 (Tools.VedComposeResearch.inl (Tools.VedComposeResearch.Atab {M}.ved_mod {M}.ved_body) 28 (Sparkle.IR.AST.Expr.ref \"_tmp_reg_input_14\"))))"
  let ren (o0 o1 : Nat) := s!"Tools.VedComposeConnect.renE (Tools.VedComposeConnect.tauOf {nm} {tabTxt o0 o1}) {cone}"
  -- the real correspondence: the cone IS the fidelity literal
  unless ← kernelEqual (← elabText (ren 4 5)) L do throwError "control void: the real table does not give the literal"
  -- instance correspondence swapped (the oracle slots exchanged): refused
  if ← kernelEqual (← elabText (ren 5 4)) L then throwError "the swapped correspondence is accepted"
  -- width table (W): the real one passes `tabW`, one slot of the wrong width does not
  let tw (g : String) := s!"Tools.VedComposeConnect.tabW {g} (Tools.VedU1Contract.declWidth {M}.ved_mod) {tabTxt 4 5} {cone}"
  unless ← kernelEqual (← elabText (tw "([4, 4] ++ [1, 4, 4, 4])")) (toExpr true) do throwError "control void: tabW rejects the real widths"
  if ← kernelEqual (← elabText (tw "([4, 4] ++ [1, 4, 5, 4])")) (toExpr true) then throwError "tabW accepts a wrong width"
  -- a leaf that is not in the table is refused by `tabW`
  let tw2 := s!"Tools.VedComposeConnect.tabW ([4, 4] ++ [1, 4, 4, 4]) (Tools.VedU1Contract.declWidth {M}.ved_mod) ([(\"_tmp_a_4\", 0)] : List (String × Nat)) {cone}"
  if ← kernelEqual (← elabText tw2) (toExpr true) then throwError "tabW accepts a cone with a leaf outside the table"
  logInfo m!"compose connect equation controls: 1 accepted, 4 refused by the kernel"

/-- info: compose connect equation controls: 1 accepted, 4 refused by the kernel -/
#guard_msgs in
run_cmd eqnControls

end Tests.Ved.ComposeConnectCheck
