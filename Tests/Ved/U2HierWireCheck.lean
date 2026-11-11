import Tools.VedU2HierRegEntry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for H2c: an instance's DATA inputs read from a NET computed from the parent's data inputs
(`Tools/VedU2HierNet.lean`, `Tools/VedU2HierRegEntry.lean`)

Nothing here is a row of the 327 inventory, claims a frozen statement, or a release.  The statement
is still `U2HRStmt` (compared below with the checker's own expected term, and an `example` spells out
the type); no binder was added.

What H2c adds to H2b: a child DATA port may be connected to a parent wire that is a pure function of
the parent DATA inputs (an assigned wire all of whose reads are, recursively, data inputs or such
wires).  The child's own theorem is applied to the stream that wire carries (`kid_inst_net`); the
tie of that stream to the stream the declaration's call expects (`F2`, docs/VED-HIER-H2-DESIGN.md
§2.1) is a goal the generated proof discharges from the closed run (`closed_run_asgOf`: every
assignment holds in every cycle's environment) — a wrong net is refused at `[proof]`.

NOT covered (refused at `[conns]`, kept): a data port read from a parent REGISTER output (in the
real rows the register is a `Signal.loop`, so the declaration's call argument is bound inside the
loop and has no closed Lean term over the inputs), from another instance's output, from the clock or
reset.  The shapes of the real rows (a counter register feeding a table child; a checksum child
feeding a byte child) are copied here as controls.

* POSITIVES (exact type, standard axioms, closed run equals the declaration);
* CONTROLS: the checker on the returned `(m, d)` of a real synthesis with ONE piece altered, each
  refused at a named stage and leaving nothing behind; entry-level refusals of the real shapes;
  positive controls (a consistent renaming of the net wires, a reordered body) are ACCEPTED.
-/

namespace Tests.Ved.U2HierWireCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
  Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry

/-! ## Declarations -/

@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

/-- A two-input register child (asymmetric in its inputs). -/
@[hardware_module]
def acc2 (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x - y
    return r

#verify_elab_deep accMod
#verify_elab_deep acc2

/-- One derived data input (`a + b`) into a parent with a register. -/
@[hardware_module]
def wireAdd (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod (a + b)
    p <~ u - p
    return (p : Signal defaultDomain (BitVec 8))

/-- Two derived data ports of one instance, asymmetric (`a + b`, `a - b`); a swap is observable. -/
@[hardware_module]
def wireTwo (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := acc2 (a + b) (a - b)
    p <~ u - p
    return (p : Signal defaultDomain (BitVec 8))

/-- A constant mask, a net shared through a `let`, two instances of one child (the synthesiser
creates a third, identical instance). -/
@[hardware_module]
def wireShared (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let s := a + b
    let u := accMod (s - a)
    let v := accMod (a &&& 15#8)
    p <~ u + v - p
    return (p : Signal defaultDomain (BitVec 8))

/-- Two instances of different children, derived and plain inputs mixed, two parent registers. -/
@[hardware_module]
def wireMix (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := acc2 a (b + a)
    let v := accMod b
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

/-- The declaration the CONTROLS alter (never accepted itself, so nothing is left under its name). -/
@[hardware_module]
def wireRef (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := acc2 (a + b) (a - b)
    let v := accMod (b + a)
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

/-- The same declaration under other names, one per positive control. -/
@[hardware_module]
def wireRn (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := acc2 (a + b) (a - b)
    let v := accMod (b + a)
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

@[hardware_module]
def wireOrd (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := acc2 (a + b) (a - b)
    let v := accMod (b + a)
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

/-! ### The shapes of the real rows (copies), refused at `[conns]` -/

/-- R223 / R92 / R220 shape: a counter register feeds the child that looks the byte up
(`httpGetByte cnt`).  Here the child is `accMod`. -/
@[hardware_module]
def shapeBurst (trigger : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    let cntSig := (cnt : Signal defaultDomain (BitVec 8))
    let byteOut := accMod cntSig
    cnt <~ cnt + trigger
    return byteOut

/-- R246 / R210 shape: the child reads a register's output through an expression of it. -/
@[hardware_module]
def shapeExpr (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let ph ← Signal.reg 0#8
    let byteOut := accMod ((ph : Signal defaultDomain (BitVec 8)) + 1#8)
    ph <~ ph + a
    return byteOut

/-- R230 / R227 shape: a latched field mixed with a live input feeds the child
(`mux start totalLen tlSig`), and a second child reads the first one's output (chained). -/
@[hardware_module]
def shapeChain (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let lat ← Signal.reg 0#8
    let ck := accMod (lat : Signal defaultDomain (BitVec 8))
    let bt := acc2 ck a
    lat <~ lat + b
    return bt

/-- A chained instance input without any register read: the second child reads the first one's
output (outside H2c). -/
@[hardware_module]
def shapeChained (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let ck := accMod (a + b)
    let bt := acc2 ck a
    p <~ bt + p
    return (p : Signal defaultDomain (BitVec 8))

/-- A derived input in a parent WITHOUT registers stays outside (H2a). -/
@[hardware_module]
def shapeNoReg (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  accMod (a + b)

/-! ## Helpers (as in `Tests/Ved/U2HierRegCheck.lean`) -/

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- MACHINE check: every axiom in the reachable closure of `n` is one of the standard three. -/
def std3Only (n : Name) : CoreM Unit := do
  let axs ← collectAxioms n
  unless axs.all (std3.contains ·) do throwError "{n}: axioms outside the standard three: {axs}"

/-- The checker's exact expected statement for `decl` (the H2b statement, UNCHANGED). -/
def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

def checkOk (decl : Name) : CommandElabM Unit := do
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    unless !(regsOf m.body).isEmpty do throwError "{decl}: the parent has no register"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    for n in [decl ++ Name.mkSimple ("ved_open_" ++ "_".intercalate (decl.components.map toString) ++ "_eq")] do
      let some (.thmInfo _) := (← getEnv).find? n | throwError "{n} is not a theorem"
      std3Only n
    logInfo m!"u2 hier wire OK {thm}: {(regsOf m.body).length} parent registers, children {", ".intercalate (d.modules.map (·.name))}"

def synthOf (decl : Name) : CommandElabM (Sparkle.IR.AST.Module × Design) := liftTermElabM do
  Sparkle.Compiler.Elab.synthesizeCombinational decl

/-! ## Positives -/

/-- info: u2 hier wire OK Tests.Ved.U2HierWireCheck.wireAdd.ved_u1: 1 parent registers, children Tests.Ved.U2HierWireCheck.accMod -/
#guard_msgs in
run_cmd checkOk ``wireAdd

/-- info: u2 hier wire OK Tests.Ved.U2HierWireCheck.wireTwo.ved_u1: 1 parent registers, children Tests.Ved.U2HierWireCheck.acc2 -/
#guard_msgs in
run_cmd checkOk ``wireTwo

/-- info: u2 hier wire OK Tests.Ved.U2HierWireCheck.wireShared.ved_u1: 1 parent registers, children Tests.Ved.U2HierWireCheck.accMod -/
#guard_msgs in
run_cmd checkOk ``wireShared

/-- info: u2 hier wire OK Tests.Ved.U2HierWireCheck.wireMix.ved_u1: 2 parent registers, children Tests.Ved.U2HierWireCheck.acc2, Tests.Ved.U2HierWireCheck.accMod -/
#guard_msgs in
run_cmd checkOk ``wireMix

/-! ## The theorem's type is unchanged: `U2HRStmt` -/

example : U2HRStmt wireAdd.ved_contract wireAdd.ved_mod wireAdd.ved_design wireAdd :=
  wireAdd.ved_u1

example : U2HRStmt wireTwo.ved_contract wireTwo.ved_mod wireTwo.ved_design wireTwo ↔
    (CorrStmt wireTwo.ved_contract ∧ ShapeCore wireTwo.ved_contract wireTwo.ved_mod ∧
      wireTwo.ved_contract.clkRst = designClkRst wireTwo.ved_design wireTwo.ved_mod ∧
      HierShapeS wireTwo.ved_design wireTwo.ved_mod = true ∧
      WidthStmt wireTwo.ved_contract wireTwo.ved_mod ∧
      (∃ b, OrderOkHS wireTwo.ved_design wireTwo.ved_mod b = true) ∧
      (∀ x ∈ wireTwo.ved_design.modules, OrderStmt x) ∧
      (∃ arr, AdmArr wireTwo.ved_design wireTwo.ved_mod arr) ∧
      ∀ arr, AdmArr wireTwo.ved_design wireTwo.ved_mod arr →
        ∀ ins, InputsOk wireTwo.ved_contract wireTwo.ved_mod ins → ∀ K, ∃ envs,
          runHS wireTwo.ved_design arr wireTwo.ved_mod (seedFwd wireTwo.ved_mod K ins) K
            (st0H wireTwo.ved_design wireTwo.ved_mod) = some envs ∧
          ∀ t, t < K → ∀ o ∈ wireTwo.ved_contract.outputs, ∃ env, envs[t]? = some env ∧
            env o.name = srcOf wireTwo.ved_contract wireTwo ins o.name t) := Iff.rfl

/-! ## The closed run on concrete values equals the declaration -/

def arrOf (d : Design) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module → List Stmt :=
  fun x => if x == m then orderBodyH d x.body else Tools.VedU1Entry.orderBody x.body

def inpS (t : Nat) (n : String) : Nat :=
  if n == "_gen_a" then [1, 2, 3, 4, 5].getD t 0 else if n == "_gen_b" then [10, 20, 30, 40, 50].getD t 0
  else if n == "clk" then t % 2 else 0

def outsOf (d : Design) (m : Sparkle.IR.AST.Module) (inp : Nat → String → Nat) (K : Nat) :
    Option (List Nat) :=
  (runHS d (arrOf d m) m (seedFwd m K inp) K (st0H d m)).map (·.map fun e => e "out")

def sigA : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4, 5].getD t 0)⟩
def sigB : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40, 50].getD t 0)⟩

def declOuts (f : Signal defaultDomain (BitVec 8) → Signal defaultDomain (BitVec 8) → Signal defaultDomain (BitVec 8))
    (K : Nat) : List Nat := (List.range K).map fun t => ((f sigA sigB).val t).toNat

/-- info: closed run = declaration: wireAdd [0, 0, 11, 22, 44, 66] -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``wireAdd
  let a := outsOf d m inpS 6
  let e := declOuts wireAdd 6
  unless a == some e do throwError "closed run of wireAdd: {a}, declaration {e}"
  logInfo m!"closed run = declaration: wireAdd {e}"

/-- info: closed run = declaration: wireTwo [0, 0, 20, 40, 80, 120] -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``wireTwo
  let a := outsOf d m inpS 6
  let e := declOuts wireTwo 6
  unless a == some e do throwError "closed run of wireTwo: {a}, declaration {e}"
  logInfo m!"closed run = declaration: wireTwo {e}"

/-- info: closed run = declaration: wireMix [255, 245, 205, 135, 15, 101] -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``wireMix
  let a := outsOf d m inpS 6
  let e := declOuts wireMix 6
  unless a == some e do throwError "closed run of wireMix: {a}, declaration {e}"
  logInfo m!"closed run = declaration: wireMix {e}"

/-! ## Controls: ONE piece altered, refused at a named stage, nothing left -/

def localConsts : CommandElabM NameSet := do
  return (← getEnv).constants.map₂.toList.foldl (fun s (n, _) => s.insert n) {}

def expectRefused (decl : Name) (stage : String) (needle : String) (m : Sparkle.IR.AST.Module)
    (d : Design) : CommandElabM Unit := do
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let r ← try
      discard <| checkU2HR decl stmt nDom m d none
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  let pre := s!"VED U1 REFUSED {decl} [{stage}]"
  match r with
  | none => throwError "{decl}: expected a refusal at [{stage}], the checker ACCEPTED"
  | some msg =>
    unless msg.startsWith pre do throwError "expected {pre} (needle `{needle}`), got: {msg}"
    if needle == "?" then logInfo m!"{pre}: {msg.take 260}"
    else unless (msg.splitOn needle).length > 1 do throwError "the refusal does not name `{needle}`: {msg}"
  let after ← localConsts
  let added := after.toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"

/-- The checker must ACCEPT the (consistently altered) `(m, d)` with the exact statement. -/
def expectAccepted (decl : Name) (m : Sparkle.IR.AST.Module) (d : Design) : CommandElabM Unit := do
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let (thm, _, _) ← checkU2HR decl stmt nDom m d none
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    std3Only thm

def mapAssign (n : String) (f : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .assign l e => if l == n then .assign l (f e) else s
    | s => s

/-- Replace the connection of port `p` by `e` in the instance NUMBER `k` (0-based). -/
def setConnAt (k : Nat) (p : String) (e : Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  let rec go : List Stmt → Nat → List Stmt
    | [], _ => []
    | s :: r, n =>
      match s with
      | .inst mn i cs => (if n == k then .inst mn i (cs.map fun q => if q.1 == p then (p, e) else q) else s) :: go r (n + 1)
      | _ => s :: go r n
  go b 0

def rop (o : Operator) (a b : String) : Sparkle.IR.AST.Expr := .op o [.ref a, .ref b]

/-- Rename a wire everywhere in a statement (left-hand sides, reads, connections, register fields). -/
partial def renE (f : String → String) : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
  | .ref x => .ref (f x)
  | .op o as => .op o (as.map (renE f))
  | .concat as => .concat (as.map (renE f))
  | .slice e hi lo => .slice (renE f e) hi lo
  | e => e

def renS (f : String → String) : Stmt → Stmt
  | .assign l e => .assign (f l) (renE f e)
  | .inst mn i cs => .inst mn i (cs.map fun (p, e) => (p, renE f e))
  | .register o k r e i => .register (f o) k r (renE f e) i
  | s => s

/- Names in the synthesised `wireRef`: nets `_tmp_arg0_1` (a + b), `_tmp_arg1_2` (a - b) feed the
`acc2` instance (ports `_gen_x`, `_gen_y`, output `_tmp_arg1_3`); `_tmp_arg0_8` (b + a) feeds the
`accMod` instance (port `_gen_x`, output `_tmp_arg1_9`); parent registers `_tmp_a_7` (p) and
`_tmp_a_14` (q); their input nets `_tmp_reg_input_6` and `_tmp_reg_input_13`. -/

def controlsRun : CommandElabM Unit := do
  let (m, d) ← synthOf ``wireRef
  let name := ``wireRef
  let mut n : Nat := 0
  /- THE NETS (the declaration's call argument against the IR's wire) -/
  -- the two wires of one instance exchanged
  expectRefused name "proof" "unsolved goals"
    { m with body := setConnAt 0 "_gen_y" (.ref "_tmp_arg0_1") (setConnAt 0 "_gen_x" (.ref "_tmp_arg1_2") m.body) } d
  n := n + 1
  -- a net computes another function (a + b becomes a - b)
  expectRefused name "proof" "unsolved goals"
    { m with body := mapAssign "_tmp_arg0_1" (fun _ => rop .sub "_gen_a" "_gen_b") m.body } d
  n := n + 1
  -- a net reads the wrong input (b + a becomes b + b)
  expectRefused name "proof" "unsolved goals"
    { m with body := mapAssign "_tmp_arg0_8" (fun _ => rop .add "_gen_b" "_gen_b") m.body } d
  n := n + 1
  -- a port reads a plain input instead of the net the declaration passes (no call of that shape)
  expectRefused name "open" "no call of"
    { m with body := setConnAt 1 "_gen_x" (.ref "_gen_a") m.body } d
  n := n + 1
  /- A CHILD INPUT MOVED ONE CYCLE: a register output / the register's own input net -/
  -- the accMod instance reads the parent register `q` (its output)
  expectRefused name "conns" "register output"
    { m with body := setConnAt 1 "_gen_x" (.ref "_tmp_a_14") m.body } d
  n := n + 1
  -- ... or the INPUT net of the register `p` (one cycle earlier than the register's output)
  expectRefused name "conns" "not connected to a parent input"
    { m with body := setConnAt 1 "_gen_x" (.ref "_tmp_reg_input_6") m.body } d
  n := n + 1
  /- A CYCLE THROUGH AN INSTANCE -/
  -- the acc2 instance's own output feeds its input
  expectRefused name "order" "combinational cycle"
    { m with body := setConnAt 0 "_gen_x" (.ref "_tmp_arg1_3") m.body } d
  n := n + 1
  -- a net reads the instance's own output and feeds the same instance
  expectRefused name "order" "combinational cycle"
    { m with body := mapAssign "_tmp_arg0_8" (fun _ => rop .add "_gen_a" "_tmp_arg1_9") m.body } d
  n := n + 1
  -- the two instances feed each other through nets
  expectRefused name "order" "combinational cycle"
    { m with body := (mapAssign "_tmp_arg0_8" (fun _ => rop .add "_gen_a" "_tmp_arg1_3")
        (mapAssign "_tmp_arg0_1" (fun _ => rop .add "_gen_a" "_tmp_arg1_9") m.body)) } d
  n := n + 1
  /- UNSUPPORTED SHAPES KEPT AT [conns] -/
  -- a chained instance input: the accMod instance reads the acc2 instance's output through a net
  expectRefused name "conns" "another instance's output"
    { m with body := mapAssign "_tmp_arg0_8" (fun _ => rop .add "_gen_a" "_tmp_arg1_3") m.body } d
  n := n + 1
  -- the child's clock port read from a derived net
  expectRefused name "hier-shape" "clock/reset"
    { m with body := setConnAt 1 "clk" (.ref "_tmp_arg0_8") m.body } d
  n := n + 1
  -- the child's reset port read from a data input
  expectRefused name "hier-shape" "clock/reset"
    { m with body := setConnAt 1 "rst" (.ref "_gen_b") m.body } d
  n := n + 1
  -- a data port read from the clock (width 1 against 8)
  expectRefused name "hier-shape" "width mismatch"
    { m with body := setConnAt 1 "_gen_x" (.ref "clk") m.body } d
  n := n + 1
  -- a net reading an undriven name
  expectRefused name "order" "undriven net"
    { m with body := mapAssign "_tmp_arg0_8" (fun _ => rop .add "_gen_a" "_tmp_nosuch") m.body,
             wires := m.wires ++ [⟨"_tmp_nosuch", .bitVector 8⟩] } d
  n := n + 1
  -- a data port connected to a constant (not a wire reference)
  expectRefused name "hier-shape" "plain wire reference"
    { m with body := setConnAt 1 "_gen_x" (.const 3 8) m.body } d
  n := n + 1
  logInfo m!"controls: {n} refused, nothing left in the environment"

/-- info: controls: 15 refused, nothing left in the environment -/
#guard_msgs in
run_cmd controlsRun

/-! ## Positive controls: consistent changes are ACCEPTED -/

/-- info: renamed nets accepted -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``wireRn
  let f : String → String := fun x =>
    if x == "_tmp_arg0_1" then "net_sum" else if x == "_tmp_arg1_2" then "net_dif"
    else if x == "_tmp_arg0_8" then "net_rev" else x
  expectAccepted ``wireRn
    { m with body := m.body.map (renS f),
             wires := m.wires.map fun w => if f w.name != w.name then { w with name := f w.name } else w } d
  logInfo "renamed nets accepted"

/-- info: reordered body accepted -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``wireOrd
  -- instances first, then the nets, then the registers (their relative order is the slot order)
  let isReg : Stmt → Bool := fun s => match s with | .register .. => true | _ => false
  let isI : Stmt → Bool := fun s => match s with | .inst .. => true | _ => false
  expectAccepted ``wireOrd
    { m with body := m.body.filter isI ++ m.body.filter (fun s => !isI s && !isReg s) ++ m.body.filter isReg } d
  logInfo "reordered body accepted"

/-! ## Entry-level refusals: the shapes of the real rows, a derived input without registers -/

def localConsts' : CommandElabM NameSet := localConsts

def entryRefused (decl : Name) (stage : String) (needle : String) : CommandElabM Unit := do
  let before ← localConsts'
  let r ← try
      discard <| vedU2HierEntryR decl
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do throwError "unexpected: {msg}"
    unless (msg.splitOn needle).length > 1 do throwError "the refusal does not name `{needle}`: {msg}"
  | none => throwError "{decl} accepted"
  let after ← localConsts'
  let added := after.toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"

/-- info: real shapes refused at [conns]: counter register, register expression, latch and chain, chained instance; no-register derived input at [conns] -/
#guard_msgs in
run_cmd do
  entryRefused ``shapeBurst "conns" "parent register output"
  entryRefused ``shapeExpr "conns" "parent register output"
  entryRefused ``shapeChain "conns" "parent register output"
  entryRefused ``shapeChained "conns" "another instance's output"
  entryRefused ``shapeNoReg "conns" "not connected to a parent input"
  logInfo "real shapes refused at [conns]: counter register, register expression, latch and chain, chained instance; no-register derived input at [conns]"

end Tests.Ved.U2HierWireCheck
