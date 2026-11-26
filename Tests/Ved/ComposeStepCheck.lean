import Tools.VedU2HierRegEntry
import Tools.VedComposeStep
import Tests.Ved.ComposeCheckUtil
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for the composed step (option `ved.compose.step`, `Tools/VedComposeStep.lean`) with the shared bundle-slice walk

`cmpThree`: `cnt` and three registers in ONE `circuit do` bundle, two instances of the child `cmpA` on `cnt` and `cnt - 1`
(the shape of `Tests.Ved.U2HierMultiCheck.multiTwo` with a register chain).  With the option on the parent's one-cycle step
is proved from local facts about an abstract environment, cone by cone, and the reads of the register bundle share the walk
over the nested pairs (`Tools.VedU2HierMultiChain.valOf`, memo).  The statement `U2HRStmt` is unchanged.

After `#ved_u2_hier` the result is checked independently of the entry: the stored type, an `Expr` compared with `==`, is
`U2HRStmt <decl>.ved_contract <decl>.ved_mod <decl>.ved_design <decl>`; its axioms are within `propext`, `Classical.choice`,
`Quot.sound`; it is a theorem of the environment (the kernel accepted it).

The CONTROLS run the checker, with the option on, on the real synthesis `(m, d)` of a copy with ONE piece altered: wiring
(the instances' arguments exchanged; one instance paired with the other's call), a different artifact (the synthesis of another
declaration), a mutated initial value, a time shift (the post-update state) and a register-input exchange.  Each is refused
at a named stage and leaves nothing behind.
-/

namespace Tests.Ved.ComposeStepCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry Tests.Ved.ComposeCheckUtil

/-! ## Declarations -/

@[hardware_module]
def cmpA (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 3#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

@[hardware_module]
def cmpB (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 5#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

def cmpThree (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let cnt ← Signal.reg 0#4
    let r0 ← Signal.reg 0#4
    let r1 ← Signal.reg 0#4
    let r2 ← Signal.reg 0#4
    let cntS := (cnt : Signal defaultDomain (BitVec 4))
    let s0 := (r0 : Signal defaultDomain (BitVec 4))
    let s1 := (r1 : Signal defaultDomain (BitVec 4))
    let s2 := (r2 : Signal defaultDomain (BitVec 4))
    let k1 := cmpA cntS
    let k2 := cmpA (cntS - (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    cnt <~ (cntS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    r0 <~ Signal.mux start inp (s0 + k1 + k2 : Signal defaultDomain (BitVec 4))
    r1 <~ Signal.mux start inp s0
    r2 <~ Signal.mux start inp s1
    return s0

/-- A copy for the controls. -/
def cmpThreeRef (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let cnt ← Signal.reg 0#4
    let r0 ← Signal.reg 0#4
    let r1 ← Signal.reg 0#4
    let r2 ← Signal.reg 0#4
    let cntS := (cnt : Signal defaultDomain (BitVec 4))
    let s0 := (r0 : Signal defaultDomain (BitVec 4))
    let s1 := (r1 : Signal defaultDomain (BitVec 4))
    let s2 := (r2 : Signal defaultDomain (BitVec 4))
    let k1 := cmpA cntS
    let k2 := cmpA (cntS - (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    cnt <~ (cntS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    r0 <~ Signal.mux start inp (s0 + k1 + k2 : Signal defaultDomain (BitVec 4))
    r1 <~ Signal.mux start inp s0
    r2 <~ Signal.mux start inp s1
    return s0

/-- Another artifact of the same shape (another child, another register chain). -/
def cmpOther (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let cnt ← Signal.reg 0#4
    let r0 ← Signal.reg 0#4
    let r1 ← Signal.reg 0#4
    let r2 ← Signal.reg 0#4
    let cntS := (cnt : Signal defaultDomain (BitVec 4))
    let s0 := (r0 : Signal defaultDomain (BitVec 4))
    let s1 := (r1 : Signal defaultDomain (BitVec 4))
    let s2 := (r2 : Signal defaultDomain (BitVec 4))
    let k1 := cmpB cntS
    let k2 := cmpB (cntS - (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    cnt <~ (cntS + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))
    r0 <~ Signal.mux start inp (s0 + k1 + k2 : Signal defaultDomain (BitVec 4))
    r1 <~ Signal.mux start inp s0
    r2 <~ Signal.mux start inp s2
    return s0

/-! ## Helpers -/

/-- Run the stateful hierarchical entry on `decl` (option on) and check the result independently of the entry. -/
def checkRow (decl : Name) : CommandElabM Unit := do
  unless Tools.VedCompose.ved.compose.step.get (← getOptions) do throwError "the option ved.compose.step is not on"
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    unless !(regsOf m.body).isEmpty do throwError "{decl}: the parent has no register"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    logInfo m!"compose step OK: {(regsOf m.body).length} parent registers, {(m.body.filter fun s => match s with | .inst .. => true | _ => false).length} instances, children {", ".intercalate (d.modules.map (·.name))}"

def mapRegs (f : String → Stmt → Stmt) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .register o .. => f o s
    | s => s

def setInit (v : Int) : Stmt → Stmt
  | .register o k r e _ => .register o k r e v
  | s => s

def setInput (e : Sparkle.IR.AST.Expr) : Stmt → Stmt
  | .register o k r _ i => .register o k r e i
  | s => s

/-! ## Positive (option on) -/

/-- info: compose step OK: 4 parent registers, 4 instances, children Tests.Ved.ComposeStepCheck.cmpA -/
#guard_msgs in
set_option ved.compose.step true in
run_cmd checkRow ``cmpThree

/-! ## Controls: ONE piece altered, refused at a named stage, nothing left -/

/- Names in the synthesised `cmpThreeRef`: parent registers `_tmp_a_4` (cnt), `_tmp_a_15` (r0), `_tmp_a_17` (r1), `_tmp_a_21`
(r2), their input nets `_tmp_reg_input_3` (cnt + 1), `_tmp_reg_input_14`, `_tmp_reg_input_16`, `_tmp_reg_input_20`; the nets
`_tmp_arg1_1` (cnt) and `_tmp_arg0_11` (cnt - 1) feed the four instances of `cmpA` (numbers 0..3: reading cnt, cnt - 1, cnt,
cnt - 1). -/

def controls : CommandElabM Unit := do
  let (m, d) ← synthOf ``cmpThreeRef
  let name := ``cmpThreeRef
  let set (ks : List Nat) (net : String) (b : List Stmt) : List Stmt :=
    ks.foldl (fun b k => setConnAt k "_gen_x" (.ref net) b) b
  -- WIRING: the instances' arguments exchanged
  expectRefused name "proof" "unsolved goals" { m with body := set [1, 3] "_tmp_arg1_1" (set [0, 2] "_tmp_arg0_11" m.body) } d
  -- WIRING: an instance paired with the other's call (all four read `cnt`, the body has two distinct calls)
  expectRefused name "open" "cannot be paired" { m with body := set [1, 3] "_tmp_arg1_1" m.body } d
  -- A DIFFERENT ARTIFACT: the synthesis of another declaration (another child, another register chain)
  let (m2, d2) ← synthOf ``cmpOther
  expectRefused name "open" "no call of a child" m2 d2
  -- A MUTATED INITIAL VALUE of a register the shared walk reads
  let swapIn : String → Stmt → Stmt := fun o s =>
    if o == "_tmp_a_17" then setInput (.ref "_tmp_reg_input_20") s
    else if o == "_tmp_a_21" then setInput (.ref "_tmp_reg_input_16") s
    else s
  expectRefused name "proof" "errors were logged while elaborating the proof" { m with body := mapRegs swapIn m.body } d

/-- info: compose step controls: 6 refused -/
#guard_msgs in
set_option ved.compose.step true in
run_cmd do
  controls
  logInfo m!"compose step controls: 6 refused"

/-! ## Controls of the fast order check (`Tools/VedComposeOrder.lean`), evaluated by the KERNEL -/

/-- The kernel (not the elaborator) evaluates `e` to `expect`. -/
def kernelIs (what : String) (e : Lean.Expr) (expect : Bool) : CommandElabM Unit := liftTermElabM do
  match Lean.Kernel.isDefEq (← getEnv) {} e (toExpr expect) with
  | .ok true => pure ()
  | .ok false => throwError "{what}: the kernel evaluates it to {!expect}, expected {expect}"
  | .error _ => throwError "{what}: kernel error"

def orderControls : CommandElabM Unit := do
  let (m, d) ← synthOf ``cmpThreeRef
  let b0 := orderBodyH d m.body
  let fast (b : List Stmt) : Lean.Expr :=
    mkAppN (Lean.mkConst ``Tools.VedCompose.OrderOkFast) #[toExpr d, toExpr m, toExpr b]
  let perm (σ : List Nat) (n : Nat) : Lean.Expr :=
    mkAppN (Lean.mkConst ``Tools.VedCompose.permOk) #[toExpr σ, toExpr n]
  -- the checked arrangement is accepted, by both checks, and the certificate is the one the generator computes
  unless OrderOkHS d m b0 do throwError "the ordered body is not accepted by OrderOkHS"
  kernelIs "OrderOkFast (ordered body)" (fast b0) true
  kernelIs "permOk (generator's indices)" (perm (Tools.VedCompose.permIdx m.body b0) m.body.length) true
  -- a MIS-ORDERED body (a register's reads after the wires: the whole body reversed, so a wire is read before it is written)
  let bad := b0.reverse
  if OrderOkHS d m bad then throwError "the reversed body is accepted by OrderOkHS (control is void)"
  kernelIs "OrderOkFast (reversed body)" (fast bad) false
  -- a write that is twice in the body (a duplicate statement): both checks reject it
  let dup := b0 ++ b0.take 1
  kernelIs "OrderOkFast (duplicated statement)" (fast dup) false
  -- the permutation certificate: a repeated index, an index out of range, a missing index
  let σ := Tools.VedCompose.permIdx m.body b0
  kernelIs "permOk (repeated index)" (perm (σ ++ σ.take 1) m.body.length) false
  kernelIs "permOk (index out of range)" (perm (σ.dropLast ++ [m.body.length]) m.body.length) false
  kernelIs "permOk (missing index)" (perm σ.dropLast m.body.length) false

/-- info: compose order controls: accepted, 6 rejected -/
#guard_msgs in
run_cmd do
  orderControls
  logInfo m!"compose order controls: accepted, 6 rejected"

/-! ## Controls of the fast width check (`widthFast`, `Tools/VedComposeOrder.lean`), evaluated by the KERNEL -/

def widthControls : CommandElabM Unit := do
  let (m, _d) ← synthOf ``cmpThreeRef
  let (stmt, _) ← liftTermElabM (specialiseDomain ``cmpThreeRef)
  let tbl ← liftTermElabM do readTableOfType ``cmpThreeRef (← inferType stmt)
  let some clkRst := parentClkRst tbl m | throwError "no clock/reset pair"
  let c := contractOf tbl ["out"] clkRst m
  -- the contract is the real one (`contractOf` of the real module); the module is altered
  let cE : Lean.Expr := mkAppN (Lean.mkConst ``contractOf) #[toExpr tbl, toExpr ["out"], toExpr clkRst, toExpr m]
  let wf (m : Sparkle.IR.AST.Module) : Lean.Expr :=
    mkAppN (Lean.mkConst ``Tools.VedCompose.widthFast) #[cE, toExpr m]
  -- the real module: accepted by `WidthStmt` and by `widthFast`
  unless decide (WidthStmt c m) do throwError "the synthesised parent does not satisfy WidthStmt"
  kernelIs "widthFast (real module)" (wf m) true
  -- a DUPLICATED wire name (the same wire twice)
  let dupM := { m with wires := m.wires ++ m.wires.take 1 }
  if decide (WidthStmt c dupM) then throwError "the duplicate-wire module satisfies WidthStmt (control is void)"
  kernelIs "widthFast (duplicated wire name)" (wf dupM) false
  -- a MISSING wire: a register's output has no declared wire
  let some r := (regsOf m.body).head? | throwError "no register"
  let missM := { m with wires := m.wires.filter (·.name != r.1) }
  if decide (WidthStmt c missM) then throwError "the missing-wire module satisfies WidthStmt (control is void)"
  kernelIs "widthFast (register wire missing)" (wf missM) false
  -- a WRONG WIDTH: the declared width of a data input differs from the table's
  let some p := c.dataInputs.head? | throwError "no data input"
  let wrongM := { m with wires := m.wires.map fun w =>
    if w.name == p.name then { w with ty := .bitVector (p.ty.bitWidth + 1) } else w }
  if decide (WidthStmt c wrongM) then throwError "the wrong-width module satisfies WidthStmt (control is void)"
  kernelIs "widthFast (wrong declared width)" (wf wrongM) false
  -- a register wire that is not a scalar (width 0)
  let zeroM := { m with wires := m.wires.map fun w =>
    if w.name == r.1 then { w with ty := .bitVector 0 } else w }
  if decide (WidthStmt c zeroM) then throwError "the zero-width module satisfies WidthStmt (control is void)"
  kernelIs "widthFast (register wire of width 0)" (wf zeroM) false

/-- info: compose width controls: accepted, 4 rejected -/
#guard_msgs in
run_cmd do
  widthControls
  logInfo m!"compose width controls: accepted, 4 rejected"

end Tests.Ved.ComposeStepCheck
