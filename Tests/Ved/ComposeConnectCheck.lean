import Tools.VedU2HierRegEntry
import Tools.VedComposeConnectGen
import Tests.Ved.ComposeCheckUtil
import IP.Crypto.SHA512HW
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

/-! ## toyK: the real child `kMux` (an 80-entry mux chain), 64-bit registers in a right-nested bundle (compose7's generator, 4 registers) -/

def toyK4 (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain (BitVec 64) :=
  circuit do
    let cnt ← Signal.reg 0#8
    let r0 ← Signal.reg 0#64
    let r1 ← Signal.reg 0#64
    let r2 ← Signal.reg 0#64
    let r3 ← Signal.reg 0#64
    let cntSig := (cnt : Signal defaultDomain (BitVec 8))
    let s0 := (r0 : Signal defaultDomain (BitVec 64))
    let s1 := (r1 : Signal defaultDomain (BitVec 64))
    let s2 := (r2 : Signal defaultDomain (BitVec 64))
    let s3 := (r3 : Signal defaultDomain (BitVec 64))
    let cnt7 := (cntSig.map (BitVec.extractLsb' 0 7 ·) : Signal defaultDomain (BitVec 7))
    let p1_7 := (Signal.pure 1#7 : Signal defaultDomain (BitVec 7))
    let kIdx := (cnt7 - p1_7 : Signal defaultDomain (BitVec 7))
    let kVal := Sparkle.IP.Crypto.SHA512HW.kMux kIdx
    cnt <~ (cntSig + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
    r0 <~ Signal.mux start inp (s0 + kVal : Signal defaultDomain (BitVec 64))
    r1 <~ Signal.mux start inp s0
    r2 <~ Signal.mux start inp s1
    r3 <~ Signal.mux start inp s2
    return s0

/-- A copy for the control. -/
def toyK4Ref (start : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 64)) :
    Signal defaultDomain (BitVec 64) :=
  circuit do
    let cnt ← Signal.reg 0#8
    let r0 ← Signal.reg 0#64
    let r1 ← Signal.reg 0#64
    let r2 ← Signal.reg 0#64
    let r3 ← Signal.reg 0#64
    let cntSig := (cnt : Signal defaultDomain (BitVec 8))
    let s0 := (r0 : Signal defaultDomain (BitVec 64))
    let s1 := (r1 : Signal defaultDomain (BitVec 64))
    let s2 := (r2 : Signal defaultDomain (BitVec 64))
    let s3 := (r3 : Signal defaultDomain (BitVec 64))
    let cnt7 := (cntSig.map (BitVec.extractLsb' 0 7 ·) : Signal defaultDomain (BitVec 7))
    let p1_7 := (Signal.pure 1#7 : Signal defaultDomain (BitVec 7))
    let kIdx := (cnt7 - p1_7 : Signal defaultDomain (BitVec 7))
    let kVal := Sparkle.IP.Crypto.SHA512HW.kMux kIdx
    cnt <~ (cntSig + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8))
    r0 <~ Signal.mux start inp (s0 + kVal : Signal defaultDomain (BitVec 64))
    r1 <~ Signal.mux start inp s0
    r2 <~ Signal.mux start inp s1
    r3 <~ Signal.mux start inp s2
    return s0

/-! ## projTx: ONE instance of the child whose output feeds the parent's own register, the declaration a projection of the circuit's
structure result (the shape of `synth_usbWebServer` = `(usbWebServer ..).uartTx`, where `respByteMux` is read once and its byte goes
through registers).  Without the option this is refused at `[open]` (`genOpenSt` needs the declaration to BE the child's call). -/

structure PT (dom : DomainConfig) where
  b : Signal dom (BitVec 4)
  v : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (PT dom) dom := ⟨⟩

def projCirc (go : Signal defaultDomain Bool) : PT defaultDomain :=
  circuit do
    let phase ← Signal.reg 0#4
    let outR ← Signal.reg 0#4
    let vR ← Signal.reg false
    let ph := (phase : Signal defaultDomain (BitVec 4))
    phase <~ Signal.mux go (ph + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4)) ph
    outR <~ mkA ph
    vR <~ go
    return ({ b := (outR : Signal defaultDomain (BitVec 4)), v := (vR : Signal defaultDomain Bool) } : PT defaultDomain)

def projTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (projCirc go).b

/-- copies for the controls (never accepted themselves); `projTxVRef` is the other field of the circuit -/
def projCircRef (go : Signal defaultDomain Bool) : PT defaultDomain :=
  circuit do
    let phase ← Signal.reg 0#4
    let outR ← Signal.reg 0#4
    let vR ← Signal.reg false
    let ph := (phase : Signal defaultDomain (BitVec 4))
    phase <~ Signal.mux go (ph + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4)) ph
    outR <~ mkA ph
    vR <~ go
    return ({ b := (outR : Signal defaultDomain (BitVec 4)), v := (vR : Signal defaultDomain Bool) } : PT defaultDomain)

def projTxRef (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) := (projCircRef go).b

/-- the other field of the same circuit (the control: its declaration against the module of `projTx`) -/
def projTxVRef (go : Signal defaultDomain Bool) : Signal defaultDomain Bool := (projCircRef go).v

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
    -- `reg_connectN` / `out_connectN`: the normalised comparison selected under `ved.compose.multiCircuit`
    let nr := countApps ti.value ``Tools.VedComposeConnect.reg_connect + countApps ti.value ``Tools.VedComposeConnect.reg_connectN
    let no := countApps ti.value ``Tools.VedComposeConnect.out_connect + countApps ti.value ``Tools.VedComposeConnect.out_connectN
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

-- toyK4: real child kMux, 64-bit registers (cnt + 4 registers = 5 `reg_connect` sites).
/-- info: compose connect OK: 5 registers by reg_connect, 1 port by out_connect, child theorem Tests.Ved.ComposeConnectCheck.toyK4.ved_child.Sparkle.IP.Crypto.SHA512HW.kMux.ved_u1, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd checkRow ``toyK4 `Tests.Ved.ComposeConnectCheck.toyK4.ved_child.Sparkle.IP.Crypto.SHA512HW.kMux.ved_u1 5

-- projTx: single instance through registers, struct projection (3 registers: phase, outR, vR)
/-- info: compose connect OK: 3 registers by reg_connect, 1 port by out_connect, child theorem Tests.Ved.ComposeConnectCheck.projTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd checkRow ``projTx `Tests.Ved.ComposeConnectCheck.projTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1 3

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

/-- info: compose connect controls (entry level): 7 refused
---
info: compose connect toyK4 control: refused -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd do
  controls
  logInfo m!"compose connect controls (entry level): 7 refused"
  -- toyK4 (real child, 64-bit registers): every register starts at 5, the declaration's loop at 0
  let (mK, dK) ← synthOf ``toyK4Ref
  expectRefusedT ``toyK4Ref "proof" "?" { mK with body := mapRegs (fun _ s => setInit 5 s) mK.body } dK (fun p => pure p)
  logInfo m!"compose connect toyK4 control: refused"

/-! ### projTx controls (entry level)

* the option OFF (default path, unchanged): refused at `[open]` exactly as before (the declaration is not one call of the child);
* a WRONG PROJECTION: the module of `projTx` (field `b`, 4 bits) against the declaration of the other field `projTxVRef` (a bit): refused;
* every register starts at 5, the declaration's loop at 0: refused at `[proof]`. -/

/-- info: compose connect projTx controls: 3 refused -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``projTxRef
  let noT : Phase1 → CommandElabM Phase1 := fun p => pure p
  -- option off: the single-call slice, as before
  expectRefusedT ``projTxRef "open" "does not reduce to a call of" m d noT
  -- the other projection of the same circuit
  expectRefusedT ``projTxVRef "artifact" "?" m d noT
  -- initial values (option on)
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true }) do
    expectRefusedT ``projTxRef "proof" "?" { m with body := mapRegs (fun _ s => setInit 5 s) m.body } d noT
  logInfo m!"compose connect projTx controls: 3 refused"

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
  -- the batched check `RegsOk` (all register slots at once): the real table and inputs -> true; oracle slots swapped, input wires
  -- exchanged -> false
  let deep := s!"{M}.ved_open_Tests_Ved_ComposeConnectCheck_multiTwo_deep"
  let needed := "([\"_tmp_a_4\", \"_tmp_a_15\", \"_gen_start\", \"_gen_inp\", \"_tmp_op_b_9\", \"_gen_k1\", \"_tmp_op_b_12\", \"_gen_k2\"] : List String)"
  let regsOk (o0 o1 : Nat) (xs : String) :=
    s!"Tools.VedComposeConnect.RegsOk {deep} {nm} {M}.ved_design {M}.ved_mod {M}.ved_body {needed} {tabTxt o0 o1} 28 28 28 ([{xs}] : List String)"
  unless ← kernelEqual (← elabText (regsOk 4 5 "\"_tmp_reg_input_3\", \"_tmp_reg_input_14\"")) (toExpr true) do
    throwError "control void: RegsOk rejects the real table"
  if ← kernelEqual (← elabText (regsOk 5 4 "\"_tmp_reg_input_3\", \"_tmp_reg_input_14\"")) (toExpr true) then
    throwError "RegsOk accepts swapped oracle slots"
  if ← kernelEqual (← elabText (regsOk 4 5 "\"_tmp_reg_input_14\", \"_tmp_reg_input_3\"")) (toExpr true) then
    throwError "RegsOk accepts exchanged register input wires"
  logInfo m!"compose connect batch controls: 1 accepted, 2 refused by the kernel"
  -- the input-bound list of `Tools.VedComposePrelude.hin_bnd`: the equation `dataInputs.map (name, declWidth) = L` is decided by the
  -- kernel; the real list -> true; a wrong width, swapped names -> false
  let inEq (l : String) :=
    s!"decide (({M}.ved_contract.dataInputs.map fun p => (p.name, Tools.VedU1Contract.declWidth {M}.ved_mod p.name)) = ({l} : List (String × Nat)))"
  unless ← kernelEqual (← elabText (inEq "[(\"_gen_start\", 1), (\"_gen_inp\", 4)]")) (toExpr true) do
    throwError "control void: the input-bound list equation rejects the real list"
  if ← kernelEqual (← elabText (inEq "[(\"_gen_start\", 1), (\"_gen_inp\", 5)]")) (toExpr true) then
    throwError "the input-bound list equation accepts a wrong width"
  if ← kernelEqual (← elabText (inEq "[(\"_gen_inp\", 1), (\"_gen_start\", 4)]")) (toExpr true) then
    throwError "the input-bound list equation accepts swapped names"
  logInfo m!"compose connect input-bound controls: 1 accepted, 2 refused by the kernel"

/-- info: compose connect equation controls: 1 accepted, 4 refused by the kernel
---
info: compose connect batch controls: 1 accepted, 2 refused by the kernel
---
info: compose connect input-bound controls: 1 accepted, 2 refused by the kernel -/
#guard_msgs in
run_cmd eqnControls

/-! ## Controls of the map-based `WOKbF` / `RegsOkF` (kernel evaluation on the accepted `multiTwo`)

The real module and table give `true`; one wrong declared width, swapped oracle slots, exchanged register input wires give `false`;
the list-scanning `WOKb` / `RegsOk` give the same verdict on every variant. -/

def fastControls : CommandElabM Unit := liftTermElabM do
  let M := "Tests.Ved.ComposeConnectCheck.multiTwo"
  let nm := s!"{M}.ved_open_Tests_Ved_ComposeConnectCheck_multiTwo_nm"
  let deep := s!"{M}.ved_open_Tests_Ved_ComposeConnectCheck_multiTwo_deep"
  let tabTxt (o0 o1 : Nat) :=
    s!"([(\"_tmp_a_4\", 0), (\"_tmp_a_15\", 1), (\"_gen_start\", 2), (\"_gen_inp\", 3), (\"_tmp_op_b_9\", {o0}), (\"_tmp_op_b_12\", {o1}), (\"_gen_k1\", {o0}), (\"_gen_k2\", {o1})] : List (String × Nat))"
  let needed := "([\"_tmp_a_4\", \"_tmp_a_15\", \"_gen_start\", \"_gen_inp\", \"_tmp_op_b_9\", \"_gen_k1\", \"_tmp_op_b_12\", \"_gen_k2\"] : List String)"
  let modW (w : String) (k : Nat) :=
    s!"(\{ {M}.ved_mod with wires := {M}.ved_mod.wires.map fun w => if w.name == \"{w}\" then \{ w with ty := Sparkle.IR.Type.HWType.bitVector {k} } else w } : Sparkle.IR.AST.Module)"
  let isTrue (t : String) : TermElabM Bool := do kernelEqual (← elabText t) (toExpr true)
  -- WOKbF: the real module -> true (and WOKb agrees); one internal wire of the wrong width -> false (both)
  let wok (f : String) (m : String) := s!"Tools.VedComposeConnect.{f} {m} {M}.ved_body"
  let wokL (m : String) := s!"Tools.VedComposeResearch.WOKb (Tools.VedU1Contract.declWidth {m}) {m} {M}.ved_body"
  unless ← isTrue (wok "WOKbF" s!"{M}.ved_mod") do throwError "control void: WOKbF rejects the real module"
  unless ← isTrue (wokL s!"{M}.ved_mod") do throwError "control void: WOKb rejects the real module"
  if ← isTrue (wok "WOKbF" (modW "_tmp_mux_else_5" 5)) then throwError "WOKbF accepts a wrong width"
  if ← isTrue (wokL (modW "_tmp_mux_else_5" 5)) then throwError "WOKb accepts a wrong width (control void)"
  logInfo m!"compose connect WOKbF controls: 1 accepted, 1 refused by the kernel"
  -- RegsOkF
  let regsOkF (m : String) (o0 o1 : Nat) (xs : String) :=
    s!"Tools.VedComposeConnect.RegsOkF {deep} {nm} {M}.ved_design {m} {M}.ved_body {needed} {tabTxt o0 o1} 28 28 28 ([{xs}] : List String)"
  let real := "\"_tmp_reg_input_3\", \"_tmp_reg_input_14\""
  unless ← isTrue (regsOkF s!"{M}.ved_mod" 4 5 real) do throwError "control void: RegsOkF rejects the real table"
  if ← isTrue (regsOkF s!"{M}.ved_mod" 5 4 real) then throwError "RegsOkF accepts swapped oracle slots"
  if ← isTrue (regsOkF s!"{M}.ved_mod" 4 5 "\"_tmp_reg_input_14\", \"_tmp_reg_input_3\"") then throwError "RegsOkF accepts exchanged register input wires"
  if ← isTrue (regsOkF (modW "_tmp_a_4" 5) 4 5 real) then throwError "RegsOkF accepts a register of the wrong width"
  logInfo m!"compose connect RegsOkF controls: 1 accepted, 3 refused by the kernel"

/-- info: compose connect WOKbF controls: 1 accepted, 1 refused by the kernel
---
info: compose connect RegsOkF controls: 1 accepted, 3 refused by the kernel -/
#guard_msgs in
run_cmd fastControls

/-! ## Controls of the one-check bundle-slice chain `ChainOkF` (kernel evaluation on the accepted `multiShared`)

A slice step is read off the module itself (a wire that is `slice (ref x) hi lo` of a concatenation of refs that is exactly one
element); the real step -> true; a wrong offset, a wrong element index, a wrong declared width, a wrong bundle name -> false. -/

def chainControls : CommandElabM Unit := do
  let (m, _) ← synthOf ``multiShared
  let M := "Tests.Ved.ComposeConnectCheck.multiShared"
  let we := declWidth m
  let asg (x : String) : Option Sparkle.IR.AST.Expr := Tools.VedU2Hier.asgOf m.body x
  let some step := m.body.findSome? (fun st => match st with
    | .assign w (.slice (.ref x) hi lo) =>
      -- `x` is the bundle wire itself or an alias (`ref y`) of it
      let y := match asg x with | some (.ref y) => y | _ => x
      match asg y with
      | some (.concat es) =>
        match es.mapM (fun e => match e with | .ref n => some n | _ => none) with
        | some names =>
          match (List.range names.length).find? (fun k =>
              ((names.drop (k + 1)).map we).foldl (· + ·) 0 == lo && hi + 1 == lo + we names[k]! && 0 < we names[k]!) with
          | some k => some (w, x, y, hi, lo, names, k)
          | none => none
        | none => none
      | _ => none
    | _ => none) | throwError "control void: no slice step in multiShared"
  let (w, x, y, hi, lo, names, k) := step
  let q (s : String) := s!"\"{s}\""
  let nameL (ns : List String) := "[" ++ ", ".intercalate (ns.map q) ++ "]"
  let tup (lo' k' : Nat) (ns : List String) := s!"({q w}, {q x}, {q y}, {hi}, {lo'}, {nameL ns}, {k'})"
  liftTermElabM do
    let isTrue (t : String) : TermElabM Bool := do kernelEqual (← elabText t) (toExpr true)
    let chk (modT : String) (t : String) := s!"Tools.VedComposeConnect.ChainOkF {modT} {M}.ved_body [{t}] [] []"
    unless ← isTrue (chk s!"{M}.ved_mod" (tup lo k names)) do throwError "control void: ChainOkF rejects the real step"
    if ← isTrue (chk s!"{M}.ved_mod" (tup (lo + 1) k names)) then throwError "ChainOkF accepts a wrong offset"
    if ← isTrue (chk s!"{M}.ved_mod" (tup lo ((k + 1) % names.length) names)) then throwError "ChainOkF accepts a wrong element index"
    let modW := s!"(\{ {M}.ved_mod with wires := {M}.ved_mod.wires.map fun w => if w.name == {q names[k]!} then \{ w with ty := Sparkle.IR.Type.HWType.bitVector {we names[k]! + 1} } else w } : Sparkle.IR.AST.Module)"
    if ← isTrue (chk modW (tup lo k names)) then throwError "ChainOkF accepts a wrong declared width"
    if ← isTrue (chk s!"{M}.ved_mod" (tup lo k (names.reverse))) then throwError "ChainOkF accepts a wrong bundle name list"
  logInfo m!"compose connect ChainOkF controls: 1 accepted, 4 refused by the kernel"

/-- info: compose connect ChainOkF controls: 1 accepted, 4 refused by the kernel -/
#guard_msgs in
run_cmd chainControls

/-! ## Chained instances (R230's shape): the output of one combinational instance feeds the next instance's data port

`chainTx`: `mkB (mkA ph)` (`ph` a register); `chain3Tx`: `mkC (mkB (mkA ph))`.  The synthesiser emits the chain twice (the second
copy is not read by any register); both copies are instances of the checked design and are paired with the same calls.  The
accepted rows are checked as above (stored type `==` `U2HRStmt`, same artifact, std3, kernel, the children's real theorems occur,
no per-cone fallback: connection lemmas only).  CONTROLS: wrong wiring, instance mix-up, width mismatch on the chained port,
the option off (the old refusal text). -/

@[hardware_module]
def mkB (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x - (Signal.pure 5#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

@[hardware_module]
def mkC (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (x + (Signal.pure 7#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4))

def chainTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let phase ← Signal.reg 0#4
    let outR ← Signal.reg 0#4
    let ph := (phase : Signal defaultDomain (BitVec 4))
    let k1 := mkA ph
    let k2 := mkB k1
    phase <~ Signal.mux go (ph + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4)) ph
    outR <~ k2
    return (outR : Signal defaultDomain (BitVec 4))

/-- A copy for the controls (never accepted itself). -/
def chainTxRef (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let phase ← Signal.reg 0#4
    let outR ← Signal.reg 0#4
    let ph := (phase : Signal defaultDomain (BitVec 4))
    let k1 := mkA ph
    let k2 := mkB k1
    phase <~ Signal.mux go (ph + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4)) ph
    outR <~ k2
    return (outR : Signal defaultDomain (BitVec 4))

def chain3Tx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let phase ← Signal.reg 0#4
    let outR ← Signal.reg 0#4
    let ph := (phase : Signal defaultDomain (BitVec 4))
    let k1 := mkA ph
    let k2 := mkB k1
    let k3 := mkC k2
    phase <~ Signal.mux go (ph + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4)) ph
    outR <~ k3
    return (outR : Signal defaultDomain (BitVec 4))

/-- As `checkRow`, for several children: every child's real theorem occurs in the proof. -/
def checkChain (decl : Name) (kidThms : List Name) (nRegs : Nat) : CommandElabM Unit := do
  unless Tools.VedComposeConnect.ved.compose.connect.get (← getOptions) do throwError "the option ved.compose.connect is not on"
  let nMsg0 := (← get).messages.toList.length
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  let logs := ((← get).messages.toList.drop nMsg0).filter fun msg => msg.severity == .information
  let logTxt ← logs.mapM fun msg => msg.data.toString
  let conn := logTxt.filter fun s => (s.splitOn "VED COMPOSE CONNECT").length > 1
  modify fun s => { s with messages := (s.messages.toList.take nMsg0).foldl (fun l msg => l.add msg) {} }
  unless conn.length == nRegs + 1 do throwError "{decl}: {conn.length} connection log lines, expected {nRegs + 1}: {conn}"
  let (m2, d2) ← synthOf decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    unless decide (m = m2) && d.topModule == d2.topModule && decide (d.modules = d2.modules) do
      throwError "{decl}: the returned module/design differ from the declaration's own synthesis"
    let nm := HNames.ofBase decl
    let some ci := (← getEnv).find? nm.mod | throwError "{nm.mod} missing"
    unless ci.value! == toExpr m2 do throwError "{nm.mod} is not the declaration's own module"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    for k in kidThms do
      unless ti.value.getUsedConstants.contains k do throwError "{thm}: the child theorem {k} does not occur"
    -- `reg_connectN` / `out_connectN`: the normalised comparison selected under `ved.compose.multiCircuit`
    let nr := countApps ti.value ``Tools.VedComposeConnect.reg_connect + countApps ti.value ``Tools.VedComposeConnect.reg_connectN
    let no := countApps ti.value ``Tools.VedComposeConnect.out_connect + countApps ti.value ``Tools.VedComposeConnect.out_connectN
    unless nr == nRegs && no == 1 do throwError "{decl}: reg_connect sites {nr} (expected {nRegs}), out_connect sites {no} (expected 1)"
    logInfo m!"compose connect chain OK: {nRegs} registers by reg_connect, 1 port by out_connect, {kidThms.length} child theorems, std3, type ==, same artifact"

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 2 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd checkChain ``chainTx [`Tests.Ved.ComposeConnectCheck.chainTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1, `Tests.Ved.ComposeConnectCheck.chainTx.ved_child.Tests.Ved.ComposeConnectCheck.mkB.ved_u1] 2

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 3 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd checkChain ``chain3Tx [`Tests.Ved.ComposeConnectCheck.chain3Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1, `Tests.Ved.ComposeConnectCheck.chain3Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkB.ved_u1, `Tests.Ved.ComposeConnectCheck.chain3Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkC.ved_u1] 2

/- Names in the synthesised `chainTxRef`: instances (in body order) 0 = `mkA` on `_tmp_op_a_2` (output wire `_tmp_arg0_6`), 1 = `mkB`
on `_tmp_arg0_6`, 2 and 3 = the dead copy of the chain (`_gen_k1`, `_gen_k2`); `_tmp_op_a_2` is the register `phase`'s read. -/

def chainTxControls : CommandElabM Unit := do
  let (m, d) ← synthOf ``chainTxRef
  let noT : Phase1 → CommandElabM Phase1 := fun p => pure p
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true }) do
    -- WRONG WIRING: the consumer's port is fed by another net (the register read instead of the producer's output), both copies
    expectRefusedT ``chainTxRef "kernel" "?" { m with body := setConnAt 3 "_gen_x" (.ref "_tmp_op_a_2") (setConnAt 1 "_gen_x" (.ref "_tmp_op_a_2") m.body) } d noT
    -- INSTANCE MIX-UP: every instance is paired with the other child's call
    expectRefusedT ``chainTxRef "proof" "unsolved goals" m d fun p => pure { p with insts := p.insts.map fun ii => { ii with call := 1 - ii.call } }
    -- WIDTH MISMATCH on the chained port: the declared width of the producer's output wire is not the port's
    expectRefusedT ``chainTxRef "hier-shape" "width mismatch" { m with wires := m.wires.map fun w =>
      if w.name == "_tmp_arg0_6" then { w with ty := .bitVector 5 } else w } d noT
  -- the option OFF: the old refusal text, unchanged
  expectRefusedT ``chainTxRef "conns" "another instance's output" m d noT

/-- info: compose connect chain controls: 4 refused -/
#guard_msgs in
run_cmd do
  chainTxControls
  logInfo m!"compose connect chain controls: 4 refused"

/-! ### A chain closer to R230's shape: a consumer with two data ports (a register-derived net and the producer's output) and a
third port reading a register directly, a struct output of three fields; the declaration's own port reads the loop.  (A port that is
directly a child's output exports no loop state unless `sparkle.deepExportState` is on: the next section.) -/

@[hardware_module]
def mkS (x c n : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  Signal.mux (n === (Signal.pure 0#4 : Signal defaultDomain (BitVec 4))) x (c + n : Signal defaultDomain (BitVec 4))

structure PT3 (dom : DomainConfig) where
  b : Signal dom (BitVec 4)
  v : Signal dom Bool
  l : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (PT3 dom) dom := ⟨⟩

def chainMixCirc (inp : Signal defaultDomain (BitVec 4)) (go : Signal defaultDomain Bool) : PT3 defaultDomain :=
  circuit do
    let cnt ← Signal.reg 0#4
    let held ← Signal.reg 0#4
    let cs := (cnt : Signal defaultDomain (BitVec 4))
    let hd := (held : Signal defaultDomain (BitVec 4))
    let p0 := (Signal.pure 0#4 : Signal defaultDomain (BitVec 4))
    let p1 := (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))
    let isIdle := cs === p0
    let isLast := cs === (Signal.pure 9#4 : Signal defaultDomain (BitVec 4))
    let isEm := ~~~isIdle
    let now := Signal.mux go inp hd
    let k1 := mkA now
    let k2 := mkS now k1 cs
    cnt <~ Signal.mux go p1 (Signal.mux isLast p0 (Signal.mux isEm (cs + p1 : Signal defaultDomain (BitVec 4)) cs))
    held <~ now
    return ({ b := Signal.mux go k2 hd, v := isEm, l := isLast } : PT3 defaultDomain)

def chainMixTx (inp : Signal defaultDomain (BitVec 4)) (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (chainMixCirc inp go).b

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 2 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
run_cmd checkChain ``chainMixTx [`Tests.Ved.ComposeConnectCheck.chainMixTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1, `Tests.Ved.ComposeConnectCheck.chainMixTx.ved_child.Tests.Ved.ComposeConnectCheck.mkS.ved_u1] 2

/-! ### The declaration's own port is DIRECTLY a child's output (connect14, option `sparkle.deepExportState`)

The open parent's port reads no register, so `Tools/DeepElab.lean` closes its capstone goal early and, without the option, exports no
loop state (`[deep]` refusal "did not export its loop state", also for ONE instance).  With `sparkle.deepExportState` the state is
proved and exported before the output simp.  `direct1Tx`: port = the output of ONE instance; `direct2Tx`: port = the output of the
second instance of a chain.  Checked as above (type `==`, same artifact, std3, kernel, the children's theorems occur, no per-cone
fallback).  CONTROLS (on a copy): the option off (the old `[deep]` text), wrong child output wiring on the direct port, wrong width. -/

def direct1Circ (inp : Signal defaultDomain (BitVec 4)) (go : Signal defaultDomain Bool) : PT3 defaultDomain :=
  circuit do
    let cnt ← Signal.reg 0#4
    let held ← Signal.reg 0#4
    let cs := (cnt : Signal defaultDomain (BitVec 4))
    let hd := (held : Signal defaultDomain (BitVec 4))
    let p0 := (Signal.pure 0#4 : Signal defaultDomain (BitVec 4))
    let p1 := (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))
    let isIdle := cs === p0
    let isLast := cs === (Signal.pure 9#4 : Signal defaultDomain (BitVec 4))
    let isEm := ~~~isIdle
    let now := Signal.mux go inp hd
    let k1 := mkA now
    cnt <~ Signal.mux go p1 (Signal.mux isLast p0 (Signal.mux isEm (cs + p1 : Signal defaultDomain (BitVec 4)) cs))
    held <~ now
    return ({ b := k1, v := isEm, l := isLast } : PT3 defaultDomain)

def direct1Tx (inp : Signal defaultDomain (BitVec 4)) (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (direct1Circ inp go).b

def direct2Circ (inp : Signal defaultDomain (BitVec 4)) (go : Signal defaultDomain Bool) : PT3 defaultDomain :=
  circuit do
    let cnt ← Signal.reg 0#4
    let held ← Signal.reg 0#4
    let cs := (cnt : Signal defaultDomain (BitVec 4))
    let hd := (held : Signal defaultDomain (BitVec 4))
    let p0 := (Signal.pure 0#4 : Signal defaultDomain (BitVec 4))
    let p1 := (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))
    let isIdle := cs === p0
    let isLast := cs === (Signal.pure 9#4 : Signal defaultDomain (BitVec 4))
    let isEm := ~~~isIdle
    let now := Signal.mux go inp hd
    let k1 := mkA now
    let k2 := mkS now k1 cs
    cnt <~ Signal.mux go p1 (Signal.mux isLast p0 (Signal.mux isEm (cs + p1 : Signal defaultDomain (BitVec 4)) cs))
    held <~ now
    return ({ b := k2, v := isEm, l := isLast } : PT3 defaultDomain)

def direct2Tx (inp : Signal defaultDomain (BitVec 4)) (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (direct2Circ inp go).b

/-- A copy for the controls (never accepted itself). -/
def direct2Ref (inp : Signal defaultDomain (BitVec 4)) (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (direct2Circ inp go).b

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option sparkle.deepExportState true in
run_cmd checkChain ``direct1Tx [`Tests.Ved.ComposeConnectCheck.direct1Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 2

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 2 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option sparkle.deepExportState true in
run_cmd checkChain ``direct2Tx [`Tests.Ved.ComposeConnectCheck.direct2Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1, `Tests.Ved.ComposeConnectCheck.direct2Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkS.ved_u1] 2

/- Names in the synthesised `direct2Ref`: `assign out = _gen_out`; `_gen_out` is the output of the second instance (`mkS`), `_tmp_arg1_23`
the output of the first (`mkA`) -/

def directControls : CommandElabM Unit := do
  let (m, d) ← synthOf ``direct2Ref
  let noT : Phase1 → CommandElabM Phase1 := fun p => pure p
  -- the option OFF (step and connect on): the old `[deep]` text
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true }) do
    expectRefusedT ``direct2Ref "deep" "did not export its loop state" m d noT
  withScope (fun sc => { sc with opts := ((sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true).setBool `sparkle.deepExportState true }) do
    -- WRONG CHILD OUTPUT WIRING on the direct port: the port is the other instance's output
    expectRefusedT ``direct2Ref "proof" "proved that the proposition" { m with body := m.body.map fun s => match s with
      | .assign "out" _ => .assign "out" (.ref "_tmp_arg1_23")
      | s => s } d noT
    -- WRONG WIDTH on the direct port: the declared width of the child's output wire
    expectRefusedT ``direct2Ref "hier-shape" "width mismatch" { m with wires := m.wires.map fun w =>
      if w.name == "_gen_out" then { w with ty := .bitVector 5 } else w } d noT

/-- info: compose connect direct-port controls: 3 refused -/
#guard_msgs in
run_cmd do
  directControls
  logInfo m!"compose connect direct-port controls: 3 refused"

/-! ### Two wired closed circuits fused into one parent (connect15, option `ved.compose.multiCircuit`)

`twoTx`: `let a := twoStageA go; twoStageB a.ph`: two `circuit do` blocks wired by a `let` OUTSIDE both (the shape of `usbWebServer`); the
child `mkA` is called in the second on the first's register read.  The declaration is not ONE `runCircuitH`: with the option the
generator fuses the two into one `runCircuitH` over the appended registers (`Tools/VedComposeMultiCircuit.lean`, `fuse_run`; A's
registers first) and proves `decl xs = fused xs` by the kernel, then continues as for one circuit.  `two2Tx`: the child's argument
reads A's register AND B's own register.  Checked as above (type `==`, same artifact, std3, kernel, the child theorem occurs, no
per-cone fallback).  CONTROLS (on a copy): the option off (the old `[deep]` text), the two registers swapped in the IR (register order
vs the fused order), wrong wiring between the circuits, wrong width. -/

structure TwoA (dom : DomainConfig) where
  ph : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (TwoA dom) dom := ⟨⟩
structure TwoB (dom : DomainConfig) where
  b : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (TwoB dom) dom := ⟨⟩

def twoStageA (go : Signal defaultDomain Bool) : TwoA defaultDomain :=
  circuit do
    let phase ← Signal.reg 0#4
    let ph := (phase : Signal defaultDomain (BitVec 4))
    phase <~ Signal.mux go (ph + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))) ph
    return ({ ph := (phase : Signal defaultDomain (BitVec 4)) } : TwoA defaultDomain)

def twoStageB (ph : Signal defaultDomain (BitVec 4)) : TwoB defaultDomain :=
  circuit do
    let outR ← Signal.reg 0#4
    outR <~ mkA ph
    return ({ b := (outR : Signal defaultDomain (BitVec 4)) } : TwoB defaultDomain)

def twoP (go : Signal defaultDomain Bool) : TwoB defaultDomain :=
  let a := twoStageA go
  twoStageB a.ph

def twoTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (twoP go).b

/-- A copy for the controls (never accepted itself). -/
def twoRef (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (twoP go).b

def twoStageB2 (ph : Signal defaultDomain (BitVec 4)) : TwoB defaultDomain :=
  circuit do
    let outR ← Signal.reg 0#4
    let o := (outR : Signal defaultDomain (BitVec 4))
    outR <~ mkA (ph + o)
    return ({ b := o } : TwoB defaultDomain)

def twoP2 (go : Signal defaultDomain Bool) : TwoB defaultDomain :=
  let a := twoStageA go
  twoStageB2 a.ph

def two2Tx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (twoP2 go).b

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``twoTx [`Tests.Ved.ComposeConnectCheck.twoTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 2

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``two2Tx [`Tests.Ved.ComposeConnectCheck.two2Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 2

/- Names in the synthesised `twoRef`: registers `_tmp_a_6` (A) and `_tmp_a_12` (B); the instance of `mkA` reads `_tmp_op_a_3` (a slice of
A's register read) on its port `_gen_x`. -/

def swapRegs (b : List Stmt) : List Stmt :=
  let ra := b.find? fun s => match s with | .register "_tmp_a_6" .. => true | _ => false
  let rb := b.find? fun s => match s with | .register "_tmp_a_12" .. => true | _ => false
  match ra, rb with
  | some a, some c => b.map fun s => match s with
    | .register "_tmp_a_6" .. => c
    | .register "_tmp_a_12" .. => a
    | s => s
  | _, _ => b

def twoControls : CommandElabM Unit := do
  let (m, d) ← synthOf ``twoRef
  let noT : Phase1 → CommandElabM Phase1 := fun p => pure p
  -- the multiCircuit option OFF (step and connect on): the old `[deep]` refusal, unchanged
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true }) do
    expectRefusedT ``twoRef "deep" "the parent has 2 registers, the open parent's circuit has 1" m d noT
  withScope (fun sc => { sc with opts := ((sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true).setBool `ved.compose.multiCircuit true }) do
    -- REGISTER ORDER: the two registers swapped in the returned IR (the fused order is A's, then B's)
    expectRefusedT ``twoRef "proof" "proved that the proposition" { m with body := swapRegs m.body } d noT
    -- WRONG WIRING between the circuits: the child is fed by B's own register instead of A's
    expectRefusedT ``twoRef "kernel" "let-declaration type mismatch" { m with body := setConnAt 0 "_gen_x" (.ref "_tmp_a_12") m.body } d noT
    -- WIDTH MISMATCH: the declared width of A's register wire
    expectRefusedT ``twoRef "proof" "proved that the proposition" { m with wires := m.wires.map fun w =>
      if w.name == "_tmp_a_6" then { w with ty := .bitVector 5 } else w } d noT

/-- info: compose connect two-circuit controls: 4 refused -/
#guard_msgs in
run_cmd do
  twoControls
  logInfo m!"compose connect two-circuit controls: 4 refused"

/-! The same family: A returns a plain `Signal` read inside B (`nestTx`, the ToyNest shape: the child's argument mixes B's register and A's
output), and A returns a struct two fields of which B reads, with a private inline helper in A (`three3Tx`, the shape of the ICMP
responder: `Tools/DeepElab.lean` option `sparkle.deepExportState`, helpers unfolded before the state export). -/

def nestParser (b : Signal defaultDomain (BitVec 4)) (v : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let r ← Signal.reg 0#4
    let rS := (r : Signal defaultDomain (BitVec 4))
    r <~ Signal.mux v b rS
    return rS

def nestTx (b : Signal defaultDomain (BitVec 4)) (v go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  let p := nestParser b v
  circuit do
    let phase ← Signal.reg 0#4
    let outR ← Signal.reg 0#4
    let ph := (phase : Signal defaultDomain (BitVec 4))
    let oS := (outR : Signal defaultDomain (BitVec 4))
    phase <~ Signal.mux go (ph + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4)) ph
    outR <~ Signal.mux go (mkA (ph + p)) oS
    return oS

/-- info: compose connect chain OK: 3 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``nestTx [`Tests.Ved.ComposeConnectCheck.nestTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 3

@[inline] private def twoHelp (acc : Signal defaultDomain (BitVec 4)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  (acc <<< (1#4 : BitVec 4)) ||| b

structure Two3A (dom : DomainConfig) where
  ph : Signal dom (BitVec 4)
  en : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Two3A dom) dom := ⟨⟩

def three3StageA (go : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) : Two3A defaultDomain :=
  circuit do
    let phase ← Signal.reg 0#4
    let dn ← Signal.reg false
    let ph := (phase : Signal defaultDomain (BitVec 4))
    phase <~ Signal.mux go (twoHelp ph inp) ph
    dn <~ go
    return ({ ph := (phase : Signal defaultDomain (BitVec 4)), en := (dn : Signal defaultDomain Bool) } : Two3A defaultDomain)

def three3StageB (a : Two3A defaultDomain) : TwoB defaultDomain :=
  circuit do
    let outR ← Signal.reg 0#4
    let o := (outR : Signal defaultDomain (BitVec 4))
    outR <~ Signal.mux a.en (mkA a.ph) o
    return ({ b := o } : TwoB defaultDomain)

def three3P (go : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) : TwoB defaultDomain :=
  let a := three3StageA go inp
  three3StageB a

def three3Tx (go : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (three3P go inp).b

/-- info: compose connect chain OK: 3 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``three3Tx [`Tests.Ved.ComposeConnectCheck.three3Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 3

structure TwoD (dom : DomainConfig) where
  b : Signal dom (BitVec 4)
  v : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (TwoD dom) dom := ⟨⟩

/-- A direct port (the child's output, no register read; the other field keeps the registers observable) of two wired circuits, with the
private helper in A: needs `sparkle.deepExportState` and the helper unfolded before the state export. -/
def twoDirStageB (a : Two3A defaultDomain) : TwoD defaultDomain :=
  circuit do
    let outR ← Signal.reg 0#4
    let o := (outR : Signal defaultDomain (BitVec 4))
    outR <~ Signal.mux a.en a.ph o
    return ({ b := mkA (a.ph + o), v := o } : TwoD defaultDomain)

def twoDirTx (go : Signal defaultDomain Bool) (inp : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (twoDirStageB (three3StageA go inp)).b

/-- info: compose connect chain OK: 3 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
set_option sparkle.deepExportState true in
run_cmd checkChain ``twoDirTx [`Tests.Ved.ComposeConnectCheck.twoDirTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 3

/-! ### K > 2 closed circuits (connect16): a chain A -> B -> C and two circuits A1, A2 both read by D

`cc3Tx`: `let a := twoStageA go; let b := twoStageB a.ph; twoStageB b.b` (a circuit read by a circuit that is itself read; fused
innermost first: registers of A, B, C).  `fan2Tx`: `let a := twoStageA go; let b := twoStageA go2; twoStageD a.ph b.ph` (two independent
circuits read by one; fused one after the other, the last let-bound first, so the registers come in let order A1, A2, D).
`fanMixTx`: A1 is read by B and B and A2 both by D.  Checked as above.  CONTROLS (chain, on a copy): the option off, the order of two
circuits swapped (registers), wrong wiring between two of the circuits, a width mismatch on one circuit's wire. -/

def twoStageD (p q : Signal defaultDomain (BitVec 4)) : TwoB defaultDomain :=
  circuit do
    let outR ← Signal.reg 0#4
    outR <~ mkA (p + q)
    return ({ b := (outR : Signal defaultDomain (BitVec 4)) } : TwoB defaultDomain)

def cc3P (go : Signal defaultDomain Bool) : TwoB defaultDomain :=
  let a := twoStageA go
  let b := twoStageB a.ph
  twoStageB b.b

def cc3Tx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (cc3P go).b

/-- A copy for the controls (never accepted itself). -/
def cc3Ref (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (cc3P go).b

def fan2P (go go2 : Signal defaultDomain Bool) : TwoB defaultDomain :=
  let a := twoStageA go
  let b := twoStageA go2
  twoStageD a.ph b.ph

def fan2Tx (go go2 : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (fan2P go go2).b

def fanMixP (go go2 : Signal defaultDomain Bool) : TwoB defaultDomain :=
  let a := twoStageA go
  let b := twoStageB a.ph
  let c := twoStageA go2
  twoStageD b.b c.ph

def fanMixTx (go go2 : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (fanMixP go go2).b

/-- info: compose connect chain OK: 3 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``cc3Tx [`Tests.Ved.ComposeConnectCheck.cc3Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 3

/-- info: compose connect chain OK: 3 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``fan2Tx [`Tests.Ved.ComposeConnectCheck.fan2Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 3

/-- info: compose connect chain OK: 4 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``fanMixTx [`Tests.Ved.ComposeConnectCheck.fanMixTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 4

/- Names in the synthesised `cc3Ref`: registers `_tmp_a_7` (A), `_tmp_a_13` (B), `_tmp_a_19` (C); instance 0 of `mkA` (in B) reads
`_tmp_op_a_4` (a slice of A's register read), instance 1 (in C) reads B's register `_tmp_a_13`, both on `_gen_x`. -/

def swapRegsAt (r1 r2 : String) (b : List Stmt) : List Stmt :=
  let ra := b.find? fun s => match s with | .register n .. => n == r1 | _ => false
  let rb := b.find? fun s => match s with | .register n .. => n == r2 | _ => false
  match ra, rb with
  | some a, some c => b.map fun s => match s with
    | .register n .. => if n == r1 then c else if n == r2 then a else s
    | s => s
  | _, _ => b

def cc3Controls : CommandElabM Unit := do
  let (m, d) ← synthOf ``cc3Ref
  let noT : Phase1 → CommandElabM Phase1 := fun p => pure p
  -- the multiCircuit option OFF (step and connect on): the old `[deep]` refusal
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true }) do
    expectRefusedT ``cc3Ref "open" "its instances' input nets form 2 distinct classes" m d noT
  withScope (fun sc => { sc with opts := ((sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true).setBool `ved.compose.multiCircuit true }) do
    -- ORDER of two circuits: the registers of A and B swapped in the returned IR (the fused order is A, B, C)
    expectRefusedT ``cc3Ref "proof" "proved that the proposition" { m with body := swapRegsAt "_tmp_a_7" "_tmp_a_13" m.body } d noT
    -- ORDER of the other pair
    expectRefusedT ``cc3Ref "proof" "proved that the proposition" { m with body := swapRegsAt "_tmp_a_13" "_tmp_a_19" m.body } d noT
    -- WRONG WIRING between B and C: the child in C is fed by A's register instead of B's
    expectRefusedT ``cc3Ref "kernel" "let-declaration type mismatch" { m with body := setConnAt 1 "_gen_x" (.ref "_tmp_a_7") m.body } d noT
    -- WIDTH MISMATCH: the declared width of B's register wire
    expectRefusedT ``cc3Ref "proof" "proved that the proposition" { m with wires := m.wires.map fun w =>
      if w.name == "_tmp_a_13" then { w with ty := .bitVector 5 } else w } d noT

/-- info: compose connect three-circuit controls: 5 refused -/
#guard_msgs in
run_cmd do
  cc3Controls
  logInfo m!"compose connect three-circuit controls: 5 refused"

/-! ### Pure-wiring tops (connect17): the declaration's value is an output function over closed circuits, no outer circuit

`indepTx`: `(indepC go).b + (indepC go2).b` (two independent circuits, neither reads the other, combined by an output function; the
old path took only the last operand's run).  `wsTx`: the struct-constructor top of R246's shape, `({ tx := b.b } : WireOut).tx` over a
circuit that reads another (the old `findRun` stopped at the constructor).  `ws2Tx`: `{ tx := b.b + c.b }` over three circuits, one
reading another, the top only wires.  Checked as above.  CONTROLS (on copies): the option off (old text), the registers of two circuits
swapped, a wrong wiring (a child fed by another circuit's register), a width mismatch on one circuit's register. -/

def indepC (go : Signal defaultDomain Bool) : TwoB defaultDomain :=
  circuit do
    let outR ← Signal.reg 0#4
    let o := (outR : Signal defaultDomain (BitVec 4))
    outR <~ Signal.mux go (mkA o) o
    return ({ b := o } : TwoB defaultDomain)

structure WireOut (dom : DomainConfig) where
  tx : Signal dom (BitVec 4)
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (WireOut dom) dom := ⟨⟩

def indepTx (go go2 : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (indepC go).b + (indepC go2).b

/-- A copy for the controls (never accepted itself). -/
def indepRef (go go2 : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (indepC go).b + (indepC go2).b

def wsP (go : Signal defaultDomain Bool) : WireOut defaultDomain :=
  let a := twoStageA go
  let b := twoStageB a.ph
  ({ tx := b.b } : WireOut defaultDomain)

def wsTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (wsP go).tx

def ws2P (go go2 : Signal defaultDomain Bool) : WireOut defaultDomain :=
  let a := twoStageA go
  let b := twoStageB a.ph
  let c := indepC go2
  ({ tx := b.b + c.b } : WireOut defaultDomain)

def ws2Tx (go go2 : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (ws2P go go2).tx

/-- A copy for the controls (never accepted itself). -/
def ws2Ref (go go2 : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (ws2P go go2).tx

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``indepTx [`Tests.Ved.ComposeConnectCheck.indepTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 2

/-- info: compose connect chain OK: 2 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``wsTx [`Tests.Ved.ComposeConnectCheck.wsTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 2

/-- info: compose connect chain OK: 3 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``ws2Tx [`Tests.Ved.ComposeConnectCheck.ws2Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 3

/-- The register names of a module body, in order. -/
def regNamesOf (b : List Stmt) : List String :=
  b.filterMap fun s => match s with | .register n .. => some n | _ => none

def wiringControls : CommandElabM Unit := do
  let noT : Phase1 → CommandElabM Phase1 := fun p => pure p
  let (m, d) ← synthOf ``ws2Ref
  let rs := regNamesOf m.body
  unless rs.length == 3 do throwError "ws2Ref: expected 3 registers, got {rs}"
  -- the option OFF (step and connect on): the old refusal
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true }) do
    expectRefusedT ``ws2Ref "open" "does not reduce to a `circuit do`" m d noT
  withScope (fun sc => { sc with opts := ((sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true).setBool `ved.compose.multiCircuit true }) do
    -- ORDER: the registers of the two wired circuits swapped
    expectRefusedT ``ws2Ref "proof" "proved that the proposition" { m with body := swapRegsAt rs[0]! rs[1]! m.body } d noT
    -- ORDER: the independent circuit's register swapped with a wired one
    expectRefusedT ``ws2Ref "proof" "proved that the proposition" { m with body := swapRegsAt rs[1]! rs[2]! m.body } d noT
    -- WRONG WIRING: the child of the independent circuit is fed by the first circuit's register
    expectRefusedT ``ws2Ref "kernel" "let-declaration type mismatch" { m with body := setConnAt 1 "_gen_x" (.ref rs[0]!) m.body } d noT
    -- WIDTH MISMATCH: the declared width of the second circuit's register wire
    expectRefusedT ``ws2Ref "proof" "proved that the proposition" { m with wires := m.wires.map fun w =>
      if w.name == rs[1]! then { w with ty := .bitVector 5 } else w } d noT
  -- two independent circuits: the option off, the registers swapped
  let (m2, d2) ← synthOf ``indepRef
  let rs2 := regNamesOf m2.body
  unless rs2.length == 2 do throwError "indepRef: expected 2 registers, got {rs2}"
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true }) do
    expectRefusedT ``indepRef "open" "its instances' input nets form 2 distinct classes" m2 d2 noT
  withScope (fun sc => { sc with opts := ((sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true).setBool `ved.compose.multiCircuit true }) do
    expectRefusedT ``indepRef "proof" "proved that the proposition" { m2 with body := swapRegsAt rs2[0]! rs2[1]! m2.body } d2 noT

/-- info: compose connect wiring controls: 7 refused -/
#guard_msgs in
run_cmd do
  wiringControls
  logInfo m!"compose connect wiring controls: 7 refused"


/-! ### A circuit read by several readers (unit 19: shared circuits are fused ONCE)

`dmTx`: `let a := twoStageA go; let s := twoStageB a.ph; twoStageD a.ph s.b` (D reads A and S, S reads A: a shared circuit).  Unit 18
pinned a refusal here: the generator fused a reader at a time and abstracted every occurrence of the circuit read, so A was fused twice
(a copy inside S and a copy of its own: 4 registers against the parent's 3).  With the option `ved.compose.multiCircuit` a circuit with
several readers makes the generator fuse every circuit ONCE (`fuseShared`, `Tools/VedU2HierMultiGen.lean`): the circuits in post-order of
the read graph, the fusion so far carrying the tuple of the circuits' outputs, a later reader reading a shared circuit by a projection of
it.  `dm2Tx`: A is read by two readers S1, S2 and D reads both (4 circuits).  `dmSopTx`: A is read by S, by U and by the top, S by U, U
by the top (R246's `sopPulse` shape: a reader that itself reads the shared circuit and is read by a later one).  `sc2Tx`, `sc4Tx`: a
pure-wiring top over 2 and 4 readers of one circuit (the scaling series; `sc8Tx` in the measurement only).  Checked as above (type `==`,
same artifact, std3, kernel, the child theorem occurs, no per-cone fallback).  CONTROLS (on copies of `dmTx`): the option off (old text),
the registers of two circuits swapped, a wrong wiring, a width mismatch. -/

def dmP (go : Signal defaultDomain Bool) : TwoB defaultDomain :=
  let a := twoStageA go
  let s := twoStageB a.ph
  twoStageD a.ph s.b

def dmTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (dmP go).b

/-- A copy for the controls (never accepted itself). -/
def dmRef (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (dmP go).b

def twoStageK (c : BitVec 4) (ph : Signal defaultDomain (BitVec 4)) : TwoB defaultDomain :=
  circuit do
    let outR ← Signal.reg 0#4
    outR <~ mkA (ph + (Signal.pure c : Signal defaultDomain (BitVec 4)))
    return ({ b := (outR : Signal defaultDomain (BitVec 4)) } : TwoB defaultDomain)

def dm2P (go : Signal defaultDomain Bool) : TwoB defaultDomain :=
  let a := twoStageA go
  let s1 := twoStageK 1#4 a.ph
  let s2 := twoStageK 2#4 a.ph
  twoStageD s1.b s2.b

def dm2Tx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (dm2P go).b

def dmSopP (go : Signal defaultDomain Bool) : TwoB defaultDomain :=
  let a := twoStageA go
  let s := twoStageB a.ph
  let u := twoStageD a.ph s.b
  twoStageD u.b a.ph

def dmSopTx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (dmSopP go).b

def sc2P (go : Signal defaultDomain Bool) : WireOut defaultDomain :=
  let a := twoStageA go
  let r1 := twoStageK 1#4 a.ph
  let r2 := twoStageK 2#4 a.ph
  ({ tx := r1.b + r2.b } : WireOut defaultDomain)

def sc2Tx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (sc2P go).tx

def sc4P (go : Signal defaultDomain Bool) : WireOut defaultDomain :=
  let a := twoStageA go
  let r1 := twoStageK 1#4 a.ph
  let r2 := twoStageK 2#4 a.ph
  let r3 := twoStageK 3#4 a.ph
  let r4 := twoStageK 4#4 a.ph
  ({ tx := r1.b + r2.b + r3.b + r4.b } : WireOut defaultDomain)

def sc4Tx (go : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  (sc4P go).tx

/-- info: compose connect chain OK: 3 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``dmTx [`Tests.Ved.ComposeConnectCheck.dmTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 3

/-- info: compose connect chain OK: 4 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``dm2Tx [`Tests.Ved.ComposeConnectCheck.dm2Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 4

/-- info: compose connect chain OK: 4 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``dmSopTx [`Tests.Ved.ComposeConnectCheck.dmSopTx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 4

/-- info: compose connect chain OK: 3 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``sc2Tx [`Tests.Ved.ComposeConnectCheck.sc2Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 3

/-- info: compose connect chain OK: 5 registers by reg_connect, 1 port by out_connect, 1 child theorems, std3, type ==, same artifact -/
#guard_msgs in
set_option ved.compose.step true in
set_option ved.compose.connect true in
set_option ved.compose.multiCircuit true in
run_cmd checkChain ``sc4Tx [`Tests.Ved.ComposeConnectCheck.sc4Tx.ved_child.Tests.Ved.ComposeConnectCheck.mkA.ved_u1] 5

def diamondControl : CommandElabM Unit := do
  let noT : Phase1 → CommandElabM Phase1 := fun p => pure p
  let (m, d) ← synthOf ``dmRef
  let rs := regNamesOf m.body
  unless rs.length == 3 do throwError "dmRef: expected 3 registers, got {rs}"
  -- the option OFF (step and connect on)
  withScope (fun sc => { sc with opts := (sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true }) do
    expectRefusedT ``dmRef "open" "its instances' input nets form 2 distinct classes" m d noT
  withScope (fun sc => { sc with opts := ((sc.opts.setBool `ved.compose.step true).setBool `ved.compose.connect true).setBool `ved.compose.multiCircuit true }) do
    -- ORDER: the registers of A and S swapped (the fused order is A, S, D)
    expectRefusedT ``dmRef "proof" "proved that the proposition" { m with body := swapRegsAt rs[0]! rs[1]! m.body } d noT
    expectRefusedT ``dmRef "proof" "unsolved goals" { m with body := swapRegsAt rs[1]! rs[2]! m.body } d noT
    -- WRONG WIRING: the child in D fed by A's register
    expectRefusedT ``dmRef "kernel" "let-declaration type mismatch" { m with body := setConnAt 1 "_gen_x" (.ref rs[0]!) m.body } d noT
    -- WIDTH MISMATCH: the declared width of S's register wire
    expectRefusedT ``dmRef "proof" "proved that the proposition" { m with wires := m.wires.map fun w =>
      if w.name == rs[1]! then { w with ty := .bitVector 5 } else w } d noT

/-- info: compose connect shared-circuit controls: 5 refused -/
#guard_msgs in
run_cmd do
  diamondControl
  logInfo m!"compose connect shared-circuit controls: 5 refused"



/-! ## Controls of the multi-circuit trace closer (`ved_bv_close3`, used by `#verify_elab_deep` under `sparkle.deepRepre`, i.e. under
`ved.compose.multiCircuit`): the register-step goals of the real chain (txSequencer, slipFramer, uartTx; the atoms are the loop-state
components) are closed by the normalise-then-interleaved-split closer; a goal with one constant changed is refused. -/

theorem closerFsm (b : Bool) (o : BitVec 8) (d : BitVec 16) (g0 : BitVec 1) (g1 : BitVec 7) (g2 : BitVec 2) (g3 g4 : BitVec 8) (g5 : BitVec 1) (g6 : BitVec 10) (g7 : BitVec 4) (g8 : BitVec 16) (g9 : BitVec 1) :
    (if g2 = 2#2 then 1#2
    else
      if
          ((g2 = 0#2 ∨ g2 = 1#2) ∧
              g0 = 1#1 ∧ ¬g1 = 74#7 ∧ ¬g1 = 75#7 ∧ ¬g1 = 76#7 ∧ ¬g1 = 77#7 ∧ ¬g1 = 78#7 ∧ ¬g1 = 79#7) ∧
            (o = 192#8 ∨ o = 219#8) then
        2#2
      else
        if
            ((g2 = 0#2 ∨ g2 = 1#2) ∧
                g0 = 1#1 ∧ ¬g1 = 74#7 ∧ ¬g1 = 75#7 ∧ ¬g1 = 76#7 ∧ ¬g1 = 77#7 ∧ ¬g1 = 78#7 ∧ ¬g1 = 79#7) ∧
              ¬o = 192#8 ∧ ¬o = 219#8 then
          1#2
        else if g2 = 1#2 ∧ g0 = 1#1 ∧ g1 = 74#7 then 0#2 else g2) =
    if (if g2 = 2#2 then 1#1 else 0#1) = 1#1 then 1#2
    else
      if
          ((if g2 = 0#2 then 1#1 else 0#1) ||| if g2 = 1#2 then 1#1 else 0#1) &&&
                (g0 &&&
                  ((~~~if g1 = 74#7 then 1#1 else 0#1) &&&
                    ~~~((if g1 = 75#7 then 1#1 else 0#1) |||
                        ((if g1 = 76#7 then 1#1 else 0#1) |||
                          ((if g1 = 77#7 then 1#1 else 0#1) |||
                            ((if g1 = 78#7 then 1#1 else 0#1) ||| if g1 = 79#7 then 1#1 else 0#1)))))) &&&
              ((if o = 192#8 then 1#1 else 0#1) ||| if o = 219#8 then 1#1 else 0#1) =
            1#1 then
        2#2
      else
        if
            ((if g2 = 0#2 then 1#1 else 0#1) ||| if g2 = 1#2 then 1#1 else 0#1) &&&
                  (g0 &&&
                    ((~~~if g1 = 74#7 then 1#1 else 0#1) &&&
                      ~~~((if g1 = 75#7 then 1#1 else 0#1) |||
                          ((if g1 = 76#7 then 1#1 else 0#1) |||
                            ((if g1 = 77#7 then 1#1 else 0#1) |||
                              ((if g1 = 78#7 then 1#1 else 0#1) ||| if g1 = 79#7 then 1#1 else 0#1)))))) &&&
                ~~~((if o = 192#8 then 1#1 else 0#1) ||| if o = 219#8 then 1#1 else 0#1) =
              1#1 then
          1#2
        else if (if g2 = 1#2 then 1#1 else 0#1) &&& (g0 &&& if g1 = 74#7 then 1#1 else 0#1) = 1#1 then 0#2 else g2 := by
  ved_bv_close3

theorem closerShift (b : Bool) (o : BitVec 8) (d : BitVec 16) (g0 : BitVec 1) (g1 : BitVec 7) (g2 : BitVec 2) (g3 g4 : BitVec 8) (g5 : BitVec 1) (g6 : BitVec 10) (g7 : BitVec 4) (g8 : BitVec 16) (g9 : BitVec 1) :
    (if g9 = 1#1 ∨ g5 = 1#1 ∧ ¬g9 = 1#1 then
      if g5 = 1#1 ∧ ¬g9 = 1#1 then 1#1 ++ (g4 ++ 0#1) else if g9 = 1#1 ∧ g8 = 0#16 then g6 >>> 1 else g6
    else 1023#10) =
    if g9 ||| g5 &&& ~~~g9 = 1#1 then
      if g5 &&& ~~~g9 = 1#1 then 1#1 ++ (g4 ++ 0#1)
      else if (g9 &&& if g8 = 0#16 then 1#1 else 0#1) = 1#1 then g6 >>> (1#10).toNat else g6
    else 1023#10 := by
  ved_bv_close3

/-- info: compose connect closer controls: 2 accepted, 1 refused -/
#guard_msgs in
set_option Elab.async false in
run_cmd do
  let msgs0 := (← get).messages
  let src := "theorem closerWrong (b : Bool) (o : BitVec 8) (d : BitVec 16) (g0 : BitVec 1) (g1 : BitVec 7) (g2 : BitVec 2) (g3 g4 : BitVec 8) (g5 : BitVec 1) (g6 : BitVec 10) (g7 : BitVec 4) (g8 : BitVec 16) (g9 : BitVec 1) :\n    (if g2 = 2#2 then 1#2\n    else\n      if\n          ((g2 = 0#2 ∨ g2 = 1#2) ∧\n              g0 = 1#1 ∧ ¬g1 = 74#7 ∧ ¬g1 = 75#7 ∧ ¬g1 = 76#7 ∧ ¬g1 = 77#7 ∧ ¬g1 = 78#7 ∧ ¬g1 = 79#7) ∧\n            (o = 192#8 ∨ o = 219#8) then\n        2#2\n      else\n        if\n            ((g2 = 0#2 ∨ g2 = 1#2) ∧\n                g0 = 1#1 ∧ ¬g1 = 74#7 ∧ ¬g1 = 75#7 ∧ ¬g1 = 76#7 ∧ ¬g1 = 77#7 ∧ ¬g1 = 78#7 ∧ ¬g1 = 79#7) ∧\n              ¬o = 192#8 ∧ ¬o = 219#8 then\n          1#2\n        else if g2 = 1#2 ∧ g0 = 1#1 ∧ g1 = 74#7 then 0#2 else g2) =\n    if (if g2 = 2#2 then 1#1 else 0#1) = 1#1 then 1#2\n    else\n      if\n          ((if g2 = 0#2 then 1#1 else 0#1) ||| if g2 = 1#2 then 1#1 else 0#1) &&&\n                (g0 &&&\n                  ((~~~if g1 = 74#7 then 1#1 else 0#1) &&&\n                    ~~~((if g1 = 75#7 then 1#1 else 0#1) |||\n                        ((if g1 = 76#7 then 1#1 else 0#1) |||\n                          ((if g1 = 77#7 then 1#1 else 0#1) |||\n                            ((if g1 = 78#7 then 1#1 else 0#1) ||| if g1 = 79#7 then 1#1 else 0#1)))))) &&&\n              ((if o = 192#8 then 1#1 else 0#1) ||| if o = 219#8 then 1#1 else 0#1) =\n            1#1 then\n        2#2\n      else\n        if\n            ((if g2 = 0#2 then 1#1 else 0#1) ||| if g2 = 1#2 then 1#1 else 0#1) &&&\n                  (g0 &&&\n                    ((~~~if g1 = 74#7 then 1#1 else 0#1) &&&\n                      ~~~((if g1 = 75#7 then 1#1 else 0#1) |||\n                          ((if g1 = 76#7 then 1#1 else 0#1) |||\n                            ((if g1 = 77#7 then 1#1 else 0#1) |||\n                              ((if g1 = 78#7 then 1#1 else 0#1) ||| if g1 = 79#7 then 1#1 else 0#1)))))) &&&\n                ~~~((if o = 192#8 then 1#1 else 0#1) ||| if o = 219#8 then 1#1 else 0#1) =\n              1#1 then\n          1#2\n        else if (if g2 = 1#2 then 1#1 else 0#1) &&& (g0 &&& if g1 = 73#7 then 1#1 else 0#1) = 1#1 then 0#2 else g2 := by\n  ved_bv_close3"
  let saved ← get
  let nm := (← getCurrNamespace) ++ `closerWrong
  let hasNm (env : Environment) : Bool :=
    env.constants.map₂.foldl (fun acc n _ => acc || nm.isPrefixOf n) false
  -- the STATEMENT alone elaborates (proof replaced by `sorry`): the refusal below is the tactic's, not the statement's
  let srcS := src.replace ":= by\n  ved_bv_close3" ":= by sorry"
  unless srcS.endsWith ":= by sorry" do throwError "control: statement text"
  let .ok stxS := Lean.Parser.runParserCategory (← getEnv) `command srcS | throwError "control: parse (statement)"
  let stmtOk ← try
      elabCommand stxS
      pure (!(← get).messages.hasErrors)
    finally set saved
  unless stmtOk do throwError "control void: the statement of closerWrong does not elaborate"
  let .ok stx := Lean.Parser.runParserCategory (← getEnv) `command src | throwError "control: parse"
  let (bad, tacErr) ← try
      elabCommand stx
      let errs := (← get).messages.toList.filter (·.severity == .error)
      let txts ← errs.mapM (·.data.toString)
      pure (!errs.isEmpty, txts.any fun t => (t.splitOn "ved_bv_close3").length > 1 || (t.splitOn "unsolved goals").length > 1
        || (t.splitOn "failed").length > 1 || (t.splitOn "omega").length > 1 || (t.splitOn "bv_decide").length > 1)
    finally set saved
  unless bad do throwError "control: the wrong register-step goal was accepted"
  unless tacErr do throwError "control: closerWrong failed, but not with a proof/tactic error"
  if hasNm (← getEnv) then throwError "control: closerWrong (or an auxiliary constant) survived the refusal"
  if (← get).messages.hasErrors || (← get).messages.toList.length != msgs0.toList.length then
    throwError "control: messages of the refused control were not restored"
  logInfo m!"compose connect closer controls: 2 accepted, 1 refused"


/-! ## Controls of the normalised comparison (`ved.compose.multiCircuit`; unit 22)

The fidelity literal of a register has `1 ++ (byte ++ 0)` as `concat [1, concat [byte, 0]]`, the Verilog cone `{1, byte, 0}` as
`concat [1, byte, 0]`.  `RegsOkNF` compares `flat n` of both sides (`flat_sound`).  Kernel evaluation of the comparison itself:
nested against flat and flat against nested are accepted, a wrong bit order and a wrong shift amount are refused, and the old
comparison (`eqE` without `flat`) refuses the nested/flat pair; then `RegsOkNF` on the accepted `multiTwo`. -/

def normControls : CommandElabM Unit := liftTermElabM do
  let isTrue (t : String) : TermElabM Bool := do kernelEqual (← elabText t) (toExpr true)
  let C := "Tools.VedComposeConnect"
  let E := "Sparkle.IR.AST.Expr"
  let sel (cat : String) (sh : Nat) :=
    s!"({E}.op .mux [{E}.ref \"c\", {cat}, {E}.op .shr [{E}.ref \"s\", {E}.const {sh} 10]])"
  let one := s!"{E}.const 1 1"
  let zero := s!"{E}.const 0 1"
  let b := s!"{E}.ref \"b\""
  let nested := s!"{E}.concat [{one}, {E}.concat [{b}, {zero}]]"
  let flatC := s!"{E}.concat [{one}, {b}, {zero}]"
  let wrongOrder := s!"{E}.concat [{one}, {E}.concat [{zero}, {b}]]"
  let eqN (x y : String) := s!"{C}.eqE ({C}.flat 12 {x}) ({C}.flat 12 {y})"
  unless ← isTrue (eqN (sel nested 1) (sel flatC 1)) do throwError "control void: nested vs flat rejected"
  unless ← isTrue (eqN (sel flatC 1) (sel nested 1)) do throwError "control void: flat vs nested rejected"
  if ← isTrue (eqN (sel flatC 1) (sel wrongOrder 1)) then throwError "the normalised comparison accepts a wrong bit order"
  if ← isTrue (eqN (sel flatC 1) (sel nested 2)) then throwError "the normalised comparison accepts a wrong shift amount"
  if ← isTrue s!"{C}.eqE {sel nested 1} {sel flatC 1}" then throwError "control void: the old comparison accepts nested vs flat"
  -- the controls are on well-formed ASTs: a 3-argument mux of width 10 that evaluates, and the mutations change concrete VALUES
  let we := "(fun n : String => if n = \"b\" then 8 else if n = \"c\" then 1 else 10)"
  let env (c bv sv : Nat) := s!"(fun n : String => if n = \"c\" then {c} else if n = \"b\" then {bv} else if n = \"s\" then {sv} else 0)"
  let wOf (x : String) := s!"(Sparkle.IR.Semantics.widthOf {we} {x} == 10)"
  let ev (x : String) (c bv sv : Nat) := s!"Sparkle.IR.Semantics.evalExpr {we} {env c bv sv} {x}"
  for x in [sel nested 1, sel flatC 1, sel wrongOrder 1, sel nested 2] do
    unless ← isTrue (wOf x) do throwError "control void: the mux control is not of width 10"
  unless ← isTrue s!"({ev (sel nested 1) 1 1 0} == some 514 && {ev (sel flatC 1) 1 1 0} == some 514)" do
    throwError "control void: nested/flat do not evaluate to 1++(b++0) = 514 at b = 1"
  unless ← isTrue s!"({ev (sel wrongOrder 1) 1 1 0} == some 513)" do throwError "control void: the wrong bit order does not evaluate to 513"
  unless ← isTrue s!"({ev (sel flatC 1) 0 0 4} == some 2 && {ev (sel nested 2) 0 0 4} == some 1)" do
    throwError "control void: the shift mutation does not change the value (4>>1 = 2 vs 4>>2 = 1)"
  logInfo m!"compose connect normalised comparison controls: 2 accepted, 2 refused (old comparison refuses nested vs flat) by the kernel"
  -- RegsOkNF on the accepted multiTwo
  let M := "Tests.Ved.ComposeConnectCheck.multiTwo"
  let nm := s!"{M}.ved_open_Tests_Ved_ComposeConnectCheck_multiTwo_nm"
  let deep := s!"{M}.ved_open_Tests_Ved_ComposeConnectCheck_multiTwo_deep"
  let tabTxt (o0 o1 : Nat) :=
    s!"([(\"_tmp_a_4\", 0), (\"_tmp_a_15\", 1), (\"_gen_start\", 2), (\"_gen_inp\", 3), (\"_tmp_op_b_9\", {o0}), (\"_tmp_op_b_12\", {o1}), (\"_gen_k1\", {o0}), (\"_gen_k2\", {o1})] : List (String × Nat))"
  let needed := "([\"_tmp_a_4\", \"_tmp_a_15\", \"_gen_start\", \"_gen_inp\", \"_tmp_op_b_9\", \"_gen_k1\", \"_tmp_op_b_12\", \"_gen_k2\"] : List String)"
  let regsN (o0 o1 : Nat) (xs : String) :=
    s!"{C}.RegsOkNF {deep} {nm} {M}.ved_design {M}.ved_mod {M}.ved_body {needed} {tabTxt o0 o1} 28 28 28 ([{xs}] : List String)"
  let real := "\"_tmp_reg_input_3\", \"_tmp_reg_input_14\""
  unless ← isTrue (regsN 4 5 real) do throwError "control void: RegsOkNF rejects the real table"
  if ← isTrue (regsN 5 4 real) then throwError "RegsOkNF accepts swapped oracle slots"
  if ← isTrue (regsN 4 5 "\"_tmp_reg_input_14\", \"_tmp_reg_input_3\"") then throwError "RegsOkNF accepts exchanged register input wires"
  logInfo m!"compose connect RegsOkNF controls: 1 accepted, 2 refused by the kernel"

/-- info: compose connect normalised comparison controls: 2 accepted, 2 refused (old comparison refuses nested vs flat) by the kernel
---
info: compose connect RegsOkNF controls: 1 accepted, 2 refused by the kernel -/
#guard_msgs in
run_cmd normControls

end Tests.Ved.ComposeConnectCheck
