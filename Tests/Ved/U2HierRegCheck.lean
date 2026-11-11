import Tools.VedU2HierRegEntry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for the stateful hierarchical entry, H2b: a PARENT WITH REGISTERS
(`Tools/VedU2HierRegEntry.lean`, `Tools/VedU2HierReg.lean`)

The small examples here are NOT part of the 327 inventory rows; nothing here claims a frozen
statement, hierarchical strict on the inventory, or a release.

* POSITIVES: `#ved_u2_hier`'s entry (`vedU2HierEntryR`) runs on a parent that has registers.  The
  theorem's exact type (`U2HRStmt c m d decl`) is rebuilt and compared, the axioms are the standard
  three (a MACHINE check, `std3Only`), and the closed run (`runHS`, parent registers included) is
  evaluated on concrete values and compared with the declaration's value.
  `oneInstance` / `threeInstances` are COPIES of Tests/Compiler/Issue107LetBoundInstanceDup.lean
  with `toggle` rewritten as an 8-bit enable counter (the original `toggle` is a `Signal.loop`
  with a `Bool` output: `#verify_elab_deep` refuses it, and the deep route's children are
  bit-vector outputs only).  `parentMix` is the declaration of Tests/Ved/NestedCacheCheck.lean,
  UNCHANGED; see its own section for what the entry does with it.
* CONTROLS: the entry's checker `checkU2HR` is run on the returned `(m, d)` of a real synthesis
  with ONE piece altered; each must be refused at a named stage with a message naming the cause,
  and leave NO constant and no message behind (the whole environment is compared, including the
  constants `#verify_elab_deep` adds at the root).  Positive controls (consistent renaming of a
  parent register, a parent register named like a child's register, reordered instances) are
  ACCEPTED with the exact statement.
-/

namespace Tests.Ved.U2HierRegCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
  Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry

/-! ## Declarations -/

/-- A child with one register (an accumulator), as in NestedCacheCheck. -/
@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

/-- Issue #107's `toggle` as an 8-bit enable counter (a register child with a `Bool` input). -/
@[hardware_module]
def toggle (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) := circuit do
  let r ← Signal.reg 0#8
  r <~ Signal.mux en (r + 1#8) r
  return (r : Signal defaultDomain (BitVec 8))

#verify_elab_deep accMod
#verify_elab_deep toggle

/-- Issue #107 `oneInstance` (copy): one let-bound instance feeds the parent's register. -/
@[hardware_module]
def oneInstance (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) := circuit do
  let r0 ← Signal.reg 0#8
  let t := toggle en
  r0 <~ t
  return (r0 : Signal defaultDomain (BitVec 8))

/-- Issue #107 `threeInstances` (copy): three distinct instances, three parent registers. -/
@[hardware_module]
def threeInstances (e0 e1 e2 : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r0 ← Signal.reg 0#8
    let r1 ← Signal.reg 0#8
    let r2 ← Signal.reg 0#8
    let a := toggle e0
    let b := toggle e1
    let c := toggle e2
    r0 <~ a
    r1 <~ b
    r2 <~ c
    return ((r0 : Signal defaultDomain (BitVec 8)) + (r1 : Signal defaultDomain (BitVec 8))
      - (r2 : Signal defaultDomain (BitVec 8)))

/-- NestedCacheCheck's `accInl`: the SAME body as `accMod`, but a plain function (inlined into the
parent, not an instance). -/
def accInl (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

/-- NestedCacheCheck's `parentMix`, unchanged: parent register `p`, an instance (`accMod`) and an
INLINED stateful call (`accInl`, a second register of the parent). -/
def parentMix (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let a := accMod x
    let b := accInl x
    p <~ a + b + p
    return p

/-- `parentMix` with the inlined accumulator written as a register of the parent's own circuit (same
shape of module: two parent registers, one instance, one feedback). -/
@[hardware_module]
def parentMixFlat (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let s ← Signal.reg 0#8
    let a := accMod x
    s <~ s + x
    p <~ a + (s : Signal defaultDomain (BitVec 8)) + p
    return p

/-- Two parent registers fed by instance outputs (`p` with feedback), mixed asymmetrically with an
instance output, so that a miswiring, a shared state or a one-cycle shift is observable. -/
@[hardware_module]
def twoRegsFed (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := accMod a
    let v := accMod b
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

/-- The same declaration under other names, one per control family (the constants of an accepted
entry stay, so each accepted run has its own). -/
@[hardware_module]
def regCtl (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := accMod a
    let v := accMod b
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

/-- The declaration the CONTROLS alter (never accepted itself, so nothing is left under its name). -/
@[hardware_module]
def regRef (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := accMod a
    let v := accMod b
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

@[hardware_module]
def regRn (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := accMod a
    let v := accMod b
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

@[hardware_module]
def regSh (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := accMod a
    let v := accMod b
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

@[hardware_module]
def regSw (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let q ← Signal.reg 1#8
    let u := accMod a
    let v := accMod b
    p <~ u - p
    q <~ v + q
    return (p : Signal defaultDomain (BitVec 8)) - (q : Signal defaultDomain (BitVec 8)) + u

/-- A parent with registers and NO instance (that is `#ved_u1_deep`). -/
@[hardware_module]
def regOnly (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    p <~ p + a
    return p

/-- A parent register whose instance input is DERIVED from the register (outside H2b). -/
@[hardware_module]
def regDerived (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod (a + (p : Signal defaultDomain (BitVec 8)))
    p <~ u
    return p

/-- One parent with two outputs (refused before synthesis). -/
def regPair (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) :=
  (fun x => (x, x)) <$> accMod a

/-! ## Helpers -/

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- MACHINE check: every axiom in the reachable closure of `n` is one of the standard three. -/
def std3Only (n : Name) : CoreM Unit := do
  let axs ← collectAxioms n
  unless axs.all (std3.contains ·) do throwError "{n}: axioms outside the standard three: {axs}"

/-- The checker's exact expected statement for `decl` (the H2b statement). -/
def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

/-- The entry run, the exact type, the standard axioms (machine-checked). -/
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
    logInfo m!"u2 hier reg OK {thm}: {(regsOf m.body).length} parent registers, children {d.modules.map (·.name)}"

def synthOf (decl : Name) : CommandElabM (Sparkle.IR.AST.Module × Design) := liftTermElabM do
  Sparkle.Compiler.Elab.synthesizeCombinational decl

/-! ## Positives: the entry accepts a parent with registers -/

/-- info: u2 hier reg OK Tests.Ved.U2HierRegCheck.oneInstance.ved_u1: 1 parent registers, children [Tests.Ved.U2HierRegCheck.toggle] -/
#guard_msgs in
run_cmd checkOk ``oneInstance

/-- info: u2 hier reg OK Tests.Ved.U2HierRegCheck.threeInstances.ved_u1: 3 parent registers, children [Tests.Ved.U2HierRegCheck.toggle] -/
#guard_msgs in
run_cmd checkOk ``threeInstances

/-- info: u2 hier reg OK Tests.Ved.U2HierRegCheck.twoRegsFed.ved_u1: 2 parent registers, children [Tests.Ved.U2HierRegCheck.accMod] -/
#guard_msgs in
run_cmd checkOk ``twoRegsFed

/-- info: u2 hier reg OK Tests.Ved.U2HierRegCheck.parentMixFlat.ved_u1: 2 parent registers, children [Tests.Ved.U2HierRegCheck.accMod] -/
#guard_msgs in
run_cmd checkOk ``parentMixFlat

/-- info: u2 hier reg OK Tests.Ved.U2HierRegCheck.regCtl.ved_u1: 2 parent registers, children [Tests.Ved.U2HierRegCheck.accMod] -/
#guard_msgs in
run_cmd checkOk ``regCtl

/-! ## The theorem's type, spelled out (an independent restatement of `U2HRStmt`) -/

example : U2HRStmt oneInstance.ved_contract oneInstance.ved_mod oneInstance.ved_design oneInstance :=
  oneInstance.ved_u1

example : U2HRStmt regCtl.ved_contract regCtl.ved_mod regCtl.ved_design regCtl ↔
    (CorrStmt regCtl.ved_contract ∧ ShapeCore regCtl.ved_contract regCtl.ved_mod ∧
      regCtl.ved_contract.clkRst = designClkRst regCtl.ved_design regCtl.ved_mod ∧
      HierShapeS regCtl.ved_design regCtl.ved_mod = true ∧
      WidthStmt regCtl.ved_contract regCtl.ved_mod ∧
      (∃ b, OrderOkHS regCtl.ved_design regCtl.ved_mod b = true) ∧
      (∀ x ∈ regCtl.ved_design.modules, OrderStmt x) ∧
      (∃ arr, AdmArr regCtl.ved_design regCtl.ved_mod arr) ∧
      ∀ arr, AdmArr regCtl.ved_design regCtl.ved_mod arr →
        ∀ ins, InputsOk regCtl.ved_contract regCtl.ved_mod ins → ∀ K, ∃ envs,
          runHS regCtl.ved_design arr regCtl.ved_mod (seedFwd regCtl.ved_mod K ins) K
            (st0H regCtl.ved_design regCtl.ved_mod) = some envs ∧
          ∀ t, t < K → ∀ o ∈ regCtl.ved_contract.outputs, ∃ env, envs[t]? = some env ∧
            env o.name = srcOf regCtl.ved_contract regCtl ins o.name t) := Iff.rfl

/-- H2a's statement is `U2HRStmt` plus the register-free clause: the two differ in exactly that
clause (the H2a statement and its checks are unchanged). -/
example (c : Contract) (m : Sparkle.IR.AST.Module) (d : Design) (f : c.table.Ty) :
    U2HStmt c m d f ↔ (U2HRStmt c m d f ∧ regsOf m.body = []) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨⟨h1, h2, h3, h4, h6, h7, h8, h9, h10⟩, h5⟩
  · rintro ⟨⟨h1, h2, h3, h4, h6, h7, h8, h9, h10⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ## The generated open parent and its kernel equation (as in H2a) -/

theorem regCtl_open_eq_stated (a b : Signal defaultDomain (BitVec 8)) :
    regCtl a b = regCtl.ved_open_Tests_Ved_U2HierRegCheck_regCtl a b (accMod a) (accMod b) :=
  regCtl.ved_open_Tests_Ved_U2HierRegCheck_regCtl_eq a b

/-- info: 'Tests.Ved.U2HierRegCheck.regCtl.ved_open_Tests_Ved_U2HierRegCheck_regCtl_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms regCtl.ved_open_Tests_Ved_U2HierRegCheck_regCtl_eq

/-! ## The closed stateful run on concrete values (parent registers included) -/

/-- Arrangements: the checked order for the top, the leaf order for every child. -/
def arrOf (d : Design) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module → List Stmt :=
  fun x => if x == m then orderBodyH d x.body else Tools.VedU1Entry.orderBody x.body

/-- Inputs: a = 1,2,3,4; b = 10,20,30,40; reset 0; a CHANGING clock. -/
def inpS (t : Nat) (n : String) : Nat :=
  if n == "_gen_a" then [1, 2, 3, 4].getD t 0 else if n == "_gen_b" then [10, 20, 30, 40].getD t 0
  else if n == "clk" then t % 2 else 0

def outsOf (d : Design) (m : Sparkle.IR.AST.Module) (inp : Nat → String → Nat) (K : Nat) :
    Option (List Nat) :=
  (runHS d (arrOf d m) m (seedFwd m K inp) K (st0H d m)).map (·.map fun e => e "out")

/- the declaration (by hand): u = 0,1,3,6; v = 0,10,30,60; p = 0,0,1,2 (p' = u - p); q = 1,1,11,41
   (q' = v + q); out = p - q + u = 255, 0, 249, 223 (mod 256) -/
#guard (regCtl ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4].getD t 0)⟩ ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40].getD t 0)⟩).val 0 == 255#8
#guard (regCtl ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4].getD t 0)⟩ ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40].getD t 0)⟩).val 1 == 0#8
#guard (regCtl ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4].getD t 0)⟩ ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40].getD t 0)⟩).val 2 == 249#8
#guard (regCtl ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4].getD t 0)⟩ ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40].getD t 0)⟩).val 3 == 223#8

/-- info: closed run: some ([255, 0, 249, 223]) (changing clock), same with a constant clock -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``regCtl
  let a := outsOf d m inpS 4
  let c := outsOf d m (fun t n => if n == "clk" then 0 else inpS t n) 4
  unless a == some [255, 0, 249, 223] do throwError "closed run of regCtl: {a}"
  unless c == a do throwError "the clock changed the run: {c}"
  logInfo m!"closed run: {a} (changing clock), same with a constant clock"

/-! ## Controls: ONE piece altered, refused at a named stage, nothing left -/

/-- All constants added in this file so far (a snapshot of the environment's local part). -/
def localConsts : CommandElabM NameSet := do
  return (← getEnv).constants.map₂.toList.foldl (fun s (n, _) => s.insert n) {}

/-- The checker with one piece altered must refuse at `stage` with a message naming `needle`, and
the environment must be EXACTLY as before the call (no constant, at the root or under `decl`). -/
def expectRefused (decl : Name) (stage : String) (needle : String) (m : Sparkle.IR.AST.Module)
    (d : Design) (clk : Option (Option (String × String)) := none) : CommandElabM Unit := do
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let r ← try
      discard <| checkU2HR decl stmt nDom m d clk
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

def mapRegs (f : String → Stmt → Stmt) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .register o .. => f o s
    | s => s

def mapAssign (n : String) (f : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .assign l e => if l == n then .assign l (f e) else s
    | s => s

def setInit (v : Int) : Stmt → Stmt
  | .register o k r e _ => .register o k r e v
  | s => s

def mapReg (o : String) (f : Stmt → Stmt) (b : List Stmt) : List Stmt :=
  mapRegs (fun o' s => if o' == o then f s else s) b

def w8 (n : String) : Port := ⟨n, .bitVector 8⟩

def isInst : Stmt → Bool
  | .inst .. => true
  | _ => false

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

/- Names in the synthesised `regCtl` (see the body): parent registers `_tmp_a_5` (p) and `_tmp_a_11`
(q); their inputs `_tmp_reg_input_4` (u - p) and `_tmp_reg_input_10` (v + q); instance output wires
`_tmp_arg1_1` and `_tmp_arg1_6`; the output chain `_tmp_op_a_15 = p - q`, `_gen_out = _tmp_op_a_15 + u`. -/

def controlsRun : CommandElabM Unit := do
  let (m, d) ← synthOf ``regRef
  let name := ``regRef
  let mut n : Nat := 0
  /- PARENT REGISTER VALUES: init, next, time -/
  -- the parent register's INIT changed (the contract's `inits` are read from `m` itself, so only the
  -- generated proof, against the declaration's init, can notice)
  expectRefused name "proof" "unsolved goals"
    { m with body := mapReg "_tmp_a_5" (setInit 2) m.body } d
  n := n + 1
  expectRefused name "proof" "unsolved goals"
    { m with body := mapReg "_tmp_a_11" (setInit 0) m.body } d
  n := n + 1
  -- the parent register's NEXT changed: `u - p` becomes `u + p`; the two registers' inputs exchanged;
  -- a constant
  expectRefused name "proof" "omega could not prove the goal"
    { m with body := mapAssign "_tmp_reg_input_4" (fun _ => rop .add "_tmp_arg1_1" "_tmp_arg2_3") m.body } d
  n := n + 1
  expectRefused name "proof" "omega could not prove the goal"
    { m with body := mapReg "_tmp_a_5" (fun _ => regAtStmt "_tmp_a_5" "_tmp_reg_input_10" 0)
                (mapReg "_tmp_a_11" (fun _ => regAtStmt "_tmp_a_11" "_tmp_reg_input_4" 1) m.body) } d
  n := n + 1
  expectRefused name "proof" "omega could not prove the goal"
    { m with body := mapAssign "_tmp_reg_input_10" (fun _ => .const 3 8) m.body } d
  n := n + 1
  -- a ONE-CYCLE TIME SHIFT: the output reads `p`'s next value (the register's input net) instead of
  -- its current one
  expectRefused name "proof" "omega could not prove the goal"
    { m with body := mapAssign "_tmp_op_a_15" (fun _ => rop .sub "_tmp_reg_input_4" "_tmp_arg2_9") m.body } d
  n := n + 1
  expectRefused name "proof" "omega could not prove the goal"
    { m with body := mapAssign "_tmp_op_a_15" (fun _ => rop .sub "_tmp_arg2_3" "_tmp_reg_input_10") m.body } d
  n := n + 1
  /- WIRING of the instances (the parent registers are fed by the oracle) -/
  -- the two instance output wires exchanged: the registers see each other's child
  expectRefused name "proof" "omega could not prove the goal"
    { m with body := setConnAt 1 "out" (.ref "_tmp_arg1_1") (setConnAt 0 "out" (.ref "_tmp_arg1_6") m.body) } d
  n := n + 1
  -- the first instance fed the other input
  expectRefused name "proof" "omega could not prove the goal"
    { m with body := setConnAt 0 "_gen_x" (.ref "_gen_b") m.body } d
  n := n + 1
  /- A PARENT REGISTER AND A CHILD'S REGISTER -/
  -- the parent register's output is an INSTANCE output wire (the net has two drivers)
  expectRefused name "order" "drives a register output"
    { m with body := m.body ++ [regAtStmt "_tmp_arg1_1" "_tmp_reg_input_4" 0] } d
  n := n + 1
  /- A REGISTER WRITTEN TWICE -/
  expectRefused name "order" "twice"
    { m with body := m.body ++ [regAtStmt "_tmp_a_5" "_tmp_reg_input_10" 0] } d
  n := n + 1
  expectRefused name "order" "twice"
    { m with body := mapReg "_tmp_a_11" (fun _ => regAtStmt "_tmp_a_5" "_tmp_reg_input_10" 1) m.body } d
  n := n + 1
  /- RESET / CLOCK MISUSE on the parent register -/
  -- a data input as the clock of one parent register
  expectRefused name "hier-shape" "clock/reset"
    { m with body := mapReg "_tmp_a_5" (fun _ => regFull "_tmp_a_5" "_gen_a" "rst" "_tmp_reg_input_4" 0) m.body } d
  n := n + 1
  -- a data input as the reset of one parent register
  expectRefused name "hier-shape" "clock/reset"
    { m with body := mapReg "_tmp_a_5" (fun _ => regFull "_tmp_a_5" "clk" "_gen_b" "_tmp_reg_input_4" 0) m.body } d
  n := n + 1
  -- a data input as the reset of BOTH parent registers (the design pair is not the contract's pair
  -- of the instances)
  expectRefused name "hier-shape" "clock/reset"
    { m with body := mapRegs (fun o s => match s with
        | .register _ k _ e i => .register o k ("_gen_b", .synchronous) e i
        | s => s) m.body } d
  n := n + 1
  -- a reset that is no input at all
  expectRefused name "hier-shape" "clock/reset"
    { m with body := mapReg "_tmp_a_5" (fun _ => regFull "_tmp_a_5" "clk" "nosuch" "_tmp_reg_input_4" 0) m.body } d
  n := n + 1
  -- clock and reset of the parent registers exchanged, the instances left on (clk, rst)
  expectRefused name "hier-shape" "clock/reset"
    { m with body := mapRegs (fun o s => match s with
        | .register _ _ _ e i => .register o "rst" ("clk", .synchronous) e i
        | s => s) m.body } d
  n := n + 1
  -- the contract forced to a data input pair: the real port names repeat, so `CorrStmt` refuses
  expectRefused name "table" "CorrStmt"
    { m with body := mapRegs (fun o s => match s with
        | .register _ k _ e i => .register o k ("_gen_b", .synchronous) e i
        | s => s) (m.body.map fun s => match s with
          | .inst mn i cs => .inst mn i (cs.map fun q => if q.1 == "rst" then ("rst", .ref "_gen_b") else q)
          | s => s) } d (some (some ("clk", "_gen_b")))
  n := n + 1
  /- ORDER / SHAPE of the parent with registers -/
  -- an undriven register input
  expectRefused name "order" "undriven net"
    { m with body := mapReg "_tmp_a_5" (fun _ => regAtStmt "_tmp_a_5" "_tmp_nosuch" 0) m.body,
             wires := m.wires ++ [w8 "_tmp_nosuch"] } d
  n := n + 1
  -- a combinational loop in the parent (a register's input net feeds a wire its own expression reads);
  -- the loop THROUGH a register (`p' = u - p`) is the feedback of the positives and is accepted
  expectRefused name "order" "combinational cycle"
    { m with body := mapAssign "_tmp_arg2_3" (fun _ => .ref "_tmp_reg_input_4") m.body } d
  n := n + 1
  -- a combinational loop THROUGH AN INSTANCE (its own output feeds its input): the instance input is
  -- no parent input, which the shape check refuses first
  expectRefused name "order" "combinational cycle"
    { m with body := setConnAt 0 "_gen_x" (.ref "_tmp_arg1_1") m.body } d
  n := n + 1
  -- an assignment to a top input / to a register output
  expectRefused name "order" "write to a top input"
    { m with body := m.body ++ [.assign "_gen_a" (.ref "_gen_b")] } d
  n := n + 1
  expectRefused name "order" "drives a register output"
    { m with body := m.body ++ [.assign "_tmp_a_11" (.ref "_gen_b")] } d
  n := n + 1
  -- a register output that is a top input
  expectRefused name "order" "register output is a top input"
    { m with body := m.body ++ [regAtStmt "_gen_a" "_tmp_reg_input_4" 0] } d
  n := n + 1
  /- SCOPE -/
  expectRefused name "conns" "not connected to a parent input"
    { m with body := setConnAt 0 "_gen_x" (.ref "_tmp_a_5") m.body } d
  n := n + 1
  logInfo m!"controls: {n} refused, nothing left in the environment"
where
  regAtStmt (o inp : String) (i : Int) : Stmt := .register o "clk" ("rst", .synchronous) (.ref inp) i
  regFull (o k r inp : String) (i : Int) : Stmt := .register o k (r, .synchronous) (.ref inp) i

/-- info: controls: 25 refused, nothing left in the environment -/
#guard_msgs in
run_cmd controlsRun

/-! ## Entry-level refusals -/

def entryRefused (decl : Name) (stage : String) (needle : String) : CommandElabM Unit := do
  let before ← localConsts
  let r ← try
      discard <| vedU2HierEntryR decl
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do throwError "unexpected: {msg}"
    unless (msg.splitOn needle).length > 1 do throwError "the refusal does not name `{needle}`: {msg}"
  | none => throwError "{decl} accepted"
  let after ← localConsts
  let added := after.toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"

/-- info: multi-output refused, no instance refused at [scope], derived instance input refused at [conns] -/
#guard_msgs in
run_cmd do
  entryRefused ``regPair "multi-output" "H3"
  entryRefused ``regOnly "scope" "no child instance"
  entryRefused ``regDerived "conns" "not connected to a parent input"
  logInfo "multi-output refused, no instance refused at [scope], derived instance input refused at [conns]"

/-! ## `parentMix` (Tests/Ved/NestedCacheCheck.lean), unchanged

The parent has its own register, ONE instance and an INLINED stateful call (`accInl`, a second
register of the parent that is not an instance).  The entry generates the open parent (the
instance call abstracted into a free signal) and runs `#verify_elab_deep` on it; the inlined
`accInl x` stays a nested `runCircuitH` inside the open parent, and DeepElab's Signal-side bridge
cannot relate it to the second register ("closers exhausted").  This is a limit of the deep route
(not of the statement); the entry REFUSES at [deep], leaving nothing behind.  `parentMixFlat` is the
same module shape with the second register written in the parent's own circuit, and is accepted
above. -/

/-- info: parentMix refused at [deep]: the inlined stateful call is outside the deep route -/
#guard_msgs in
run_cmd do
  entryRefused ``parentMix "deep" "closers exhausted"
  logInfo "parentMix refused at [deep]: the inlined stateful call is outside the deep route"

/-! ## Positive controls: meaning-preserving changes are ACCEPTED with the exact statement -/

def checkOkWith (decl : Name) (m : Sparkle.IR.AST.Module) (d : Design) : CommandElabM Unit := do
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let (thm, _, _) ← checkU2HR decl stmt nDom m d
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    std3Only thm
    logInfo m!"accepted {decl}"

/-- Consistent renaming of a parent register (output and every read of it): the key of the state is
the name, so the slice follows. -/
def renameName (a b : String) (b0 : List Stmt) : List Stmt :=
  let rn (x : String) : String := if x == a then b else x
  let rec re : Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
    | .ref x => .ref (rn x)
    | .op o args => .op o (args.map re)
    | .concat args => .concat (args.map re)
    | .slice e h l => .slice (re e) h l
    | e => e
  b0.map fun s => match s with
    | .assign l e => .assign (rn l) (re e)
    | .register o k r e i => .register (rn o) k r (re e) i
    | .inst mn i cs => .inst mn i (cs.map fun (p, e) => (p, re e))
    | s => s

/-- info: accepted Tests.Ved.U2HierRegCheck.regRn -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``regRn
  checkOkWith ``regRn
    { m with body := renameName "_tmp_a_5" "_tmp_a_77" m.body,
             wires := m.wires.map fun p => if p.name == "_tmp_a_5" then { p with name := "_tmp_a_77" } else p } d

/-- A parent register named like the CHILD's register (`accMod`'s register output name): the state is
keyed by (path, name), so parent slice `[]` and the instance slices `[inst]` do not share, and the
theorem is proved (the control a flat, name-keyed state would fail). -/
def childRegName (d : Design) : String :=
  match d.modules.head? with
  | some c => ((regsOf c.body).head?.map (·.1)).getD "?"
  | none => "?"

/-- info: accepted Tests.Ved.U2HierRegCheck.regSh -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``regSh
  let cn := childRegName d
  unless cn != "?" && cn != "_tmp_a_5" do throwError "the child's register name: {cn}"
  checkOkWith ``regSh
    { m with body := renameName "_tmp_a_5" cn m.body,
             wires := m.wires.map fun p => if p.name == "_tmp_a_5" then { p with name := cn } else p } d

-- the two instances exchanged in the body AND their output wires exchanged (a symmetric re-labelling)
/-- info: accepted Tests.Ved.U2HierRegCheck.regSw -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``regSw
  match m.body.filter isInst with
  | [i0, i1] =>
    let rest := m.body.filter fun s => !isInst s
    checkOkWith ``regSw { m with body := i1 :: i0 :: rest } d
  | _ => throwError "unexpected body"

-- The closed run of the renamed (shared-name) design is the same as the original's.
/-- info: renamed to the child's register name: same run -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``regCtl
  let cn := childRegName d
  let m' := { m with body := renameName "_tmp_a_5" cn m.body,
                     wires := m.wires.map fun p => if p.name == "_tmp_a_5" then { p with name := cn } else p }
  unless outsOf d m' inpS 4 == outsOf d m inpS 4 do throwError "renaming changed the run"
  logInfo "renamed to the child's register name: same run"

/-! ## Axioms of the new lemmas, MACHINE-checked -/

run_cmd liftCoreM do
  for n in [``Tools.VedU2Hier.outputsOnHS_of_stepR, ``Tools.VedU2Hier.runHSTrace_next,
      ``Tools.VedU2Hier.restrictTo_perm, ``Tools.VedU2Hier.nextKeys_eq_regOuts,
      ``Tools.VedU2Hier.applyH_root_cons, ``oneInstance.ved_u1, ``threeInstances.ved_u1,
      ``twoRegsFed.ved_u1, ``parentMixFlat.ved_u1, ``regCtl.ved_u1, ``regRn.ved_u1,
      ``regSh.ved_u1, ``regSw.ved_u1, ``regCtl_open_eq_stated] do
    std3Only n

end Tests.Ved.U2HierRegCheck
