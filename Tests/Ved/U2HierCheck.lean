import Tools.VedU2HierEntry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for the stateful hierarchical entry, H2a (`Tools/VedU2HierEntry.lean`)

The small examples here are NOT part of the 327 inventory rows.  Nothing here claims a frozen
statement, hierarchical strict on the inventory, or a release.

* ENTRY RUNS: `#ved_u2_hier` on a register-free parent that calls the register child `accMod`
  twice with different inputs, combined asymmetrically (`p - q + a`), so that a miswiring or a
  shared state is observable; and on a parent of a TWO-register child with a Bool data input
  (the #160 multi-register / Bool generator).  The theorem's exact type is rebuilt and compared,
  the axioms are the standard three (a MACHINE check, `std3Only`, not `#print axioms`), and the
  closed stateful run (`runHS`) is evaluated on concrete values and compared with the
  declaration's value.
* CLOCK / RESET: the final theorem is instantiated at a CHANGING clock with reset 0 and at a
  universally quantified clock; a nonzero reset is outside the statement (`InputsOk` fails) and
  the run really differs from the declaration there.
* CONTROLS: the entry's own checker `checkU2H` is run on the returned `(m, d)` with ONE piece
  altered; each must be refused at a named stage (and the message must name the cause) and leave
  NO constant of its base.  Positive controls (consistent renaming of instance names, reordering
  of the instances) are ACCEPTED with the exact statement.
-/

namespace Tests.Ved.U2HierCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
  Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry

/-! ## Declarations -/

/-- Child with one register: an accumulator with an input. -/
@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + x
    return a

/-- Another register function (init 1): the "another child" control. -/
@[hardware_module]
def accModOther (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (1#8)
    let a := (r : Signal defaultDomain (BitVec 8))
    r <~ a + x
    return a

/-- Register-free parent: two instances of `accMod` on different inputs, combined asymmetrically. -/
@[hardware_module]
def parTwo (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

/-- The same declaration under other names, one per control family (so the entry's constants
never clash). -/
@[hardware_module]
def parCtl (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

@[hardware_module]
def parRn (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

@[hardware_module]
def parSw (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accMod a
  let q := accMod b
  p - q + a

/-- A parent that calls another register child (for the "another design" control). -/
@[hardware_module]
def parOther (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let p := accModOther a
  let q := accModOther b
  p - q + a

/-- One parent with two outputs (refused before synthesis). -/
def parPair (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) :=
  (fun x => (x, x)) <$> accMod a

/-- A child with TWO registers and a Bool data input named like the generator's own binder
(the #160 route), and a parent that calls it twice. -/
@[hardware_module]
def twoReg (reset : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    if reset then
      a <~ 0#8
      b <~ 0#8
    else
      a <~ a + 1#8
      b <~ b + 2#8
    return a + b

@[hardware_module]
def parMulti (r0 r1 : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let p := twoReg r0
  let q := twoReg r1
  p - q

/-- A parent that feeds an instance from a DERIVED wire (outside H2a). -/
@[hardware_module]
def parDerived (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  accMod (a + b)

#verify_elab_deep accMod
#verify_elab_deep twoReg

/-! ## Helpers -/

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- MACHINE check: every axiom in the reachable closure of `n` is one of the standard three. -/
def std3Only (n : Name) : CoreM Unit := do
  let axs ← collectAxioms n
  unless axs.all (std3.contains ·) do throwError "{n}: axioms outside the standard three: {axs}"

/-- The checker's exact expected statement for `decl`. -/
def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

/-- The entry run, the exact type, the standard axioms (machine-checked). -/
def checkOk (decl : Name) : CommandElabM Unit := liftTermElabM do
  let (_, d, thm, nDom, _) ← vedU2HierEntry decl
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HStmt c m d decl"
  discard <| Tools.VedStrictAudit.strictAudit thm
  std3Only thm
  let nm := HNames.ofBase decl
  -- the generated open parent and its kernel equation are theorems / definitions in the environment
  let _ := nm
  for n in [decl ++ `ved_open_eq] do
    let some (.thmInfo _) := (← getEnv).find? n | throwError "{n} is not a theorem"
    std3Only n
  logInfo m!"u2 hier OK {thm} children {d.modules.map (·.name)}"

/-- info: u2 hier OK Tests.Ved.U2HierCheck.parTwo.ved_u1 children [Tests.Ved.U2HierCheck.accMod] -/
#guard_msgs in
run_cmd checkOk ``parTwo

/-! ## The generated open parent and its kernel equation (Q8) -/

/-- The open parent was GENERATED from the declaration's body (the two calls abstracted into free
signals); its equation with the original constant is a kernel theorem with no axioms. -/
theorem parTwo_open_eq_stated (a b : Signal defaultDomain (BitVec 8)) :
    parTwo a b = parTwo.ved_open a b (accMod a) (accMod b) := parTwo.ved_open_eq a b

/-- info: 'Tests.Ved.U2HierCheck.parTwo.ved_open_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms parTwo.ved_open_eq

example (a b p q : Signal defaultDomain (BitVec 8)) : parTwo.ved_open a b p q = p - q + a := rfl

/-! ## The theorem's type, spelled out (the final statement is not a hypothesis of anything) -/

example : U2HStmt parTwo.ved_contract parTwo.ved_mod parTwo.ved_design parTwo := parTwo.ved_u1

/-- The statement, expanded (an independent restatement of `U2HStmt` and its output clause). -/
example : U2HStmt parTwo.ved_contract parTwo.ved_mod parTwo.ved_design parTwo ↔
    (CorrStmt parTwo.ved_contract ∧ ShapeCore parTwo.ved_contract parTwo.ved_mod ∧
      parTwo.ved_contract.clkRst = designClkRst parTwo.ved_design parTwo.ved_mod ∧
      HierShapeS parTwo.ved_design parTwo.ved_mod = true ∧ regsOf parTwo.ved_mod.body = [] ∧
      WidthStmt parTwo.ved_contract parTwo.ved_mod ∧
      (∃ b, OrderOkHS parTwo.ved_design parTwo.ved_mod b = true) ∧
      (∀ x ∈ parTwo.ved_design.modules, OrderStmt x) ∧
      (∃ arr, AdmArr parTwo.ved_design parTwo.ved_mod arr) ∧
      ∀ arr, AdmArr parTwo.ved_design parTwo.ved_mod arr →
        ∀ ins, InputsOk parTwo.ved_contract parTwo.ved_mod ins → ∀ K, ∃ envs,
          runHS parTwo.ved_design arr parTwo.ved_mod (seedFwd parTwo.ved_mod K ins) K
            (st0H parTwo.ved_design parTwo.ved_mod) = some envs ∧
          ∀ t, t < K → ∀ o ∈ parTwo.ved_contract.outputs, ∃ env, envs[t]? = some env ∧
            env o.name = srcOf parTwo.ved_contract parTwo ins o.name t) := Iff.rfl

/-! ## The closed stateful run on concrete values (miswiring and shared state are observable) -/

/-- Arrangements: the checked order for the top, the leaf order for every child. -/
def arrOf (d : Design) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module → List Stmt :=
  fun x => if x == m then orderBodyH d x.body else Tools.VedU1Entry.orderBody x.body

/-- Inputs: a = 1,2,3,4; b = 10,20,30,40; reset 0; a CHANGING clock. -/
def inpS (t : Nat) (n : String) : Nat :=
  if n == "_gen_a" then [1, 2, 3, 4].getD t 0 else if n == "_gen_b" then [10, 20, 30, 40].getD t 0
  else if n == "clk" then t % 2 else 0

/-- Same data, a constant clock. -/
def inpC (t : Nat) (n : String) : Nat :=
  if n == "clk" then 0 else inpS t n

def outsOf (d : Design) (m : Sparkle.IR.AST.Module) (inp : Nat → String → Nat) (K : Nat) :
    Option (List Nat) :=
  (runHS d (arrOf d m) m (seedFwd m K inp) K (st0H d m)).map (·.map fun e => e "out")

def synthOf (decl : Name) : CommandElabM (Sparkle.IR.AST.Module × Design) := liftTermElabM do
  Sparkle.Compiler.Elab.synthesizeCombinational decl

/- the declaration: p = 0,1,3,6; q = 0,10,30,60; out = p - q + a = 1, 249, 232, 206 (mod 256) -/
#guard (parTwo ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4].getD t 0)⟩ ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40].getD t 0)⟩).val 0 == 1#8
#guard (parTwo ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4].getD t 0)⟩ ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40].getD t 0)⟩).val 1 == 249#8
#guard (parTwo ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4].getD t 0)⟩ ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40].getD t 0)⟩).val 2 == 232#8
#guard (parTwo ⟨fun t => BitVec.ofNat 8 ([1, 2, 3, 4].getD t 0)⟩ ⟨fun t => BitVec.ofNat 8 ([10, 20, 30, 40].getD t 0)⟩).val 3 == 206#8

/-- info: closed run: some ([1, 249, 232, 206]) (changing clock), same with a constant clock -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``parTwo
  let a := outsOf d m inpS 4
  let c := outsOf d m inpC 4
  unless a == some [1, 249, 232, 206] do throwError "closed run of parTwo: {a}"
  unless c == a do throwError "the clock changed the run: {c}"
  logInfo m!"closed run: {a} (changing clock), same with a constant clock"

/-! ## Clock and reset: the final theorem at a changing clock, and at every clock -/

theorem inputsOk_clk (clk : Nat → Nat) (A B : Nat → Nat) (hA : ∀ t, A t < 256) (hB : ∀ t, B t < 256) :
    InputsOk parTwo.ved_contract parTwo.ved_mod
      (fun t n => if n == "_gen_a" then A t else if n == "_gen_b" then B t
        else if n == "clk" then clk t else 0) := by
  refine ⟨?_, ?_⟩
  · intro t p hp
    simp [parTwo.ved_contract, contractOf, Contract.dataInputs, parTwo.ved_mod, declWidth] at hp ⊢
    rcases hp with rfl | rfl <;> simp [hA, hB]
  · intro t kr hkr
    have h : parTwo.ved_contract.clkRst = some ("clk", "rst") := by decide
    rw [h] at hkr
    cases hkr
    simp

/-- The final theorem at a CHANGING clock (`t % 2`) with reset 0: an instance of the theorem, not a
restatement. -/
theorem parTwo_changing_clock (arr : Sparkle.IR.AST.Module → List Stmt)
    (hadm : AdmArr parTwo.ved_design parTwo.ved_mod arr) (K : Nat) :
    ∃ envs, runHS parTwo.ved_design arr parTwo.ved_mod
        (seedFwd parTwo.ved_mod K (fun t n => if n == "_gen_a" then (t * 37 + 1) % 256
          else if n == "_gen_b" then (t * 11 + 5) % 256 else if n == "clk" then t % 2 else 0)) K
        (st0H parTwo.ved_design parTwo.ved_mod) = some envs ∧
      ∀ t, t < K → ∀ o ∈ parTwo.ved_contract.outputs, ∃ env, envs[t]? = some env ∧
        env o.name = srcOf parTwo.ved_contract parTwo
          (fun t n => if n == "_gen_a" then (t * 37 + 1) % 256
            else if n == "_gen_b" then (t * 11 + 5) % 256 else if n == "clk" then t % 2 else 0)
          o.name t :=
  parTwo.ved_u1.2.2.2.2.2.2.2.2.2 arr hadm _
    (inputsOk_clk (fun t => t % 2) (fun t => (t * 37 + 1) % 256) (fun t => (t * 11 + 5) % 256)
      (fun t => Nat.mod_lt _ (by decide)) (fun t => Nat.mod_lt _ (by decide))) K

/-- ... and at EVERY clock stream (a universally quantified clock, no range assumed). -/
theorem parTwo_any_clock (arr : Sparkle.IR.AST.Module → List Stmt)
    (hadm : AdmArr parTwo.ved_design parTwo.ved_mod arr) (clk : Nat → Nat) (A B : Nat → Nat)
    (hA : ∀ t, A t < 256) (hB : ∀ t, B t < 256) (K : Nat) :
    ∃ envs, runHS parTwo.ved_design arr parTwo.ved_mod
        (seedFwd parTwo.ved_mod K (fun t n => if n == "_gen_a" then A t
          else if n == "_gen_b" then B t else if n == "clk" then clk t else 0)) K
        (st0H parTwo.ved_design parTwo.ved_mod) = some envs :=
  (parTwo.ved_u1.2.2.2.2.2.2.2.2.2 arr hadm _ (inputsOk_clk clk A B hA hB) K).imp fun _ h => h.1

/-- A NONZERO reset is outside the statement: `InputsOk` fails ... -/
def insRst (t : Nat) (n : String) : Nat := if n == "rst" then (if t == 1 then 1 else 0) else inpS t n

theorem insRst_not_ok : ¬ InputsOk parTwo.ved_contract parTwo.ved_mod insRst := by
  intro h
  have hc : parTwo.ved_contract.clkRst = some ("clk", "rst") := by decide
  have := h.2 1 ("clk", "rst") hc
  simp [insRst] at this

/- ... and the run really differs from the declaration there (the child state is reset at cycle 1):
p = 0, 1, 0, 3 and q = 0, 10, 0, 30, so out = 1, 249, 3, 233 instead of 1, 249, 232, 206. -/
/-- info: reset 1 at cycle 1: some ([1, 249, 3, 233]) <> the declaration's [1, 249, 232, 206] -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``parTwo
  let a := outsOf d m insRst 4
  unless a == some [1, 249, 3, 233] do throwError "run with a reset: {a}"
  unless a != some [1, 249, 232, 206] do throwError "a reset did not change the run"
  logInfo m!"reset 1 at cycle 1: {a} <> the declaration's [1, 249, 232, 206]"

/-! ## A second entry run: a child with TWO registers and a Bool data input (the #160 generator) -/

/-- info: u2 hier OK Tests.Ved.U2HierCheck.parMulti.ved_u1 children [Tests.Ved.U2HierCheck.twoReg] -/
#guard_msgs in
run_cmd checkOk ``parMulti

/-! ## Controls: ONE piece altered, refused at a named stage, nothing left -/

/-- The constants of this file's environment under `decl`. -/
def constsUnder (decl : Name) : MetaM (List Name) := do
  return (← getEnv).constants.map₂.toList.filterMap fun (n, _) =>
    if decl.isPrefixOf n then some n else none

/-- The checker with one piece altered must refuse at `stage` with a message naming `needle`, and
the environment under `decl` must be exactly as before the call. -/
def expectRefused (decl : Name) (stage : String) (needle : String) (m : Sparkle.IR.AST.Module)
    (d : Design) (clk : Option (Option (String × String)) := none) : CommandElabM Unit :=
  liftTermElabM do
  let before ← constsUnder decl
  let (stmt, nDom) ← specialiseDomain decl
  let r ← try
      discard <| checkU2H decl stmt nDom m d clk
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  let pre := s!"VED U1 REFUSED {decl} [{stage}]"
  match r with
  | none => throwError "{decl}: expected a refusal at [{stage}], the checker ACCEPTED"
  | some msg =>
    unless msg.startsWith pre do throwError "expected {pre} (needle `{needle}`), got: {msg}"
    unless (msg.splitOn needle).length > 1 do throwError "the refusal does not name `{needle}`: {msg}"
  let nm := HNames.ofBase decl
  for n in [nm.mod, nm.design, nm.contract, nm.outs, nm.body, nm.thm, decl ++ `ved_open,
      decl ++ `ved_open_eq] do
    if (← getEnv).contains n then throwError "{n} is still in the environment after the refusal"
  let after ← constsUnder decl
  let added := after.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left under {decl} after the refusal: {added}"

def mapFirst (p : Stmt → Bool) (f : Stmt → Stmt) : List Stmt → List Stmt
  | [] => []
  | s :: r => if p s then f s :: r else s :: mapFirst p f r

def isInstOf (n : String) : Stmt → Bool
  | .inst mn _ _ => mn == n
  | _ => false

def accName : String := "Tests.Ved.U2HierCheck.accMod"

/-- Replace the connection of port `p` by `e` in an instance statement. -/
def setConn (p : String) (e : Sparkle.IR.AST.Expr) : Stmt → Stmt
  | .inst mn i cs => .inst mn i (cs.map fun q => if q.1 == p then (p, e) else q)
  | s => s

/-- Replace the connection of port `p` by `e` in the instance NUMBER `k` (0-based). -/
def setConnAt (k : Nat) (p : String) (e : Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  let rec go : List Stmt → Nat → List Stmt
    | [], _ => []
    | s :: r, n =>
      match s with
      | .inst .. => (if n == k then setConn p e s else s) :: go r (n + 1)
      | _ => s :: go r n
  go b 0

def regAt (n : String) (e : Sparkle.IR.AST.Expr) : Stmt :=
  .register n "clk" ("rst", .synchronous) e 0

def w8 (n : String) : Port := ⟨n, .bitVector 8⟩

def withChild (d : Design) (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) : Design :=
  { d with modules := d.modules.map fun c => if c.name == accName then f c else c }

/-- A child whose register input is an undriven wire. -/
def undrivenRegChild (c : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { c with wires := c.wires ++ [w8 "_tmp_u"], body := c.body.map undrivenReg }
where
  undrivenReg : Stmt → Stmt
    | .register o k r _ i => .register o k r (.ref "_tmp_u") i
    | s => s

/-- The controls' summary line. -/
def controlsRun : CommandElabM Unit := do
  let (m, d) ← synthOf ``parCtl
  let name := ``parCtl
  let mut n : Nat := 0
  /- PARENT netlist / order items -/
  -- 1. duplicate register outputs
  expectRefused name "order" "twice"
    { m with body := m.body ++ [regAt "_gen_r" (.ref "_gen_a"), regAt "_gen_r" (.ref "_gen_b")],
             wires := m.wires ++ [w8 "_gen_r"] } d
  n := n + 1
  -- 2. register against an assignment
  expectRefused name "order" "drives a register output"
    { m with body := m.body ++ [regAt "_gen_r" (.ref "_gen_a"), .assign "_gen_r" (.ref "_gen_b")],
             wires := m.wires ++ [w8 "_gen_r"] } d
  n := n + 1
  -- 3. register against an instance output
  expectRefused name "order" "drives a register output"
    { m with body := m.body ++ [regAt "_gen_p" (.ref "_gen_a")] } d
  n := n + 1
  -- 4. a write to a top input (an assignment; an instance output with its old wire still driven)
  expectRefused name "order" "write to a top input"
    { m with body := m.body ++ [.assign "_gen_a" (.ref "_gen_b")] } d
  n := n + 1
  expectRefused name "order" "write to a top input"
    { m with body := setConnAt 1 "out" (.ref "_gen_a") m.body ++ [.assign "_gen_q" (.ref "_gen_b")] } d
  n := n + 1
  -- 5. an undriven register input
  expectRefused name "order" "undriven net"
    { m with body := m.body ++ [regAt "_gen_r" (.ref "_gen_u")],
             wires := m.wires ++ [w8 "_gen_r", w8 "_gen_u"] } d
  n := n + 1
  -- 6. a combinational cycle through an instance: its own output feeds its own input; and two
  --    instances feeding each other
  expectRefused name "order" "combinational cycle"
    { m with body := setConnAt 0 "_gen_x" (.ref "_gen_p") m.body } d
  n := n + 1
  expectRefused name "order" "combinational cycle"
    { m with body := setConnAt 1 "_gen_x" (.ref "_gen_p") (setConnAt 0 "_gen_x" (.ref "_gen_q") m.body) } d
  n := n + 1
  -- 7. an undriven net read by an instance; an undriven output
  expectRefused name "order" "undriven net"
    { m with body := setConnAt 0 "_gen_x" (.ref "_gen_u") m.body, wires := m.wires ++ [w8 "_gen_u"] } d
  n := n + 1
  expectRefused name "order" "no driver"
    { m with body := m.body.filter fun s => match s with | .assign "out" _ => false | _ => true } d
  n := n + 1
  /- CHILD netlist items (the child's own `OrderStmt`, refused inside the child's U1 entry) -/
  expectRefused name "child" "[order]"
    (d := withChild d fun c => { c with body := c.body ++
      [.register "_tmp_a_3" "clk" ("rst", .synchronous) (.ref "_tmp_reg_input_2") 0] }) (m := m)
  n := n + 1
  expectRefused name "child" "[order]"
    (d := withChild d fun c => { c with body := c.body ++ [.assign "_tmp_a_3" (.ref "_gen_x")] }) (m := m)
  n := n + 1
  expectRefused name "child" "[order]" (d := withChild d undrivenRegChild) (m := m)
  n := n + 1
  expectRefused name "hier-shape" "not sane"
    (d := withChild d fun c => { c with body := c.body ++ [.assign "_gen_x" (.ref "_tmp_arg1_1")] }) (m := m)
  n := n + 1
  /- CLOCK / RESET, with the parent's correct table fixed (its data inputs `_gen_a`, `_gen_b`) -/
  -- a constant reset
  expectRefused name "hier-shape" "plain wire reference"
    { m with body := m.body.map (setConn "rst" (.const 0 1)) } d
  n := n + 1
  -- the two instances do not share ONE pair
  expectRefused name "hier-shape" "clock/reset"
    { m with body := setConnAt 1 "rst" (.ref "_gen_b") m.body } d
  n := n + 1
  -- a data input as the reset of both: the design pair is not the contract's real pair
  expectRefused name "clkrst" "clock/reset pair"
    { m with body := m.body.map (setConn "rst" (.ref "_gen_b")) } d
  n := n + 1
  -- a data input as the clock of both
  expectRefused name "clkrst" "clock/reset pair"
    { m with body := m.body.map (setConn "clk" (.ref "_gen_a")) } d
  n := n + 1
  -- clock and reset exchanged
  expectRefused name "clkrst" "clock/reset pair"
    { m with body := m.body.map fun s => setConn "clk" (.ref "rst") (setConn "rst" (.ref "clk") s) } d
  n := n + 1
  -- the contract forced to the design's pair `(clk, _gen_b)`: the REAL port names repeat
  -- (`_gen_b` is both a data input and the reset), so `CorrStmt` refuses
  expectRefused name "table" "CorrStmt"
    { m with body := m.body.map (setConn "rst" (.ref "_gen_b")) } d (some (some ("clk", "_gen_b")))
  n := n + 1
  /- WIRING -/
  -- the data connection of the first instance exchanged for the other input
  expectRefused name "proof" "unsolved goals"
    { m with body := setConnAt 0 "_gen_x" (.ref "_gen_b") m.body } d
  n := n + 1
  -- the two output wires exchanged
  expectRefused name "proof" "unsolved goals"
    { m with body := setConnAt 1 "out" (.ref "_gen_p") (setConnAt 0 "out" (.ref "_gen_q") m.body) } d
  n := n + 1
  -- a connection missing, extra, duplicated, of the wrong width, a non-wire
  expectRefused name "hier-shape" "not connected"
    { m with body := mapFirst (isInstOf accName) (fun s => match s with
        | .inst mn i (a :: r) => .inst mn i (a :: r.drop 1) | s => s) m.body } d
  n := n + 1
  expectRefused name "hier-shape" "no such port"
    { m with body := mapFirst (isInstOf accName) (fun s => match s with
        | .inst mn i cs => .inst mn i (cs ++ [("_gen_zz", .ref "_gen_a")]) | s => s) m.body } d
  n := n + 1
  expectRefused name "hier-shape" "duplicate port connection"
    { m with body := mapFirst (isInstOf accName) (fun s => match s with
        | .inst mn i (a :: r) => .inst mn i (a :: a :: r) | s => s) m.body } d
  n := n + 1
  expectRefused name "hier-shape" "width mismatch"
    { m with wires := m.wires.map fun p => if p.name == "_gen_p" then { p with ty := .bitVector 4 } else p } d
  n := n + 1
  expectRefused name "hier-shape" "plain wire reference"
    { m with body := setConnAt 0 "_gen_x" (.const 1 8) m.body } d
  n := n + 1
  /- THE CHILD -/
  -- the child's body altered (`+` becomes `-`): its U1 theorem is refused
  expectRefused name "child" "[proof]"
    (d := withChild d fun c => { c with body := c.body.map fun s => match s with
      | .assign l (.op .add args) => .assign l (.op .sub args)
      | s => s }) (m := m)
  n := n + 1
  -- the register's initial value altered
  expectRefused name "child" "[proof]"
    (d := withChild d fun c => { c with body := c.body.map fun s => match s with
      | .register o k r e _ => .register o k r e 1
      | s => s }) (m := m)
  n := n + 1
  -- the child's module taken from ANOTHER run: same name, other module (init 1)
  let (_, d2) ← synthOf ``parOther
  expectRefused name "child" "[proof]"
    (d := { d with modules := d2.modules.map fun c => { c with name := accName } }) (m := m)
  n := n + 1
  /- THE DESIGN -/
  expectRefused name "hier-shape" "not the returned module" m d2
  n := n + 1
  expectRefused name "hier-shape" "not instantiated"
    m { d with modules := d.modules ++ d2.modules }
  n := n + 1
  expectRefused name "hier-shape" "duplicate child module names"
    m { d with modules := d.modules ++ d.modules }
  n := n + 1
  expectRefused name "hier-shape" "not the returned module" m { d with topModule := "other" }
  n := n + 1
  expectRefused name "hier-shape" "is not in the returned design" m { d with modules := [] }
  n := n + 1
  /- SCOPE: a parent with a (clean) register is H2b; an instance fed by a wire that is not a parent
     input is outside H2a -/
  expectRefused name "scope" "H2b"
    { m with body := m.body ++ [regAt "_gen_r" (.ref "_gen_a")], wires := m.wires ++ [w8 "_gen_r"] } d
  n := n + 1
  expectRefused name "conns" "not connected to a parent input"
    { m with body := .assign "_gen_w" (.op .add [.ref "_gen_a", .ref "_gen_b"]) :: setConnAt 0 "_gen_x" (.ref "_gen_w") m.body,
             wires := m.wires ++ [w8 "_gen_w"] } d
  n := n + 1
  logInfo m!"controls: {n} refused, nothing left under the base"

/-- info: controls: 37 refused, nothing left under the base -/
#guard_msgs in
run_cmd controlsRun

/-! ## Entry-level refusals before or at the very start -/

def entryRefused (decl : Name) (stage : String) : CommandElabM Unit := liftTermElabM do
  let r ← try
      discard <| vedU2HierEntry decl
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match r with
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do throwError "unexpected: {msg}"
    pure ()
  | none => throwError "{decl} accepted"

/-- info: multi-output refused -/
#guard_msgs in
run_cmd do
  entryRefused ``parPair "multi-output"
  logInfo "multi-output refused"

/-- info: derived instance input refused at [conns] -/
#guard_msgs in
run_cmd do
  entryRefused ``parDerived "conns"
  logInfo "derived instance input refused at [conns]"

/-! ## Positive controls: meaning-preserving changes are ACCEPTED with the exact statement -/

def checkOkWith (decl : Name) (m : Sparkle.IR.AST.Module) (d : Design) : CommandElabM Unit :=
  liftTermElabM do
  let (stmt, nDom) ← specialiseDomain decl
  let (thm, _, _) ← checkU2H decl stmt nDom m d
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HStmt c m d decl"
  std3Only thm
  logInfo m!"accepted {decl}"

/-- Consistent renaming of the instance names (`u0`, `u1`): the paths of the state follow. -/
def renameInsts (b : List Stmt) : List Stmt :=
  let rec go : List Stmt → Nat → List Stmt
    | [], _ => []
    | .inst mn _ cs :: r, k => .inst mn s!"u{k}" cs :: go r (k + 1)
    | s :: r, k => s :: go r k
  go b 0

/-- info: accepted Tests.Ved.U2HierCheck.parRn -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``parRn
  checkOkWith ``parRn { m with body := renameInsts m.body } d

-- The two instances exchanged in the body AND their names exchanged (a symmetric re-labelling).
/-- info: accepted Tests.Ved.U2HierCheck.parSw -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``parSw
  match m.body with
  | .inst a i0 c0 :: .inst b i1 c1 :: rest =>
    checkOkWith ``parSw { m with body := .inst b i1 c1 :: .inst a i0 c0 :: rest } d
  | _ => throwError "unexpected body"

-- The closed run of the renamed design is the same as the original's.
/-- info: renamed: same run -/
#guard_msgs in
run_cmd do
  let (m, d) ← synthOf ``parTwo
  let m' := { m with body := renameInsts m.body }
  unless outsOf d m' inpS 4 == outsOf d m inpS 4 do throwError "renaming changed the run"
  logInfo "renamed: same run"

/-! ## Type-level controls: another design / declaration / child does not typecheck -/

def typeMismatch (what : String) (stx : Syntax) (ty : Lean.Expr) : CommandElabM Unit := liftTermElabM do
  let ok ← try
      withoutErrToSorry do
        discard <| elabTermEnsuringType stx ty
        synthesizeSyntheticMVarsNoPostponing
      pure true
    catch _ => pure false
  if ok then throwError "{what}: the substituted proof was ACCEPTED"
  logInfo m!"{what}: refused"

/-- info: another declaration's proof: refused -/
#guard_msgs in
run_cmd do
  typeMismatch "another declaration's proof" (← `(Tests.Ved.U2HierCheck.parRn.ved_u1))
    (expectedOf ``parTwo 0)

/-- info: another Design: refused -/
#guard_msgs in
run_cmd do
  let nm := HNames.ofBase ``parTwo
  let nm2 := HNames.ofBase ``parRn
  let ty := mkAppN (Lean.mkConst ``U2HStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm2.design, Lean.mkConst ``parTwo]
  typeMismatch "another Design" (← `(Tests.Ved.U2HierCheck.parTwo.ved_u1)) ty

/-- info: another child's proof: refused -/
#guard_msgs in
run_cmd do
  let k := Names.ofBase (`Tests.Ved.U2HierCheck.parMulti ++ `ved_child ++ ``twoReg)
  let ty := mkAppN (Lean.mkConst ``U1Stmt)
    #[Lean.mkConst k.contract, Lean.mkConst k.mod, Lean.mkConst ``accMod]
  typeMismatch "another child's proof"
    (← `(Tests.Ved.U2HierCheck.parTwo.ved_child.Tests.Ved.U2HierCheck.accMod.ved_u1)) ty

/-! ## Axioms of the new lemmas, MACHINE-checked -/

run_cmd liftCoreM do
  for n in [``Tools.VedU2Hier.orderOkHS_sound, ``Tools.VedU2Hier.orderOkHS_hwr,
      ``Tools.VedU2Hier.exists_arrHS, ``Tools.VedU2Hier.fold_oracle,
      ``Tools.VedU2Hier.runHSTrace_cycle, ``Tools.VedU2Hier.outputsOnHS_of_oracle,
      ``Tools.VedU2Hier.kid_inst, ``Tools.VedU2Hier.connsIn_sound, ``Tools.VedU2Hier.dataIn_sound,
      ``Tools.VedU2Hier.runModule_congr_seed, ``parTwo_changing_clock, ``parTwo_any_clock,
      ``insRst_not_ok, ``inputsOk_clk, ``parTwo.ved_u1, ``parMulti.ved_u1,
      ``parTwo.ved_open_eq, ``Tools.VedU2Hier.runHS_proj, ``Tools.VedU2Hier.runHS_proj_aux,
      ``Tools.VedU2Hier.runHS_exists, ``Tools.VedU2Hier.runHS_child_clkRst,
      ``Tools.VedU2Hier.childSucc_of_outputsOn, ``Tools.VedU2Hier.instPair_tie,
      ``Tools.VedU2Hier.st0H_slice, ``Tools.VedU2Hier.runHS_inputs, ``Tools.VedU2Hier.stepHS_succ,
      ``Tools.VedU2Hier.runHS_stateless, ``Tools.VedU2Hier.runHS_leaf] do
    std3Only n

end Tests.Ved.U2HierCheck
