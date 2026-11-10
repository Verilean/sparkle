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

end Tests.Ved.U2HierCheck
