import Tools.VedU1Entry
import IP.Crypto.Keccak256HW

/-!
# `#ved_u1` on the real `Sparkle.IP.Crypto.Keccak256HW.keccakRcHW`

The original declaration (a 32-entry `kLut!` of 64-bit constants over a 5-bit index, no copy), not a small
stand-in.  After `#ved_u1` the three facts are checked independently of the entry:

* the stored type of `keccakRcHW.ved_u1` is, as an `Expr` compared with `==`, the hand-rebuilt
  `U1Stmt keccakRcHW.ved_contract keccakRcHW.ved_mod (@keccakRcHW defaultDomain)`;
* its axioms are within `propext`, `Classical.choice`, `Quot.sound`;
* an OBSERVATION from another run: a fresh `synthesizeCombinational` gives a module equal
  (`DecidableEq`) to the one the registered `ved_mod` denotes.  This is a second synthesis,
  not evidence about the entry's own run.  That the theorem is about the SAME run's
  artifact comes from the entry itself (`vedU1EntryS` keeps the returned `m`, `checkU1E`
  registers `toExpr m`, checks it evaluates back to `m`, and compares the theorem's full
  type), not from this re-synthesis.

The 32-deep `mux` chain needs the entry's finite elaboration budget (`withProofBudget`:
`simp` recurses once per level); the kernel still checks the result in full.

Runs in the VED workflow as its own step next to rconHW (it imports the Keccak IP),
separate from the fast U1 step.
-/

namespace Tests.Ved.U1KeccakRcCheck

open Lean Elab Command Term Meta
open Tools.VedU1Contract Tools.VedU1Entry

#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.Crypto.Keccak256HW.keccakRcHW

def checkKeccakRc : CommandElabM Unit := liftTermElabM do
  let decl := ``Sparkle.IP.Crypto.Keccak256HW.keccakRcHW
  let nm := Names.ofBase decl
  let thm := decl ++ `ved_u1
  let stmt := mkApp (Lean.mkConst decl) (Lean.mkConst ``Sparkle.Core.Domain.defaultDomain)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m (@keccakRcHW defaultDomain)"
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  -- observation from ANOTHER run: a fresh synthesis equals the registered `ved_mod`
  -- (the same-run binding is the entry's, see the header)
  let some v := (← getConstInfo nm.mod).value? | throwError "no value of {nm.mod}"
  let registered ← evalModule v
  let (fresh, _) ← Sparkle.Compiler.Elab.synthesizeCombinational decl
  unless registered = fresh do throwError "{nm.mod} differs from a fresh synthesis"
  logInfo m!"OK type, axioms {ax.size}, ved_mod = a fresh synthesis (another run)"

/-- info: OK type, axioms 3, ved_mod = a fresh synthesis (another run) -/
#guard_msgs in
run_cmd checkKeccakRc

end Tests.Ved.U1KeccakRcCheck
