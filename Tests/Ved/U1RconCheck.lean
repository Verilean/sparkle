import Tools.VedU1Entry
import IP.Crypto.AESHW

/-!
# `#ved_u1` on the real `Sparkle.IP.Crypto.AESHW.rconHW`

The original declaration (a 16-entry `kLut!` over a 4-bit index, no copy), not a small
stand-in.  After `#ved_u1` the three facts are checked independently of the entry:

* the stored type of `rconHW.ved_u1` is, as an `Expr` compared with `==`, the hand-rebuilt
  `U1Stmt rconHW.ved_contract rconHW.ved_mod (@rconHW defaultDomain)`;
* its axioms are within `propext`, `Classical.choice`, `Quot.sound`;
* `rconHW.ved_mod` is the module the entry returned: a fresh `synthesizeCombinational`
  gives a module equal (`DecidableEq`) to the one the registered `ved_mod` denotes.

Not in the VED CI workflow: it imports the AES IP and the kernel decision over the 4-bit
index is the most expensive check of this family.
-/

namespace Tests.Ved.U1RconCheck

open Lean Elab Command Term Meta
open Tools.VedU1Contract Tools.VedU1Entry

#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.Crypto.AESHW.rconHW

def checkRcon : CommandElabM Unit := liftTermElabM do
  let decl := ``Sparkle.IP.Crypto.AESHW.rconHW
  let nm := Names.ofBase decl
  let thm := decl ++ `ved_u1
  let stmt := mkApp (Lean.mkConst decl) (Lean.mkConst ``Sparkle.Core.Domain.defaultDomain)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m (@rconHW defaultDomain)"
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  -- `ved_mod` is the module of the entry's run
  let some v := (← getConstInfo nm.mod).value? | throwError "no value of {nm.mod}"
  let registered ← evalModule v
  let (fresh, _) ← Sparkle.Compiler.Elab.synthesizeCombinational decl
  unless registered = fresh do throwError "{nm.mod} differs from a fresh synthesis"
  logInfo m!"OK type, axioms {ax.size}, ved_mod = synthesis"

/-- info: OK type, axioms 3, ved_mod = synthesis -/
#guard_msgs in
run_cmd checkRcon

end Tests.Ved.U1RconCheck
