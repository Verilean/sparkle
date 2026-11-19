import Sparkle
import Tools.VedMemEntry
import Tools.VedMemLoop
import Tools.VedMemPack

/-!
# Checks for the closing stage of the packed memory rows (sparkle-ved-memory-rest)

Small examples that pin what R034 needed (`Tools/VedMemLoop.lean`, `Tools/VedMemPack.lean`):

* `ved_mem_addr`, `Expr.replace` path (goals of at least `addrReplaceMinTree` = 5e7 tree nodes, here a shared DAG of 2.7e8): two reads of the
  same memory at addresses of different spelling are unified (the `congrArg` of the new goal is built in the context that holds the
  `have`-introduced `hmaddr`; it threw "unknown free variable", the addresses stayed different atoms, goals that read one word twice
  were unprovable).
* `clearSigHyps`: the hypotheses about signals go, the others stay.
* `ved_omega_t`: the leaf of R034 goal 44 (`omega` needs 3.0M heartbeats, over the 2M cap of `ved_omega`) closes; a false residual of that
  shape is refused.
* `ved_omega_n` / `ved_mod_norm`: the leaves of R034 goal 54 (flags of a 16-bit sum in two spellings, nested `%` / `/`, the v2 = 4 case and the
  `65536 - (..) % 65536` case) close; a false one is refused.
* `ved_ctrl_cases` + `ved_leaf_gate`: a control case split with such a leaf closes; with a false leaf `ved_ctrl_cases` fails, the flag is
  set, the gate refuses (the leafwise closers are skipped) once and resets.
-/

namespace Tests.Ved.VedMemCloseCheck

open Lean Elab Command Term Meta Tactic
open Sparkle.Core.Domain Sparkle.Core.Signal

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## ved_mem_addr on a goal of 2.7e8 tree nodes -/

/-- `x + x` nested `k` times: a shared DAG of `2 ^ k` leaves -/
def bigDag (x : Expr) : Nat → MetaM Expr
  | 0 => pure x
  | k + 1 => do
    let t ← bigDag x k
    mkAppM ``HAdd.hAdd #[t, t]

elab "big_dag " k:num x:term : term => do
  bigDag (← elabTerm x (some (mkConst ``Nat))) k.getNat

/-- the distinct addresses of the `memState` reads of an expression -/
def memAddrs (e : Expr) : Array Expr := Id.run do
  let isMem := fun (x : Expr) => x.isAppOf ``Sparkle.Core.Signal.Signal.memState && x.getAppNumArgs ≥ 9
  let mut r : Array Expr := #[]
  for o in Tools.VedU1WireShare.collectDag isMem e do
    unless r.contains (o.getAppArgs[8]!) do r := r.push (o.getAppArgs[8]!)
  return r

def addrCheck : TermElabM Unit := do
  let ty ← elabType (← `(∀ {dom : DomainConfig} (wa : Signal dom (BitVec 4)) (wd : Signal dom (BitVec 16)) (we : Signal dom Bool) (x : Nat),
    (Signal.memState (fun _ => 0#16) wa wd we 3 (1#4 + 2#4)).toNat + (big_dag 27 x)
      = (Signal.memState (fun _ => 0#16) wa wd we 3 3#4).toNat + (big_dag 27 x)))
  forallTelescope (← instantiateMVars ty) fun _ body => do
    let sz := Tools.VedU1Loop.treeSizeVal body
    unless sz ≥ Tools.VedMemLoop.addrReplaceMinTree do throwError "goal too small for the Expr.replace path: {sz}"
    unless (memAddrs body).size == 2 do throwError "expected two spellings of the address before"
    let m ← mkFreshExprMVar body
    let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| ved_mem_addr)))
    let [g] := gs | throwError "ved_mem_addr: {gs.length} goals"
    let n := (memAddrs (← instantiateMVars (← g.getType))).size
    unless n == 1 do throwError "ved_mem_addr: {n} addresses left (not unified)"
    logInfo m!"ved_mem_addr: one address left (goal of {sz} tree nodes)"

/-- info: ved_mem_addr: one address left (goal of 4294967601 tree nodes) -/
#guard_msgs in
#eval addrCheck

/-! ## clearSigHyps -/

elab "ved_sig_hyp_test" : tactic => do
  Tools.VedMemPack.clearSigHyps
  withMainContext do
    let mut sig : Nat := 0
    let mut other : Nat := 0
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if (d.type.find? fun e => e.isConst && e.constName!.getPrefix == `Sparkle.Core.Signal.Signal).isSome then sig := sig + 1
        else if d.userName == `hnat then other := other + 1
    unless sig == 0 && other == 1 do throwError "clearSigHyps: {sig} signal hypotheses left, {other} of 1 others"

theorem sigHyps {dom : DomainConfig} (s : Signal dom (BitVec 4)) (hs : s = s) (hnat : 1 = 1) : True := by
  ved_sig_hyp_test
  trivial

/-! ## ved_omega_t (R034 goal 44) -/

theorem leaf44 (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) :
    (x4.toNat % 65536 + x6.toNat % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768))) % 65536 % 65536 =
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768))) % 65536 := by
  ved_omega_t

/-- a refusal control: `ved_omega_t` does not prove a false residual -/
theorem refuse44 (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) : True := by
  fail_if_success (have _h := (show (x4.toNat % 65536 + x6.toNat % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768))) % 65536 % 65536 =
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 1) % 65536 by ved_omega_t); trivial)
  trivial

/-! ## ved_omega_n (R034 goal 54) -/

/-- the sum of the packed flags in two spellings (v2 = 4 case of goal 54) -/
theorem leaf54a (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) :
    (1024 * ((16 * ((2 * (((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2) +
        ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2) % 4)) % 64) +
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 64 % 1024) % 65536 =
    1024 * ((2 * ((x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2) +
        (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2) * 16) +
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 64 % 1024 := by
  ved_omega_n

/-- the `65536 - (..) % 65536` case (v2 = 6 of goal 54): plain `omega` does not end on it -/
theorem leaf54b (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) :
    ((x4.toNat % 65536 + (65536 - x6.toNat % 65536)) % 65536 +
        (65536 - (32768 * (x5.toNat % 65536 / 32768 % 2) + x5.toNat % 65536 / 2 % 32768 + (65536 - x7 % 65536)) % 65536) + 32) % 65536 / 32768 % 2 =
      (65536 - (65536 - x7 + (32768 * (x5.toNat / 32768 % 2) + x5.toNat / 2 % 32768)) % 65536 + (65536 - x6.toNat + x4.toNat) + 32) % 65536
        / 32768 % 2 := by
  ved_omega_n

/-- a refusal control: the same sums, a false flag -/
theorem refuse54 (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) : True := by
  fail_if_success (have _h := (show ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2 =
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 33) % 65536 / 32768 % 2 by ved_omega_n); trivial)
  trivial

/-! ## ved_ctrl_cases and the gate -/

theorem ctrl54 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) :
    (if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat) := by
  ved_ctrl_cases

elab "ved_assert_leaf_flag" : tactic => do
  unless ← Tools.VedMemPack.ctrlLeafFailed.get do throwError "ctrlLeafFailed not set"

/-- the leaf is false: `ved_ctrl_cases` fails and sets the flag, the gate refuses once and resets it -/
theorem gate54 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) : True := by
  fail_if_success (have _h := (show (if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 33) % 65536 / 32768 % 2
    else x4.toNat) by ved_ctrl_cases); trivial)
  ved_assert_leaf_flag
  fail_if_success (ved_leaf_gate skip)
  ved_leaf_gate skip
  trivial

/-! ## axioms -/

elab "#ved_axioms " ids:ident* : command => do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for id in ids do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    let axs ← liftCoreM (collectAxioms n)
    unless axs.all (std.contains ·) do throwError "{n}: axioms {axs}"
  logInfo m!"axioms within std3: {ids.size} declarations"

/-- info: axioms within std3: 8 declarations -/
#guard_msgs in
#ved_axioms Tools.VedMemPack.ved_mod_sum sigHyps leaf44 refuse44 leaf54a leaf54b ctrl54 gate54

end Tests.Ved.VedMemCloseCheck
