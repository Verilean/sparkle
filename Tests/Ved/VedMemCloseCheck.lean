import Sparkle
import Sparkle.Compiler.Elab
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
* `ved_goal_gate n`: at most `n` open goals pass, more are refused (the case-split gate of the memory loop; `n = 0` disables it).  The limit is the public option `ved.mem.goalGate` (default 512), read by `#ved_u1_mem` and put into its script.
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

/-- the leaf is false, the context has big hypotheses (the ones `omega` would read): `ved_ctrl_cases` fails and sets the flag, the gate refuses once and resets it -/
theorem gate54 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16)
    (hbig : ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat)) ∧ ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat)) ∧ ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat))) : True := by
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

elab "ved_assert_no_leaf_flag" : tactic => do
  if ← Tools.VedMemPack.ctrlLeafFailed.get then throwError "ctrlLeafFailed set without big hypotheses"

/-- the same false leaf without big hypotheses: `ved_ctrl_cases` fails, the flag stays unset (the leafwise closers may still run) -/
theorem gateSmall54 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16) : True := by
  fail_if_success (have _h := (show (if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 33) % 65536 / 32768 % 2
    else x4.toNat) by ved_ctrl_cases); trivial)
  ved_assert_no_leaf_flag
  trivial

/-- the flag of a failing call does not survive the NEXT `ved_ctrl_cases`: after a failure that set it (and was not read by a
gate), a succeeding call clears it and the gate runs its tactic -/
theorem gateResetOk54 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16)
    (hbig : ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat)) ∧ ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat)) ∧ ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat))) : True := by
  fail_if_success (have _h := (show (if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 33) % 65536 / 32768 % 2
    else x4.toNat) by ved_ctrl_cases); trivial)
  ved_assert_leaf_flag
  have _ok : (if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat) := by ved_ctrl_cases
  ved_assert_no_leaf_flag
  ved_leaf_gate skip
  trivial

/-- likewise after a failing next call whose residual does not have the gated shape (no `(a % m) / k`): the flag is cleared on entry -/
theorem gateResetFail54 (c : BitVec 3) (x4 x5 x6 : BitVec 16) (x7 : Nat) (h7 : x7 < 2 ^ 16)
    (hbig : ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat)) ∧ ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat)) ∧ ((if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 32) % 65536 / 32768 % 2
    else x4.toNat))) : True := by
  fail_if_success (have _h := (show (if c.toNat % 8 = 4 then
      ((x4.toNat % 65536 + x6.toNat % 65536) % 65536 +
        (x5.toNat % 65536 + (32768 * (x7 % 65536 / 32768 % 2) + x7 % 65536 / 2 % 32768)) % 65536 + 32) % 65536 / 32768 % 2
    else x4.toNat) =
    (if c.toNat % 8 = 4 then
      (x4.toNat + x6.toNat + (x5.toNat + (32768 * (x7 / 32768 % 2) + x7 / 2 % 32768)) + 33) % 65536 / 32768 % 2
    else x4.toNat) by ved_ctrl_cases); trivial)
  ved_assert_leaf_flag
  fail_if_success (have _h := (show (if c.toNat % 8 = 4 then x4.toNat else x5.toNat) = x6.toNat by ved_ctrl_cases); trivial)
  ved_assert_no_leaf_flag
  ved_leaf_gate skip
  trivial

/-! ## ved_mem_budget / withLocalHb: the local budget of `ved_pack_wire_m`'s fallback

Same rule as `ved_budget` (ved/perf-r281): local max = min(what is left of the ambient budget, local), at least 1; with an
unlimited ambient budget the local one alone; on exhaustion the state from before is restored.  `burn_hb k` (test-only)
allocates `k * 1000` heartbeats honouring the limit, so the numbers are heartbeats, not wall-clock. -/

/-- Test-only: burn `k * 1000` heartbeats, honouring the heartbeat limit. -/
elab "burn_hb " k:num : tactic => do
  let start ← IO.getNumHeartbeats
  let target := k.getNat * 1000
  let r ← IO.mkRef ([] : List Nat)
  let mut i := 0
  while (← IO.getNumHeartbeats) - start < target do
    Core.checkSystem "burn_hb"
    r.set (List.replicate 20 i)
    i := i + 1

/-- The old local budget of `ved_pack_wire_m` (0362a39c and before; the control): clock restarted, local value alone -/
elab "ved_mem_budget_old " n:num t:tactic : tactic => do
  let hb ← IO.getNumHeartbeats
  let r ← withTheReader Core.Context (fun c => { c with initHeartbeats := hb, maxHeartbeats := n.getNat * 1000 }) do
    tryCatchRuntimeEx (do evalTactic t; pure true) fun e => if e.isRuntime then pure false else throw e
  unless r do throwError "ved_mem_budget_old: local heartbeat budget exhausted"

-- enough budget
example : True := by ved_mem_budget 1000 (burn_hb 20; trivial)

-- ambient unlimited: the local cap applies (without it the same work succeeds)
set_option maxHeartbeats 0 in
example : True := by burn_hb 300; trivial

/-- error: ved_mem_budget: local heartbeat budget exhausted -/
#guard_msgs in
set_option maxHeartbeats 0 in
example : True := by ved_mem_budget 100 (burn_hb 300; trivial)

-- the remaining ambient budget is respected: 100 thousand, 80 burned, `t` needs 60 (< local 1000)
/-- error: ved_mem_budget: local heartbeat budget exhausted -/
#guard_msgs in
set_option maxHeartbeats 100 in
example : True := by burn_hb 80; ved_mem_budget 1000 (burn_hb 60; trivial)

-- control: the old rule lets the same script through (the ambient limit is exceeded)
set_option maxHeartbeats 100 in
example : True := by burn_hb 80; ved_mem_budget_old 1000 (burn_hb 60; trivial)

-- within what is left it passes
set_option maxHeartbeats 100 in
example : True := by burn_hb 80; ved_mem_budget 1000 (burn_hb 5; trivial)

-- partial state change, then out of budget: the next alternative / the next tactic sees the ORIGINAL goal
example : True ∧ True := by
  first
    | ved_mem_budget 10 (refine ⟨?_, ?_⟩; burn_hb 300; all_goals trivial)
    | exact ⟨trivial, trivial⟩

example : True ∧ True := by
  (try ved_mem_budget 10 (refine ⟨?_, ?_⟩; burn_hb 300)) <;> exact ⟨trivial, trivial⟩

-- a failure that is not a runtime exception passes through
/--
error: boom
⊢ True
-/
#guard_msgs in
example : True := by ved_mem_budget 10 (fail "boom")

/-! ## ved_goal_gate (sparkle-ved-perf-mem-refused) -/

/-- three open goals, limit three: the gate lets the proof through (the control where it must not skip) -/
theorem goalGateOk : True ∧ True ∧ True := by
  refine ⟨?_, ?_, ?_⟩
  ved_goal_gate 3
  all_goals trivial

/-- four open goals, limit three: the gate refuses (the refusal is an ordinary tactic failure, the `[proof]` refusal of the entry) -/
theorem goalGateRefuses : True := by
  have _h : True ∧ True ∧ True ∧ True := by
    refine ⟨?_, ?_, ?_, ?_⟩
    fail_if_success (ved_goal_gate 3)
    all_goals trivial
  trivial

/-- a raised limit lets four goals through -/
theorem goalGateRaised : True := by
  have _h : True ∧ True ∧ True ∧ True := by
    refine ⟨?_, ?_, ?_, ?_⟩
    ved_goal_gate 4
    all_goals trivial
  trivial

/-- limit 0 disables the gate -/
theorem goalGateOff : True := by
  have _h : True ∧ True ∧ True ∧ True := by
    refine ⟨?_, ?_, ?_, ?_⟩
    ved_goal_gate 0
    all_goals trivial
  trivial

/-- info: 512 -/
#guard_msgs in
#eval Tools.VedMemEntry.ved.mem.goalGate.defValue

/-! ### through the real entry (`#ved_u1_mem` reads `ved.mem.goalGate` and puts it into the generated script) -/

declare_signal_state FState
  | fsm  : BitVec 2  := 0#2
  | idx  : BitVec 5  := 0#5
  | last : BitVec 16 := 0#16

/-- a loop with two memories (the `memFsm` of `VedMemCheck`): its case split leaves a handful of goals -/
def gateFsm {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let fsm := FState.fsm state
    let idx := FState.idx state
    let isProcess := fsm === (1#2 : Signal dom _)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let outMemRead := Signal.memory readAddr4 inputCoeff isProcess (Signal.pure 0#4)
    let fsmNext := Signal.mux start (Signal.pure 1#2) (Signal.mux (idx === (15#5 : Signal dom _)) (Signal.pure 0#2) fsm)
    let idxNext := Signal.mux isProcess (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#5 idxNext, Signal.register 0#16 outMemRead]
  FState.last state

/-- the same module under other names (each accepted run stores a theorem under the declaration's name) -/
def gateFsmB {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData

def gateFsmD {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData

def gateFsmE {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData

def gateFsmC {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData

-- the case split leaves 18 goals; limit 7: refused at `[proof]`, the refusal names the configured value 7
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.gateFsm [proof]: ved_goal_gate: 18 goals after the case split exceed the configured limit ved.mem.goalGate (7); raise it with `set_option ved.mem.goalGate N` or disable the gate with `set_option ved.mem.goalGate 0` -/
#guard_msgs in
set_option ved.mem.goalGate 7 in
#ved_u1_mem gateFsm

-- limit 17 (one below the goal count): still refused, value 17
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.gateFsm [proof]: ved_goal_gate: 18 goals after the case split exceed the configured limit ved.mem.goalGate (17); raise it with `set_option ved.mem.goalGate N` or disable the gate with `set_option ved.mem.goalGate 0` -/
#guard_msgs in
set_option ved.mem.goalGate 17 in
#ved_u1_mem gateFsm

-- limit 18 (raised): the entry accepts
#guard_msgs (drop info) in
set_option ved.mem.goalGate 18 in
#ved_u1_mem gateFsm

-- limit 0 disables the gate: accepted
#guard_msgs (drop info) in
set_option ved.mem.goalGate 0 in
#ved_u1_mem gateFsmB

-- default (512): accepted
#guard_msgs (drop info) in
#ved_u1_mem gateFsmC

/-! ## ved.mem.loopGate / ved.mem.h0Budget (sparkle-ved-perf-mem-timeout)

`ved_loop_unfold_mem` refuses a loop with more than `ved.mem.loopGate` tree nodes (default 10^7; strict rows 6k-44k, R025/R035 1.6e9/3.2e7 observed),
and the base case of the memory loop (`h0`) runs in `ved_h0_budget`, a local heartbeat limit `ved.mem.h0Budget` (units of `maxHeartbeats`; default 1000000, strict rows
35k-260k).  Both are heuristic limits with public options; 0 disables.  The entry reads the options and puts the values into the script (`(limit := n)` of `ved_loop_unfold_mem`, `ved_h0_budget n`), like `ved.mem.goalGate`; the entry-level refusals are exercised below on `lgA`, a module whose memory loop is really unfolded (`gateFsm`'s loop is never gated: its limit 1 passes), and on the real rows (R025/R028). -/

/-- info: 10000000 -/
#guard_msgs in
#eval Tools.VedMemLoop.ved.mem.loopGate.defValue

/-- info: 1000000 -/
#guard_msgs in
#eval Tools.VedMemLoop.ved.mem.h0Budget.defValue

/-- Test-only: run `t`, which must fail, and every string of `subs` must occur in the error message (and none of `nots`); the state is restored. -/
elab "expect_err " subs:str,+ &"without" nots:str,* " in " t:tactic : tactic => do
  let s ← Tactic.saveState
  let msg? ← tryCatchRuntimeEx (do Tactic.evalTactic t; pure none) fun e => do pure (some (← e.toMessageData.toString))
  s.restore
  let some msg := msg? | throwError "expect_err: the tactic did not fail"
  for x in subs.getElems do
    unless (msg.splitOn x.getString).length > 1 do throwError "expect_err: `{x.getString}` not in the message:\n{msg}"
  for x in nots.getElems do
    if (msg.splitOn x.getString).length > 1 then throwError "expect_err: `{x.getString}` is in the message:\n{msg}"
  -- the goal `True` is closed by assignment (no heartbeat check: an exhausted ambient budget would stop `trivial`)
  (← Tactic.getMainGoal).assign (mkConst ``True.intro)
  Tactic.replaceMainGoal []

-- `ved_h0_budget n`: enough (the default 1000000) passes
example : True := by ved_h0_budget 1000000 (burn_hb 20; trivial)

-- (1) control: the LOCAL limit stops the run (ambient unlimited): neutral text with the minimum, the local value named as the smaller one, no claim of a "needs more"
/-- error: ved_h0_budget: the base case (h0) did not finish within min(local ved.mem.h0Budget, remaining ambient budget) = 100 heartbeats (units of maxHeartbeats): the local limit ved.mem.h0Budget = 100 was the smaller one (the ambient budget is unlimited); raise `maxHeartbeats` or `set_option ved.mem.h0Budget N`, or disable the local limit with `set_option ved.mem.h0Budget 0` -/
#guard_msgs in
set_option maxHeartbeats 0 in
example : True := by ved_h0_budget 100 (burn_hb 300; trivial)

-- local limit smaller than a finite ambient budget (8M here): still the local text (the ambient number is not part of it)
set_option maxHeartbeats 8000000 in
example : True := by
  expect_err "= 100 heartbeats", "the local limit ved.mem.h0Budget = 100 was the smaller one", "remaining ambient budget was not smaller" without "needs more", "too small" in
    ved_h0_budget 100 (burn_hb 300; trivial)

-- a raised limit passes the same work
set_option maxHeartbeats 0 in
example : True := by ved_h0_budget 400 (burn_hb 300; trivial)

-- (1) control: the AMBIENT budget is smaller than the local limit (100 thousand, 80 burned, 60 needed, local 1000000): the text says ambient / min, never "local limit too small"
set_option maxHeartbeats 100 in
example : True := by
  burn_hb 80
  expect_err "min(local ved.mem.h0Budget, remaining ambient budget)", "the remaining ambient budget (maxHeartbeats) =", "was the smaller one, not the local limit ved.mem.h0Budget = 1000000" without "needs more", "was the smaller one (the remaining" in
    ved_h0_budget 1000000 (burn_hb 60; trivial)

-- (1) control: `h0Budget 0` (local off) with an unlimited ambient budget runs unbounded ...
set_option maxHeartbeats 0 in
example : True := by ved_h0_budget 0 (burn_hb 300; trivial)

-- ... and still respects the ambient budget: exhausted -> refused (not run unbounded), the text says the local limit is off and the ambient budget ended the run
set_option maxHeartbeats 100 in
example : True := by
  burn_hb 80
  expect_err "the local limit ved.mem.h0Budget is off (0)", "the remaining ambient budget (maxHeartbeats) =", "ended the run" without "needs more", "too small" in
    ved_h0_budget 0 (burn_hb 60; trivial)

-- (1) control: failures that are not heartbeat limits keep their own classification (the state is restored; no h0Budget text)
/-- error: boom
⊢ True -/
#guard_msgs in
example : True := by ved_h0_budget 100 (fail "boom")

/-- Test-only: recurse `n` levels deep with `withIncRecDepth` (a `maxRecDepth` runtime exception, not a heartbeat limit) -/
partial def deepRec : Nat → MetaM Unit
  | 0 => pure ()
  | n + 1 => withIncRecDepth (deepRec n)

elab "deep_rec " n:num : tactic => deepRec n.getNat

set_option maxRecDepth 50 in
example : True := by
  expect_err "maximum recursion depth" without "ved_h0_budget", "did not finish", "ved.mem.h0Budget" in
    ved_h0_budget 1000000 (deep_rec 1000)

set_option maxRecDepth 50 in
example : True := by
  expect_err "maximum recursion depth" without "ved_h0_budget", "did not finish", "ved.mem.h0Budget" in
    ved_h0_budget 0 (deep_rec 1000)

-- state restored on failure: the next tactic sees the original goal
example : True ∧ True := by
  set_option maxHeartbeats 0 in
  (try ved_h0_budget 10 (refine ⟨?_, ?_⟩; burn_hb 300)) <;> exact ⟨trivial, trivial⟩

-- raised / disabled limits accept (the same module under other names)
#guard_msgs (drop info) in
set_option ved.mem.loopGate 100000 in
#ved_u1_mem gateFsmD

#guard_msgs (drop info) in
set_option ved.mem.loopGate 0 in
set_option ved.mem.h0Budget 0 in
#ved_u1_mem gateFsmE

/-! ### through the real entry, on a loop that IS unfolded (sparkle-ved-perf-mem-timeout)

`lgA` is `memQuant` of `VedMemCheck` under other names (a counter that reads an input memory and writes a registered output memory): its loop
is unfolded by `ved_loop_unfold_mem`, so the gate computes the tree size and `h0` runs under `ved_h0_budget`.  The gate refuses when
`treeSize > ved.mem.loopGate` (strictly greater: a limit equal to the tree size accepts, one less refuses). -/

declare_signal_state LState
  | idx  : BitVec 5  := 0#5
  | busy : Bool      := false
  | last : BitVec 16 := 0#16

def lgA {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let idx := LState.idx state
    let busy := LState.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1
    let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
    let outMemRead := Signal.memory readAddr4 result busy (Signal.pure 0#4)
    let done := busy &&& (idx === 15#5)
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  LState.last state

/-- the same module under other names (each accepted run stores a theorem under the declaration's name) -/
def lgB {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData
def lgC {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData
def lgD {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData
def lgE {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData

-- low loopGate (1): `[proof]` refusal naming the configured value and the tree size (1297 nodes)
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.lgA [proof]: ved_loop_unfold_mem: the loop has 1297 tree nodes, more than the configured limit ved.mem.loopGate (1); raise it with `set_option ved.mem.loopGate N` or disable the gate with `set_option ved.mem.loopGate 0` -/
#guard_msgs in
set_option ved.mem.loopGate 1 in
#ved_u1_mem lgA

-- boundary: limit = tree size - 1 (1296): refused, the value is named
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.lgA [proof]: ved_loop_unfold_mem: the loop has 1297 tree nodes, more than the configured limit ved.mem.loopGate (1296); raise it with `set_option ved.mem.loopGate N` or disable the gate with `set_option ved.mem.loopGate 0` -/
#guard_msgs in
set_option ved.mem.loopGate 1296 in
#ved_u1_mem lgA

-- boundary: limit = tree size (1297): accepted (the same module under another name has the same tree size: its refusal at 1296 is the same text)
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.lgB [proof]: ved_loop_unfold_mem: the loop has 1297 tree nodes, more than the configured limit ved.mem.loopGate (1296); raise it with `set_option ved.mem.loopGate N` or disable the gate with `set_option ved.mem.loopGate 0` -/
#guard_msgs in
set_option ved.mem.loopGate 1296 in
#ved_u1_mem lgB

#guard_msgs (drop info) in
set_option ved.mem.loopGate 1297 in
#ved_u1_mem lgB

-- low h0Budget (1): `[proof]` refusal with the neutral text (the local limit was the smaller one; ambient default 8M)
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.lgA [proof]: ved_h0_budget: the base case (h0) did not finish within min(local ved.mem.h0Budget, remaining ambient budget) = 1 heartbeats (units of maxHeartbeats): the local limit ved.mem.h0Budget = 1 was the smaller one (the remaining ambient budget was not smaller); raise `maxHeartbeats` or `set_option ved.mem.h0Budget N`, or disable the local limit with `set_option ved.mem.h0Budget 0` -/
#guard_msgs in
set_option ved.mem.h0Budget 1 in
#ved_u1_mem lgA

-- sufficient values (a large h0Budget with the tight loopGate), 0 for both, and the defaults: accepted
#guard_msgs (drop info) in
set_option ved.mem.h0Budget 5000000 in
set_option ved.mem.loopGate 1297 in
#ved_u1_mem lgC

#guard_msgs (drop info) in
set_option ved.mem.loopGate 0 in
set_option ved.mem.h0Budget 0 in
#ved_u1_mem lgD

#guard_msgs (drop info) in
#ved_u1_mem lgE

/-- the stored theorem's type is the statement the entry builds over the contract / module constants it registered, and its axioms are
exactly the three standard ones (read by `collectAxioms`) -/
def storedOk (decl : Name) : TermElabM Unit := do
  let (stmt, _) ← Tools.VedU1Contract.specialiseDomain decl
  let thm := decl ++ `ved_mem
  let ti ← getConstInfo thm
  let expected := mkAppN (Lean.mkConst ``Tools.VedMem.MemStmt)
    #[Lean.mkConst (decl ++ `ved_contract), Lean.mkConst (decl ++ `ved_mod), stmt]
  unless ti.type == expected do throwError "{thm}: stored type differs from the statement"
  let axs ← collectAxioms thm
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) && std.all (axs.contains ·) do throwError "{thm}: axioms {axs}"
  logInfo m!"stored type == statement, axioms std3: {decl}"

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.lgB -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``lgB
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.lgC -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``lgC
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.lgD -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``lgD
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.lgE -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``lgE

/-! ### `loopGate 0` does not walk the loop

`loopGateCheck L 0` returns before `treeSizeVal` (a fact of the code: the `gate == 0` early return).  This control only shows the
behaviour on a shared DAG whose tree has 2^64 nodes: gate 0 accepts it, a non-zero limit counts it and refuses.  Because the count is
memoised over the shared DAG, it is quick for a non-zero limit too, so this control alone is NOT evidence that gate 0 skips the walk (a
naive tree traversal of that term would not end; `treeSizeVal` is not naive). -/

/-- info: gate 0: no walk, accepted; gate 10^7: refused -/
#guard_msgs in
run_cmd liftTermElabM do
  let big ← bigDag (mkNatLit 1) 64
  Tools.VedMemLoop.loopGateCheck big 0
  let r ← try Tools.VedMemLoop.loopGateCheck big 10000000; pure "accepted" catch _ => pure "refused"
  unless r.startsWith "refused" do throwError "the gate did not refuse a huge tree"
  logInfo m!"gate 0: no walk, accepted; gate 10^7: {r}"

/-! ### `ved_no_recover`: a failing stage ends the proof, the later stages do not run

`mark_stage` logs `STAGE RAN`.  With error recovery on, the failing `case` is logged and admitted and the next `case` runs (the mark shows);
under `ved_no_recover` the first failure ends the proof at once (no mark). -/

elab "mark_stage" : tactic => logInfo "STAGE RAN"

-- with recovery (the old behaviour): the error is logged and the later stage still runs
/--
error: stage one failed
⊢ True
---
info: STAGE RAN
-/
#guard_msgs in
theorem recoverRuns : True ∧ True := by
  refine ⟨?a, ?b⟩
  case a => fail "stage one failed"
  case b => mark_stage; trivial

-- under `ved_no_recover`: the failing stage ends the proof, `mark_stage` never runs (no `STAGE RAN`)
/--
error: stage one failed
⊢ True
-/
#guard_msgs in
theorem noRecoverStops : True ∧ True := by
  ved_no_recover (
    refine ⟨?a, ?b⟩
    case a => fail "stage one failed"
    case b => mark_stage; trivial)

-- the same for `all_goals`: the first failing goal ends it
/--
error: stage one failed
case a
⊢ True
-/
#guard_msgs in
theorem noRecoverAllGoals : True ∧ True := by
  ved_no_recover (
    refine ⟨?a, ?b⟩
    all_goals (first | fail "stage one failed")
    mark_stage)

/-! ## axioms -/

elab "#ved_axioms " ids:ident* : command => do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for id in ids do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    let axs ← liftCoreM (collectAxioms n)
    unless axs.all (std.contains ·) do throwError "{n}: axioms {axs}"
  logInfo m!"axioms within std3: {ids.size} declarations"

/-- info: axioms within std3: 13 declarations -/
#guard_msgs in
#ved_axioms Tools.VedMemPack.ved_mod_sum sigHyps leaf44 refuse44 leaf54a leaf54b ctrl54 gate54 gateSmall54 gateResetOk54 gateResetFail54 goalGateOk goalGateRefuses

end Tests.Ved.VedMemCloseCheck
