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
set_option ved.mem.causalDagMaskCheck true

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

def gateFsmC {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData

-- the case split leaves 18 goals; limit 7: refused at `[proof]`, the refusal names the configured value 7
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.gateFsm [proof]: errors were logged while elaborating the proof; first: ved_goal_gate: 18 goals after the case split exceed the configured limit ved.mem.goalGate (7); raise it with `set_option ved.mem.goalGate N` or disable the gate with `set_option ved.mem.goalGate 0` -/
#guard_msgs in
set_option ved.mem.goalGate 7 in
#ved_u1_mem gateFsm

-- limit 17 (one below the goal count): still refused, value 17
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.gateFsm [proof]: errors were logged while elaborating the proof; first: ved_goal_gate: 18 goals after the case split exceed the configured limit ved.mem.goalGate (17); raise it with `set_option ved.mem.goalGate N` or disable the gate with `set_option ved.mem.goalGate 0` -/
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


/-! ## ved_causal_dag (sparkle-ved-mem-r033-proof)

The causal side condition of the strong fixpoint equation (`∀ t s1 s2, (∀ k ≤ t, s1.val k = s2.val k) → (F s1).val (t+1) =
(F s2).val (t+1)`) closed by the lock-step walk `ved_causal_dag` (option `ved.mem.causalDag`, default off).  The controls
present, exactly:

* `causalDagMem` / `causalDagMemMacro`: a memory written and read through the loop state; the walk closes it (directly, and as the
  first alternative of `ved_causal []`), axioms within std3.
* `causalDagOff`: option off, `ved_causal_dag` refuses at once with its fixed text; `causalSimpMem`: option off, `ved_causal []`
  runs the simp path and closes the same goal.
* `innerLoopMem`, `innerLoopMemDirect`: option on, a memory whose read address is an inner `Signal.loop` driven by the state.  The
  walk closes it (`ved_causal_dag` alone; `innerLoopMem` through `ved_causal []`): stored type `==` the statement, axioms within
  std3.  The inner loop is a `Tools.VedMemNest.loop_val_congr_le` step whose two premises are walked (under `a b`, and under
  `t' (t' < k) a b hab`), no whole-goal simp.  `nestedLoopMem` (two nested inner loops) and `loopReadsMem` (an inner loop whose
  body reads a `memState` of its own state) are closed by the walk too.
* `ignoredRead` (REAL FALLBACK): a loop read at cycle `t+1` whose body adds `s1.map` of a function that is constant by a Boolean
  identity.  The walk reaches `s1.val (t'+1)` against `s2.val (t'+1)` for `t' < t+1`, `h` gives cycles `≤ t` only, the
  bound is not proved and the walk refuses (`ignoredReadDirect`: the fixed text `ved_causal_dag: bound not proved`);
  `ved_causal []` closes the same goal through the simp path (`ved_causal_simp`, `ved_loop_congr`).
* `ved_walk_fallback` (STATE RESTORATION): after the failed walk the goal list, the metavariable context (counter, declarations,
  assignments) and the heartbeat clock/limit that the fallback sees are those from before the walk; the fingerprint check itself
  is shown to see a change (`ved_fp_changes`).
* CACHE SCOPE: the cache of the walk is scoped per binder (`DagCache.scope`: inner scopes read the outer entries, never write into
  them).  `dagCacheScope` checks the cache itself; `sharedPair` is a memory whose two signals are constant `⟨fun _ => s1.val 0⟩`,
  so the pair `s1.val 0` / `s2.val 0` occurs outside the `memState` binders and again under them: the walk closes it and the
  kernel accepts the result (axioms std3).  (The unscoped cache was not run on this example: that a stale entry would give an
  ill-typed proof is not demonstrated here.)
-/

/-- the causal side condition of a registered-read memory written at the state's address -/
theorem causalDagMem {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.register 0#4 s1)).val (t + 1)
        = (Signal.memory s2 wd we (Signal.register 0#4 s2)).val (t + 1) := by
  set_option ved.mem.causalDag true in ved_causal_dag

/-- info: causalDagMem: axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let axs ← collectAxioms ``causalDagMem
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) do throwError "causalDagMem: axioms {axs}"
  logInfo "causalDagMem: axioms within std3"

/-- the same goal through `ved_causal` with the option on: the walk closes it -/
theorem causalDagMemMacro {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.register 0#4 s1)).val (t + 1)
        = (Signal.memory s2 wd we (Signal.register 0#4 s2)).val (t + 1) := by
  set_option ved.mem.causalDag true in ved_causal []

-- control: with the option off the tactic refuses at once
/-- error: ved_causal_dag: option ved.mem.causalDag is off -/
#guard_msgs in
theorem causalDagOff {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.register 0#4 s1)).val (t + 1)
        = (Signal.memory s2 wd we (Signal.register 0#4 s2)).val (t + 1) := by
  ved_causal_dag

/-- control: option off, `ved_causal` runs the simp path and closes the same goal -/
theorem causalSimpMem {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.register 0#4 s1)).val (t + 1)
        = (Signal.memory s2 wd we (Signal.register 0#4 s2)).val (t + 1) := by
  ved_causal []


/-! ### a real fallback: an inner `Signal.loop` the walk does not know -/

set_option hygiene false in
local macro "innerLoopMemStmt" : term => `(∀ {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool)
    (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.loop fun (st : Signal dom (BitVec 4)) =>
          Signal.register 0#4 (Signal.mux (s1.map (fun x => x.getLsbD 0)) (st + 1#4) st))).val (t + 1)
        = (Signal.memory s2 wd we (Signal.loop fun (st : Signal dom (BitVec 4)) =>
          Signal.register 0#4 (Signal.mux (s2.map (fun x => x.getLsbD 0)) (st + 1#4) st))).val (t + 1))

-- the walk alone closes it (`loop_val_congr_le`, premises walked)
theorem innerLoopMemDirect : innerLoopMemStmt := by
  intro dom wd we
  set_option ved.mem.causalDag true in ved_causal_dag

/-- option on: the walk closes it as the first alternative of `ved_causal` -/
theorem innerLoopMem : innerLoopMemStmt := by
  intro dom wd we
  set_option ved.mem.causalDag true in ved_causal []

/-- info: innerLoopMem: type exact, axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let ty ← instantiateMVars (← Term.elabType (← `(innerLoopMemStmt)))
  unless (← getConstInfo ``innerLoopMem).type == ty do throwError "innerLoopMem: stored type differs from the statement"
  let axs ← collectAxioms ``innerLoopMem
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) do throwError "innerLoopMem: axioms {axs}"
  logInfo "innerLoopMem: type exact, axioms within std3"

/-! ### two nested inner loops, an inner loop reading a `memState` -/

set_option hygiene false in
local macro "nestedLoopMemStmt" : term => `(∀ {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool)
    (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.loop fun (st : Signal dom (BitVec 4)) =>
          Signal.register 0#4 (Signal.mux (s1.map (fun x => x.getLsbD 0))
            (Signal.loop fun (st2 : Signal dom (BitVec 4)) => Signal.register 0#4 (st2 + st)) st))).val (t + 1)
        = (Signal.memory s2 wd we (Signal.loop fun (st : Signal dom (BitVec 4)) =>
          Signal.register 0#4 (Signal.mux (s2.map (fun x => x.getLsbD 0))
            (Signal.loop fun (st2 : Signal dom (BitVec 4)) => Signal.register 0#4 (st2 + st)) st))).val (t + 1))

/-- two nested inner loops (the inner one driven by the state of the middle one, which is driven by the outer state): closed by the walk -/
theorem nestedLoopMem : nestedLoopMemStmt := by
  intro dom wd we
  set_option ved.mem.causalDag true in ved_causal_dag

set_option hygiene false in
local macro "loopReadsMemStmt" : term => `(∀ {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool)
    (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.loop fun (st : Signal dom (BitVec 4)) =>
          Signal.register 0#4 (Signal.mux (s1.map (fun x => x.getLsbD 0))
            ((Signal.memory st (Signal.register 0#8 wd) we (Signal.register 0#4 st)).map (fun (x : BitVec 8) => x.extractLsb' 0 4)) st))).val (t + 1)
        = (Signal.memory s2 wd we (Signal.loop fun (st : Signal dom (BitVec 4)) =>
          Signal.register 0#4 (Signal.mux (s2.map (fun x => x.getLsbD 0))
            ((Signal.memory st (Signal.register 0#8 wd) we (Signal.register 0#4 st)).map (fun (x : BitVec 8) => x.extractLsb' 0 4)) st))).val (t + 1))

/-- an inner loop whose body reads a `memState` of the loop's own state: closed by the walk -/
theorem loopReadsMem : loopReadsMemStmt := by
  intro dom wd we
  set_option ved.mem.causalDag true in ved_causal_dag

/-! ### the unsupported shape that remains: a read of the outer signal the walk cannot bound (REAL FALLBACK)

The loop (read at cycle `t+1`, not through a memory) adds `s1.map (fun x => if (x.getLsbD 0 && !x.getLsbD 0) = true then 1#4
else 0#4)`, a function that is constant `0#4` by a Boolean identity.  The walk compares the two sides argument by argument and
reaches `s1.val (t'+1)` against `s2.val (t'+1)` for the inner time `t' < t+1`: `h` gives only cycles `≤ t`, so for `t' = t` the
bound is not proved and the walk refuses (it does not know the identity).  The simp path (`ved_causal_simp`) rewrites it away first and closes the goal. -/

set_option hygiene false in
local macro "ignoredReadStmt" : term => `(∀ {dom : DomainConfig}
    (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.loop fun (st : Signal dom (BitVec 4)) =>
          Signal.register 0#4 st + s1.map (fun x => if (x.getLsbD 0 && !x.getLsbD 0) = true then 1#4 else 0#4)).val (t + 1)
        = (Signal.loop fun (st : Signal dom (BitVec 4)) =>
          Signal.register 0#4 st + s2.map (fun x => if (x.getLsbD 0 && !x.getLsbD 0) = true then 1#4 else 0#4)).val (t + 1))

/-- error: ved_causal_dag: bound not proved -/
#guard_msgs in
theorem ignoredReadDirect : ignoredReadStmt := by
  intro dom
  set_option ved.mem.causalDag true in ved_causal_dag

/-- option on: the walk is tried, refuses, and the simp path closes the goal -/
theorem ignoredRead : ignoredReadStmt := by
  intro dom
  set_option ved.mem.causalDag true in ved_causal []

/-! ### state after a failed walk -/

/-- a fingerprint of the tactic state: open goals, metavariable counter / declarations / assignments, heartbeat clock and limit -/
def stateFp : TacticM (List Nat) := do
  let m ← getMCtx
  let c ← readThe Core.Context
  return [(← getGoals).length, (← getGoals).foldl (fun a g => a * 31 + g.name.hash.toNat % 1000003) 7, m.mvarCounter, m.decls.toList.length,
    m.eAssignment.toList.length, m.dAssignment.toList.length, c.maxHeartbeats, c.initHeartbeats]

/-- `ved_fp_is a b ..`: the state has the fingerprint `a b ..` -/
elab "ved_fp_is " ns:num* : tactic => do
  let fp ← stateFp
  unless fp == ns.toList.map (·.getNat) do throwError "ved_fp_is: the state differs: {fp}"

/-- `ved_walk_fallback n w fb`: `first | ved_mem_budget n w | (the state is the one from before `w`; fb)` -/
elab "ved_walk_fallback " n:num w:tactic " || " fb:tactic : tactic => do
  let ns := (← stateFp).toArray.map fun x => Syntax.mkNumLit (toString x)
  evalTactic (← `(tactic| first | (ved_mem_budget $n $w) | (ved_fp_is $ns* ; $fb)))

/-- control of the check: `ved_fp_changes tac` fails when `tac` leaves the fingerprint as it was -/
elab "ved_fp_changes " t:tactic : tactic => do
  let fp0 ← stateFp
  evalTactic t
  if (← stateFp) == fp0 then throwError "ved_fp_changes: the state did not change"

example : ∀ n : Nat, n = n := by ved_fp_changes (intro n); rfl

/-- the walk makes progress (`intro`, `rcases`) before it fails at the loop; the fallback sees the state from before it, and the
simp path then closes the goal (the whole state is the one `ved_causal []` itself relies on) -/
theorem innerLoopMemRestored : ignoredReadStmt := by
  intro dom
  set_option ved.mem.causalDag true in
  ved_walk_fallback 200000 (ved_causal_dag) || (ved_causal_simp [])

/-! ### the cache of the walk is scoped per binder -/

/-- info: dagCacheScope ok -/
#guard_msgs in
run_cmd liftTermElabM do
  let c ← Tools.VedMemLoop.DagCache.new
  let k : Expr × Expr := (mkNatLit 1, mkNatLit 2)
  let k' : Expr × Expr := (mkNatLit 3, mkNatLit 4)
  c.insert k (mkNatLit 10)
  let inner ← c.scope
  unless (← inner.find? k) == some (mkNatLit 10) do throwError "inner scope does not read the outer entry"
  inner.insert k' (mkNatLit 11)
  unless (← inner.find? k') == some (mkNatLit 11) do throwError "inner scope lost its own entry"
  unless (← c.find? k').isNone do throwError "an inner entry reached the outer scope"
  let sibling ← c.scope
  unless (← sibling.find? k').isNone do throwError "an inner entry reached a sibling scope"
  logInfo "dagCacheScope ok"

/-- the same subterm pair (`s1.val 0` against `s2.val 0`, the constant signals) outside the `memState` binders and under them -/
theorem sharedPair {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory (⟨fun _ => s1.val 0⟩ : Signal dom (BitVec 4)) wd we (⟨fun _ => s1.val 0⟩ : Signal dom (BitVec 4))).val (t + 1)
        = (Signal.memory (⟨fun _ => s2.val 0⟩ : Signal dom (BitVec 4)) wd we (⟨fun _ => s2.val 0⟩ : Signal dom (BitVec 4))).val (t + 1) := by
  set_option ved.mem.causalDag true in ved_causal_dag

/-! ### scope levels: a proof is stored in the outermost scope whose binders it does not mention

`dagCacheLevels` (the cache itself, with real binder variables): a proof that mentions no binder of the scope `s1` it was found in is
stored in the root and a sibling scope `s2` reads it, and it type-checks in `s2`'s context; a proof that mentions the binder `x`
of `s1` stays in `s1` (a sibling does not read it, and checking it where `x` is not in scope fails: the control is a real one).
-/

/-- info: dagCacheLevels ok -/
#guard_msgs in
open Tools.VedMemLoop in
run_cmd liftTermElabM do
  dgHits.set {}
  let c ← DagCache.new
  let s1 ← c.scope
  let s2 ← c.scope
  let kFree : Expr × Expr := (mkNatLit 1, mkNatLit 2)
  let kBind : Expr × Expr := (mkNatLit 3, mkNatLit 4)
  let pFree := mkApp (mkConst ``Nat.le_refl) (mkNatLit 5)
  let sh := c.sh
  -- the proof that mentions the binder, built under the binder of `s1`
  let pBind ← withLocalDeclD `x (mkConst ``Nat) fun x => do
    s1.reg #[x]
    let p := mkApp (mkConst ``Nat.le_refl) x
    let m ← termMask sh p
    unless m == 2 do throwError "mask of a proof of a depth-1 variable is {m}, not 2"
    s1.store kBind p m
    unless (← s1.find? kBind) == some p do throwError "the own scope lost the binder proof"
    unless (← s2.find? kBind).isNone do throwError "a binder proof reached a sibling"
    unless (← c.find? kBind).isNone do throwError "a binder proof reached the root"
    -- the control is real: the proof does not check where `x` is not in scope
    return p
  let bad ← try Meta.check pBind; pure false catch _ => pure true
  unless bad do throwError "the binder proof checks outside its scope (control void)"
  -- a closed proof built in `s1` goes to the root and is served to the sibling
  let mFree ← termMask sh pFree
  unless mFree == 0 do throwError "mask of a closed proof is {mFree}"
  s1.store kFree pFree mFree
  let some (e, found) ← s2.findE? kFree | throwError "the sibling does not read the promoted proof"
  unless found.depth == 0 do throwError "the promoted proof is not in the root"
  unless e.by_ == s1.id do throwError "wrong inserter"
  Meta.check e.proof
  let h ← Tools.VedMemLoop.dgHits.get
  unless h.promoted == 1 do throwError "promoted counter {h.promoted}"
  logInfo "dagCacheLevels ok"

elab "ved_hits_reset" : tactic => Tools.VedMemLoop.dgHits.set {}
elab "ved_hits_show " tag:str : tactic => do
  let h ← Tools.VedMemLoop.dgHits.get
  logInfo m!"{tag.getString} own={h.own} ancestor={h.ancestor} shared={h.shared} inserts={h.inserts} promoted={h.promoted}"
elab "ved_hits_expect_shared " n:num : tactic => do
  let h ← Tools.VedMemLoop.dgHits.get
  unless h.shared ≥ n.getNat do throwError "sibling-shared hits {h.shared} < {n.getNat} (promoted {h.promoted})"
elab "ved_hits_expect_no_shared" : tactic => do
  let h ← Tools.VedMemLoop.dgHits.get
  unless h.shared == 0 do throwError "sibling-shared hits {h.shared}, expected none"

set_option Elab.async false in
/-- the same pair under the `memState` binders of the address and of the data side (siblings): the walk with the mask check on
(every stored proof is traversed and its mask compared with the composed one); the pair is promoted to the root and the second
side is served by it (a sibling-shared hit); the kernel accepts the theorem -/
theorem sharedPairShared {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory (⟨fun _ => s1.val 0⟩ : Signal dom (BitVec 4)) wd we (⟨fun _ => s1.val 0⟩ : Signal dom (BitVec 4))).val (t + 1)
        = (Signal.memory (⟨fun _ => s2.val 0⟩ : Signal dom (BitVec 4)) wd we (⟨fun _ => s2.val 0⟩ : Signal dom (BitVec 4))).val (t + 1) := by
  ved_hits_reset
  set_option ved.mem.causalDag true in set_option ved.mem.causalDagMaskCheck true in ved_causal_dag
  ved_hits_show "sharedPairShared"
  ved_hits_expect_shared 1

set_option Elab.async false in
/-- end to end, proofs that DO use binder variables: the three sibling sides of this memory read the state signal (`s1.val j` under the
binder `j`, proved by `h j` with the bound from `hj`).  Those proofs mention `j`/`hj`: none is promoted and none is served to a sibling (promoted 0, shared 0; the mask check, which compares
every stored proof's traversed mask with the composed one, would fail otherwise; a promoted proof that escaped its binders would fail the
kernel too); whatever closed pairs the walk shares are served; the theorem is kernel-accepted with its exact statement -/
theorem siblingBinderProofs {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.register 0#4 s1)).val (t + 1)
        = (Signal.memory s2 wd we (Signal.register 0#4 s2)).val (t + 1) := by
  ved_hits_reset
  set_option ved.mem.causalDag true in set_option ved.mem.causalDagMaskCheck true in ved_causal_dag
  ved_hits_show "siblingBinderProofs"
  ved_hits_expect_no_shared

/-- info: causal controls: axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``innerLoopMemRestored, ``ignoredRead, ``nestedLoopMem, ``loopReadsMem, ``innerLoopMemDirect, ``sharedPair, ``sharedPairShared, ``siblingBinderProofs, ``causalDagMemMacro, ``causalSimpMem] do
    let axs ← collectAxioms n
    unless axs.all (std.contains ·) do throwError "{n}: axioms {axs}"
  logInfo "causal controls: axioms within std3"

end Tests.Ved.VedMemCloseCheck
