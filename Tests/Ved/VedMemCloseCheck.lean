import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedMemLoop
import Tools.VedMemS94Fix
import Tools.VedMemS94Peel
import Tools.VedMemS94Gen
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

/-! ### the gate guards only the simp fallback (integration of `ved/perf-mem-timeout` and `ved/mem-r033-proof`)

With the option `ved.mem.causalDag` ON, `ved_loop_unfold_mem` runs the DAG walk FIRST (`ved_mem_budget 200000 (ved_causal_dag)`); only
when the walk fails is `ved.mem.loopGate` checked, and then `ved_causal_simp` runs.  So (a) the walk closes `lgA`'s causal side condition
and a low gate never refuses it; (b) on `lgH`, whose memory read address (registered read) is an inner `Signal.loop` (the walk has no rule for a loop and
refuses with its fixed text `ved_causal_dag: loop`, shown by `innerLoopMemDirect` above), a low gate refuses with the loopGate text (the gate
guards the fallback); (c) the same design with gate 0 / a gate equal to the tree size (1469) is accepted through the fallback; (d) with the option
OFF the refusals / acceptances of `lgA`..`lgE` above are unchanged (they run with the option off). -/

def lgF {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData

def lgH {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let idx := LState.idx state
    let busy := LState.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1
    let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
    let innerAddr := Signal.loop fun (st : Signal dom (BitVec 4)) => Signal.register 0#4 (Signal.mux busy (st + 1#4) st)
    let outMemRead := Signal.memory readAddr4 result busy innerAddr
    let done := busy &&& (idx === 15#5)
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  LState.last state

def lgI {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgH start writeEn writeAddr writeData
def lgJ {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgH start writeEn writeAddr writeData

-- (a) option ON, gate 1: the walk closes the causal side condition, the entry accepts
#guard_msgs (drop info) in
set_option ved.mem.causalDag true in
set_option ved.mem.loopGate 1 in
#ved_u1_mem lgF

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.lgF -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``lgF

-- (b) option ON, gate 1, the walk refuses (causalDagBudget 1; since the inner-`Signal.loop` rule the walk closes lgH within its default budget): the loopGate text (tree 1677; the gate is reached only because the walk failed)
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.lgH [proof]: ved_loop_unfold_mem: the loop has 1677 tree nodes, more than the configured limit ved.mem.loopGate (1); raise it with `set_option ved.mem.loopGate N` or disable the gate with `set_option ved.mem.loopGate 0` -/
#guard_msgs in
set_option ved.mem.causalDag true in
set_option ved.mem.causalDagBudget 1 in
set_option ved.mem.loopGate 1 in
#ved_u1_mem lgH

-- (c) option ON, gate 0 / large gate: accepted through the fallback
#guard_msgs (drop info) in
set_option ved.mem.causalDag true in
set_option ved.mem.loopGate 0 in
#ved_u1_mem lgI

#guard_msgs (drop info) in
set_option ved.mem.causalDag true in
set_option ved.mem.loopGate 1469 in
#ved_u1_mem lgJ

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.lgI -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``lgI
/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.lgJ -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``lgJ

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

/-! ## `ved.mem.causalDagBudget`: the local cap of the walk -/

/-- info: causalDagBudget default 200000 -/
#guard_msgs in
run_cmd do
  logInfo m!"causalDagBudget default {Tools.VedMemLoop.ved.mem.causalDagBudget.get (← getOptions)}"

/-- with a tiny cap the walk is refused (the `fail_if_success`: it runs out of its local budget), `ved_causal` then closes the goal by the
`ved_causal_simp` fallback -/
theorem causalBudgetTiny {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.register 0#4 s1)).val (t + 1)
        = (Signal.memory s2 wd we (Signal.register 0#4 s2)).val (t + 1) := by
  set_option ved.mem.causalDag true in
  set_option ved.mem.causalDagBudget 1 in
  (fail_if_success ved_causal_budget (ved_causal_dag))
  set_option ved.mem.causalDag true in
  set_option ved.mem.causalDagBudget 1 in
  ved_causal []

/-- the same goal with the default cap: the walk closes it (the macro without the fallback alternative) -/
theorem causalBudgetDefault {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.register 0#4 s1)).val (t + 1)
        = (Signal.memory s2 wd we (Signal.register 0#4 s2)).val (t + 1) := by
  set_option ved.mem.causalDag true in ved_causal_budget (ved_causal_dag)

/-- 0 = no local cap: the walk closes it under the ambient budget only -/
theorem causalBudgetZero {dom : DomainConfig} (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) :
    ∀ (t : Nat) (s1 s2 : Signal dom (BitVec 4)), (∀ k, k ≤ t → s1.val k = s2.val k) →
      (Signal.memory s1 wd we (Signal.register 0#4 s1)).val (t + 1)
        = (Signal.memory s2 wd we (Signal.register 0#4 s2)).val (t + 1) := by
  set_option ved.mem.causalDag true in set_option ved.mem.causalDagBudget 0 in ved_causal_budget (ved_causal_dag)

/-- info: causal budget controls: axioms within std3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``causalBudgetTiny, ``causalBudgetDefault, ``causalBudgetZero] do
    let axs ← collectAxioms n
    unless axs.all (std.contains ·) do throwError "{n}: axioms {axs}"
  logInfo "causal budget controls: axioms within std3"


/-! ### `ved.mem.h0Dag` (sparkle-ved-mem-h0-dag): the base case h0 closed without simp over the registers' inputs

h0's goals are `st0 c m name = (X.val 0).proj.toNat`, `X` a bundle of `Signal.register init x` (the loop body, huge on R033, sits in the `x`).  With the
option ON `ved_h0_dag_close` closes each by one `isDefEq` (the value at time 0 of a register is its init; the inputs `x` are never visited) as the FIRST
alternative inside `ved_h0_budget`; the old `ved_loop_simp` step is the fallback.  Controls: (1) ON, `h0Budget 10000`: accepted (the old step, controls
above, is refused under that limit, observed: the old step needs between 10000 and 30000 thousand heartbeats on this design, the closer fewer than 5000); (2) OFF, `h0Budget 10000`: the old step's refusal unchanged (the option is
off by default); (3) ON, the closer refused (test seam `h0DagRefuse`): the old step is the fallback: accepted, and under `h0Budget 10000` the old step's
refusal text (the old step ran). -/

def h0K {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData
def h0L {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData
def h0M {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData
def h0N {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := lgA start writeEn writeAddr writeData

-- (1) ON, h0Budget 10000
#guard_msgs (drop info) in
set_option ved.mem.h0Dag true in
set_option ved.mem.h0Budget 10000 in
#ved_u1_mem h0K

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.h0K -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``h0K

-- (2) OFF (explicit), h0Budget 10000: the old step's refusal
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.h0L [proof]: ved_h0_budget: the base case (h0) did not finish within min(local ved.mem.h0Budget, remaining ambient budget) = 10000 heartbeats (units of maxHeartbeats): the local limit ved.mem.h0Budget = 10000 was the smaller one (the remaining ambient budget was not smaller); raise `maxHeartbeats` or `set_option ved.mem.h0Budget N`, or disable the local limit with `set_option ved.mem.h0Budget 0` -/
#guard_msgs in
set_option ved.mem.h0Dag false in
set_option ved.mem.h0Budget 10000 in
#ved_u1_mem h0L

-- (3) ON, the closer refuses: old step is the fallback
run_cmd Tools.VedMemLoop.h0DagRefuse.set true

#guard_msgs (drop info) in
set_option ved.mem.h0Dag true in
set_option ved.mem.h0Budget 0 in
#ved_u1_mem h0M

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.h0M -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``h0M

/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.h0N [proof]: ved_h0_budget: the base case (h0) did not finish within min(local ved.mem.h0Budget, remaining ambient budget) = 10000 heartbeats (units of maxHeartbeats): the local limit ved.mem.h0Budget = 10000 was the smaller one (the remaining ambient budget was not smaller); raise `maxHeartbeats` or `set_option ved.mem.h0Budget N`, or disable the local limit with `set_option ved.mem.h0Budget 0` -/
#guard_msgs in
set_option ved.mem.h0Dag true in
set_option ved.mem.h0Budget 10000 in
#ved_u1_mem h0N

run_cmd Tools.VedMemLoop.h0DagRefuse.set false

/-! ### `ved.mem.hstepDag` (sparkle-ved-mem-hstep): the step case's `obtain` and the hypotheses' simp as targeted rewrites

The step case of the memory loop takes the invariant `hR` apart with `obtain ⟨hreg*, hM*, hL*⟩ := hR` (R033: 95 components, observed 426 s: each
`cases` step abstracts the goal) and then runs `ved_loop_simp [..] at hreg* hM* hL* hD*` (every hypothesis re-simplifies the same loops).  With the
option ON `ved_obtain_dag` takes `hR` apart by projections and `ved_hnorm_dag` simplifies each distinct loop of the hypotheses once; the old tactics
are the fallback.  Controls: (1) ON, packed: accepted (stored type == statement, std3), the log `hstepRan` has `obtain_dag` and `hnorm_dag`;
(2) OFF (explicit): accepted, nothing ran; (3) ON, both refuse (test seam `hstepRefuse`): the old tactics are the fallback, accepted, nothing ran;
(4) ON, unpacked entry: accepted, both ran. -/

declare_signal_state HState
  | fsm  : BitVec 2  := 0#2
  | sub  : BitVec 3  := 0#3
  | last : BitVec 16 := 0#16

def hsA {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) :=
  let state := Signal.loop fun state =>
    let fsm := HState.fsm state
    let sub := HState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn sub4
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux isRow (inputCoeff + 1#16) (HState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  bundle2 (HState.last state) (HState.sub state)

def hsB {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsC {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsD {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let fsm := HState.fsm state
    let sub := HState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn sub4
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux isRow (inputCoeff + 1#16) (HState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  HState.last state

def storedPackedOk (decl : Name) : TermElabM Unit := do
  let (stmt, _) ← Tools.VedU1Contract.specialiseDomain decl
  let thm := decl ++ `ved_mem
  let ti ← getConstInfo thm
  let expected := mkAppN (Lean.mkConst ``Tools.VedMemEntry.MemPackedStmt)
    #[Lean.mkConst (decl ++ `ved_contract), Lean.mkConst (decl ++ `ved_mod), stmt]
  unless ti.type == expected do throwError "{thm}: stored type differs from the statement"
  let axs ← collectAxioms thm
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) && std.all (axs.contains ·) do throwError "{thm}: axioms {axs}"
  logInfo m!"stored type == statement, axioms std3: {decl}"

def guardLogCheck (want : List String) : CommandElabM Unit := do
  let got := (← Tools.VedMemLoop.hstepGuardLog.get).toList
  unless got == want do throwError "guard log: {got}, expected {want}"
  logInfo m!"guard log: {got}"

def hstepRanCheck (want : List String) : CommandElabM Unit := do
  let got := (← Tools.VedMemLoop.hstepRan.get).toList
  unless got == want do throwError "hstepRan: {got}, expected {want}"
  logInfo m!"hstep ran: {got}"

/-- info: hstepDag default false -/
#guard_msgs in
run_cmd do
  logInfo m!"hstepDag default {Tools.VedMemLoop.ved.mem.hstepDag.get (← getOptions)}"

-- (1) ON, packed
run_cmd Tools.VedMemLoop.hstepRan.set #[]
#guard_msgs (drop info) in
set_option ved.mem.hstepDag true in
#ved_u1_mem_packed hsA

/-- info: hstep ran: [obtain_dag, hnorm_dag] -/
#guard_msgs in
run_cmd hstepRanCheck ["obtain_dag", "hnorm_dag"]

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsA -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsA

-- (2) OFF (explicit)
run_cmd Tools.VedMemLoop.hstepRan.set #[]
#guard_msgs (drop info) in
set_option ved.mem.hstepDag false in
#ved_u1_mem_packed hsB

/-- info: hstep ran: [] -/
#guard_msgs in
run_cmd hstepRanCheck []

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsB -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsB

-- (3) ON, both refuse: the old tactics are the fallback
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.hstepRefuse.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepDag true in
#ved_u1_mem_packed hsC
run_cmd Tools.VedMemLoop.hstepRefuse.set false

/-- info: hstep ran: [] -/
#guard_msgs in
run_cmd hstepRanCheck []

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsC -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsC

-- (4) ON, unpacked
run_cmd Tools.VedMemLoop.hstepRan.set #[]
#guard_msgs (drop info) in
set_option ved.mem.hstepDag true in
#ved_u1_mem hsD

/-- info: hstep ran: [obtain_dag, hnorm_dag] -/
#guard_msgs in
run_cmd hstepRanCheck ["obtain_dag", "hnorm_dag"]

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsD -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``hsD


/-! ### `ved.mem.hstepNorm` (sparkle-ved-mem-hstep, second unit): the simps of the step case do not normalise the loops; the goal's loops are made the hypotheses' loops

The goal's `srcOf` loop (the declaration with its lets and name lookups, the state spelled as the product) and the hypotheses' loop (`R`: lets inlined, names
literal, the state `HState`) are the same loop only by definitional unfolding: `ved_hstep_unify` replaces the goal's by the hypotheses'.  The option is
`false` by default; the old script is the fallback. -/

def hsE {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsF {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsG {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsH {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsI {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := hsD start writeEn writeAddr writeData

def hsJ {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsK {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsL {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsM {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsN {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsO {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsP {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsQ {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData
def hsR {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX1 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX2 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX3 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX4 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX5 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX6 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX7 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX8 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def hsX9 {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := hsA start writeEn writeAddr writeData

def noIteCongrHitsCheck (atLeast : Bool) : CommandElabM Unit := do
  let n ← Tools.VedMemS94Fix.noIteCongrHits.get
  if atLeast then
    unless n ≥ 1 do throwError "noIteCongrHits: {n}, expected at least 1"
    logInfo m!"the stage-94 simp ran without ite_congr"
  else
    unless n == 0 do throwError "noIteCongrHits: {n}, expected 0"
    logInfo m!"the stage-94 simp ran with ite_congr"

/-- info: s94NoIteCongr default false -/
#guard_msgs in
run_cmd do
  logInfo m!"s94NoIteCongr default {Tools.VedMemS94Fix.ved.mem.s94NoIteCongr.get (← getOptions)}"

def loopAtomHitsCheck (atLeast : Bool) : CommandElabM Unit := do
  let (g, a, _) ← Tools.VedMemLoop.loopAtomHits.get
  if atLeast then
    unless g ≥ 1 && a ≥ 1 do throwError "loopAtomHits: ({g}, {a}), expected at least one goal with one loop atom"
    logInfo m!"loops were atoms during the stage-94 simp"
  else
    unless g == 0 && a == 0 do throwError "loopAtomHits: ({g}, {a}), expected 0"
    logInfo m!"loops were not made atoms"

/-- info: s94LoopAtom default false -/
#guard_msgs in
run_cmd do
  logInfo m!"s94LoopAtom default {Tools.VedMemLoop.ved.mem.s94LoopAtom.get (← getOptions)}"

def envFreezeHitsCheck (atLeast : Bool) : CommandElabM Unit := do
  let n ← Tools.VedMemLoop.envFreezeHits.get
  if atLeast then
    unless n ≥ 1 do throwError "envFreezeHits: {n}, expected at least one environment function left alone"
    logInfo m!"environment functions not entered"
  else
    unless n == 0 do throwError "envFreezeHits: {n}, expected 0"
    logInfo m!"environment functions entered (freeze not used)"

/-- info: s94EnvFreeze default false -/
#guard_msgs in
run_cmd do
  logInfo m!"s94EnvFreeze default {Tools.VedMemLoop.ved.mem.s94EnvFreeze.get (← getOptions)}"

def hnormStatsCheck : CommandElabM Unit := do
  let (c, _) ← Tools.VedMemLoop.hnormStats.get
  unless c ≥ 1 do throwError "hnormStats: no loop of the goal was made a loop of a hypothesis"
  logInfo m!"hstep_unify converted at least one loop"

/-- info: hstepNorm default false -/
#guard_msgs in
run_cmd do
  logInfo m!"hstepNorm default {Tools.VedMemLoop.ved.mem.hstepNorm.get (← getOptions)}"

def declWidthHitsCheck (atLeast : Bool) : CommandElabM Unit := do
  let n ← Tools.VedMemLoop.declWidthHits.get
  if atLeast then
    unless n ≥ 1 do throwError "declWidthHits: {n}, expected the table to answer at least one `declWidth M \"wire\"`"
    logInfo m!"declWidth answered from the table"
  else
    unless n == 0 do throwError "declWidthHits: {n}, expected 0"
    logInfo m!"declWidth table not used"

def bindStrictHitsCheck (atLeast : Bool) : CommandElabM Unit := do
  let n ← Tools.VedMemLoop.bindStrictHits.get
  if atLeast then
    unless n ≥ 1 do throwError "bindStrictHits: {n}, expected at least one `Option.bind` step in order"
    logInfo m!"Option.bind evaluated in order"
  else
    unless n == 0 do throwError "bindStrictHits: {n}, expected 0"
    logInfo m!"Option.bind in order not used"

-- (5) hstepNorm ON, packed
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.declWidthHits.set 0
run_cmd Tools.VedMemLoop.envFreezeHits.set 0
run_cmd Tools.VedMemLoop.bindStrictHits.set 0
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsE

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: hstep_unify converted at least one loop -/
#guard_msgs in
run_cmd hnormStatsCheck

/-- info: declWidth answered from the table -/
#guard_msgs in
run_cmd declWidthHitsCheck true

/-- info: Option.bind evaluated in order -/
#guard_msgs in
run_cmd bindStrictHitsCheck true

/-- info: environment functions entered (freeze not used) -/
#guard_msgs in
run_cmd envFreezeHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsE -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsE

-- (6) hstepNorm ON and hstepDag ON, unpacked
run_cmd Tools.VedMemLoop.hstepRan.set #[]
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.hstepDag true in
#ved_u1_mem hsI

/-- info: hstep ran: [obtain_dag, norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["obtain_dag", "norm_skip"]

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsI -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``hsI

-- (7) OFF (explicit), hstepDag on: the first unit's tactics, no norm_skip
run_cmd Tools.VedMemLoop.hstepRan.set #[]
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm false in
set_option ved.mem.hstepDag true in
#ved_u1_mem_packed hsF

/-- info: hstep ran: [obtain_dag, hnorm_dag] -/
#guard_msgs in
run_cmd hstepRanCheck ["obtain_dag", "hnorm_dag"]

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsF -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsF

-- (8) ON, the new branch refuses: the old script closes
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.hstepRefuse.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsH
run_cmd Tools.VedMemLoop.hstepRefuse.set false

/-- info: hstep ran: [] -/
#guard_msgs in
run_cmd hstepRanCheck []

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsH -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsH

-- (9) OFF (default), nothing of the new branch
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.declWidthHits.set 0
run_cmd Tools.VedMemLoop.envFreezeHits.set 0
run_cmd Tools.VedMemLoop.bindStrictHits.set 0
#guard_msgs (drop info) in
#ved_u1_mem_packed hsG

/-- info: hstep ran: [] -/
#guard_msgs in
run_cmd hstepRanCheck []

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsG -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsG

/-- info: declWidth table not used -/
#guard_msgs in
run_cmd declWidthHitsCheck false

/-- info: Option.bind in order not used -/
#guard_msgs in
run_cmd bindStrictHitsCheck false

/-- info: environment functions entered (freeze not used) -/
#guard_msgs in
run_cmd envFreezeHitsCheck false


-- (10) ON, the new branch fails LATE (after its tail stages, test seam `hstepFailLate`): the old script closes and the kernel accepts the result.
-- Before `ved_hstep_fallback_reset` the kernel said "unknown constant _private._stdin.0._proof_N": the global proof caches (`proofCache`,
-- `ved_omega_c`'s) kept proofs that mention auxiliary lemmas of the failed branch, which the state restore had removed from the environment.
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.hstepFailLate.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsJ
run_cmd Tools.VedMemLoop.hstepFailLate.set false

/-- info: hstep ran: [] -/
#guard_msgs in
run_cmd hstepRanCheck []

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsJ -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsJ

-- (11) ON, the new branch ends with a HEARTBEAT TIMEOUT (runtime exception, test seam `hstepTimeoutLate`): `first` would let it propagate and the proof
-- would be refused (the strict-row regression of ved-hstep7); `ved_hstep_guard` restores the state and the old script closes.
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.hstepTimeoutLate.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsK
run_cmd Tools.VedMemLoop.hstepTimeoutLate.set false

/-- info: hstep ran: [] -/
#guard_msgs in
run_cmd hstepRanCheck []

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsK -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsK

-- (12) ON, the local cap of the new branch (`ved.mem.hstepNewBudget`, here 1 thousand heartbeats) is exceeded for real: the branch is abandoned, the old script closes.
run_cmd Tools.VedMemLoop.hstepRan.set #[]
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.hstepNewBudget 1 in
#ved_u1_mem_packed hsL

/-- info: hstep ran: [] -/
#guard_msgs in
run_cmd hstepRanCheck []

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsL -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsL

-- (13) ON, the new branch is forced to fail late (heartbeat timeout seam): the old script closes on what is left of the ambient budget (no refund), the stored
-- type is the statement; the guard log says the new branch was abandoned.
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.hstepGuardLog.set #[]
run_cmd Tools.VedMemLoop.hstepTimeoutLate.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsM
run_cmd Tools.VedMemLoop.hstepTimeoutLate.set false

/-- info: hstep ran: [] -/
#guard_msgs in
run_cmd hstepRanCheck []

/-- info: guard log: [new abandoned, old closed] -/
#guard_msgs in
run_cmd guardLogCheck ["new abandoned", "old closed"]

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsM -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsM

/-! ### `ved_hstep_guard` contract (sparkle-ved-mem-hstep, review of 93b85dc2)

The guard wraps the whole step case: a new branch that returns normally but leaves a goal (partial progress; skip) is a failure, state and proof caches are
restored and the old script runs; if the old script cannot close it either, the declaration is refused and the refusal names the step case.  The old script
runs on what is left of the ambient budget (no refund): a fixed small `maxHeartbeats` that the new branch uses part of and new + old would exceed is refused
with the heartbeat error.  With `ved.mem.hstepNorm` off the new branch is not tried at all (guard log empty). -/

-- (14) ON, the new branch makes partial progress and returns with a goal left (test seam `hstepPartial`): NEW is abandoned, OLD closes, stored type exact, std3
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.hstepGuardLog.set #[]
run_cmd Tools.VedMemLoop.hstepPartial.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsN
run_cmd Tools.VedMemLoop.hstepPartial.set false

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: guard log: [new abandoned, old closed] -/
#guard_msgs in
run_cmd guardLogCheck ["new abandoned", "old closed"]

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsN -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsN

-- (15) ON, the new branch leaves a goal and the old script cannot close either (test seam `hstepOldFail`): REFUSED, naming the step case; no theorem added
run_cmd Tools.VedMemLoop.hstepGuardLog.set #[]
run_cmd Tools.VedMemLoop.hstepPartial.set true
run_cmd Tools.VedMemLoop.hstepOldFail.set true
/-- error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.hsO [proof]: errors were logged while elaborating the proof; first: ved_hstep_guard: the step case (hstep) is not closed: the new branch was abandoned (new branch left 1 goal(s) (1 of them new) of the step case) and the old script failed: ved_hstep_fallback: the old script fails (test seam) -/
#guard_msgs in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsO
run_cmd Tools.VedMemLoop.hstepPartial.set false
run_cmd Tools.VedMemLoop.hstepOldFail.set false

/-- info: guard log: [new abandoned, old failed] -/
#guard_msgs in
run_cmd guardLogCheck ["new abandoned", "old failed"]

/-- info: no theorem Tests.Ved.VedMemCloseCheck.hsO.ved_mem -/
#guard_msgs in
run_cmd do
  if (← getEnv).contains (``hsO ++ `ved_mem) then throwError "theorem added"
  logInfo m!"no theorem {``hsO ++ `ved_mem}"

-- (16) default (option off): the new branch is not tried (guard log empty) and the old script closes
run_cmd Tools.VedMemLoop.hstepGuardLog.set #[]
#guard_msgs (drop info) in
#ved_u1_mem_packed hsP

/-- info: guard log: [] -/
#guard_msgs in
run_cmd guardLogCheck []

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsP -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsP

-- (17) a small fixed `maxHeartbeats` (120000, units of 1000 heartbeats; `ved.u1.proofHeartbeats 0`: the entry's 8000000 floor is off): the new branch (forced to fail late) uses part of it (observed 71161), new + old
-- (observed 72535k + 87906k) would exceed it.  No refund: REFUSED with the heartbeat error (the old script is not given the new branch's heartbeats back).
run_cmd Tools.VedMemLoop.hstepGuardLog.set #[]
run_cmd Tools.VedMemLoop.hstepTimeoutLate.set true
/--
error: VED U1 REFUSED Tests.Ved.VedMemCloseCheck.hsQ [proof]: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (120000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option maxHeartbeats 120000 in
set_option ved.u1.proofHeartbeats 0 in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsQ
run_cmd Tools.VedMemLoop.hstepTimeoutLate.set false

/-- info: guard log: [new abandoned, old failed] -/
#guard_msgs in
run_cmd guardLogCheck ["new abandoned", "old failed"]

/-- info: no theorem Tests.Ved.VedMemCloseCheck.hsQ.ved_mem -/
#guard_msgs in
run_cmd do
  if (← getEnv).contains (``hsQ ++ `ved_mem) then throwError "theorem added"
  logInfo m!"no theorem {``hsQ ++ `ved_mem}"

-- (18) the same with room (400000): accepted (new + old within the ambient budget), stored type exact, std3; new <= 120000 < new + old (sanity of (17))
run_cmd Tools.VedMemLoop.hstepGuardLog.set #[]
run_cmd Tools.VedMemLoop.hstepTimeoutLate.set true
#guard_msgs (drop info) in
set_option maxHeartbeats 400000 in
set_option ved.u1.proofHeartbeats 0 in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed hsR
run_cmd Tools.VedMemLoop.hstepTimeoutLate.set false

/-- info: guard log: [new abandoned, old closed] -/
#guard_msgs in
run_cmd guardLogCheck ["new abandoned", "old closed"]

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsR -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsR

/-- info: new < 120000k < new + old -/
#guard_msgs in
run_cmd do
  let (n, o) ← Tools.VedMemLoop.hstepGuardHb.get
  unless n / 1000 < 120000 && 120000 < (n + o) / 1000 do throwError "heartbeats new {n} old {o} do not straddle 120000k"
  logInfo m!"new < 120000k < new + old"


-- (S11) hstepNorm ON and s94EnvFreeze ON, packed: the environment functions are left alone, the proof is accepted, the stored type is exact
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.envFreezeHits.set 0
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
#ved_u1_mem_packed hsX1

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: environment functions not entered -/
#guard_msgs in
run_cmd envFreezeHitsCheck true

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX1 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX1

-- (S12) hstepNorm ON and s94LoopAtom ON, packed: the loops are atoms during the stage-94 simp, the proof is accepted, the stored type is exact
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.loopAtomHits.set (0, 0, 0)
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94LoopAtom true in
#ved_u1_mem_packed hsX2

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: loops were atoms during the stage-94 simp -/
#guard_msgs in
run_cmd loopAtomHitsCheck true

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX2 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX2

-- (S12b) s94LoopAtom OFF (hstepNorm ON): accepted, the loops were not made atoms
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.loopAtomHits.set (0, 0, 0)
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
#ved_u1_mem_packed hsX3

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: loops were not made atoms -/
#guard_msgs in
run_cmd loopAtomHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX3 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX3

-- (S12c) s94LoopAtom ON, the atom step refuses (test seam `loopAtomRefuse`): the plain simp is the fallback, accepted, no atoms
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.loopAtomHits.set (0, 0, 0)
run_cmd Tools.VedMemLoop.loopAtomRefuse.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94LoopAtom true in
#ved_u1_mem_packed hsX4
run_cmd Tools.VedMemLoop.loopAtomRefuse.set false

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: loops were not made atoms -/
#guard_msgs in
run_cmd loopAtomHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX4 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX4

-- (S12d) s94LoopAtom ON, the atom step fails after its inner simp (test seam `loopAtomFailLate`): state restored, plain simp, accepted, no atoms
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemLoop.loopAtomHits.set (0, 0, 0)
run_cmd Tools.VedMemLoop.loopAtomFailLate.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94LoopAtom true in
#ved_u1_mem_packed hsX5
run_cmd Tools.VedMemLoop.loopAtomFailLate.set false

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: loops were not made atoms -/
#guard_msgs in
run_cmd loopAtomHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX5 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX5


-- (S13) hstepNorm ON and s94NoIteCongr ON, packed: the stage-94 simp runs without ite_congr, the proof is accepted, the stored type is exact
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemS94Fix.noIteCongrHits.set 0
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94NoIteCongr true in
#ved_u1_mem_packed hsX6

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: the stage-94 simp ran without ite_congr -/
#guard_msgs in
run_cmd noIteCongrHitsCheck true

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX6 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX6

-- (S13b) s94NoIteCongr OFF (hstepNorm ON): accepted, ite_congr was in use
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemS94Fix.noIteCongrHits.set 0
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
#ved_u1_mem_packed hsX7

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: the stage-94 simp ran with ite_congr -/
#guard_msgs in
run_cmd noIteCongrHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX7 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX7

-- (S13c) s94NoIteCongr ON, the wrapper refuses (test seam `noIteCongrRefuse`): the old simp is the fallback, accepted, counter 0
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemS94Fix.noIteCongrHits.set 0
run_cmd Tools.VedMemS94Fix.noIteCongrRefuse.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94NoIteCongr true in
#ved_u1_mem_packed hsX8
run_cmd Tools.VedMemS94Fix.noIteCongrRefuse.set false

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: the stage-94 simp ran with ite_congr -/
#guard_msgs in
run_cmd noIteCongrHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX8 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX8

-- (S13d) s94NoIteCongr ON, the wrapper fails after its inner simp (test seam `noIteCongrFailLate`): entry put back, old simp, accepted, counter 0
run_cmd Tools.VedMemLoop.hstepRan.set #[]
run_cmd Tools.VedMemS94Fix.noIteCongrHits.set 0
run_cmd Tools.VedMemS94Fix.noIteCongrFailLate.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94NoIteCongr true in
#ved_u1_mem_packed hsX9
run_cmd Tools.VedMemS94Fix.noIteCongrFailLate.set false

/-- info: hstep ran: [norm_skip] -/
#guard_msgs in
run_cmd hstepRanCheck ["norm_skip"]

/-- info: the stage-94 simp ran with ite_congr -/
#guard_msgs in
run_cmd noIteCongrHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.hsX9 -/
#guard_msgs in
run_cmd liftTermElabM <| storedPackedOk ``hsX9

/-! ## ved.mem.s94PeelDag (sparkle-ved-mem-s94, eleventh unit)

After the memory loop's case split the memory array of a goal is a DAG of nested updates of all the memories; `ved_mem_peel` walks it as a
tree (`3 * 2^27 - 2` steps per goal on R033).  With the option ON the peel first projects the array on the goal's memory name (an update of
another memory is dropped, shared nodes are visited once, `Tools/VedMemS94Peel.lean`) and closes the chain of the memory's own writes; the
old peel is the fallback.  Controls: (1) the tactic on a small array (an `if` of another memory over a shared update of that memory
under the own write): closes it, the three side goals of the write are the hypotheses; (2) the same with a wrong initial image: refused;
(3) a memory name that is not a literal: refused; (4) a loop with two memories (`gateFsm`: the data of the second is read from the
first, the first is written at `writeAddr`, the second at the counter, so the two write the same address in one cycle when
`writeAddr = idx[3:0]`; the case split leaves 18 goals; the script of `ved.mem.hstepNorm`, the only one that has the shared `peelAlt`) ON: accepted, stored type exact, std3, counter >= 1; (5) OFF: accepted,
counter 0; (6) ON, the tactic refuses (test seam `peelDagRefuse`): the old peel is the fallback, accepted, counter 0; (7) ON, the tactic
fails after its work (test seam `peelDagFailLate`): the state is restored, old peel, accepted, counter 0. -/

/-- info: s94PeelDag default false -/
#guard_msgs in
run_cmd do
  logInfo m!"s94PeelDag default {Tools.VedMemS94Peel.ved.mem.s94PeelDag.get (← getOptions)}"

def peelDagHitsCheck (atLeast : Bool) : CommandElabM Unit := do
  let n ← Tools.VedMemS94Peel.peelDagHits.get
  if atLeast then
    unless n ≥ 1 do throwError "peelDagHits: {n}, expected at least 1"
    logInfo m!"the DAG peel ran"
  else
    unless n == 0 do throwError "peelDagHits: {n}, expected 0"
    logInfo m!"the DAG peel did not run"

-- (P1) the tactic on a small DAG: the update of "mb" under an `if`, over the own write of "ma", over a shared update of "mb"
run_cmd Tools.VedMemS94Peel.peelDagHits.set 0
open Tools.VedMem Sparkle.IR.Semantics in
example {dom : DomainConfig} (wa : Signal dom (BitVec 4)) (wd : Signal dom (BitVec 16)) (we : Signal dom Bool)
    (n : Nat) (mems : MEnv) (c1 c2 av dv : Nat)
    (hM : MemInv "ma" (fun _ => 0#16) wa wd we n mems)
    (hen : we.val n = true) (hav : av = (wa.val n).toNat) (hdv : dv = (wd.val n).toNat) :
    MemInv "ma" (fun _ => 0#16) wa wd we (n + 1)
      (if c1 = 0 then
        (fun nm i => if nm = "ma" ∧ i = av then dv else
          (if c2 = 0 then mems else fun nm i => if nm = "mb" ∧ i = 3 then 5 else mems nm i) nm i)
      else
        (fun nm i => if nm = "mb" ∧ i = 7 then 1 else
          (fun nm i => if nm = "ma" ∧ i = av then dv else
            (if c2 = 0 then mems else fun nm i => if nm = "mb" ∧ i = 3 then 5 else mems nm i) nm i) nm i)) := by
  ved_mem_peel_dag hM
  all_goals assumption

/-- info: the DAG peel ran -/
#guard_msgs in
run_cmd peelDagHitsCheck true

open Tools.VedMem Sparkle.IR.Semantics in
-- (P2) a wrong initial image: the invariant hypothesis is about the all-zero image, the goal about `7`: refused
/-- error: ved_mem_peel_dag: no invariant hypothesis matches the memory array (name, initial contents, ports and cycle must agree) -/
#guard_msgs in
example {dom : DomainConfig} (wa : Signal dom (BitVec 4)) (wd : Signal dom (BitVec 16)) (we : Signal dom Bool)
    (n : Nat) (mems : MEnv) (c2 av dv : Nat)
    (hM : MemInv "ma" (fun _ => 0#16) wa wd we n mems)
    (hen : we.val n = true) (hav : av = (wa.val n).toNat) (hdv : dv = (wd.val n).toNat) :
    MemInv "ma" (fun _ => 7#16) wa wd we (n + 1)
      (fun nm i => if nm = "ma" ∧ i = av then dv else
          (if c2 = 0 then mems else fun nm i => if nm = "mb" ∧ i = 3 then 5 else mems nm i) nm i) := by
  ved_mem_peel_dag hM
  all_goals assumption

open Tools.VedMem Sparkle.IR.Semantics in
-- (P3) a memory name that is not a literal: refused
/-- error: ved_mem_peel_dag: the memory name is not a string literal -/
#guard_msgs in
example {dom : DomainConfig} (wa : Signal dom (BitVec 4)) (wd : Signal dom (BitVec 16)) (we : Signal dom Bool)
    (n : Nat) (mems : MEnv) (nm0 : String) (av dv : Nat)
    (hM : MemInv nm0 (fun _ => 0#16) wa wd we n mems)
    (hen : we.val n = true) (hav : av = (wa.val n).toNat) (hdv : dv = (wd.val n).toNat) :
    MemInv nm0 (fun _ => 0#16) wa wd we (n + 1)
      (fun nm i => if nm = nm0 ∧ i = av then dv else mems nm i) := by
  ved_mem_peel_dag hM
  all_goals assumption

def peelDagGateA {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData
def peelDagGateB {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData
def peelDagGateC {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData
def peelDagGateD {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData

-- (P4) ON, two memories (the same address can be written by both in one cycle): accepted, stored type exact, std3, counter >= 1
run_cmd Tools.VedMemS94Peel.peelDagHits.set 0
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
#ved_u1_mem peelDagGateA

/-- info: the DAG peel ran -/
#guard_msgs in
run_cmd peelDagHitsCheck true

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.peelDagGateA -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``peelDagGateA

-- (P5) OFF: accepted, the DAG peel did not run
run_cmd Tools.VedMemS94Peel.peelDagHits.set 0
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
#ved_u1_mem peelDagGateB

/-- info: the DAG peel did not run -/
#guard_msgs in
run_cmd peelDagHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.peelDagGateB -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``peelDagGateB

-- (P6) ON, the tactic refuses (test seam): the old peel is the fallback, accepted, counter 0
run_cmd Tools.VedMemS94Peel.peelDagHits.set 0
run_cmd Tools.VedMemS94Peel.peelDagRefuse.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
#ved_u1_mem peelDagGateC
run_cmd Tools.VedMemS94Peel.peelDagRefuse.set false

/-- info: the DAG peel did not run -/
#guard_msgs in
run_cmd peelDagHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.peelDagGateC -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``peelDagGateC

-- (P7) ON, the tactic fails after its work (test seam): state restored, old peel, accepted, counter 0
run_cmd Tools.VedMemS94Peel.peelDagHits.set 0
run_cmd Tools.VedMemS94Peel.peelDagFailLate.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
#ved_u1_mem peelDagGateD
run_cmd Tools.VedMemS94Peel.peelDagFailLate.set false

/-- info: the DAG peel did not run -/
#guard_msgs in
run_cmd peelDagHitsCheck false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.peelDagGateD -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``peelDagGateD

/-! ## `ved.mem.s94GenOnce` (sparkle-ved-mem-s94, fourteenth unit)

The loop states are generalised once on the shared goal (stamp 95, `ved_loop_gen_once`), without `Bool` case splits; the loop values that the stage-99 simp creates later are
replaced by the tuple of the kept equation (`ved_loop_gen_resid`); the old per-goal `ved_loop_gen_mem` is the fallback. -/

declare_signal_state GState
  | fsm  : BitVec 2  := 0#2
  | idx  : BitVec 5  := 0#5
  | flag : Bool := false
  | last : BitVec 16 := 0#16

/-- a loop with a `Bool` state component (the write enable of the first memory depends on it) -/
def genBool {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let fsm := GState.fsm state
    let idx := GState.idx state
    let flag := GState.flag state
    let isProcess := fsm === (1#2 : Signal dom _)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let enable := Signal.mux flag isProcess (Signal.pure false)
    let outMemRead := Signal.memory readAddr4 inputCoeff enable (Signal.pure 0#4)
    let fsmNext := Signal.mux start (Signal.pure 1#2) (Signal.mux (idx === (15#5 : Signal dom _)) (Signal.pure 0#2) fsm)
    let idxNext := Signal.mux isProcess (idx + 1#5) (Signal.pure 0#5)
    let flagNext := Signal.mux start (Signal.pure true) (Signal.mux isProcess (Signal.pure false) flag)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#5 idxNext, Signal.register false flagNext, Signal.register 0#16 outMemRead]
  GState.last state

def genOnceA {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData
def genOnceB {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData
def genOnceC {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData
def genOnceD {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := gateFsm start writeEn writeAddr writeData
def genOnceE {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := genBool start writeEn writeAddr writeData
def genOnceF {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := genBool start writeEn writeAddr writeData

/-- (once, clean, left) must be as given: the tactic ran / the residual step found nothing left / it ran the old tactic -/
def genOnceCheck (once : Bool) (clean : Bool) (left : Bool) : CommandElabM Unit := do
  let a ← Tools.VedMemS94Gen.genOnceHits.get
  let c ← Tools.VedMemS94Gen.genResidClean.get
  let l ← Tools.VedMemS94Gen.genResidLeft.get
  unless (a ≥ 1) == once && (c ≥ 1) == clean && (l ≥ 1) == left do throwError "genOnce counters: once {a} clean {c} left {l}"
  logInfo m!"genOnce counters ok: once={once} clean={clean} left={left}"
  Tools.VedMemS94Gen.genOnceHits.set 0
  Tools.VedMemS94Gen.genResidClean.set 0
  Tools.VedMemS94Gen.genResidLeft.set 0

run_cmd Tools.VedMemS94Gen.genOnceHits.set 0
run_cmd Tools.VedMemS94Gen.genResidClean.set 0
run_cmd Tools.VedMemS94Gen.genResidLeft.set 0

-- (G1) ON, two memories: accepted, stored type exact, std3, the tactic ran (counter >= 1), nothing left for the old tactic
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
set_option ved.mem.s94GenOnce true in
#ved_u1_mem genOnceA

/-- info: genOnce counters ok: once=true clean=true left=false -/
#guard_msgs in
run_cmd genOnceCheck true true false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.genOnceA -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``genOnceA

-- (G2) OFF: accepted, counters 0 (the per-goal tactic only)
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
#ved_u1_mem genOnceB

/-- info: genOnce counters ok: once=false clean=false left=false -/
#guard_msgs in
run_cmd genOnceCheck false false false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.genOnceB -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``genOnceB

-- (G3) ON, the tactic refuses (test seam): the old per-goal tactic is the fallback, accepted
run_cmd Tools.VedMemS94Gen.genOnceRefuse.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
set_option ved.mem.s94GenOnce true in
#ved_u1_mem genOnceC
run_cmd Tools.VedMemS94Gen.genOnceRefuse.set false

/-- info: genOnce counters ok: once=false clean=false left=true -/
#guard_msgs in
run_cmd genOnceCheck false false true

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.genOnceC -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``genOnceC

-- (G4) ON, the tactic fails after its work (test seam): state restored, old per-goal tactic, accepted
run_cmd Tools.VedMemS94Gen.genOnceFailLate.set true
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
set_option ved.mem.s94GenOnce true in
#ved_u1_mem genOnceD
run_cmd Tools.VedMemS94Gen.genOnceFailLate.set false

/-- info: genOnce counters ok: once=false clean=false left=true -/
#guard_msgs in
run_cmd genOnceCheck false false true

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.genOnceD -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``genOnceD

-- (G5) ON, a loop with a `Bool` state component (no Bool split anywhere): accepted
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
set_option ved.mem.s94GenOnce true in
#ved_u1_mem genOnceE

/-- info: genOnce counters ok: once=true clean=true left=false -/
#guard_msgs in
run_cmd genOnceCheck true true false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.genOnceE -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``genOnceE

-- (G6) OFF on the same Bool loop: accepted, counters 0
#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
set_option ved.mem.s94EnvFreeze true in
set_option ved.mem.s94PeelDag true in
#ved_u1_mem genOnceF

/-- info: genOnce counters ok: once=false clean=false left=false -/
#guard_msgs in
run_cmd genOnceCheck false false false

/-- info: stored type == statement, axioms std3: Tests.Ved.VedMemCloseCheck.genOnceF -/
#guard_msgs in
run_cmd liftTermElabM <| storedOk ``genOnceF

end Tests.Ved.VedMemCloseCheck
