import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedMemLoop
import Tools.VedMemS94Gen
import Tools.VedMemS94Local

/-!
# Controls for the s94r pieces of the local route (sparkle-ved-mem-s94)

* `ved_loop_canon`: two spellings of one loop (here: `id` around the body, `isDefEq` at default transparency) are made one loop (the goal becomes `x = x`, the stored
  proof is checked by the kernel: `theorem`), two different loops are left alone (the tactic fails and the goal is unchanged), the test seam refuses, a late failure
  restores the goal.
* `ved_addr_eq_local2`: an address built by `BitVec` `+ * ++ ite` closes against its `ofNat` / `toNat` spelling; a wrong constant is refused.
* `ved_mem_addr_l` with `memCanon`: two `memState` atoms whose write ports are two spellings of one signal and whose addresses are two spellings of one address are one atom afterwards
  (`rfl` closes), with the addresses really different the atoms stay apart.
-/

namespace Tests.Ved.VedMemLocalCheck

open Lean Elab Command Term Meta Tactic
open Sparkle.Core.Domain Sparkle.Core.Signal

set_option linter.unusedVariables false

/-! ## ved_loop_canon -/

theorem canon_ok {dom : DomainConfig} (s : Nat) :
    ((Signal.loop (dom := dom) fun (st : Signal dom (BitVec 3)) => Signal.register 0#3 (st + 1#3)).val s) =
    ((Signal.loop (dom := dom) fun (st : Signal dom (BitVec 3)) => id (Signal.register 0#3 (st + 1#3))).val s) := by
  ved_loop_canon
  rfl

/-- info: loop_canon controls: same loop made one, other loop refused, seam refuses, late failure restores -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let good ← `(∀ (s : Nat), ((Signal.loop (dom := defaultDomain) fun (st : Signal defaultDomain (BitVec 3)) => Signal.register 0#3 (st + 1#3)).val s) =
      ((Signal.loop (dom := defaultDomain) fun (st : Signal defaultDomain (BitVec 3)) => id (Signal.register 0#3 (st + 1#3))).val s))
  let bad ← `(∀ (s : Nat), ((Signal.loop (dom := defaultDomain) fun (st : Signal defaultDomain (BitVec 3)) => Signal.register 0#3 (st + 1#3)).val s) =
      ((Signal.loop (dom := defaultDomain) fun (st : Signal defaultDomain (BitVec 3)) => Signal.register 0#3 (st + 2#3)).val s))
  let hits0 ← Tools.VedMemS94Gen.canonHits.get
  let (c1, _) ← tryT good (← `(tactic| (intro s; ved_loop_canon; with_reducible rfl)))
  unless c1 do throwError "canon: the same loop was not made one"
  unless (← Tools.VedMemS94Gen.canonHits.get) == hits0 + 1 do throwError "canon: counter"
  let (c2, ok2) ← tryT bad (← `(tactic| (intro s; ved_loop_canon; rfl)))
  if c2 || ok2 then throwError "canon: two different loops were treated as one"
  Tools.VedMemS94Gen.canonRefuse.set true
  let (_, ok3) ← tryT good (← `(tactic| (intro s; ved_loop_canon; rfl)))
  Tools.VedMemS94Gen.canonRefuse.set false
  if ok3 then throwError "canon: seam did not refuse"
  -- a late failure (seam): the tactic fails and the `first` alternative runs on the goal as it was (here `skip`, then the plain `rfl` fails: the goal was restored, not half-rewritten)
  Tools.VedMemS94Gen.canonFailLate.set true
  let (c4, ok4) ← tryT good (← `(tactic| (intro s; (first | ved_loop_canon | skip); with_reducible rfl)))
  Tools.VedMemS94Gen.canonFailLate.set false
  if c4 || ok4 then throwError "canon: late failure left a rewritten goal (rfl closed it) or did not fail"
  logInfo m!"loop_canon controls: same loop made one, other loop refused, seam refuses, late failure restores"
/-! ## ved_addr_eq_local2 -/

/-- info: addr_eq_local2 controls: BitVec arithmetic address closes, wrong constant refused -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryClose (stmt : Term) (tac : TSyntax `tactic) : TermElabM Bool := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure gs.isEmpty
    catch _ => pure false
  let tac ← `(tactic| (intro a b; ved_addr_eq_local2))
  unless ← tryClose (← `(∀ (a : BitVec 5) (b : BitVec 5), (if a.toNat = 4 ∨ a.toNat = 3 then (4#8 * (0#6 ++ BitVec.extractLsb' 2 2 b) + (0#6 ++ BitVec.extractLsb' 0 2 b)) else 0#8) =
      BitVec.ofNat 8 (if (a.toNat % 32 = 4 ∨ a.toNat % 32 = 3) then ((b.toNat % 32 / 4 % 4) * 4 + b.toNat % 32 % 4) else 0))) tac do
    throwError "addr_eq_local2: the BitVec arithmetic address was not closed"
  unless ← tryClose (← `(∀ (a : BitVec 5) (b : BitVec 5), (if a.toNat = 4 then (b - 1#5).extractLsb' 0 4 else 0#4) =
      BitVec.ofNat 4 (if a.toNat % 32 = 4 then (32 - 1 + b.toNat % 32) % 32 % 16 else 0))) tac do
    throwError "addr_eq_local2: the subtraction address was not closed"
  if ← tryClose (← `(∀ (a : BitVec 5) (b : BitVec 5), (if a.toNat = 4 ∨ a.toNat = 3 then (4#8 * (0#6 ++ BitVec.extractLsb' 2 2 b) + (0#6 ++ BitVec.extractLsb' 0 2 b)) else 0#8) =
      BitVec.ofNat 8 (if (a.toNat % 32 = 4 ∨ a.toNat % 32 = 3) then ((b.toNat % 32 / 4 % 4) * 4 + b.toNat % 32 % 4 + 1) else 0))) tac then
    throwError "addr_eq_local2: a wrong constant was accepted"
  logInfo m!"addr_eq_local2 controls: BitVec arithmetic address closes, wrong constant refused"

@[reducible] def rid {α : Type} (a : α) : α := a

/-! ## ved_mem_addr_l + memCanon -/

/-- info: mem_canon controls: two spellings of one memory are one atom, different addresses stay apart -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryClose (stmt : Term) (tac : TSyntax `tactic) : TermElabM Bool := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure gs.isEmpty
    catch _ => pure false
  let tac ← `(tactic| (intro r n; ved_mem_addr_l))
  let stmt (addr2 : Term) : TermElabM Term := `(∀ (r n : Nat),
      (Signal.memState (dom := defaultDomain) (fun _ => 0#16) ⟨fun t => BitVec.ofNat 4 t⟩ ⟨fun t => BitVec.ofNat 16 t⟩ ⟨fun t => decide (t % 2 = 0)⟩ n (BitVec.ofNat 4 r)).toNat =
      (Signal.memState (dom := defaultDomain) (fun _ => 0#16) ⟨fun t => rid (BitVec.ofNat 4 t)⟩ ⟨fun t => BitVec.ofNat 16 t⟩ ⟨fun t => decide (t % 2 = 0)⟩ n $addr2).toNat)
  unless ← tryClose (← stmt (← `(BitVec.extractLsb' 0 4 (BitVec.ofNat 8 r)))) tac do
    throwError "mem_canon: two spellings of one memory were not made one atom"
  if ← tryClose (← stmt (← `(BitVec.ofNat 4 (r + 1)))) tac then
    throwError "mem_canon: atoms at different addresses were identified"
  logInfo m!"mem_canon controls: two spellings of one memory are one atom, different addresses stay apart"

end Tests.Ved.VedMemLocalCheck
