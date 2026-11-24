import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedMemLoop
import Tools.VedMemS94Gen
import Tools.VedMemS94Addr
import Tools.VedMemS94Local
import Tools.VedMemS94Opaque
import Tools.VedMemS94Inv

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

/-! ## ved_mem_opaque (s94s) -/

/-- kernel-checked: the abstracted goal is proved by `omega` (the atoms are unknown words), the original goal follows by applying it to the keys -/
theorem opaque_ok {dom : DomainConfig} (init : BitVec 4 → BitVec 8) (wa : Signal dom (BitVec 4)) (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) (n : Nat) (a b : BitVec 4) :
    (Signal.memState init wa wd we n a).toNat + (Signal.memState init wa wd we n b).toNat ≥ (Signal.memState init wa wd we n b).toNat := by
  ved_mem_opaque
  omega

/-- the address stays visible: an atom inside the address argument of another atom is abstracted too, the two keys are two variables -/
theorem opaque_nested {dom : DomainConfig} (init : BitVec 4 → BitVec 8) (init2 : BitVec 8 → BitVec 8) (wa : Signal dom (BitVec 4)) (wd : Signal dom (BitVec 8))
    (wa2 : Signal dom (BitVec 8)) (wd2 : Signal dom (BitVec 8)) (we : Signal dom Bool) (n : Nat) (a : BitVec 4) :
    (Signal.memState init2 wa2 wd2 we n (Signal.memState init wa wd we n a)).toNat ≥ (Signal.memState init2 wa2 wd2 we n (Signal.memState init wa wd we n a)).toNat := by
  ved_mem_opaque
  omega

/-- info: mem_opaque controls: atoms abstracted (counter +1, no memState left), different memories stay two variables, seam refuses, late failure restores, no atom refused -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let mem (n : Nat) : TermElabM Term := `(Signal.memState (dom := defaultDomain) (fun _ => 0#8) ⟨fun t => BitVec.ofNat 4 t⟩ ⟨fun t => BitVec.ofNat 8 t⟩ ⟨fun t => decide (t % 2 = 0)⟩ $(Lean.quote n) (BitVec.ofNat 4 r))
  -- the same memory twice (equal words): closes after the abstraction
  let same ← `(∀ (r : Nat), ($(← mem 3)).toNat = ($(← mem 3)).toNat + 0)
  -- two different memories (time 3 / time 4): the equation is not provable from the abstraction (the two keys are two variables)
  let diff ← `(∀ (r : Nat), ($(← mem 3)).toNat = ($(← mem 4)).toNat)
  let hits0 ← Tools.VedMemS94Opaque.opaqueHits.get
  let (c1, _) ← tryT same (← `(tactic| (intro r; ved_mem_opaque; omega)))
  unless c1 do throwError "opaque: the abstracted goal was not closed"
  unless (← Tools.VedMemS94Opaque.opaqueHits.get) == hits0 + 1 do throwError "opaque: counter"
  let (c2, _) ← tryT diff (← `(tactic| (intro r; ved_mem_opaque; omega)))
  if c2 then throwError "opaque: two different memories were identified"
  -- no memState atom is left in the target after the abstraction
  let (c3, ok3) ← tryT same (← `(tactic| (intro r; ved_mem_opaque; (fail_if_success (simp only [Signal.memState])); omega)))
  if !ok3 || !c3 then throwError "opaque: a memState atom was still visible after the abstraction"
  Tools.VedMemS94Opaque.opaqueRefuse.set true
  let (_, ok4) ← tryT same (← `(tactic| (intro r; ved_mem_opaque; omega)))
  Tools.VedMemS94Opaque.opaqueRefuse.set false
  if ok4 then throwError "opaque: seam did not refuse"
  -- late failure: the first alternative fails after its work, the `skip` alternative leaves the goal as it was (the original statement, still containing memState, is closed by `omega` directly)
  Tools.VedMemS94Opaque.opaqueFailLate.set true
  let (c5, ok5) ← tryT same (← `(tactic| (intro r; (first | ved_mem_opaque | skip); (fail_if_success (intro ved_M0)); omega)))
  Tools.VedMemS94Opaque.opaqueFailLate.set false
  if !ok5 || !c5 then throwError "opaque: late failure left an abstracted goal"
  -- no memState atom at all: refused
  let (_, ok6) ← tryT (← `(∀ (r : Nat), r + 0 = r)) (← `(tactic| (intro r; ved_mem_opaque)))
  if ok6 then throwError "opaque: a goal without atoms was accepted"
  logInfo m!"mem_opaque controls: atoms abstracted (counter +1, no memState left), different memories stay two variables, seam refuses, late failure restores, no atom refused"

/-! ## ved_cone_clear second hop (`ved.mem.s94Cone2`) and `ved_cone_opaque` (`ved.mem.s94OpaqueH`) (s94t) -/

set_option ved.mem.s94Cone2 true in
/-- kernel-checked: with the second hop the premise `p = 2` of the path hypothesis survives the cone clear, `omega` closes the goal -/
theorem cone2_ok (p s : Nat) (h2 : p = 2) (h1 : ¬(p = 2 ∧ s = 5)) : s ≠ 5 := by
  revert p s
  intro p s h2 h1
  ved_cone_clear
  omega

set_option ved.mem.s94OpaqueH true in
/-- kernel-checked: the memState key of a HYPOTHESIS is abstracted (the hypothesis re-introduced under its name), `omega` closes the goal, the original goal follows -/
theorem opaqueH_ok {dom : DomainConfig} (init : BitVec 4 → BitVec 8) (wa : Signal dom (BitVec 4)) (wd : Signal dom (BitVec 8)) (we : Signal dom Bool) (n : Nat) (a : BitVec 4)
    (h : (Signal.memState init wa wd we n a).toNat = 5) : (Signal.memState init wa wd we n a).toNat + 1 = 6 := by
  ved_cone_opaque
  omega

/-- info: cone2 / opaqueH controls: OFF clears the premise and keeps the atoms (counters unchanged), ON keeps the small premise (counter +1) and abstracts the hypothesis atom (counter +1), an unrelated entry is still cleared, a goal without atoms is left alone -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let withOpt (o : Name) (v : Bool) (x : TermElabM (Bool × Bool)) : TermElabM (Bool × Bool) := withOptions (fun os => os.setBool o v) x
  -- the premise is cleared without the option
  let cone ← `(∀ (p s q : Nat), p = 2 → ¬(p = 2 ∧ s = 5) → q = 7 → s ≠ 5)
  let tacC ← `(tactic| (intro p s q h2 h1 hq; ved_cone_clear; omega))
  let k0 ← Tools.VedMemS94Local.cone2Kept.get
  let (cOff, _) ← withOpt `ved.mem.s94Cone2 false (tryT cone tacC)
  if cOff then throwError "cone2: OFF: the premise survived the one-hop cone"
  unless (← Tools.VedMemS94Local.cone2Kept.get) == k0 do throwError "cone2: OFF: counter moved"
  let (cOn, okOn) ← withOpt `ved.mem.s94Cone2 true (tryT cone tacC)
  if !okOn || !cOn then throwError "cone2: ON: the premise did not survive"
  unless (← Tools.VedMemS94Local.cone2Kept.get) == k0 + 1 do throwError "cone2: ON: counter"
  -- an entry over a variable that no kept hypothesis mentions (here q, only in `hq`) is still cleared
  let (cQ, okQ) ← withOpt `ved.mem.s94Cone2 true (tryT cone (← `(tactic| (intro p s q h2 h1 hq; ved_cone_clear; (fail_if_success (have := hq)); omega))))
  if !okQ || !cQ then throwError "cone2: ON: the unrelated entry was kept (or the premise cleared)"
  -- hypothesis atoms
  let mem : TermElabM Term := `(Signal.memState (dom := defaultDomain) (fun _ => 0#8) ⟨fun t => BitVec.ofNat 4 t⟩ ⟨fun t => BitVec.ofNat 8 t⟩ ⟨fun t => decide (t % 2 = 0)⟩ 3 (BitVec.ofNat 4 r))
  let stmt ← `(∀ (r : Nat), ($(← mem)).toNat = 5 → ($(← mem)).toNat + 1 = 6)
  let tacH ← `(tactic| (intro r h; ved_cone_opaque; (fail_if_success (simp only [Signal.memState] at *)); omega))
  let h0 ← Tools.VedMemS94Local.coneOpaqueHits.get
  let (hOff, _) ← withOpt `ved.mem.s94OpaqueH false (tryT stmt tacH)
  if hOff then throwError "opaqueH: OFF: the atom was abstracted"
  unless (← Tools.VedMemS94Local.coneOpaqueHits.get) == h0 do throwError "opaqueH: OFF: counter moved"
  let (hOn, okH) ← withOpt `ved.mem.s94OpaqueH true (tryT stmt tacH)
  if !okH || !hOn then throwError "opaqueH: ON: the hypothesis atom was not abstracted"
  unless (← Tools.VedMemS94Local.coneOpaqueHits.get) == h0 + 1 do throwError "opaqueH: ON: counter"
  -- no atom anywhere: nothing happens, the goal is closed by omega as before
  let (hN, okN) ← withOpt `ved.mem.s94OpaqueH true (tryT (← `(∀ (r : Nat), r = 5 → r + 1 = 6)) (← `(tactic| (intro r h; ved_cone_opaque; omega))))
  if !okN || !hN then throwError "opaqueH: a goal without atoms was changed"
  unless (← Tools.VedMemS94Local.coneOpaqueHits.get) == h0 + 1 do throwError "opaqueH: counter moved without an atom"
  logInfo m!"cone2 / opaqueH controls: OFF clears the premise and keeps the atoms (counters unchanged), ON keeps the small premise (counter +1) and abstracts the hypothesis atom (counter +1), an unrelated entry is still cleared, a goal without atoms is left alone"

/-! ## ved_addr_eq_bv (`ved.mem.s94Addr`) and ved_cong (s94u) -/

set_option ved.mem.s94Addr true in
/-- kernel-checked: an address equality of the shape of R033 goal 139 (an `if` over a state field, `*` / `++` on one side, `ofNat` of a `%` / `/` form on the other) is closed by the toNat
translation, the `if` split and `decide +kernel` over the BitVec variables of each leaf -/
theorem addr_bv_ok (a b c : BitVec 5) :
    (if a.toNat = 13 then 16#8 * (0#3 ++ b) + (0#3 ++ c) else 0#8) =
    BitVec.ofNat 8 (if a.toNat = 13 then (b.toNat % 32 * 16 + c.toNat % 32) % 256 else 0) := by
  ved_addr_eq_bv

/-- info: addr_bv controls: OFF refused, ON closes (leaf counter moves), a WRONG address equality is refused (also with the late-failure `first`: the goal is as it was), more than 12 bits are refused -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let withOpt (o : Name) (v : Bool) (x : TermElabM (Bool × Bool)) : TermElabM (Bool × Bool) := withOptions (fun os => os.setBool o v) x
  let good ← `(∀ (a b : BitVec 5), (if a.toNat = 13 then 16#8 * (0#3 ++ b) else 0#8) = BitVec.ofNat 8 (if a.toNat = 13 then b.toNat % 32 * 16 % 256 else 0))
  let tac ← `(tactic| (intro a b; ved_addr_eq_bv))
  let l0 ← Tools.VedMemS94Local.bvEnumLeaves.get
  let (cOff, _) ← withOpt `ved.mem.s94Addr false (tryT good tac)
  if cOff then throwError "addr_bv: OFF: the equality was closed"
  unless (← Tools.VedMemS94Local.bvEnumLeaves.get) == l0 do throwError "addr_bv: OFF: counter moved"
  let (cOn, okOn) ← withOpt `ved.mem.s94Addr true (tryT good tac)
  if !okOn || !cOn then throwError "addr_bv: ON: the equality was not closed"
  unless (← Tools.VedMemS94Local.bvEnumLeaves.get) > l0 do throwError "addr_bv: ON: counter"
  -- a wrong equality (8 * b instead of 16 * b on the right)
  let bad ← `(∀ (a b : BitVec 5), (if a.toNat = 13 then 16#8 * (0#3 ++ b) else 0#8) = BitVec.ofNat 8 (if a.toNat = 13 then b.toNat % 32 * 8 % 256 else 0))
  let (cBad, _) ← withOpt `ved.mem.s94Addr true (tryT bad tac)
  if cBad then throwError "addr_bv: a WRONG address equality was closed"
  -- late failure: the first alternative fails after its work (split, reverts), the goal is the original BitVec equality again
  let (cLate, okLate) ← withOpt `ved.mem.s94Addr true (tryT bad (← `(tactic| (intro a b; (first | ved_addr_eq_bv | skip); apply BitVec.eq_of_toNat_eq))))
  if !okLate || cLate then throwError "addr_bv: late failure did not restore the goal"
  -- too many bits in one leaf (two 8-bit variables = 16 > 12): refused
  let wide ← `(∀ (x y : BitVec 8), x + y = y + x)
  let (cW, _) ← withOpt `ved.mem.s94Addr true (tryT wide (← `(tactic| (intro x y; ved_addr_eq_bv))))
  if cW then throwError "addr_bv: 16 bits were enumerated"
  logInfo m!"addr_bv controls: OFF refused, ON closes (leaf counter moves), a WRONG address equality is refused (also with the late-failure `first`: the goal is as it was), more than 12 bits are refused"

/-! ## ved_atom_args, ved_ite_div (`ved.mem.s94Addr`), ved_hyp_split_omega (`ved.mem.s94HypSplit`) (s94u) -/

set_option ved.mem.s94HypSplit true in
/-- kernel-checked: the `if` is in a HYPOTHESIS (the target has none): `omega` alone cannot, the split of the hypothesis `if` and `omega` per leaf close it -/
theorem hypsplit_ok (a b : Nat) (h1 : b < 2) (h : (if a = 0 then 1 else 0) % 2 = 0) (h2 : ¬(a = 5 ∧ b = 1)) : a ≠ 0 := by
  ved_hyp_split_omega

set_option ved.mem.s94Addr true in
/-- kernel-checked: the two spellings `ofNat 4 x.toNat` / `extractLsb' 0 4 x` of one address are one atom for `omega` after `ved_atom_args` -/
theorem atom_ok (M : BitVec 4 → BitVec 16) (x : BitVec 5) (h : (M (BitVec.ofNat 4 x.toNat)).toNat = 3) : (M (BitVec.extractLsb' 0 4 x)).toNat = 3 := by
  ved_atom_args
  omega

set_option ved.mem.s94Addr true in
/-- kernel-checked: `(if p then 1 else 0) / 2` is 0 -/
theorem itediv_ok (p : Prop) [Decidable p] (h : (if p then 1 else 0) / 2 = 1) : False := by
  ved_ite_div
  omega

/-- info: hyp_split / atom_args / ite_div controls: OFF refused / unchanged, ON closes (counters +1), a false statement is refused, late failure restores the goal -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let withOpt (o : Name) (v : Bool) (x : TermElabM (Bool × Bool)) : TermElabM (Bool × Bool) := withOptions (fun os => os.setBool o v) x
  -- hyp split
  let hs ← `(∀ (a b : Nat), b < 2 → (if a = 0 then (1 : Nat) else 0) % 2 = 0 → ¬(a = 5 ∧ b = 1) → a ≠ 0)
  let tacH ← `(tactic| (intro a b h1 h h2; ved_hyp_split_omega_g))
  let k0 ← Tools.VedMemS94Local.hypSplitHits.get
  let (hOff, _) ← withOpt `ved.mem.s94HypSplit false (tryT hs tacH)
  if hOff then throwError "hypsplit: OFF: the goal was closed"
  unless (← Tools.VedMemS94Local.hypSplitHits.get) == k0 do throwError "hypsplit: OFF: counter moved"
  let (hOn, okOn) ← withOpt `ved.mem.s94HypSplit true (tryT hs tacH)
  if !okOn || !hOn then throwError "hypsplit: ON: not closed"
  unless (← Tools.VedMemS94Local.hypSplitHits.get) == k0 + 1 do throwError "hypsplit: ON: counter"
  -- a false statement (a = 0 allowed) is refused
  let bad ← `(∀ (a b : Nat), b < 2 → (if a = 0 then (1 : Nat) else 0) % 2 = 1 → ¬(a = 5 ∧ b = 1) → a ≠ 0)
  let (hBad, _) ← withOpt `ved.mem.s94HypSplit true (tryT bad (← `(tactic| (intro a b h1 h h2; ved_hyp_split_omega_g))))
  if hBad then throwError "hypsplit: a FALSE statement was closed"
  -- late failure: the goal is as it was (not closed, still a Not-equal goal)
  let (hLate, okLate) ← withOpt `ved.mem.s94HypSplit true (tryT bad (← `(tactic| (intro a b h1 h h2; (first | ved_hyp_split_omega_g | skip); guard_target =ₛ a ≠ 0))))
  if !okLate || hLate then throwError "hypsplit: late failure did not restore the goal"
  -- atom args
  let atS ← `(∀ (M : BitVec 4 → BitVec 16) (x : BitVec 5), (M (BitVec.ofNat 4 x.toNat)).toNat = 3 → (M (BitVec.extractLsb' 0 4 x)).toNat = 3)
  let tacA ← `(tactic| (intro M x h; ved_atom_args; omega))
  let a0 ← Tools.VedMemS94Local.atomArgsHits.get
  let (aOff, _) ← withOpt `ved.mem.s94Addr false (tryT atS tacA)
  if aOff then throwError "atom_args: OFF: closed"
  unless (← Tools.VedMemS94Local.atomArgsHits.get) == a0 do throwError "atom_args: OFF: counter moved"
  let (aOn, okA) ← withOpt `ved.mem.s94Addr true (tryT atS tacA)
  if !okA || !aOn then throwError "atom_args: ON: not closed"
  unless (← Tools.VedMemS94Local.atomArgsHits.get) == a0 + 1 do throwError "atom_args: ON: counter"
  -- ite div
  let dv ← `(∀ (p : Prop) [Decidable p], (if p then (1 : Nat) else 0) / 2 = 1 → False)
  let tacD ← `(tactic| (intro p _ h; ved_ite_div; omega))
  let (dOff, _) ← withOpt `ved.mem.s94Addr false (tryT dv tacD)
  if dOff then throwError "ite_div: OFF: closed"
  let (dOn, okD) ← withOpt `ved.mem.s94Addr true (tryT dv tacD)
  if !okD || !dOn then throwError "ite_div: ON: not closed"
  logInfo m!"hyp_split / atom_args / ite_div controls: OFF refused / unchanged, ON closes (counters +1), a false statement is refused, late failure restores the goal"

/-! ## ved_if_read_share / ved_share99_one (option `ved.mem.s94Share99`, stage 99 across goals) -/

set_option ved.mem.s94Share99 true in
/-- kernel-checked: three goals, two of them with the same `(a + b).toNat` spine, simplified with one shared simp cache -/
theorem share99_ok (a b c : BitVec 8) : (a + b).toNat < 300 ∧ (a + c).toNat < 300 ∧ (a + b).toNat + 0 < 400 := by
  refine ⟨?_, ?_, ?_⟩
  ved_if_read_share [Nat.add_zero]
  all_goals omega

/-- info: share99 controls: OFF refused, ON = plain route goal by goal (the spines of different goals are not mixed), cache filled, counters, late failure restores -/
#guard_msgs in
run_cmd liftTermElabM do
  let stmt ← `(∀ (a b c : BitVec 8), (a + b).toNat < 300 ∧ (a + c).toNat < 300 ∧ (a + b).toNat < 7)
  let goalsOf (tac : TSyntax `tactic) : TermElabM (Option (List String)) := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      let mut out : List String := []
      for g in gs do out := out ++ [(← g.withContext do ppExpr (← instantiateMVars (← g.getType))).pretty]
      pure (some out)
    catch _ => pure none
  let withOpt (o : Name) (v : Bool) (x : TermElabM (Option (List String))) : TermElabM (Option (List String)) := withOptions (fun os => os.setBool o v) x
  let plain ← goalsOf (← `(tactic| (intro a b c; refine ⟨?_, ?_, ?_⟩; all_goals (try ved_loop_simp [Nat.add_zero]))))
  let some plain := plain | throwError "share99: the plain route failed"
  Tools.VedMemS94Gen.share99State.set none
  -- OFF: refused
  let k0 ← Tools.VedMemS94Gen.share99Hits.get
  let off ← withOpt `ved.mem.s94Share99 false (goalsOf (← `(tactic| (intro a b c; refine ⟨?_, ?_, ?_⟩; ved_share99_one [Nat.add_zero]))))
  if off.isSome then throwError "share99: OFF: the step ran"
  unless (← Tools.VedMemS94Gen.share99Hits.get) == k0 do throwError "share99: OFF: counter moved"
  -- ON, the stage tactic: the same goals as the plain route
  let on ← withOpt `ved.mem.s94Share99 true (goalsOf (← `(tactic| (intro a b c; refine ⟨?_, ?_, ?_⟩; ved_if_read_share [Nat.add_zero]))))
  let some on := on | throwError "share99: ON: failed"
  unless on == plain do throwError "share99: ON: the goals differ from the plain route: {on} vs {plain}"
  unless (← Tools.VedMemS94Gen.share99Hits.get) == k0 + 3 do throwError "share99: ON: counter"
  unless (← Tools.VedMemS94Gen.share99State.get).isNone do throwError "share99: the state was not dropped at the end of the stage"
  -- ON, three single steps without a reset: the cache is filled, the goals are still the plain route's
  let on3 ← withOpt `ved.mem.s94Share99 true (goalsOf (← `(tactic| (intro a b c; refine ⟨?_, ?_, ?_⟩; all_goals (ved_share99_one [Nat.add_zero])))))
  let some on3 := on3 | throwError "share99: ON (steps): failed"
  unless on3 == plain do throwError "share99: ON (steps): the goals differ from the plain route"
  let some st ← Tools.VedMemS94Gen.share99State.get | throwError "share99: no state after the steps"
  if (st.cache.fold (fun n _ _ => n + 1) 0) == 0 then throwError "share99: empty cache"
  Tools.VedMemS94Gen.share99State.set none
  -- late failure (seam): the goal is as it was, the state and the counter unchanged
  let k1 ← Tools.VedMemS94Gen.share99Hits.get
  Tools.VedMemS94Gen.share99FailLate.set true
  let late ← withOpt `ved.mem.s94Share99 true (goalsOf (← `(tactic| (intro a b c; refine ⟨?_, ?_, ?_⟩; all_goals (first | ved_share99_one [Nat.add_zero] | skip)))))
  Tools.VedMemS94Gen.share99FailLate.set false
  let some late := late | throwError "share99: late: failed"
  unless late.length == 3 && late.all (·.contains '+') && late.all (!·.contains '%') do throwError "share99: late failure did not restore the goals: {late}"
  unless (← Tools.VedMemS94Gen.share99Hits.get) == k1 && (← Tools.VedMemS94Gen.share99State.get).isNone do throwError "share99: late failure changed the counter or the state"
  -- the refuse seam
  Tools.VedMemS94Gen.share99Refuse.set true
  let ref ← withOpt `ved.mem.s94Share99 true (goalsOf (← `(tactic| (intro a b c; refine ⟨?_, ?_, ?_⟩; ved_share99_one [Nat.add_zero]))))
  Tools.VedMemS94Gen.share99Refuse.set false
  if ref.isSome then throwError "share99: the seam did not refuse"
  logInfo m!"share99 controls: OFF refused, ON = plain route goal by goal (the spines of different goals are not mixed), cache filled, counters, late failure restores"

/-! ## ved_mem_spell (option `ved.mem.s94Spell`): two spellings of one memory are one atom -/

set_option ved.mem.s94Spell true in
open Sparkle.Core.Signal Sparkle.Core.Domain in
/-- kernel-checked: after `ved_mem_spell` the two reads (a `BitVec` equation against its `toNat` form, a literal factor on the other side) are one atom -/
theorem spell_ok (init : BitVec 4 → BitVec 8) (wa : Signal defaultDomain (BitVec 4)) (we : Signal defaultDomain Bool) (x : Nat → BitVec 5) (n : Nat) (a : BitVec 4)
    (h : (Signal.memState init wa (Signal.mk fun t => if (x t).toNat = 3 then (BitVec.ofNat 8 4) * (BitVec.ofNat 8 5) else 0#8) we n a).toNat ≠ 0) :
    (Signal.memState init wa (Signal.mk fun t => if x t = BitVec.ofNat 5 3 then (BitVec.ofNat 8 5) * (BitVec.ofNat 8 4) else 0#8) we n a).toNat ≠ 0 := by
  ved_mem_spell
  exact h

/-- info: spell controls: OFF refused, ON merges the two spellings (counter +1), two really different memories are refused, late failure restores the goal -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let withOpt (v : Bool) (x : TermElabM (Bool × Bool)) : TermElabM (Bool × Bool) := withOptions (fun os => os.setBool `ved.mem.s94Spell v) x
  let mk (c1 c2 : Nat) : TermElabM Term := `(∀ (init : BitVec 4 → BitVec 8) (wa : Signal defaultDomain (BitVec 4)) (we : Signal defaultDomain Bool) (x : Nat → BitVec 5) (n : Nat) (a : BitVec 4),
    (Signal.memState init wa (Signal.mk fun t => if (x t).toNat = 3 then (BitVec.ofNat 8 4) * (BitVec.ofNat 8 5) else 0#8) we n a).toNat ≠ 0 →
    (Signal.memState init wa (Signal.mk fun t => if x t = BitVec.ofNat 5 3 then (BitVec.ofNat 8 $(Syntax.mkNumLit (toString c1))) * (BitVec.ofNat 8 $(Syntax.mkNumLit (toString c2))) else 0#8) we n a).toNat ≠ 0)
  let good ← mk 5 4
  let bad ← mk 5 6
  let tac ← `(tactic| (intro init wa we x n a h; ved_mem_spell; exact h))
  let k0 ← Tools.VedMemS94Local.spellHits.get
  let (off, _) ← withOpt false (tryT good tac)
  if off then throwError "spell: OFF: closed"
  unless (← Tools.VedMemS94Local.spellHits.get) == k0 do throwError "spell: OFF: counter moved"
  let (on, okOn) ← withOpt true (tryT good tac)
  if !on || !okOn then throwError "spell: ON: not closed"
  unless (← Tools.VedMemS94Local.spellHits.get) == k0 + 1 do throwError "spell: ON: counter"
  -- two really different memories (4 * 6 against 4 * 5): the atoms are not merged, the goal stays open (or the tactic fails)
  let (badC, _) ← withOpt true (tryT bad tac)
  if badC then throwError "spell: DIFFERENT memories were merged"
  -- late failure (seam): the goal is as it was
  Tools.VedMemS94Local.spellFailLate.set true
  let (late2, _) ← withOpt true (tryT good (← `(tactic| (intro init wa we x n a h; (first | ved_mem_spell | skip); guard_target =ₛ (Signal.memState init wa (Signal.mk fun t => if x t = BitVec.ofNat 5 3 then (BitVec.ofNat 8 5) * (BitVec.ofNat 8 4) else 0#8) we n a).toNat ≠ 0; exact h))))
  Tools.VedMemS94Local.spellFailLate.set false
  if late2 then throwError "spell: late failure: the goal was closed"
  logInfo m!"spell controls: OFF refused, ON merges the two spellings (counter +1), two really different memories are refused, late failure restores the goal"

/-! ## ved.mem.s94StateSplit: one case split on the state value, ved.mem.s94MulShift: the multiply-shift closing -/

set_option ved.mem.s94StateSplit true in
/-- kernel-checked: an `if` tower over the 3-bit state `s` (5 comparisons `s.toNat = k`) closes by one case split on `s.toNat` (8 cases), the literal conditions decided, `omega` per case -/
theorem state_split_ok (s : BitVec 3) (x : Nat) (hx : x < 10) :
    (if s.toNat = 0 then x + 1 else if s.toNat = 1 then x + 2 else if s.toNat = 2 then x else if s.toNat = 3 then 7 else if s.toNat = 4 then 9 else 0) % 16 =
    (if s.toNat = 0 then x + 1 else if s.toNat = 1 then x + 2 else if s.toNat = 2 then x else if s.toNat = 3 then 7 else if s.toNat = 4 then 9 else 0) := by
  ved_local_close_state

set_option ved.mem.s94MulShift true in
/-- kernel-checked: the two spellings of one multiply-shift (conditions spelled `(if u % 2 = 1 then 1 else 0) % 2 = 0` / `u % 2 = 0`, `a % 65536` / `a`, `b % 2^(16+16)` / `b`) are one term for `omega` -/
theorem mulshift_ok (a u b0 b1 c m : Nat) (ha : a < 65536) (hb0 : b0 < 4294967296) (hb1 : b1 < 4294967296) :
    (((a % 65536) * (if (if u % 2 = 1 then 1 else 0) % 2 = 0 then b0 else b1) + c) % 4294967296 / 2 ^ (m % 32)) % 65536 =
    ((a * (if u % 2 = 0 then b0 % 2 ^ (16 + 16) else b1 % 2 ^ (16 + 16)) + c) % 2 ^ (16 + 16) / 2 ^ (m % 32)) % 65536 := by
  ved_local_close_mulshift

/-- info: state / mulshift controls: OFF refused, ON closes (counters), a false statement is refused, late failure restores the goal, the refuse seam refuses -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let withOpt (o : Name) (v : Bool) (x : TermElabM (Bool × Bool)) : TermElabM (Bool × Bool) := withOptions (fun os => os.setBool o v) x
  -- state split
  let st (m : Nat) : TermElabM Term := `(∀ (s : BitVec 3) (x : Nat), x < 10 →
    (if s.toNat = 0 then x + 1 else if s.toNat = 1 then x + 2 else if s.toNat = 2 then x else if s.toNat = 3 then 7 else if s.toNat = 4 then 9 else 0) % $(Syntax.mkNumLit (toString m)) =
    (if s.toNat = 0 then x + 1 else if s.toNat = 1 then x + 2 else if s.toNat = 2 then x else if s.toNat = 3 then 7 else if s.toNat = 4 then 9 else 0))
  let stTac ← `(tactic| (intro s x hx; ved_local_close_state))
  let (off, _) ← withOpt `ved.mem.s94StateSplit false (tryT (← st 16) stTac)
  if off then throwError "state: OFF: closed"
  let b0 ← Tools.VedMemS94Local.stateSplitBranches.get
  let (on, _) ← withOpt `ved.mem.s94StateSplit true (tryT (← st 16) stTac)
  unless on do throwError "state: ON: not closed"
  unless (← Tools.VedMemS94Local.stateSplitBranches.get) == b0 + 8 do throwError "state: ON: expected 8 branches"
  -- a false statement (`% 8` with x + 2 up to 11): refused
  let (bad, _) ← withOpt `ved.mem.s94StateSplit true (tryT (← st 8) stTac)
  if bad then throwError "state: a false statement was closed"
  -- late failure: the split goal is restored (the closed flag stays false), the seam is reset
  Tools.VedMemS94Local.stateSplitFailLate.set true
  let (late, _) ← withOpt `ved.mem.s94StateSplit true (tryT (← st 16) (← `(tactic| (intro s x hx; first | (ved_state_split; ved_state_simp; all_goals ved_state_branch; ved_state_late) | skip))))
  Tools.VedMemS94Local.stateSplitFailLate.set false
  if late then throwError "state: late failure: the goal was closed"
  Tools.VedMemS94Local.stateSplitRefuse.set true
  let (ref, _) ← withOpt `ved.mem.s94StateSplit true (tryT (← st 16) stTac)
  Tools.VedMemS94Local.stateSplitRefuse.set false
  if ref then throwError "state: the refuse seam closed the goal"
  -- multiply-shift
  let ms (k : Nat) : TermElabM Term :=
    if k == 0 then `(∀ (a u b0 b1 c m : Nat), a < 65536 → b0 < 4294967296 → b1 < 4294967296 →
      (((a % 65536) * (if (if u % 2 = 1 then 1 else 0) % 2 = 0 then b0 else b1) + c) % 4294967296 / 2 ^ (m % 32)) % 65536 =
      ((a * (if u % 2 = 0 then b0 % 2 ^ (16 + 16) else b1 % 2 ^ (16 + 16)) + c) % 2 ^ (16 + 16) / 2 ^ (m % 32)) % 65536)
    else `(∀ (a u b0 b1 c m : Nat), a < 65536 → b0 < 4294967296 → b1 < 4294967296 →
      (((a % 65536) * (if (if u % 2 = 1 then 1 else 0) % 2 = 0 then b0 else b1) + c) % 4294967296 / 2 ^ (m % 32)) % 65536 =
      ((a * (if u % 2 = 0 then b0 % 2 ^ (16 + 16) else b1 % 2 ^ (16 + 16)) + c + 1) % 2 ^ (16 + 16) / 2 ^ (m % 32)) % 65536)
  let msTac ← `(tactic| (intro a u b0 b1 c m ha hb0 hb1; ved_local_close_mulshift))
  let (moff, _) ← withOpt `ved.mem.s94MulShift false (tryT (← ms 0) msTac)
  if moff then throwError "mulshift: OFF: closed"
  let (mon, _) ← withOpt `ved.mem.s94MulShift true (tryT (← ms 0) msTac)
  unless mon do
    let ty ← elabTerm (← ms 0) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let mv ← mkFreshExprMVar ty
    let msg ← withOptions (fun os => os.setBool `ved.mem.s94MulShift true) <| try
        let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic msTac))
        pure s!"goals left {gs.length}"
      catch e => pure (← e.toMessageData.toString)
    throwError "mulshift: ON: not closed: {msg.take 800}"
  let (mbad, _) ← withOpt `ved.mem.s94MulShift true (tryT (← ms 1) msTac)
  if mbad then throwError "mulshift: a false statement was closed"
  Tools.VedMemS94Local.mulShiftFailLate.set true
  let (mlate, _) ← withOpt `ved.mem.s94MulShift true (tryT (← ms 0) (← `(tactic| (intro a u b0 b1 c m ha hb0 hb1; first | ved_local_close_mulshift | skip))))
  Tools.VedMemS94Local.mulShiftFailLate.set false
  if mlate then throwError "mulshift: late failure: the goal was closed"
  Tools.VedMemS94Local.mulShiftRefuse.set true
  let (mref, _) ← withOpt `ved.mem.s94MulShift true (tryT (← ms 0) msTac)
  Tools.VedMemS94Local.mulShiftRefuse.set false
  if mref then throwError "mulshift: the refuse seam closed the goal"
  logInfo m!"state / mulshift controls: OFF refused, ON closes (counters), a false statement is refused, late failure restores the goal, the refuse seam refuses"

/-- kernel-checked: `ved_conj_prune` cuts a 7-conjunct bound hypothesis to the conjuncts about the atoms of the target (the three about `y` are dropped) -/
theorem conj_prune_ok (x y : Nat) (h : x < 2 ∧ y < 3 ∧ x < 5 ∧ y < 9 ∧ x < 7 ∧ y < 8 ∧ x < 11) : x + 1 ≤ 2 := by
  ved_conj_prune
  omega

/-- kernel-checked: `ved_read_bounds` supplies `(f e).toNat < 2 ^ w` for a read of a variable function -/
theorem read_bounds_ok (f : BitVec 3 → BitVec 8) (e : BitVec 3) : (f e).toNat < 256 := by
  ved_read_bounds
  omega

/-- info: conj_prune / read_bounds controls: the three conjuncts about y dropped (counter +3), a hypothesis with fewer than 6 conjuncts refused, a goal without a read refused, a target about y closes from the kept conjunct y < 3 -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let d0 ← Tools.VedMemS94Local.conjPruneDropped.get
  let (ok, _) ← tryT (← `(∀ (x y : Nat), x < 2 ∧ y < 3 ∧ x < 5 ∧ y < 9 ∧ x < 7 ∧ y < 8 ∧ x < 11 → x + 1 ≤ 2)) (← `(tactic| (intro x y h; ved_conj_prune; omega)))
  unless ok do throwError "conj_prune: not closed"
  unless (← Tools.VedMemS94Local.conjPruneDropped.get) == d0 + 3 do throwError "conj_prune: dropped counter"
  let (small, _) ← tryT (← `(∀ (x y : Nat), x < 2 ∧ y < 3 → x + 1 ≤ 2)) (← `(tactic| (intro x y h; ved_conj_prune; omega)))
  if small then throwError "conj_prune: a small conjunction was cut"
  -- the target is about y: the conjuncts about x are dropped, the conjunct y < 3 stays: closes; but a statement that needs `x < 2` for a target about y and x is not closed by the pruned hypothesis
  let (need, _) ← tryT (← `(∀ (x y : Nat), x < 2 ∧ y < 3 ∧ x < 5 ∧ y < 9 ∧ x < 7 ∧ y < 8 ∧ x < 11 → y + 1 ≤ 3)) (← `(tactic| (intro x y h; ved_conj_prune; omega)))
  unless need do throwError "conj_prune: a target about y must close from y < 3"
  let (noRd, _) ← tryT (← `(∀ (x : Nat), x = x)) (← `(tactic| (intro x; ved_read_bounds)))
  if noRd then throwError "read_bounds: a goal without a read was accepted"
  logInfo m!"conj_prune / read_bounds controls: the three conjuncts about y dropped (counter +3), a hypothesis with fewer than 6 conjuncts refused, a goal without a read refused, a target about y closes from the kept conjunct y < 3"

/-! ## s94x: spellings of one value inside a memory read (`Tools/VedMemS94Addr.lean`), reads at `if` addresses, `|||` bounds, gates -/

set_option ved.mem.s94AddrNorm true in
/-- kernel-checked: the two spellings of one address (R033 goals 33 34: `ofNat 9 ((c * 68 + a * 4 + b) % 512)` against `68#9 * (0#7 ++ c) + 4#9 * (0#4 ++ a) + (0#6 ++ b)`) are unified inside a read of
a variable memory function, the equation is then `rfl` -/
theorem addr_unify_ok (M : BitVec 9 → BitVec 16) (c : BitVec 2) (a : BitVec 5) (b : BitVec 3) :
    (M (BitVec.ofNat 9 ((c.toNat * 68 + a.toNat * 4 + b.toNat) % 512))).toNat = (M (68#9 * (0#7 ++ c) + 4#9 * (0#4 ++ a) + (0#6 ++ b))).toNat := by
  ved_spell_unify
  rfl

set_option ved.mem.s94AddrNorm true in
/-- kernel-checked: two spellings of one exponent are one exponent -/
theorem pow_unify_ok (x : BitVec 3) : 2 ^ ((x.toNat + 7) % 8) = 2 ^ ((7 + x.toNat) % 8) := by
  ved_spell_unify
  rfl

set_option ved.mem.s94ReadLift true in
/-- kernel-checked: a read at an `if` address is the `if` of the reads (and its `toNat` the `if` of the `toNat`s) -/
theorem read_lift_ok (f : BitVec 3 → BitVec 8) (p : Prop) [Decidable p] (a b : BitVec 3) :
    (f (if p then a else b)).toNat = if p then (f a).toNat else (f b).toNat := by
  ved_read_lift
  rfl

set_option ved.mem.s94OrDisj true in
/-- kernel-checked: `(x ||| y) % 256 = x ||| y` for two bytes (the bound `x ||| y < 2 ^ 8` from `Nat.or_lt_two_pow`) -/
theorem or_bounds_ok (x y : BitVec 8) : (x.toNat ||| y.toNat) % 256 = x.toNat ||| y.toNat := by
  ved_or_bounds
  omega

set_option ved.mem.s94OrDisj true in
/-- kernel-checked: the same for `&&&` with a mask below the power -/
theorem and_bounds_ok (x : Nat) : (x &&& 120) % 128 = x &&& 120 := by
  ved_or_bounds
  omega

/-- info: addr_unify / pow_unify / read_lift / or_bounds / gates controls: OFF refused, ON closes (counters), a false statement is refused, late failure restores the goal, the refuse seam refuses -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let withOpt (o : Name) (v : Bool) (x : TermElabM (Bool × Bool)) : TermElabM (Bool × Bool) := withOptions (fun os => os.setBool o v) x
  -- the address spellings
  let ad (k : Nat) : TermElabM Term := `(∀ (M : BitVec 9 → BitVec 16) (c : BitVec 2) (a : BitVec 5) (b : BitVec 3),
    (M (BitVec.ofNat 9 ((c.toNat * 68 + a.toNat * 4 + b.toNat + $(Syntax.mkNumLit (toString k))) % 512))).toNat = (M (68#9 * (0#7 ++ c) + 4#9 * (0#4 ++ a) + (0#6 ++ b))).toNat)
  let adTac ← `(tactic| (intro M c a b; ved_spell_unify; rfl))
  let (off, _) ← withOpt `ved.mem.s94AddrNorm false (tryT (← ad 0) adTac)
  if off then throwError "addr: OFF: closed"
  let h0 ← Tools.VedMemS94Addr.unifyHits.get
  let (on, _) ← withOpt `ved.mem.s94AddrNorm true (tryT (← ad 0) adTac)
  unless on do throwError "addr: ON: not closed"
  unless (← Tools.VedMemS94Addr.unifyHits.get) == h0 + 1 do throwError "addr: ON: expected one unified pair"
  -- a false statement (an address off by one): the two spellings are not one value, nothing is unified, the goal is not closed
  let (bad, _) ← withOpt `ved.mem.s94AddrNorm true (tryT (← ad 1) adTac)
  if bad then throwError "addr: a false statement was closed"
  Tools.VedMemS94Addr.unifyFailLate.set true
  let (late, _) ← withOpt `ved.mem.s94AddrNorm true (tryT (← ad 0) (← `(tactic| (intro M c a b; first | (ved_spell_unify; rfl) | skip))))
  Tools.VedMemS94Addr.unifyFailLate.set false
  if late then throwError "addr: late failure: the goal was closed"
  Tools.VedMemS94Addr.unifyRefuse.set true
  let (ref, _) ← withOpt `ved.mem.s94AddrNorm true (tryT (← ad 0) adTac)
  Tools.VedMemS94Addr.unifyRefuse.set false
  if ref then throwError "addr: the refuse seam closed the goal"
  -- the exponents: a false statement (`+ 6`) is refused
  let ex (k : Nat) : TermElabM Term := `(∀ (x : BitVec 3), 2 ^ ((x.toNat + 7) % 8) = 2 ^ ((x.toNat + $(Syntax.mkNumLit (toString k))) % 8))
  let (e1, _) ← withOpt `ved.mem.s94AddrNorm true (tryT (← ex 7) (← `(tactic| (intro x; ved_spell_unify))))
  let (e2, e2ok) ← withOpt `ved.mem.s94AddrNorm true (tryT (← ex 6) (← `(tactic| (intro x; ved_spell_unify; rfl))))
  if e2 then throwError "pow: a false statement was closed"
  -- read lift
  let rl (bad : Bool) : TermElabM Term :=
    if bad then `(∀ (f : BitVec 3 → BitVec 8) (p : Prop) [Decidable p] (a b : BitVec 3), (f (if p then a else b)).toNat = (f a).toNat)
    else `(∀ (f : BitVec 3 → BitVec 8) (p : Prop) [Decidable p] (a b : BitVec 3), (f (if p then a else b)).toNat = if p then (f a).toNat else (f b).toNat)
  let rlTac ← `(tactic| (intro f p _ a b; ved_read_lift; rfl))
  let (roff, _) ← withOpt `ved.mem.s94ReadLift false (tryT (← rl false) rlTac)
  if roff then throwError "lift: OFF: closed"
  let l0 ← Tools.VedMemS94Addr.liftHits.get
  let (ron, _) ← withOpt `ved.mem.s94ReadLift true (tryT (← rl false) rlTac)
  unless ron do throwError "lift: ON: not closed"
  unless (← Tools.VedMemS94Addr.liftHits.get) > l0 do throwError "lift: ON: counter"
  let (rbad, _) ← withOpt `ved.mem.s94ReadLift true (tryT (← rl true) rlTac)
  if rbad then throwError "lift: a false statement was closed"
  Tools.VedMemS94Addr.liftFailLate.set true
  let (rlate, _) ← withOpt `ved.mem.s94ReadLift true (tryT (← rl false) (← `(tactic| (intro f p _ a b; first | (ved_read_lift; rfl) | skip))))
  Tools.VedMemS94Addr.liftFailLate.set false
  if rlate then throwError "lift: late failure: the goal was closed"
  Tools.VedMemS94Addr.liftRefuse.set true
  let (rref, _) ← withOpt `ved.mem.s94ReadLift true (tryT (← rl false) rlTac)
  Tools.VedMemS94Addr.liftRefuse.set false
  if rref then throwError "lift: the refuse seam closed the goal"
  -- `|||` bounds
  let ob (m : Nat) : TermElabM Term := `(∀ (x y : BitVec 8), (x.toNat ||| y.toNat) % $(Syntax.mkNumLit (toString m)) = x.toNat ||| y.toNat)
  let obTac ← `(tactic| (intro x y; ved_or_bounds; omega))
  let (ooff, _) ← withOpt `ved.mem.s94OrDisj false (tryT (← ob 256) obTac)
  if ooff then throwError "or: OFF: closed"
  let o0 ← Tools.VedMemS94Addr.orHits.get
  let (oon, _) ← withOpt `ved.mem.s94OrDisj true (tryT (← ob 256) obTac)
  unless oon do throwError "or: ON: not closed"
  unless (← Tools.VedMemS94Addr.orHits.get) > o0 do throwError "or: ON: counter"
  let (obad, _) ← withOpt `ved.mem.s94OrDisj true (tryT (← ob 128) obTac)
  if obad then throwError "or: a false statement (% 128) was closed"
  Tools.VedMemS94Addr.orFailLate.set true
  let (olate, _) ← withOpt `ved.mem.s94OrDisj true (tryT (← ob 256) (← `(tactic| (intro x y; first | (ved_or_bounds; omega) | skip))))
  Tools.VedMemS94Addr.orFailLate.set false
  if olate then throwError "or: late failure: the goal was closed"
  Tools.VedMemS94Addr.orRefuse.set true
  let (oref, _) ← withOpt `ved.mem.s94OrDisj true (tryT (← ob 256) obTac)
  Tools.VedMemS94Addr.orRefuse.set false
  if oref then throwError "or: the refuse seam closed the goal"
  -- gates (`ved.mem.s94Gates`): off, every goal passes; on, a goal without a state variable / a variable power is refused
  let noPow ← `(∀ (x : Nat), x = x)
  let withPow ← `(∀ (x m : Nat), x % 2 ^ (m % 8) = x % 2 ^ (m % 8))
  let (g0, g0ok) ← withOpt `ved.mem.s94Gates false (tryT noPow (← `(tactic| (intro x; ved_pow_gate))))
  unless g0ok do throwError "gate: OFF: refused"
  let (_, g1ok) ← withOpt `ved.mem.s94Gates true (tryT noPow (← `(tactic| (intro x; ved_pow_gate))))
  if g1ok then throwError "gate: ON: a goal without a variable power passed"
  let (_, g2ok) ← withOpt `ved.mem.s94Gates true (tryT withPow (← `(tactic| (intro x m; ved_pow_gate))))
  unless g2ok do throwError "gate: ON: a goal with a variable power was refused"
  let (_, g3ok) ← withOpt `ved.mem.s94Gates true (tryT noPow (← `(tactic| (intro x; ved_state_cheap_gate))))
  if g3ok then throwError "gate: ON: a goal without a state variable passed"
  let skipped0 ← Tools.VedMemS94Local.gateSkipped.get
  let _ ← withOpt `ved.mem.s94Gates true (tryT noPow (← `(tactic| (intro x; ved_state_cheap_gate))))
  unless (← Tools.VedMemS94Local.gateSkipped.get) == skipped0 + 1 do throwError "gate: skipped counter"
  -- state split threshold (`ved.mem.s94StateMinConds`): two comparisons are enough for a split only with the option lowered
  let two ← `(∀ (s : BitVec 3) (x : Nat), x < 10 → (if s.toNat = 0 then x + 1 else if s.toNat = 1 then x else 0) % 16 = (if s.toNat = 0 then x + 1 else if s.toNat = 1 then x else 0))
  let (_, m4) ← withOpt `ved.mem.s94StateSplit true (tryT two (← `(tactic| (intro s x hx; ved_state_split))))
  if m4 then throwError "min conds: a split on two comparisons with the default threshold"
  let (_, m2) ← withOptions (fun os => (os.setBool `ved.mem.s94StateSplit true).insert `ved.mem.s94StateMinConds (DataValue.ofNat 2)) (tryT two (← `(tactic| (intro s x hx; ved_state_split))))
  unless m2 do throwError "min conds: no split on two comparisons with the threshold 2"
  -- the state attempt under the gates (the state variable is there, one branch is far below the branch limit): still closes, and a false statement is still refused
  let stG (m : Nat) : TermElabM Term := `(∀ (s : BitVec 3) (x : Nat), x < 10 →
    (if s.toNat = 0 then x + 1 else if s.toNat = 1 then x + 2 else if s.toNat = 2 then x else if s.toNat = 3 then 7 else if s.toNat = 4 then 9 else 0) % $(Syntax.mkNumLit (toString m)) =
    (if s.toNat = 0 then x + 1 else if s.toNat = 1 then x + 2 else if s.toNat = 2 then x else if s.toNat = 3 then 7 else if s.toNat = 4 then 9 else 0))
  let stGTac ← `(tactic| (intro s x hx; ved_local_close_state))
  let (gOn, _) ← withOptions (fun os => (os.setBool `ved.mem.s94StateSplit true).setBool `ved.mem.s94Gates true) (tryT (← stG 16) stGTac)
  unless gOn do throwError "gates: the state attempt did not close under the gates"
  let (gBad, _) ← withOptions (fun os => (os.setBool `ved.mem.s94StateSplit true).setBool `ved.mem.s94Gates true) (tryT (← stG 8) stGTac)
  if gBad then throwError "gates: a false statement was closed under the gates"
  logInfo m!"addr_unify / pow_unify / read_lift / or_bounds / gates controls: OFF refused, ON closes (counters), a false statement is refused, late failure restores the goal, the refuse seam refuses"

/-! ### s94y: the once-proved address pair (`ved.mem.s94PairLemma`) and the pairing of the invariant (`ved.mem.s94PairFix`) -/

set_option ved.mem.s94PairLemma true in
/-- the pair of R033 goals 33 / 34 (branch ck156 = 6): `ved_bv_addr_eq` with the option closes it by `addr_borrow_6` (kernel-checked) -/
theorem pair_lemma_ok (a d e : BitVec 5) :
    BitVec.ofNat 6 (((a.toNat + 31) % 32 * 7 + (d.toNat + (32 - e.toNat) + 31) % 32) % 64) =
      7#6 * BitVec.extractLsb' 0 6 (a - 1#5) + BitVec.extractLsb' 0 6 (d - e - 1#5) := by
  ved_bv_addr_eq

/-- info: pair lemma controls: under the pair limit (1.5M heartbeats) OFF fails (omega), ON closes (the lemma, both orientations), a false pair is refused, the zext pair still closes with the option on -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryCap (cap : Nat) (stmt : Term) (tac : TSyntax `tactic) : TermElabM Bool := do
    let ty ← elabTerm stmt none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let mv ← mkFreshExprMVar ty
    let hb0 ← IO.getNumHeartbeats
    tryCatchRuntimeEx
      (do
        let gs ← withTheReader Core.Context (fun c => { c with maxHeartbeats := cap, initHeartbeats := hb0 }) do
          Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
        pure gs.isEmpty)
      (fun _ => pure false)
  let withOpt (v : Bool) (x : TermElabM Bool) : TermElabM Bool := withOptions (fun os => os.setBool `ved.mem.s94PairLemma v) x
  let pr (k : Nat) (swap : Bool) : TermElabM Term := do
    let n : Term := ⟨Syntax.mkNumLit (toString k)⟩
    if swap then `(∀ (a d e : BitVec 5), BitVec.ofNat 6 ($n) * BitVec.extractLsb' 0 6 (a - 1#5) + BitVec.extractLsb' 0 6 (d - e - 1#5) =
      BitVec.ofNat 6 (((a.toNat + 31) % 32 * 7 + (d.toNat + (32 - e.toNat) + 31) % 32) % 64))
    else `(∀ (a d e : BitVec 5), BitVec.ofNat 6 (((a.toNat + 31) % 32 * 7 + (d.toNat + (32 - e.toNat) + 31) % 32) % 64) =
      BitVec.ofNat 6 ($n) * BitVec.extractLsb' 0 6 (a - 1#5) + BitVec.extractLsb' 0 6 (d - e - 1#5))
  let tac ← `(tactic| (intro a d e; have := a.isLt; have := d.isLt; have := e.isLt; ved_bv_addr_eq))
  let cap := 1500000
  if ← withOpt false (tryCap cap (← pr 7 false) tac) then throwError "pair lemma: OFF closed under the pair limit (the control measures nothing)"
  unless ← withOpt true (tryCap cap (← pr 7 false) tac) do throwError "pair lemma: ON did not close the pair under the pair limit"
  unless ← withOpt true (tryCap cap (← pr 7 true) tac) do throwError "pair lemma: ON did not close the swapped pair under the pair limit"
  if ← withOpt true (tryCap 12000000 (← pr 6 false) tac) then throwError "pair lemma: a false pair (6#6 * ..) was closed"
  -- the other pair of the family still closes with the option on (the lemma does not apply, `first` falls through to the general proof)
  let zx ← `(∀ (c : BitVec 2) (a : BitVec 5) (b : BitVec 3), BitVec.ofNat 9 ((c.toNat * 68 + a.toNat * 4 + b.toNat) % 512) = 68#9 * (0#7 ++ c) + 4#9 * (0#4 ++ a) + (0#6 ++ b))
  unless ← withOpt true (tryCap 12000000 zx (← `(tactic| (intro c a b; have := c.isLt; have := a.isLt; have := b.isLt; ved_bv_addr_eq)))) do
    throwError "pair lemma: the zext pair did not close with the option on"
  logInfo m!"pair lemma controls: under the pair limit (1.5M heartbeats) OFF fails (omega), ON closes (the lemma, both orientations), a false pair is refused, the zext pair still closes with the option on"

declare_signal_state PairState
  | ra   : BitVec 2  := 0#2
  | rb   : BitVec 2  := 0#2
  | rc   : BitVec 2  := 0#2
  | idx  : BitVec 5  := 0#5
  | last : BitVec 16 := 0#16

set_option Elab.async false in
/-- the registers `ra` and `rc` are the same constant register (the synthesizer builds ONE register for them, 4 registers for 5 components), `rb` another 2-bit register: the old pairing
gives `rc` to the most recent taken 2-bit register (`rb`'s) and the invariant says `rb = 0` at every cycle -/
def pairFsm {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let rb := PairState.rb state
    let idx := PairState.idx state
    let isProcess := rb === (1#2 : Signal dom _)
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let outMemRead := Signal.memory readAddr4 inputCoeff isProcess (Signal.pure 0#4)
    let rbNext := Signal.mux start (Signal.pure 1#2) (Signal.mux (idx === (15#5 : Signal dom _)) (Signal.pure 0#2) rb)
    let idxNext := Signal.mux isProcess (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#2 (Signal.pure 0#2), Signal.register 0#2 rbNext, Signal.register 0#2 (Signal.pure 0#2),
      Signal.register 0#5 idxNext, Signal.register 0#16 outMemRead]
  PairState.last state

-- option ON: accepted (the constant register is paired with the register of the same hardware), the theorem is stored
#guard_msgs (drop info) in
set_option Elab.async false in
set_option ved.mem.s94PairFix true in
#ved_u1_mem pairFsm

set_option Elab.async false in
/-- the same design under another name (each accepted run stores a theorem under the declaration's name) -/
def pairFsmB {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) := pairFsm start writeEn writeAddr writeData

-- option OFF: refused at `[proof]` (the invariant of the old pairing is false); nothing is stored
#guard_msgs (drop all) in
set_option Elab.async false in
set_option ved.mem.s94PairFix false in
#ved_u1_mem pairFsmB

/-- info: pair fix controls: ON accepted (theorem stored, one component re-paired), OFF refused (nothing stored) -/
#guard_msgs in
run_cmd do
  unless (← getEnv).contains `Tests.Ved.VedMemLocalCheck.pairFsm.ved_mem do throwError "pair fix: ON: no theorem stored"
  unless (← Tools.VedMemS94Inv.pairFixCount.get) == 1 do throwError "pair fix: ON: expected one re-paired component, got {← Tools.VedMemS94Inv.pairFixCount.get}"
  if (← getEnv).contains `Tests.Ved.VedMemLocalCheck.pairFsmB.ved_mem then throwError "pair fix: OFF: the entry accepted the design with the wrong pairing"
  logInfo m!"pair fix controls: ON accepted (theorem stored, one component re-paired), OFF refused (nothing stored)"

/-! ### s94aa: `rewriteAll` (the bug), `ved.mem.s94PairCache`, `ved.mem.s94BitArgs`, `ved.mem.s94PairCtx`, `ved_orb_mod`, `ved.mem.s94CondSplit`, `ved.mem.s94StateSplit2`, `ved.mem.s94CondAbsurd` -/

/-- the `rewriteAll` of 91d04a03 (before the fix), kept here as the control of the bug: the hypotheses are visited by the identifiers of one snapshot of the context and the proof `h` is used as given, while
`replaceLocalDecl` re-introduces every later hypothesis with a new identifier -/
def oldRewriteAll (g : MVarId) (a b h : Expr) : MetaM (MVarId × Nat) := do
  let aTy ← g.withContext (inferType a)
  let rw (T : Expr) : MetaM (Option (Expr × Expr)) := do
    if (T.find? (· == a)).isNone then return none
    withLocalDeclD `ved_x aTy fun x => do
      let Tabs := T.replace fun e => if e == a then some x else none
      let motive ← mkLambdaFVars #[x] Tabs
      let T' := Tabs.replaceFVar x b
      let pf ← mkExpectedTypeHint (← mkAppM ``congrArg #[motive, h]) (← mkEq T T')
      return some (T', pf)
  let mut g := g
  let mut n := 0
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let t ← instantiateMVars d.type
    unless (← g.withContext (isProp t)) do continue
    if let some (t', pf) ← g.withContext (rw t) then
      let r ← g.replaceLocalDecl d.fvarId t' pf
      g := r.mvarId
      n := n + 1
  let tgt ← instantiateMVars (← g.getType)
  if let some (t', pf) ← g.withContext (rw tgt) then
    g ← g.replaceTargetEq t' pf
    n := n + 1
  return (g, n)

set_option ved.mem.s94AddrNorm true in
/-- kernel-checked: two hypotheses and the target carry the later spelling of one exponent (`rewriteAll` replaces it in all three; the old code threw `unknown free variable` at the second hypothesis) -/
theorem unify_two_hyps_ok (x : BitVec 3) (h1 : 2 ^ ((x.toNat + 7) % 8) ≤ 200) (h2 : 2 ^ ((7 + x.toNat) % 8) ≤ 300)
    (h3 : 2 ^ ((7 + x.toNat) % 8) ≥ 1) : 2 ^ ((7 + x.toNat) % 8) ≤ 200 := by
  ved_spell_unify
  exact h1

set_option ved.mem.s94OrDisj true in
/-- kernel-checked: `ved_orb_mod` rewrites `(x ||| y) % 256` by the bound `ved_or_bounds` proved (no discharger) and `simp only` closes the equation -/
theorem orb_mod_ok (x y : BitVec 8) : (x.toNat ||| y.toNat) % 256 = x.toNat ||| y.toNat := by
  ved_or_bounds
  ved_orb_mod

/-- info: s94aa controls: rewriteAll (old code loses its work on two hypotheses, new code keeps it, no change when the term does not occur), PairCache (hit counter, OFF no hit), BitArgs / PairCtx (ON closes, OFF refused, false refused), ved_orb_mod, CondSplit (ON closes, OFF refused, false refused, a closed condition is evaluated not split), StateSplit2 (counter), CondAbsurd (ON closes a contradiction, OFF refused, consistent hypotheses refused) -/
#guard_msgs in
run_cmd liftTermElabM do
  let tryT (stmt : Term) (tac : TSyntax `tactic) : TermElabM (Bool × Bool) := do
    let ty ← elabTerm stmt none
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let mv ← mkFreshExprMVar ty
    try
      let gs ← Tactic.run mv.mvarId! (do Tactic.withoutRecover (Tactic.evalTactic tac))
      pure (gs.isEmpty, true)
    catch _ => pure (false, false)
  let withOpts (os : List (Name × Bool)) (x : TermElabM (Bool × Bool)) : TermElabM (Bool × Bool) :=
    withOptions (fun o => os.foldl (fun o (n, v) => o.setBool n v) o) x
  -- 1. rewriteAll: the old code throws on two hypotheses that carry the term, the new one replaces it in both and in the target; nothing occurs: the goal is returned untouched
  let ty ← elabTerm (← `(∀ (x : BitVec 3), 2 ^ ((x.toNat + 7) % 8) ≤ 200 → 2 ^ ((7 + x.toNat) % 8) ≤ 300 → 2 ^ ((7 + x.toNat) % 8) ≥ 1 → 2 ^ ((7 + x.toNat) % 8) ≤ 200)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let mkCase : TermElabM (MVarId × Expr × Expr × Expr) := do
    let mv ← mkFreshExprMVar ty
    let (_, g) ← mv.mvarId!.introN 4 [`x, `h1, `h2, `h3]
    g.withContext do
      -- the two spellings are read off the hypotheses `h1 : a ≤ 200`, `h2 : b ≤ 300`
      let hTy (n : Name) : MetaM Expr := do
        let some d := (← getLCtx).findFromUserName? n | throwError "{n}"
        instantiateMVars d.type
      let a := (← hTy `h1).getArg! 2
      let b := (← hTy `h2).getArg! 2
      let eq ← mkEq b a
      let h ← mkFreshExprMVar eq
      let gs ← Tactic.run h.mvarId! (Tactic.evalTactic (← `(tactic| simp only [Nat.add_comm])))
      unless gs.isEmpty do throwError "rewriteAll control: the equation of the two spellings was not proved"
      pure (g, b, a, ← instantiateMVars h)
  let lbl {α} (nm : String) (x : TermElabM α) : TermElabM α := try x catch e => throwError "{nm}: {e.toMessageData}"
  let (g0, b0, a0, h0) ← lbl "mkCase0" mkCase
  let oldRes ← try let _ ← (oldRewriteAll g0 b0 a0 h0).run'; pure true catch _ => pure false
  if oldRes then throwError "rewriteAll control: the OLD code did not lose its work on two hypotheses (the control measures nothing)"
  let (g1, b1, a1, h1) ← lbl "mkCase1" mkCase
  let (g1', k1) ← lbl "new rewriteAll" (Tools.VedMemS94Addr.rewriteAll g1 b1 a1 h1)
  unless k1 == 3 do throwError "rewriteAll control: expected 3 propositions replaced (2 hypotheses and the target), got {k1}"
  let (g2, _, _, _) ← lbl "mkCase2" mkCase
  let (e2, r2) ← g2.withContext do
    let c ← elabTerm (← `($(mkIdent `x))) none
    let e ← mkAppM ``Nat.succ #[← mkAppM ``BitVec.toNat #[c]]
    pure (e, ← mkEqRefl e)
  let (g2', k2) ← Tools.VedMemS94Addr.rewriteAll g2 e2 e2 r2
  unless k2 == 0 && g2' == g2 do throwError "rewriteAll control: a term that does not occur changed the goal (k = {k2})"
  -- 2. PairCache: two goals of one context carry the same pair: the second proof is the first one (hit counter); OFF: no hit
  let pcS ← `(∀ (x : BitVec 3), 2 ^ ((x.toNat + 7) % 8) = 2 ^ ((7 + x.toNat) % 8) ∧ 2 ^ ((x.toNat + 7) % 8) = 2 ^ ((7 + x.toNat) % 8))
  let pcT ← `(tactic| (intro x; constructor; all_goals (ved_spell_unify; rfl)))
  let pc (v : Bool) : TermElabM (Bool × Bool) := withOpts [(`ved.mem.s94AddrNorm, true), (`ved.mem.s94PairCache, v)] (tryT pcS pcT)
  let n0 ← Tools.VedMemS94Addr.pairCacheHits.get
  let (pOff, _) ← pc false
  unless pOff do throwError "pair cache: OFF: not closed"
  unless (← Tools.VedMemS94Addr.pairCacheHits.get) == n0 do throwError "pair cache: OFF: a hit"
  let (pOn, _) ← pc true
  unless pOn do throwError "pair cache: ON: not closed"
  unless (← Tools.VedMemS94Addr.pairCacheHits.get) == n0 + 1 do throwError "pair cache: ON: expected one hit"
  -- 3. BitArgs / PairCtx: the arguments of `|||` that are two spellings of one number
  let ba (k : Nat) : TermElabM Term := `(∀ (a : Nat), ((a + 3) % 8 ||| 1) = ((3 + a + $(Syntax.mkNumLit (toString k))) % 8 ||| 1))
  let baTac ← `(tactic| (intro a; ved_spell_unify; rfl))
  let (bOff, _) ← withOpts [(`ved.mem.s94AddrNorm, true), (`ved.mem.s94BitArgs, false)] (tryT (← ba 0) baTac)
  if bOff then throwError "bit args: OFF closed"
  let (bOn, _) ← withOpts [(`ved.mem.s94AddrNorm, true), (`ved.mem.s94BitArgs, true)] (tryT (← ba 0) baTac)
  unless bOn do throwError "bit args: ON not closed"
  let (bCtx, _) ← withOpts [(`ved.mem.s94AddrNorm, true), (`ved.mem.s94BitArgs, true), (`ved.mem.s94PairCtx, true)] (tryT (← ba 0) baTac)
  unless bCtx do throwError "pair ctx: ON not closed"
  let (bBad, _) ← withOpts [(`ved.mem.s94AddrNorm, true), (`ved.mem.s94BitArgs, true), (`ved.mem.s94PairCtx, true)] (tryT (← ba 1) baTac)
  if bBad then throwError "bit args: a false statement was closed"
  -- 4. CondSplit: the conditions are decided one at a time
  let cs (k : Nat) : TermElabM Term := `(∀ (x : Nat), x < 4 → ((if x = 0 then 1 else 2) + (if x = 0 then 3 else 4)) = (if x = 0 then 4 else $(Syntax.mkNumLit (toString k))))
  let csTac ← `(tactic| (intro x hx; ved_cond_split 4))
  let (cOff, _) ← withOpts [(`ved.mem.s94CondSplit, false)] (tryT (← cs 6) csTac)
  if cOff then throwError "cond split: OFF closed"
  let sp0 ← Tools.VedMemS94Local.condSplits.get
  let (cOn, _) ← withOpts [(`ved.mem.s94CondSplit, true)] (tryT (← cs 6) csTac)
  unless cOn do throwError "cond split: ON not closed"
  unless (← Tools.VedMemS94Local.condSplits.get) == sp0 + 1 do throwError "cond split: expected one split"
  let (cBad, _) ← withOpts [(`ved.mem.s94CondSplit, true)] (tryT (← cs 7) csTac)
  if cBad then throwError "cond split: a false statement was closed"
  -- a closed condition is evaluated, not split (the false branch of `(1 ^^^ 1) % 2 = 0`... is decided by `decide`)
  let sp1 ← Tools.VedMemS94Local.condSplits.get
  let (gOn, _) ← withOpts [(`ved.mem.s94CondSplit, true)] (tryT (← `(∀ (x : Nat), (if (1 ^^^ 1) % 2 = 0 then x else x + 1) = x)) (← `(tactic| (intro x; ved_cond_split 4))))
  unless gOn do throwError "cond split: a closed condition: not closed"
  unless (← Tools.VedMemS94Local.condSplits.get) == sp1 do throwError "cond split: a closed condition was split"
  -- 5. StateSplit2: a second split on a variable with one comparison (counter), refused when the option is off
  let ss2 ← `(∀ (x : BitVec 2), (if x.toNat = 1 then 5 else 6) ≤ 6)
  let ssTac ← `(tactic| (intro x; ved_state_split2; all_goals simp))
  let (sOff, _) ← withOpts [(`ved.mem.s94StateSplit2, false)] (tryT ss2 ssTac)
  if sOff then throwError "state split 2: OFF closed"
  let ns0 ← Tools.VedMemS94Local.nestedSplits.get
  let (sOn, _) ← withOpts [(`ved.mem.s94StateSplit2, true)] (tryT ss2 ssTac)
  unless sOn do throwError "state split 2: ON not closed"
  unless (← Tools.VedMemS94Local.nestedSplits.get) == ns0 + 1 do throwError "state split 2: counter"
  -- 6. CondAbsurd: contradictory case hypotheses close any goal; consistent ones do not
  let hcI := mkIdent `ved_hc
  let ab (stmt : Term) (tac : TSyntax `tactic) (v : Bool) : TermElabM (Bool × Bool) := withOpts [(`ved.mem.s94CondAbsurd, v)] (tryT stmt tac)
  let abTac ← `(tactic| (intro x $hcI:ident $hcI:ident; ved_hc_absurd))
  let abS ← `(∀ (x : Nat), x % 8 = 3 → x % 8 = 4 → 1 = 2)
  let (aOff, _) ← ab abS abTac false
  if aOff then throwError "cond absurd: OFF closed"
  let (aOn, _) ← ab abS abTac true
  unless aOn do throwError "cond absurd: ON not closed"
  let (aBad, _) ← ab (← `(∀ (x : Nat), x % 8 = 3 → x % 8 ≤ 4 → 1 = 2)) abTac true
  if aBad then throwError "cond absurd: consistent hypotheses closed a false goal"
  logInfo m!"s94aa controls: rewriteAll (old code loses its work on two hypotheses, new code keeps it, no change when the term does not occur), PairCache (hit counter, OFF no hit), BitArgs / PairCtx (ON closes, OFF refused, false refused), ved_orb_mod, CondSplit (ON closes, OFF refused, false refused, a closed condition is evaluated not split), StateSplit2 (counter), CondAbsurd (ON closes a contradiction, OFF refused, consistent hypotheses refused)"

end Tests.Ved.VedMemLocalCheck
