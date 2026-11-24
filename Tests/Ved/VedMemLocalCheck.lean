import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedMemLoop
import Tools.VedMemS94Gen
import Tools.VedMemS94Local
import Tools.VedMemS94Opaque

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

end Tests.Ved.VedMemLocalCheck
