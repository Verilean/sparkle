import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedMemPack

/-!
# The process-global caches of the VED closing tactics are scoped (follow-up of the per-call leaf-failure flag)

Five global `IO.Ref`s can change or break the proof of one declaration through a value another declaration wrote (under `Elab.async`, or in a file
with several entries).  Each control below forces the hazard deterministically (it does not rely on declarations really overlapping):

* `proofCache` (`proveRead`): seeded with a proof that mentions a constant absent from the environment (an auxiliary `_proof_N` of another
  declaration); the hit must be refused and a fresh proof (kernel-checked) used.
* `vedOmegaOk` (`ved_omega_c`): the same seed.
* `vedOmegaFail`: a resource-limit failure (`ved_omega` turns the runtime exception into an ordinary failure; forced here with a recursion limit just above the current depth) must not be cached; the next call with the normal
  budget proves the goal.
* `declWidthTab`: filled per module and never erased; the table of module A is the same after a real entry for module B ran.
* `hnormLoops` / `hstepAttempted`: keyed by `ved.mem.runId`; two run keys are interleaved and neither sees (or clears) the other's value.

Positive controls: two real packed entries (one with `ved.mem.hstepNorm` on, which uses the table and the loops, one with it off) are accepted and
their stored proofs have the depth, node count and axioms recorded from the code before the change.
-/

namespace Tests.Ved.VedSharedRefsCheck

open Lean Elab Command Term Meta Tactic
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.StateMacro
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedMemEntry

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `proofCache` -/

/-- the cached `ved_omega_c` of `VedU1ScriptSeqGen` (the memory stage's uncached one is `ved_omega_mc` of `VedMemPack`; they used to share the name, both parsed, and the uncached one ran) -/
def runOmegaC : TacticM Unit := do
  evalTactic (← `(tactic| ved_omega_c))

/-- the fake auxiliary constant that is not in the environment -/
def fakeName : Name := `SrFake.missing_proof_1

/-- seed `proofCache` for the main goal `S = F` with a proof that mentions an absent constant, then `proveRead`: the hit must be refused -/
elab "sr_proofcache" : tactic => withMainContext do
  let some (_, S, F) := (← instantiateMVars (← getMainTarget)).eq? | throwError "not an equation"
  let eq ← mkEq S F
  let fvs ← Tools.VedMemPack.closure eq
  let closed ← mkForallFVars fvs eq
  Tools.VedMemPack.proofCache.set {}
  Tools.VedMemPack.proofCache.modify (·.insert closed (some (mkConst fakeName)))
  let some p ← Tools.VedMemPack.proveRead S F | throwError "proveRead: no proof"
  if p.getUsedConstants.contains fakeName then throwError "proofCache: a hit returned a proof that mentions an absent constant"
  -- the fresh proof replaced the seed
  match (← Tools.VedMemPack.proofCache.get)[closed]? with
  | some (some q) => if q.getUsedConstants.contains fakeName then throwError "proofCache: the seed is still stored"
  | _ => throwError "proofCache: no fresh proof stored"
  Tools.VedMemPack.proofCache.set {}
  (← getMainGoal).assign p

example (x : Nat) : x + 0 = x := by sr_proofcache

/-! ## `vedOmegaOk` -/

/-- the name `ved_omega_c` parses to the cached tactic only (no choice node with the memory stage's one) and the memory-stage tactic has its own name -/
elab "sr_omega_names" : tactic => do
  let stx ← `(tactic| ved_omega_c)
  unless stx.raw.isOfKind `Tools.VedU1ScriptSeq.tacticVed_omega_c do
    throwError "ved_omega_c parses to {stx.raw.getKind} (alternatives: {stx.raw.getArgs.map (·.getKind)}), expected the cached tactic only"
  let m ← `(tactic| ved_omega_mc)
  unless m.raw.isOfKind `Tools.VedMemPack.tacticVed_omega_mc do throwError "ved_omega_mc parses to {m.raw.getKind}"

/-- the cached tactic called by its name fills `vedOmegaOk` -/
elab "sr_omega_fill" : tactic => do
  evalTactic (← `(tactic| ved_omega_c_reset))
  evalTactic (← `(tactic| ved_omega_c))
  if (← Tools.VedU1ScriptSeq.vedOmegaOk.get).isEmpty then throwError "ved_omega_c did not fill vedOmegaOk"
  evalTactic (← `(tactic| ved_omega_c_reset))

/-- the memory-stage tactic (`ved_omega_mc`) is uncached -/
elab "sr_omega_mc_uncached" : tactic => do
  evalTactic (← `(tactic| ved_omega_c_reset))
  evalTactic (← `(tactic| ved_omega_mc))
  unless (← Tools.VedU1ScriptSeq.vedOmegaOk.get).isEmpty do throwError "ved_omega_mc filled vedOmegaOk"

example (x y : Nat) (h : x < 8) : x + y < y + 8 := by sr_omega_names; sr_omega_fill
example (x y : Nat) (h : x < 8) : x + y < y + 8 := by sr_omega_mc_uncached

/-- the memory-stage `ved_omega_s` runs the uncached tactic: `vedOmegaOk` stays empty -/
elab "sr_omega_s_uncached" : tactic => do
  evalTactic (← `(tactic| ved_omega_c_reset))
  evalTactic (← `(tactic| ved_omega_s))
  unless (← Tools.VedU1ScriptSeq.vedOmegaOk.get).isEmpty do throwError "ved_omega_s ran the cached tactic"

example (x y : Nat) (h : x < 8) : x + y < y + 8 := by sr_omega_s_uncached

/-- seed `vedOmegaOk` for the main goal with a proof of an absent constant: `ved_omega_c` must not use it -/
elab "sr_omegaok" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  evalTactic (← `(tactic| ved_omega_c_reset))
  Tools.VedU1ScriptSeq.vedOmegaOk.modify (·.insert tgt (mkConst fakeName, #[]))
  runOmegaC
  let v ← instantiateMVars (mkMVar g)
  if v.getUsedConstants.contains fakeName then throwError "vedOmegaOk: a hit used a proof that mentions an absent constant"
  evalTactic (← `(tactic| ved_omega_c_reset))

example (x y : Nat) (h : x < 8) : x + y < y + 8 := by sr_omegaok

/-! ## `vedOmegaFail` -/

/-- `ved_omega_c` under a recursion limit just above the current depth fails with `ved_omega`'s budget message (it turns the runtime exception into an ordinary failure); nothing
is cached, and the next call with the normal limit proves the goal -/
elab "sr_omegafail" : tactic => withMainContext do
  evalTactic (← `(tactic| ved_omega_c_reset))
  let failed ← try
      withTheReader Core.Context (fun c => { c with maxRecDepth := c.currRecDepth + 4 }) do
        runOmegaC
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match failed with
  | none => throwError "vedOmegaFail: the run under the recursion limit succeeded (vacuous control)"
  | some m => unless m.startsWith "ved_omega: no proof within the budget" do throwError "vedOmegaFail: other failure (vacuous control): {m}"
  unless (← Tools.VedU1ScriptSeq.vedOmegaFail.get).isEmpty do throwError "vedOmegaFail: a resource-limit failure was cached"
  runOmegaC

example (x y z : Nat) (h : x < 8) (h2 : y < x + z) : x + y < z + 16 := by sr_omegafail

/-! ## `hnormLoops` / `hstepAttempted`: two run keys interleaved -/

/-- the loops stored for run `n`: their number -/
def loopsOf (n : Nat) : IO (Option Nat) := return ((← Tools.VedMemLoop.hnormLoops.get)[n]?).map (·.size)

elab "sr_expect_loops " n:num k:num : tactic => do
  let got ← loopsOf n.getNat
  unless got == some k.getNat do throwError "hnormLoops[{n.getNat}] = {got}, expected {some k.getNat}"

elab "sr_expect_no_loops " n:num : tactic => do
  unless (← loopsOf n.getNat) == none do throwError "hnormLoops[{n.getNat}] is set"

/-- the loop of run 1 and the loop of run 2 differ in their state type: the stored arrays must too -/
elab "sr_expect_loops_differ " : tactic => do
  let m ← Tools.VedMemLoop.hnormLoops.get
  let some a := m[1]? | throwError "run 1 has no loops"
  let some b := m[2]? | throwError "run 2 has no loops"
  if a == b then throwError "run 1 and run 2 loops are equal"

example (d : DomainConfig) :
    (∀ _ : Signal.loop (dom := d) (fun s : Signal d (BitVec 2) => s) = Signal.loop (fun s : Signal d (BitVec 2) => s), True) ∧
    (∀ _ : Signal.loop (dom := d) (fun s : Signal d (BitVec 3) => s) = Signal.loop (fun s : Signal d (BitVec 3) => s), True ∧ True) := by
  refine ⟨?a, ?b⟩
  · intro h
    (set_option ved.mem.runId 1 in ved_hstep_loops)
    sr_expect_loops 1 1
    sr_expect_no_loops 2
    trivial
  · intro h
    (set_option ved.mem.runId 2 in ved_hstep_loops)
    sr_expect_loops 1 1
    sr_expect_loops 2 1
    sr_expect_loops_differ
    -- clearing run 1 leaves run 2
    (set_option ved.mem.runId 1 in ved_hstep_loops_clear)
    sr_expect_no_loops 1
    sr_expect_loops 2 1
    (set_option ved.mem.runId 2 in ved_hstep_loops_clear)
    sr_expect_no_loops 2
    exact ⟨trivial, trivial⟩

/-- the fallback reset of run 2 does not empty the caches while only run 1's new branch started; run 1's does -/
elab "sr_marker_set" : tactic => do
  Tools.VedMemPack.proofCache.modify (·.insert (mkConst `SrMarker) none)

elab "sr_marker_clear" : tactic => Tools.VedMemPack.proofCache.set {}

elab "sr_marker_expect " b:ident : tactic => do
  let has := (← Tools.VedMemPack.proofCache.get).contains (mkConst `SrMarker)
  unless has == (b.getId == `true) do throwError "proofCache marker present: {has}"

example : True ∧ True := by
  sr_marker_set
  (set_option ved.mem.hstepNorm true in set_option ved.mem.runId 1 in ved_hstep_norm_on)
  (set_option ved.mem.runId 2 in ved_hstep_fallback_reset)
  sr_marker_expect true
  (set_option ved.mem.runId 1 in ved_hstep_fallback_reset)
  sr_marker_expect false
  -- the flag of run 1 was consumed
  sr_marker_set
  (set_option ved.mem.runId 1 in ved_hstep_fallback_reset)
  sr_marker_expect true
  sr_marker_clear
  exact ⟨trivial, trivial⟩

/-! ## Real entries -/

declare_signal_state SState
  | fsm  : BitVec 2  := 0#2
  | sub  : BitVec 3  := 0#3
  | last : BitVec 16 := 0#16

/-- control fields and a 16-bit data addition (the shape of `hsA` of `VedMemCloseCheck`): runs with `ved.mem.hstepNorm` on -/
def srA {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) :=
  let state := Signal.loop fun state =>
    let fsm := SState.fsm state
    let sub := SState.sub state
    let isRow := fsm === (1#2 : Signal dom _)
    let sub4 := 0#1 ++ sub
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn sub4
    let fsmNext := Signal.mux start (Signal.pure 1#2) fsm
    let subNext := sub + 1#3
    let lastNext := Signal.mux isRow (inputCoeff + 1#16) (SState.last state)
    bundleAll! [Signal.register 0#2 fsmNext, Signal.register 0#3 subNext, Signal.register 0#16 lastNext]
  bundle2 (SState.last state) (SState.sub state)

/-- the same body, hstepNorm off (the closing script of the packed entry) -/
def srB {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16 × BitVec 3) := srA start writeEn writeAddr writeData

/-- depth, node count and axioms of the stored proof term -/
def entrySummary (decl : Name) : TermElabM String := do
  let ti ← getConstInfo (decl ++ `ved_mem)
  let .thmInfo t := ti | throwError "not a theorem"
  let v := t.value
  let axs ← collectAxioms (decl ++ `ved_mem)
  return s!"depth {v.approxDepth} nodes {v.sizeWithoutSharing} axioms {axs.toList.map (·.toString) |>.toArray.qsort (· < ·)}"

/-- depth, node count and axioms of the stored proofs, recorded on the code before the change (a28a4811) -/
def srASummary : String := "depth 192 nodes 83957056 axioms #[Classical.choice, Quot.sound, propext]"
def srBSummary : String := "depth 255 nodes 70110284 axioms #[Classical.choice, Quot.sound, propext]"

/-- the entry's module constant (what `declWidthTab` is keyed by) -/
def srModA : Name := `Tests.Ved.VedSharedRefsCheck.srA.ved_mod

-- the table of another module is in `declWidthTab` before the entry runs; it must be the same afterwards (the entry puts its own table next to it)
run_cmd do
  Tools.VedMemLoop.declWidthTab.modify (·.insert `SrOther.ved_mod (({} : Std.HashMap String Nat).insert "w" 7))

#guard_msgs (drop info) in
set_option ved.mem.hstepNorm true in
#ved_u1_mem_packed srA

run_cmd liftTermElabM do
  let tabs ← Tools.VedMemLoop.declWidthTab.get
  let some o := tabs[`SrOther.ved_mod]? | throwError "declWidthTab: the table of another module was removed"
  unless o.toList == [("w", 7)] do throwError "declWidthTab: the table of another module changed"
  let some mine := tabs[srModA]? | throwError "declWidthTab: no table for the entry's module (the module is erased)"
  unless mine.size > 0 do throwError "declWidthTab: empty table for the entry's module"
  unless (← Tools.VedMemLoop.hnormLoops.get).isEmpty do throwError "hnormLoops: the run was not erased"
  unless (← Tools.VedMemLoop.hstepAttempted.get).isEmpty do throwError "hstepAttempted: the run was not erased"
  let a ← entrySummary ``srA
  logInfo m!"SUMMARY srA {a}"
  unless a == srASummary do throwError "srA: the stored proof differs from the one before the change: {a}"
  logInfo m!"caches after srA: proofCache {(← Tools.VedMemPack.proofCache.get).size} omegaOk {(← Tools.VedU1ScriptSeq.vedOmegaOk.get).size}"

#guard_msgs (drop info) in
#ved_u1_mem_packed srB

run_cmd liftTermElabM do
  let b ← entrySummary ``srB
  logInfo m!"SUMMARY srB {b}"
  unless b == srBSummary do throwError "srB: the stored proof differs from the one before the change: {b}"
  logInfo m!"caches after srB: proofCache {(← Tools.VedMemPack.proofCache.get).size} omegaOk {(← Tools.VedU1ScriptSeq.vedOmegaOk.get).size}"

end Tests.Ved.VedSharedRefsCheck
