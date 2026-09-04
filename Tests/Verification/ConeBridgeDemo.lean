/-
  Per-instance instantiation of the SEAM (Tools/ConeFold*.lean) — the
  first machine-checked link between Arc 1's generated recurrence and
  Arc 2's fold semantics, demonstrated on `cnt8`.

  `#verify_elab cnt8` emits (Tests/Verification/VerifyElabDemo.lean):
  * `cnt8_irTrace` — the register recurrence, whose step evaluates the
    register's RESOLVED INLINED cone in the seed environment;
  * `cnt8_body` / `cnt8_stopAtM` / `cnt8_wtM` / `cnt8_coneRaw_*` — the
    topo-sorted module body, stop set, width table and raw cone as
    object constants.

  `cnt8_step_agrees` below proves: that cone evaluation equals the
  value the module-level combinational fold (`evalAssigns`, Arc 2's
  `stepModule` phase 1) assigns to the register's input wire — i.e.
  the generated recurrence steps exactly like the certified module
  semantics.  Every hypothesis of the bridge capstone
  (`cone_resolved_agrees_at_seed`) is discharged per instance:
  the decidable checkers by `native_decide` (they scan HashMaps, whose
  hashing cannot kernel-reduce), seed-boundedness by the generated
  `cnt8_irTrace_bound`.

  Run: `lake env lean Tests/Verification/ConeBridgeDemo.lean`
-/
import Tests.Verification.VerifyElabDemo
import Tools.ConeFoldSlices

namespace Sparkle.Tests.ConeBridgeDemo

open Sparkle.IR.Semantics Sparkle.IR.Reorder Tools.ConeFold
open Sparkle.Tests.VerifyElabDemo
open Sparkle.IR.Optimize (buildDefMap)

/-- The seed environment `cnt8_irTrace`'s step evaluates cones in is
    width-bounded: the register component by the generated trace bound,
    everything else is 0. -/
theorem cnt8_seed_bounded (t : Nat) :
    ∀ n, cnt8_envAt (cnt8_irTrace t) t n < 2 ^ cnt8_weM n := by
  intro n
  simp only [cnt8_envAt]
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    subst h
    have hb := cnt8_irTrace_bound t
    simpa [cnt8_weM] using hb
  · exact Nat.two_pow_pos _

/-- THE SEAM, per instance: the register-cone evaluation performed by
    `cnt8_irTrace`'s step equals the value the combinational fold
    assigns to the register's input wire. -/
theorem cnt8_step_agrees (t : Nat) {env1 : Env}
    (hrun : evalAssigns cnt8_weM (fun _ _ => 0) _root_.cnt8_body
      (cnt8_envAt (cnt8_irTrace t) t) = some env1) :
    evalExpr cnt8_weM (cnt8_envAt (cnt8_irTrace t) t)
        _root_.cnt8_cone__tmp_a_4
      = some (env1 "_tmp_reg_input_3") := by
  have hres : _root_.cnt8_cone__tmp_a_4
      = resolveSlicesT cnt8_wtM 10000
          _root_.cnt8_coneRaw__tmp_a_4 := by
    native_decide
  rw [hres]
  exact cone_resolved_agrees_at_seed cnt8_weM (fun _ _ => 0)
    cnt8_stopAtM cnt8_wtM
    (woCheck_sound [] _root_.cnt8_body (by native_decide))
    (memFreeCheck_sound _ (by native_decide))
    (noSelfReadCheck_sound _ (by native_decide))
    hrun
    (hwfCheck_sound cnt8_weM cnt8_stopAtM _root_.cnt8_body
      (by native_decide))
    (hwt_of_assoc cnt8_weM _root_.cnt8_wtL (by native_decide))
    (cnt8_seed_bounded t)
    (stopAtFrozenCheck_sound cnt8_stopAtM _root_.cnt8_body
      (by native_decide))
    (fuel := 10000) (e := .ref "_tmp_reg_input_3")
    (hinl := by native_decide)
    10000
    (hv := by simp [evalExpr])

/-- Corollary in recurrence form: `cnt8_irTrace`'s next state IS the
    fold's value of the register-input wire. -/
theorem cnt8_irTrace_step (t : Nat) {env1 : Env}
    (hrun : evalAssigns cnt8_weM (fun _ _ => 0) _root_.cnt8_body
      (cnt8_envAt (cnt8_irTrace t) t) = some env1) :
    cnt8_irTrace (t + 1) = env1 "_tmp_reg_input_3" := by
  simp only [cnt8_irTrace]
  rw [cnt8_step_agrees t hrun]
  rfl

end Sparkle.Tests.ConeBridgeDemo
