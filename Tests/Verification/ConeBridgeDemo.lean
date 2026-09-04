/-
  Per-instance SEAM demo (Tools/ConeFold*.lean): the generated
  recurrence meets the module-level fold semantics.

  `#verify_elab` now auto-emits, per circuit:
  * `{base}_seed_bounded` — the seed environment the recurrence
    evaluates cones in is width-bounded;
  * `{base}_step_{reg}` / `{base}_step_out` — each cone evaluation in
    the seed equals the value the combinational fold (`evalAssigns`,
    Arc 2's `stepModule` phase 1) assigns to the register-input /
    output wire.  Hypotheses are discharged by the ConeFoldSlices
    decidable checkers via `native_decide` (HashMap hashing cannot
    kernel-reduce) and by the generated `{base}_irTrace_bound`.

  This file pins the emission on `cnt8` and states the recurrence-form
  corollary: `cnt8_irTrace`'s next state IS the fold's value of the
  register's input wire.

  Run: `lake env lean Tests/Verification/ConeBridgeDemo.lean`
-/
import Tests.Verification.VerifyElabDemo
import Tools.ConeFoldSlices

namespace Sparkle.Tests.ConeBridgeDemo

open Sparkle.IR.Semantics
open Sparkle.Tests.VerifyElabDemo

/-- Recurrence form of the generated bridge lemma: the next state of
    the recurrence is exactly what the certified module semantics
    computed for the register's input wire. -/
theorem cnt8_irTrace_step (t : Nat) {env1 : Env}
    (hrun : evalAssigns cnt8_weM (fun _ _ => 0) _root_.cnt8_body
      (cnt8_envAt (cnt8_irTrace t) t) = some env1) :
    cnt8_irTrace (t + 1) = env1 "_tmp_reg_input_3" := by
  simp only [cnt8_irTrace]
  rw [cnt8_step__tmp_a_4 t hrun
    (show evalExpr cnt8_weM env1 _root_.cnt8_regIn__tmp_a_4
        = some (env1 "_tmp_reg_input_3") by
      simp [_root_.cnt8_regIn__tmp_a_4, evalExpr])]
  rfl

-- the multi-register / inputs-bearing emissions typecheck too
#check @accEn_step__tmp_a_5
#check @twoReg_seed_bounded
#check @rstCnt_step_out
#check @fsm3_step_out

-- the register phase and the cycle-level composition
#check @cnt8_regstep
#check @twoReg_regstep
#check @twoReg_state_trace
-- THE HEADLINE: the DSL's Signal value at cycle t = the module fold's
-- output wire under the iterated certified step semantics
#check @cnt8_signal_fold
#check @accEn_signal_fold
#check @rstCnt_signal_fold
#check @fsm3_signal_fold

-- …and against runModule itself — the object Arc 2's certified
-- capstones (certified_body_trace / certified_forward_trace) are
-- stated over: the t-th trace entry's output wire IS the Signal value
#check @cnt8_signal_runModule
#check @accEn_signal_runModule
#check @twoReg_signal_runModule
#check @fsm3_signal_runModule

-- THE FULL CHAIN: Signal ≡ the VERILOG SEMANTICS of the certified
-- twin emission (M4's runModuleSV), per instance, every cycle
#check @cnt8_signal_sv
#check @accEn_signal_sv
#check @twoReg_signal_sv
#check @rstCnt_signal_sv
#check @fsm3_signal_sv

end Sparkle.Tests.ConeBridgeDemo
