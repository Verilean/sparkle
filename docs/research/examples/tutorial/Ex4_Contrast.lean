-- Tutorial example 4: where the automatic proof stops. Two small changes, two refusals.
--   (A) the result is a pair (count, flag) instead of one value;
--   (B) the child module's input is computed from the parent's own register.
-- Every refusal is pinned with `#guard_msgs (error)`, so the file exits 0. A refusal is
-- NOT a counterexample: it only says that this entry built no theorem.
-- Run from the repository root:
--   lake build Tools.VedU2HierRegEntry
--   lake env lean docs/research/examples/tutorial/Ex4_Contrast.lean ; echo "exit $?"
import Tools.VedU2HierRegEntry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-! ## (A) one value becomes a pair -/

/-- A counter in the style of example 2 (a `Signal.loop` of two registers: it adds `d` while
`en` is high) that ALSO reports a flag that becomes true one cycle after the count is observed
at 255 and then stays true: the result is the pair
(count, flag). -/
def countFlag (en : Signal defaultDomain Bool) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8 × Bool) :=
  let st := Signal.loop fun state =>
    let c := projN! state 2 0
    let f := projN! state 2 1
    let cNext := Signal.mux en (c + d) c
    let fNext := Signal.mux (c === 255#8) (Signal.pure true) f
    bundleAll! [Signal.register 0#8 cNext, Signal.register false fNext]
  bundle2 (projN! st 2 0) (projN! st 2 1)

/--
error: VED U1 REFUSED countFlag [multi-output]: 2 output projections in one `Signal` (the synthesizer packs it into one port `out`); refused
-/
#guard_msgs (error) in
#ved_u1 countFlag

/-! ## (B) a child fed from the parent's register -/

@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

#verify_elab_deep accMod

/-- Accepted: the child is fed with the parent's input `a`. -/
@[hardware_module]
def parentOk (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod a
    p <~ u
    return (p : Signal defaultDomain (BitVec 8))

#ved_u2_hier parentOk

/-- info: 'parentOk.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parentOk.ved_u1

/-- The ONLY change: the child is fed with `a + p`, a value computed from the parent's
register `p`, instead of `a`. -/
@[hardware_module]
def parentDerived (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod (a + (p : Signal defaultDomain (BitVec 8)))
    p <~ u
    return (p : Signal defaultDomain (BitVec 8))

/--
error: VED U1 REFUSED parentDerived [conns]: instance _tmp_inst_accMod_4: data port _gen_x of accMod is not connected to a parent input or to a net computed from parent inputs only: _tmp_arg0_1 is computed from a net that is not a function of the data inputs: _tmp_a_5 is a parent register output (a register-driven instance input has no closed Lean term over the parent inputs when the register is a loop: H2c covers nets computed from parent data inputs only)
-/
#guard_msgs (error) in
#ved_u2_hier parentDerived
