-- Tutorial example 3: a parent with a register and a child module (a real module
-- boundary), through the hierarchy entry `#ved_u2_hier`.
-- Run from the repository root:
--   lake build Tools.VedU2HierRegEntry
--   lake env lean docs/research/examples/tutorial/Ex3_Hierarchy.lean ; echo "exit $?"
import Tools.VedU2HierRegEntry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- The CHILD: a module with one 8-bit register (an accumulator). The attribute
`@[hardware_module]` is what makes it a separate module in the returned design. -/
@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

-- The child's own facts (the deep route), proved once, then reused by the parent.
#verify_elab_deep accMod

/-- The PARENT: its own register `p` (starts at 0), one instance of `accMod` fed with the
parent's input `a`, and the parent's own arithmetic: `p := p + child`. The output is `p`. -/
@[hardware_module]
def parent8 (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod a
    p <~ p + u
    return (p : Signal defaultDomain (BitVec 8))

#ved_u2_hier parent8

/-- info: 'parent8.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parent8.ved_u1

-- The returned design keeps the child as a module of its own.
example : parent8.ved_design.modules.map (·.name) = ["accMod"] := by decide
