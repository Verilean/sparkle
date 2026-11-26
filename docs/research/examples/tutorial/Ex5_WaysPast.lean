-- Tutorial example 5: ways past a refusal that this snapshot supports.
--   (A) an existing route: the packed-port entry takes the pair result of example 4;
--   (B) splitting: a real module boundary (kept as a child) versus a plain function
--       (inlined, no child, so `#ved_u2_hier` has nothing to reuse);
--   (C) removing the boundary: the flat route takes the register-fed child input.
-- Run from the repository root:
--   lake build Tools.VedU2HierRegEntry
--   lake build Tools.VedU1PackedEntry
--   lake env lean docs/research/examples/tutorial/Ex5_WaysPast.lean ; echo "exit $?"
import Tools.VedU2HierRegEntry
import Tools.VedU1PackedEntry
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-! ## (A) the packed route: one port `out`, first component in the high bits -/

/-- A counter in the style of example 2 (a `Signal.loop` of two registers: it adds `d` while
`en` is high) that ALSO reports a flag "the count has reached 255": the result is the pair
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

#ved_u1_packed countFlag

/-- info: 'countFlag.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms countFlag.ved_u1

/-! ## (B) a real boundary versus a plain function -/

@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

#verify_elab_deep accMod

/-- The same body as `accMod`, but a plain function: no `@[hardware_module]`. -/
def accInl (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

/-- Child through the attribute: kept as an instance. -/
@[hardware_module]
def withChild (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accMod a
    p <~ u
    return (p : Signal defaultDomain (BitVec 8))

#ved_u2_hier withChild

/-- info: 'withChild.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms withChild.ved_u1

-- the design keeps the child; the parent's own registers are the parent's only
example : withChild.ved_design.modules.map (·.name) = ["accMod"] := by decide

/-- The same circuit with the plain function: the body is inlined into the parent. -/
def withPlain (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accInl a
    p <~ u
    return (p : Signal defaultDomain (BitVec 8))

/--
error: VED U1 REFUSED withPlain [scope]: the parent has no child instance (a parent without instances is `#ved_u1` / `#ved_u1_deep`)
-/
#guard_msgs (error) in
#ved_u2_hier withPlain

/-! ## (C) no boundary: the flat route takes what the hierarchy route refused (example 4) -/

/-- The register-fed input of example 4, with the child written as a plain function. -/
def flatDerived (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let u := accInl (a + (p : Signal defaultDomain (BitVec 8)))
    p <~ u
    return (p : Signal defaultDomain (BitVec 8))

#verify_elab_deep flatDerived
#ved_u1_deep flatDerived

/-- info: 'flatDerived.ved_u1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatDerived.ved_u1

-- the flat module owns both registers: the parent's `p` and the inlined accumulator's `r`
example : (flatDerived.ved_mod.body.filter
    (fun s => match s with | .register .. => true | _ => false)).length = 2 := by decide
