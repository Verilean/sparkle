/-
  `#verify_elab_deep` demo — ordinary `circuit do` definitions,
  certified through the GENERAL theorem.

  For each circuit the command reifies the elaborated cones into a
  deep `Cdo` value, applies `Cdo.elab_general` (ONE theorem, proven
  once for every circuit in the grammar), and generates only the
  Signal-side bridge.  Everything about the IR — evaluation, bounds,
  the trace recurrence — is the general theorem, not generated tactics.

  Compare `VerifyElabDemo.lean` (`#verify_elab`): same circuits, but
  there the IR side is re-proven per circuit.  This file is the
  CompCert-shaped version.

  v0 scope: BitVec inputs (Bool inputs need an encoding wrapper —
  next).  Run: `lake env lean Tests/Verification/DeepElabReifyDemo.lean`
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Tools.DeepElab

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core

namespace Sparkle.Tests.DeepElabReifyDemo

def cnt8 : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    c <~ c + 1#8
    return c

#verify_elab_deep cnt8

def accEn (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 0#4
    acc <~ Signal.mux (en.map (· == 1#1)) (acc + d) acc
    return acc

#verify_elab_deep accEn

def subEn (en : Signal defaultDomain (BitVec 1))
    (d : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let acc ← Signal.reg 9#4
    acc <~ Signal.mux (en.map (· == 1#1)) (acc - d) acc
    return acc

#verify_elab_deep subEn

def twoReg (d : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 4) :=
  circuit do
    let a ← Signal.reg 0#4
    let b ← Signal.reg 0#4
    a <~ a + d
    b <~ a
    return b

#verify_elab_deep twoReg

def fsm3 : Signal defaultDomain (BitVec 2) :=
  circuit do
    let state ← Signal.reg 0#2
    match state with
    | 0#2 => state <~ 1#2
    | 1#2 => state <~ 2#2
    | 2#2 => state <~ 0#2
    | _   => state <~ 0#2
    return state

#verify_elab_deep fsm3

#print axioms cnt8_deep_trace
#print axioms accEn_deep_trace
#print axioms subEn_deep_trace
#print axioms twoReg_deep_trace
#print axioms fsm3_deep_trace

end Sparkle.Tests.DeepElabReifyDemo
