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

  Bool inputs enter through their 1-bit encoding.  Run: `lake env lean Tests/Verification/DeepElabReifyDemo.lean`
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

/-- Statement-level `if` with a `Bool` input — enters the deep circuit
    through its 1-bit encoding. -/
def rstCnt (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let cnt ← Signal.reg 0#8
    if reset then
      cnt <~ 0#8
    else
      cnt <~ cnt + 1#8
    return cnt

#verify_elab_deep rstCnt

def twoIf (reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    let b ← Signal.reg 0#8
    if reset then
      a <~ 0#8
      b <~ 0#8
    else
      a <~ a + 1#8
      b <~ a
    return b

#verify_elab_deep twoIf

/-- A single Bool output: exercises the `bif`-encoded output family. -/
def isZeroDemo (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain Bool :=
  circuit do
    let acc ← Signal.reg 0#8
    let a := (acc : Signal defaultDomain (BitVec 8))
    acc <~ a + d
    return (a.map (· == 0#8))

#verify_elab_deep isZeroDemo

/-- A struct return with TWO ports (BitVec + Bool): exercises the
    per-field Cdo generation and the struct-projection bridge
    (runCircuitH_proj_eq + `.eq_1` unfold). -/
structure TwoOutDemo (dom : DomainConfig) where
  sum  : Signal dom (BitVec 8)
  flag : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TwoOutDemo dom) dom := ⟨⟩

def twoOutDemo (d : Signal defaultDomain (BitVec 8)) :
    TwoOutDemo defaultDomain :=
  circuit do
    let acc ← Signal.reg 0#8
    let a := (acc : Signal defaultDomain (BitVec 8))
    acc <~ a + d
    let f := (a.map (· == 0#8) : Signal defaultDomain Bool)
    return ({ sum := a, flag := f } : TwoOutDemo defaultDomain)

#verify_elab_deep twoOutDemo

/-- A concat OUTPUT: three registers packed MSB-first into a wider
    word.  Exercises n-ary concat fidelity (concatNorm) and the
    slice-of-slice fusion in resolveSlicesW that collapses firtool's
    slice-reconstructed output back to the register concat. -/
def packerDemo (d : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 12) :=
  circuit do
    let a ← Signal.reg 0#4
    let b ← Signal.reg 0#4
    let c ← Signal.reg 0#4
    let av := (a : Signal defaultDomain (BitVec 4))
    let bv := (b : Signal defaultDomain (BitVec 4))
    let cv := (c : Signal defaultDomain (BitVec 4))
    a <~ d
    b <~ av
    c <~ bv
    return (av ++ bv ++ cv)

#verify_elab_deep packerDemo

/-- Signal.mux over a Signal.beq condition with Signal.pure constants:
    exercises the method-style mux / beq / pure `.val`-push lemmas. -/
def selRegDemo (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg 0#8
    let a := (acc : Signal defaultDomain (BitVec 8))
    let isMax := Signal.beq a (Signal.pure 255#8)
    acc <~ Signal.mux isMax (Signal.pure 0#8) (a + d)
    return a

#verify_elab_deep selRegDemo

/-- A Bool-typed REGISTER (`Signal.reg false`): the loop-state HList
    holds it as `Bool` while the deep embedding sees `BitVec 1`.
    Exercises the register-type detection (from runCircuitH's αs), the
    Bool-decoded pack slot, and the stateAt-generalizing 1-bit closer. -/
def flipRegDemo (en : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  circuit do
    let st ← Signal.reg false
    let s := (st : Signal defaultDomain Bool)
    st <~ Signal.mux en (~~~s) s
    return s

#verify_elab_deep flipRegDemo

#print axioms cnt8_deep_trace
#print axioms accEn_deep_trace
#print axioms subEn_deep_trace
#print axioms twoReg_deep_trace
#print axioms fsm3_deep_trace
#print axioms rstCnt_deep_trace
#print axioms twoIf_deep_trace
#print axioms isZeroDemo_deep_trace
#print axioms twoOutDemo_sum_deep_trace
#print axioms twoOutDemo_flag_deep_trace
#print axioms packerDemo_deep_trace
#print axioms selRegDemo_deep_trace
#print axioms flipRegDemo_deep_trace

end Sparkle.Tests.DeepElabReifyDemo
