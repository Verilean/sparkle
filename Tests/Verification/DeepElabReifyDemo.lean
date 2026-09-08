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

/-! NESTED `circuit do`: a helper circuit instantiated inside another
    circuit's body.  The IR flattens both into one register list.  (The
    elaborator used to emit the inner registers TWICE — `runCircuitH`
    evaluates its body for the next-state and again for the output —
    which `Sparkle.IR.RegDedup` now merges; the bridge still carries
    the duplicate-copy machinery, generated `_dup_r*` equalities, for
    any copy the merge cannot identify.)  The Signal side keeps one
    `Signal.loop` per node; the bridge discharges each inner loop with
    `loop_trace_guarded_at` (its body may read the outer live signal,
    known only as a prefix) against a candidate register block. -/

/-- Inner counter: independent of the outer state. -/
def innerCnt (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 4) :=
  circuit do
    let c ← Signal.reg (3#4)
    let cs := (c : Signal defaultDomain (BitVec 4))
    let one := (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))
    c <~ Signal.mux en (cs + one) cs
    return cs

/-- Outer accumulator zero-extending the inner count. -/
def outerNest (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg (5#8)
    let a := (acc : Signal defaultDomain (BitVec 8))
    let c := innerCnt en
    let z := (Signal.pure 0#4 : Signal defaultDomain (BitVec 4))
    let ext := (z ++ c : Signal defaultDomain (BitVec 8))
    acc <~ a + ext
    return a

#verify_elab_deep outerNest

/-- Inner circuit with a Bool register that READS the outer register
    (feedback through the enclosing live signal — the guarded case). -/
def innerAcc (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg (1#8)
    let f ← Signal.reg false
    let as := (a : Signal defaultDomain (BitVec 8))
    let fs := (f : Signal defaultDomain Bool)
    a <~ Signal.mux en (as + x) as
    f <~ Signal.mux fs (Signal.pure false) (Signal.pure true)
    return Signal.mux fs as (as + x)

/-- Outer: feeds its register into the inner circuit and OUTPUTS the
    inner result (so the output reads the second IR copy). -/
def outerFb (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg (0#8)
    let a := (acc : Signal defaultDomain (BitVec 8))
    let y := innerAcc en a
    acc <~ y
    return y

#verify_elab_deep outerFb

/-! TWO-LEVEL NESTING: the innermost circuit reads a signal mixing the
    mid-level and the outer register.  Term nesting exceeds circuit
    nesting here (the inner circuit's input carries the mid loop's term,
    whose body carries the inner circuit again), and the innermost step
    obligation needs prefix facts about BOTH enclosing live signals —
    `loop_trace_guardedP_at` with a conjunction guard, accumulated by the
    recursive discharge. -/

def lvl2 (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg (1#8)
    let cs := (c : Signal defaultDomain (BitVec 8))
    c <~ Signal.mux en (cs + x) cs
    return cs

def lvl1 (en : Signal defaultDomain Bool) (y : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let m ← Signal.reg (2#8)
    let ms := (m : Signal defaultDomain (BitVec 8))
    let z := lvl2 en (ms + y)
    m <~ z
    return ms + z

def lvl0 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let o ← Signal.reg (0#8)
    let os := (o : Signal defaultDomain (BitVec 8))
    let w := lvl1 en os
    o <~ w
    return w

#verify_elab_deep lvl0

/-! NON-SIGNAL VALUE PARAMETERS: a circuit taking a `BitVec` / `Nat`
    parameter is certified through a specialized wrapper def — the same
    pattern synthesis needs.  The wrapper's body is an application of
    the parameterized circuit, not a `runCircuitH`; the generator follows
    the head chain by delta-unfolding (`accK15 → accK`) and unfolds it in
    the proof with the constants' first equations. -/

/-- BitVec value parameter `k`. -/
def accK (k : BitVec 8) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg (0#8)
    let a := (acc : Signal defaultDomain (BitVec 8))
    let kk := (Signal.pure k : Signal defaultDomain (BitVec 8))
    acc <~ a + (d &&& kk)
    return a

def accK15 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  accK 0x0F#8 d

#verify_elab_deep accK15

/-- Nat value parameter turned into a constant inside the circuit. -/
def accN (lim : Nat) (d : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let acc ← Signal.reg (0#8)
    let a := (acc : Signal defaultDomain (BitVec 8))
    let l := (Signal.pure (BitVec.ofNat 8 lim) : Signal defaultDomain (BitVec 8))
    acc <~ a + d + l
    return a

def accN200 (d : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  accN 200 d

#verify_elab_deep accN200

/-! A SYNCHRONOUS MEMORY (`Signal.memory`): the deep circuit is a `CdoM`
    (contents state + a read latch slot), the Signal side sees the memory
    as two nested loops (`Signal.memory_eq_loops`: the latch as a one-slot
    loop over the contents loop), the certified statement is the capstone
    `CdoM.elab_general`, and the IR replay runs over `stepIterM` (state ×
    memory contents): the latch slot is stepped by `syncReadLatches`, the
    contents by `memNexts`, both landing on the deep recurrence
    (`memAcc_deep_memstep`), so `memAcc_deep_signal_run` is the same
    `runModule` statement as for memory-free circuits.  `Signal.memory`
    itself is a `def` with a pure `memState` specification since the
    memory-spec commit. -/
def memAcc (wa : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 8))
    (we : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let ptr ← Signal.reg (0#4)
    let acc ← Signal.reg (0#8)
    let p := (ptr : Signal defaultDomain (BitVec 4))
    let a := (acc : Signal defaultDomain (BitVec 8))
    let rd := Signal.memory wa wd we p
    ptr <~ p + (Signal.pure 1#4 : Signal defaultDomain (BitVec 4))
    acc <~ a + rd
    return a

#verify_elab_deep memAcc

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
#print axioms outerNest_deep_trace
#print axioms outerFb_deep_trace
#print axioms accK15_deep_trace
#print axioms accN200_deep_trace
#print axioms lvl0_deep_trace
#check @lvl0_deep_signal_run
#print axioms memAcc_deep_trace
#check @memAcc_deep_md0_succ
#check @memAcc_deep_rd2_succ
-- the memory replay: contents step and the runModule statement
#check @memAcc_deep_memstep
#check @memAcc_deep_signal_run
#print axioms memAcc_deep_signal_run
-- the two-pass duplicate of the memory is merged (RegDedup): one memory
run_cmd do
  let d ← Lean.Elab.Command.liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical ``Sparkle.Tests.DeepElabReifyDemo.memAcc)
  for m in d.modules do
    let n := (m.body.filter fun st => match st with | .memory .. => true | _ => false).length
    unless n == 1 do
      throwError "memAcc: expected exactly one memory after duplicate merging, got {n}"
#check @accK15_deep_signal_run
#check @accN200_deep_signal_run

-- nested-circuit pins: the merged register set (RegDedup: 3 registers
-- for outerFb, not 5) and the readers the Signal-side bridge is
-- stated over
#check @outerFb_deep_rd2_succ
#check @outerNest_deep_signal_run
#check @outerFb_deep_signal_run
run_cmd do
  let d ← Lean.Elab.Command.liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical ``Sparkle.Tests.DeepElabReifyDemo.outerFb)
  for m in d.modules do
    let n := (Tools.VerifyElab.theRegisters m).length
    unless n == 3 do
      throwError "outerFb: expected 3 registers after duplicate merging, got {n}"


-- deep-bridge replay pins: the general-theorem route's per-instance
-- chain (seed bound → register phase → cycle trace → Signal ≡ runModule),
-- generated by #verify_elab_deep and audited against sorryAx
#check @twoReg_deep_regstep
#check @twoReg_deep_state_trace
#check @twoReg_deep_signal_run
#check @packerDemo_deep_regstep
#check @packerDemo_deep_signal_run
#check @rstCnt_deep_signal_run
#check @twoOutDemo_sum_deep_signal_run
#check @twoOutDemo_flag_deep_signal_run
#check @isZeroDemo_deep_signal_run

end Sparkle.Tests.DeepElabReifyDemo
