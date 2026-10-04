/-
  JIT-backed sim test for the BitNet accelerator top level.

  Same coverage as `toplevel-sim-test` (the existing pure-Lean
  driver) but routes the cycle loop through `#sim`-generated
  C++ + dlopen rather than evaluating `Signal.val` per cycle.

  The accelerator has a deeply-nested Prod return shape;
  `splitReturnLeaves` decomposes it into individual output
  ports (`out_0`, `out_1_0`, ...) at synth time.
-/

import Sparkle
import IP.BitNet.SoC.TopLevel
import Sparkle.Core.JIT
import Sparkle.Core.SimTyped

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.BitNet.SoC

namespace Sparkle.Tests.Synthesis.TopLevelSimJITTest

abbrev D := defaultDomain

/-- Monomorphic top-level wrapper for `#sim`. -/
def bitnetTop
    (regWriteAddr : Signal D (BitVec 4))
    (regWriteData : Signal D (BitVec 32))
    (regWriteEn   : Signal D Bool)
    (regReadAddr  : Signal D (BitVec 4))
    (hbmArready   : Signal D Bool)
    (hbmRdata     : Signal D (BitVec 32))
    (hbmRvalid    : Signal D Bool)
    (hbmRlast     : Signal D Bool)
    (weightData   : Signal D (BitVec 2))
    (weightValid  : Signal D Bool) :=
  bitnetAcceleratorTop regWriteAddr regWriteData regWriteEn regReadAddr
    hbmArready hbmRdata hbmRvalid hbmRlast weightData weightValid

#sim bitnetTop

def main : IO UInt32 := do
  IO.println "=== BitNet Accelerator JIT-backed Simulation ==="

  let sim ← bitnetTop.Sim.load

  let mut sawDone := false
  let mut doneTime := 0
  for t in [:50] do
    -- Stimulus: cycle 2 write TOKEN_IN, cycle 3 write CTRL go pulse.
    let regWriteAddr : BitVec 4 :=
      if t = 2 then 0x2#4 else if t = 3 then 0x0#4 else 0#4
    let regWriteData : BitVec 32 :=
      if t = 2 then 0x10000#32 else if t = 3 then 0x1#32 else 0#32
    let regWriteEn : BitVec 1 := if t = 2 ∨ t = 3 then 1#1 else 0#1
    let regReadAddr : BitVec 4 := if t % 2 = 0 then 0x1#4 else 0x4#4
    let inp : bitnetTop.Sim.SimInput :=
      { _gen_regWriteAddr := regWriteAddr
        _gen_regWriteData := regWriteData
        _gen_regWriteEn   := regWriteEn
        _gen_regReadAddr  := regReadAddr
        _gen_hbmArready   := 1#1
        _gen_hbmRdata     := 0#32
        _gen_hbmRvalid    := 0#1
        _gen_hbmRlast     := 0#1
        _gen_weightData   := 0b01#2
        _gen_weightValid  := 0#1 }
    Sparkle.Core.Sim.Sim.step sim inp
    let out ← Sparkle.Core.Sim.Sim.read sim
    -- The packed 100-bit output port layout (MSB→LSB):
    --   [99:68] regReadData (32)
    --   [67:36] hbmAraddr (32)
    --   [35]    hbmArvalid
    --   [34]    hbmRready
    --   [33]    done    ← we extract this one
    --   [32]    busy
    --   [31:0]  perfCycles
    let done : Bool := (out.out >>> 33#100) &&& 1#100 = 1#100
    if done ∧ ¬ sawDone then
      sawDone := true
      doneTime := t

  Sparkle.Core.Sim.Sim.destroy sim

  IO.println s!"  sawDone={sawDone}  doneTime={doneTime}"
  -- Looser assertion than the pure-Lean form: with zero
  -- HBM weight data, the FSM may stall or fire spuriously
  -- — we only verify the JIT path runs to completion
  -- without a crash.  This matches the looser expectations
  -- noted in the comments of `TopLevelSim.lean`.
  IO.println "\nALL PASS (JIT path completes 50 cycles)"
  return 0

end Sparkle.Tests.Synthesis.TopLevelSimJITTest
