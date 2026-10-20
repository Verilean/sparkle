import Sparkle.Core.CircuitDo
import Sparkle.Compiler.InlineAttr
import Tools.ShippingCorpusSweep

/-! # `#corpus_design_sweep` on three declarations of this file (round par/b-36)

WRITTEN, NOT BUILT. TARGET-ONLY. It pins the command's row format and its
"never an error" behaviour WITHOUT the driver script and without any corpus
file: the candidates are the definitions DECLARED IN THIS FILE.

* `csReg`: a register leaf (the shape of `counter2`,
  `Tests/Compiler/ShippingMachineInstTest.lean` 59, eight bits) — PREDICTED
  class `LEAF-REG`, outcome `COVERED`, form `machine_design_leaf0`.
* `csComb`: a slotless machine leaf with a hardware `let` — PREDICTED
  `LEAF-COMB` / `COVERED` / `machine_design_comb0` IF the machine reader
  reads it; if a combinational gate takes it first, `GATE` / `COVERED` /
  `gate_design0`. Which of the two is NOT determined by reading.
* `csGate`: the body of `pick` (a gate-route declaration) —
  PREDICTED `GATE` / `COVERED` / `gate_design0`.

Nothing is asserted (the classes are predictions). The rows go to the log
(`CORPUS ROW …`) and are appended to `/dev/null`; the tops file does not
exist (an empty list). Mode `all`: untagged definitions the machine reader
reads are candidates too. -/
namespace Sparkle.Tests.Compiler.CorpusSweepSelfTest
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

@[hardware_module]
def csReg (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    let cS := (c : Signal defaultDomain (BitVec 8))
    c <~ Signal.mux en (cS + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) cS
    return cS

@[hardware_module]
def csComb (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let s := x ^^^ y
  Signal.mux (s === (Signal.pure 0#8 : Signal defaultDomain (BitVec 8))) x (s + s)

@[hardware_module]
def csGate (sel : Signal defaultDomain (BitVec 2)) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux (sel === (Signal.pure 0#2 : Signal defaultDomain (BitVec 2))) x
    (x ^^^ (Signal.pure 0xFF#8 : Signal defaultDomain (BitVec 8)))

end Sparkle.Tests.Compiler.CorpusSweepSelfTest

set_option maxHeartbeats 0 in
#corpus_design_sweep "/dev/null" "/nonexistent/corpus-sweep-selftest.tops" "Tests/Compiler/CorpusSweepSelfTest.lean" "all"
