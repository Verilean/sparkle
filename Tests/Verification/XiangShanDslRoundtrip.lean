/-
  XiangShan `verilog → IR → lean₄ → IR → proof`, end to end.

  Every definition below is VERBATIM the circuit-DSL source that
  `lake exe sv-to-dsl` printed from the real firtool-generated RTL of the
  XiangShan Kunminghu core (`<Module>_dsl`).  So this file is
  machine-written Sparkle source for a production CPU's logic — and
  `#verify_dsl_roundtrip` then proves that re-synthesizing it yields a
  design whose register/output cones are equal (`bv_decide`,
  kernel-checked) to the IR the decompiler started from.

  Chain of custody per module:

      XiangShan .sv
        --SVParser-->      IR      (co-sim + yosys-equiv checked in CI)
        --toCircuitDsl-->  the definitions below
        --synthesize-->    IR'
        --bv_decide-->     IR ≡ IR' per cone   ← this file

  Regenerate with:
      lake exe sv-to-dsl <rtl-dir> --emit <out>   # then paste a module

  Run: `lake env lean Tests/Verification/XiangShanDslRoundtrip.lean`
  (bv_decide, KnownIssues #2: interpreter/interactive only).
-/

import Sparkle
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo
import Sparkle.Compiler.Elab
import Tools.SVParser.DslEmit

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Tests.XiangShanDslRoundtrip

def AddWModule_dsl (io_src : Signal defaultDomain (BitVec 32)) (io_srcw : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  (io_srcw + io_src)

#verify_dsl_roundtrip AddWModule_dsl

def PipelineStallReason_dsl (io_prePipeStall : Signal defaultDomain (BitVec 1)) (io_prePipeStallReason : Signal defaultDomain (BitVec 7)) (io_prePipeBubble : Signal defaultDomain (BitVec 1)) (io_prePipeBubbleReason : Signal defaultDomain (BitVec 7)) (io_redirect : Signal defaultDomain (BitVec 1)) (io_redirectReason : Signal defaultDomain (BitVec 7)) (io_currentPipeStall : Signal defaultDomain (BitVec 1)) (io_currentPipeStallReason : Signal defaultDomain (BitVec 7)) : Signal defaultDomain (BitVec 7) :=
  circuit do
    let r0 ← Signal.reg (0#7)
    let r1 ← Signal.reg (0#1)
    let r2 ← Signal.reg (0#7)
    let r3 ← Signal.reg (0#1)
    let r4 ← Signal.reg (0#7)
    let r5 ← Signal.reg (0#1)
    r0 <~ io_currentPipeStallReason
    r1 <~ io_currentPipeStall
    r2 <~ io_prePipeStallReason
    r3 <~ io_prePipeStall
    r4 <~ io_redirectReason
    r5 <~ io_redirect
    return (Signal.mux (((io_redirect ||| (r5 : Signal defaultDomain (BitVec 1)))).map (· == 1#1)) (Signal.mux ((io_redirect).map (· == 1#1)) io_redirectReason (r4 : Signal defaultDomain (BitVec 7))) (Signal.mux (((r3 : Signal defaultDomain (BitVec 1))).map (· == 1#1)) (r2 : Signal defaultDomain (BitVec 7)) (Signal.mux (((r1 : Signal defaultDomain (BitVec 1))).map (· == 1#1)) (r0 : Signal defaultDomain (BitVec 7)) (Signal.mux ((io_prePipeBubble).map (· == 1#1)) io_prePipeBubbleReason (Signal.pure (0#7) : Signal defaultDomain (BitVec 7))))))

#verify_dsl_roundtrip PipelineStallReason_dsl

def VtypeModule_dsl (robCommit_vtype_valid : Signal defaultDomain (BitVec 1)) (robCommit_vtype_bits_VILL : Signal defaultDomain (BitVec 1)) (robCommit_vtype_bits_VMA : Signal defaultDomain (BitVec 1)) (robCommit_vtype_bits_VTA : Signal defaultDomain (BitVec 1)) (robCommit_vtype_bits_VSEW : Signal defaultDomain (BitVec 3)) (robCommit_vtype_bits_VLMUL : Signal defaultDomain (BitVec 3)) : Signal defaultDomain (BitVec 64) :=
  circuit do
    let r0 ← Signal.reg (0#3)
    let r1 ← Signal.reg (0#3)
    let r2 ← Signal.reg (0#1)
    let r3 ← Signal.reg (0#1)
    let r4 ← Signal.reg (1#1)
    r0 <~ (Signal.mux ((robCommit_vtype_valid).map (· == 1#1)) robCommit_vtype_bits_VLMUL (r0 : Signal defaultDomain (BitVec 3)))
    r1 <~ (Signal.mux ((robCommit_vtype_valid).map (· == 1#1)) robCommit_vtype_bits_VSEW (r1 : Signal defaultDomain (BitVec 3)))
    r2 <~ (Signal.mux ((robCommit_vtype_valid).map (· == 1#1)) robCommit_vtype_bits_VTA (r2 : Signal defaultDomain (BitVec 1)))
    r3 <~ (Signal.mux ((robCommit_vtype_valid).map (· == 1#1)) robCommit_vtype_bits_VMA (r3 : Signal defaultDomain (BitVec 1)))
    r4 <~ (Signal.mux ((robCommit_vtype_valid).map (· == 1#1)) robCommit_vtype_bits_VILL (r4 : Signal defaultDomain (BitVec 1)))
    return ((((((r4 : Signal defaultDomain (BitVec 1)) ++ (Signal.pure (0#55) : Signal defaultDomain (BitVec 55))) ++ (r3 : Signal defaultDomain (BitVec 1))) ++ (r2 : Signal defaultDomain (BitVec 1))) ++ (r1 : Signal defaultDomain (BitVec 3))) ++ (r0 : Signal defaultDomain (BitVec 3)))

#verify_dsl_roundtrip VtypeModule_dsl

end Sparkle.Tests.XiangShanDslRoundtrip
