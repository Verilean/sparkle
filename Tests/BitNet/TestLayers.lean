/-
  Hespera FFN Layer Tests

  Unit tests for all FFN datapath layers:
  - Scale multiply
  - ReLU²
  - Residual add (with saturation)
  - Element-wise multiply
  - RMSNorm
  - FFN block composition
-/

import Examples.BitNet.Config
import Examples.BitNet.Types
import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Backend.Verilog
import Examples.BitNet.BitLinear.Scale
import Examples.BitNet.Layers.ReLUSq
import Examples.BitNet.Layers.ResidualAdd
import Examples.BitNet.Layers.ElemMul
import Examples.BitNet.Layers.RMSNorm
import Examples.BitNet.Layers.FFN

namespace Sparkle.Examples.BitNet.Tests.Layers

open Sparkle.Examples.BitNet
open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.Verilog

/-- Simple test harness -/
def check (name : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"  PASS: {name}"
  else
    IO.eprintln s!"  FAIL: {name}"

-- ============================================================================
-- Pure-Lean Spec Tests (Types.lean reference implementations)
-- ============================================================================

def testScaleSpec : IO Unit := do
  IO.println "--- Scale Multiply Spec Tests ---"

  -- 1.0 × 1.0 = 1.0
  let acc1 : Accumulator := BitVec.ofNat 48 0x10000
  let scale1 : ScaleFactor := BitVec.ofNat 32 0x01000000
  check "spec: 1.0×1.0=1.0" (fixedPointScale acc1 scale1 == BitVec.ofNat 32 0x10000)

  -- 2.0 × 0.5 = 1.0
  let acc2 : Accumulator := BitVec.ofNat 48 0x20000
  let scale2 : ScaleFactor := BitVec.ofNat 32 0x00800000
  check "spec: 2.0×0.5=1.0" (fixedPointScale acc2 scale2 == BitVec.ofNat 32 0x10000)

  -- Negative accumulator
  let accNeg : Accumulator := BitVec.ofInt 48 (-0x10000)
  check "spec: -1.0×1.0=-1.0"
    (fixedPointScale accNeg scale1 == BitVec.ofInt 32 (-0x10000))

  -- Zero
  check "spec: 0×1.0=0"
    (fixedPointScale (BitVec.ofNat 48 0) scale1 == BitVec.ofNat 32 0)

def testReLUSqSpec : IO Unit := do
  IO.println "--- ReLU² Spec Tests ---"

  -- Positive: 2.0² = 4.0
  check "spec: relu²(2.0)=4.0"
    (reluSquared (BitVec.ofNat 32 0x20000) == BitVec.ofNat 32 0x40000)

  -- Positive: 1.0² = 1.0
  check "spec: relu²(1.0)=1.0"
    (reluSquared (BitVec.ofNat 32 0x10000) == BitVec.ofNat 32 0x10000)

  -- Negative → 0
  check "spec: relu²(-1.0)=0"
    (reluSquared (BitVec.ofInt 32 (-0x10000)) == BitVec.ofNat 32 0)

  -- Zero → 0
  check "spec: relu²(0)=0"
    (reluSquared (BitVec.ofNat 32 0) == BitVec.ofNat 32 0)

  -- 0.5² = 0.25
  check "spec: relu²(0.5)=0.25"
    (reluSquared (BitVec.ofNat 32 0x8000) == BitVec.ofNat 32 0x4000)

def testResidualAddSpec : IO Unit := do
  IO.println "--- Residual Add Spec Tests ---"

  -- Normal: 1.0 + 1.0 = 2.0
  check "spec: 1.0+1.0=2.0"
    (residualAdd (BitVec.ofNat 32 0x10000) (BitVec.ofNat 32 0x10000)
      == BitVec.ofNat 32 0x20000)

  -- Normal: 2.0 + (-1.0) = 1.0
  check "spec: 2.0+(-1.0)=1.0"
    (residualAdd (BitVec.ofNat 32 0x20000) (BitVec.ofInt 32 (-0x10000))
      == BitVec.ofNat 32 0x10000)

  -- Positive overflow saturation
  check "spec: pos overflow saturates"
    (residualAdd (BitVec.ofNat 32 0x7FFFFFFF) (BitVec.ofNat 32 1)
      == BitVec.ofNat 32 0x7FFFFFFF)

  -- Negative overflow saturation
  check "spec: neg overflow saturates"
    (residualAdd (BitVec.ofInt 32 (-(2^31))) (BitVec.ofInt 32 (-1))
      == BitVec.ofInt 32 (-(2^31)))

  -- Identity: x + 0 = x
  check "spec: x+0=x"
    (residualAdd (BitVec.ofNat 32 0x12345) (BitVec.ofNat 32 0)
      == BitVec.ofNat 32 0x12345)

def testElemMulSpec : IO Unit := do
  IO.println "--- Element Multiply Spec Tests ---"

  -- 2.0 × 3.0 = 6.0
  check "spec: 2.0×3.0=6.0"
    (elemMul (BitVec.ofNat 32 0x20000) (BitVec.ofNat 32 0x30000)
      == BitVec.ofNat 32 0x60000)

  -- 1.0 × 1.0 = 1.0
  check "spec: 1.0×1.0=1.0"
    (elemMul (BitVec.ofNat 32 0x10000) (BitVec.ofNat 32 0x10000)
      == BitVec.ofNat 32 0x10000)

  -- Negative × positive
  check "spec: -2.0×3.0=-6.0"
    (elemMul (BitVec.ofInt 32 (-0x20000)) (BitVec.ofNat 32 0x30000)
      == BitVec.ofInt 32 (-0x60000))

  -- Multiply by zero
  check "spec: x×0=0"
    (elemMul (BitVec.ofNat 32 0x20000) (BitVec.ofNat 32 0)
      == BitVec.ofNat 32 0)

  -- 2.0 × 0.5 = 1.0
  check "spec: 2.0×0.5=1.0"
    (elemMul (BitVec.ofNat 32 0x20000) (BitVec.ofNat 32 0x8000)
      == BitVec.ofNat 32 0x10000)

-- ============================================================================
-- RTL Module Structure Tests
-- ============================================================================

def testScaleRTL : IO Unit := do
  IO.println "--- Scale Multiply RTL Tests ---"

  let cfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }
  let m := Sparkle.Examples.BitNet.BitLinear.buildScaleMultiply cfg

  -- Check module structure
  check "scale: has clk, rst, acc, scale inputs"
    (m.inputs.length == 4)
  check "scale: has result output"
    (m.outputs.length == 1)
  check "scale: output is 32-bit"
    (m.outputs.head?.map (·.ty) == some (.bitVector 32))
  check "scale: module named ScaleMultiply"
    (m.name == "ScaleMultiply")

  -- Generate and print Verilog
  let verilog := toVerilog m
  check "scale: generates non-empty Verilog" (verilog.length > 100)
  IO.println ""
  IO.println "  --- Scale Multiply Verilog ---"
  IO.println verilog

def testReLUSqRTL : IO Unit := do
  IO.println "--- ReLU² RTL Tests ---"

  let m := Sparkle.Examples.BitNet.Layers.buildReLUSq

  check "relusq: has x input" (m.inputs.length == 1)
  check "relusq: has y output" (m.outputs.length == 1)
  check "relusq: input is 32-bit"
    (m.inputs.head?.map (·.ty) == some (.bitVector 32))
  check "relusq: output is 32-bit"
    (m.outputs.head?.map (·.ty) == some (.bitVector 32))
  check "relusq: module named ReLUSq" (m.name == "ReLUSq")

  let verilog := toVerilog m
  check "relusq: generates non-empty Verilog" (verilog.length > 50)
  IO.println ""
  IO.println "  --- ReLU² Verilog ---"
  IO.println verilog

def testResidualAddRTL : IO Unit := do
  IO.println "--- Residual Add RTL Tests ---"

  let m := Sparkle.Examples.BitNet.Layers.buildResidualAdd

  check "resadd: has a, b inputs" (m.inputs.length == 2)
  check "resadd: has y output" (m.outputs.length == 1)
  check "resadd: both inputs are 32-bit"
    (m.inputs.all (fun p => p.ty == .bitVector 32))
  check "resadd: output is 32-bit"
    (m.outputs.head?.map (·.ty) == some (.bitVector 32))
  check "resadd: module named ResidualAdd" (m.name == "ResidualAdd")

  let verilog := toVerilog m
  check "resadd: generates non-empty Verilog" (verilog.length > 50)
  IO.println ""
  IO.println "  --- Residual Add Verilog ---"
  IO.println verilog

def testElemMulRTL : IO Unit := do
  IO.println "--- Element Multiply RTL Tests ---"

  let m := Sparkle.Examples.BitNet.Layers.buildElemMul

  check "emul: has a, b inputs" (m.inputs.length == 2)
  check "emul: has y output" (m.outputs.length == 1)
  check "emul: both inputs are 32-bit"
    (m.inputs.all (fun p => p.ty == .bitVector 32))
  check "emul: output is 32-bit"
    (m.outputs.head?.map (·.ty) == some (.bitVector 32))
  check "emul: module named ElemMul" (m.name == "ElemMul")

  let verilog := toVerilog m
  check "emul: generates non-empty Verilog" (verilog.length > 50)
  IO.println ""
  IO.println "  --- Element Multiply Verilog ---"
  IO.println verilog

def testRMSNormRTL : IO Unit := do
  IO.println "--- RMSNorm RTL Tests ---"

  let rmsCfg : Sparkle.Examples.BitNet.Layers.RMSNormConfig := { dim := 16 }  -- Small dim for testing
  let genCfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }
  let m := Sparkle.Examples.BitNet.Layers.buildRMSNorm rmsCfg genCfg

  -- Check module structure
  check "rmsnorm: has clk, rst, start, x_in, scale_in inputs"
    (m.inputs.length == 5)
  check "rmsnorm: has y_out, done, elem_idx, reading outputs"
    (m.outputs.length == 4)
  check "rmsnorm: module named RMSNorm_16" (m.name == "RMSNorm_16")

  -- Check has registers (FSM state, counter, accumulators)
  let regCount := m.body.foldl (fun acc s =>
    match s with
    | .register .. => acc + 1
    | _ => acc) 0
  check "rmsnorm: has FSM registers" (regCount ≥ 4)

  let verilog := toVerilog m
  check "rmsnorm: generates non-empty Verilog" (verilog.length > 200)
  IO.println ""
  IO.println "  --- RMSNorm Verilog (dim=16) ---"
  IO.println verilog

def testFFNBlockRTL : IO Unit := do
  IO.println "--- FFN Block RTL Tests ---"

  -- Small test weights
  let gateWeights : Array Int := #[1, -1, 0, 1]
  let upWeights   : Array Int := #[-1, 1, 1, 0]
  let downWeights : Array Int := #[1, 0, -1, 1]

  let ffnCfg : Sparkle.Examples.BitNet.Layers.FFNConfig := {
    hiddenDim := 4
    ffnDim := 4
    baseBitWidth := 32
    pipelineEvery := 0
  }
  let genCfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }
  let m := Sparkle.Examples.BitNet.Layers.buildFFNBlock ffnCfg genCfg gateWeights upWeights downWeights

  -- Check module structure
  check "ffn: module named FFNBlock_4x4" (m.name == "FFNBlock_4x4")
  check "ffn: has top-level inputs" (m.inputs.length ≥ 5)
  check "ffn: has y_out and done outputs" (m.outputs.length == 2)

  -- Check that instances are created
  let instCount := m.body.foldl (fun acc s =>
    match s with
    | .inst .. => acc + 1
    | _ => acc) 0
  check "ffn: has sub-module instances" (instCount ≥ 5)

  let verilog := toVerilog m
  check "ffn: generates non-empty Verilog" (verilog.length > 200)
  IO.println ""
  IO.println "  --- FFN Block Verilog (4x4, truncated) ---"
  -- Print first 2000 chars to avoid overwhelming output
  let truncated := if verilog.length > 2000 then (verilog.take 2000).toString ++ "\n  ... (truncated)" else verilog
  IO.println truncated

def runAll : IO Unit := do
  IO.println "=== FFN Layer Tests ==="
  IO.println ""
  testScaleSpec
  testReLUSqSpec
  testResidualAddSpec
  testElemMulSpec
  IO.println ""
  testScaleRTL
  testReLUSqRTL
  testResidualAddRTL
  testElemMulRTL
  testRMSNormRTL
  testFFNBlockRTL
  IO.println ""
  IO.println "=== All FFN layer tests complete ==="

end Sparkle.Examples.BitNet.Tests.Layers
