/-
  Hespera SoC Tests

  Tests for the dual-architecture SoC generator:
  1. ArchMode and config types
  2. Dynamic BitLinear RTL
  3. HardwiredUnrolled SoC
  4. TimeMultiplexed SoC
  5. Cross-architecture comparison
-/

import Examples.BitNet.Config
import Examples.BitNet.Types
import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.Backend.Verilog
import Examples.BitNet.BitLinear.Core
import Examples.BitNet.BitLinear.Dynamic
import Examples.BitNet.SoC.Top

namespace Sparkle.Examples.BitNet.Tests.SoC

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
-- Shared test data (2-layer toy model, dim=4, ffnDim=4)
-- ============================================================================

def testGenCfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }

def testLayerWeights : Array LayerWeights := #[
  { gateWeights := #[1, -1, 0, 1],
    upWeights   := #[-1, 1, 1, 0],
    downWeights := #[1, 0, -1, 1] },
  { gateWeights := #[0, 1, -1, -1],
    upWeights   := #[1, 0, 0, 1],
    downWeights := #[-1, 1, 1, 0] }
]

def testLayerScales : Array LayerScales := #[
  { gateScale := 0x01000000, upScale := 0x01000000, downScale := 0x01000000 },
  { gateScale := 0x00800000, upScale := 0x01000000, downScale := 0x00C00000 }
]

def testSoCConfigHW : SoCConfig := {
  archMode := .HardwiredUnrolled
  nLayers := 2
  dim := 4
  ffnDim := 4
}

def testSoCConfigTM : SoCConfig := {
  archMode := .TimeMultiplexed
  nLayers := 2
  dim := 4
  ffnDim := 4
}

-- ============================================================================
-- 1. ArchMode and Config Type Tests
-- ============================================================================

def testArchMode : IO Unit := do
  IO.println "--- ArchMode Type Tests ---"

  -- ArchMode values are distinct
  check "HardwiredUnrolled != TimeMultiplexed"
    (ArchMode.HardwiredUnrolled != ArchMode.TimeMultiplexed)

  -- SoCConfig creation and field access
  let cfg := testSoCConfigHW
  check "SoCConfig.nLayers = 2" (cfg.nLayers == 2)
  check "SoCConfig.dim = 4" (cfg.dim == 4)
  check "SoCConfig.ffnDim = 4" (cfg.ffnDim == 4)
  check "SoCConfig.archMode = HardwiredUnrolled"
    (cfg.archMode == .HardwiredUnrolled)

  -- LayerWeights structure
  let lw := testLayerWeights[0]!
  check "LayerWeights gate has 4 elements" (lw.gateWeights.size == 4)
  check "LayerWeights up has 4 elements" (lw.upWeights.size == 4)
  check "LayerWeights down has 4 elements" (lw.downWeights.size == 4)

-- ============================================================================
-- 2. Dynamic BitLinear RTL Tests
-- ============================================================================

def testDynamicBitLinear : IO Unit := do
  IO.println "--- Dynamic BitLinear RTL Tests ---"

  let cfg : GeneratorConfig := { baseBitWidth := 32, pipelineEvery := 0 }
  let inDim := 4
  let m := BitLinear.buildDynamicBitLinear inDim cfg

  -- Module has correct I/O: 2-bit weight inputs + activation inputs + result output
  -- Inputs: clk + rst + 4 weight inputs (2-bit) + 4 activation inputs (32-bit) = 10
  check "dynamic: 10 inputs (clk+rst+4w+4act)" (m.inputs.length == 10)

  -- All inDim weight inputs present (no pruning)
  let weightInputs := m.inputs.filter (fun p => p.name.startsWith "w_")
  check "dynamic: 4 weight inputs" (weightInputs.length == 4)

  -- All weight inputs are 2-bit
  let allWeights2bit := weightInputs.all (fun p => p.ty == .bitVector 2)
  check "dynamic: all weight inputs are 2-bit" allWeights2bit

  -- All inDim activation inputs present
  let actInputs := m.inputs.filter (fun p => p.name.startsWith "act_")
  check "dynamic: 4 activation inputs" (actInputs.length == 4)

  -- Result output exists
  check "dynamic: 1 output" (m.outputs.length == 1)
  check "dynamic: output named 'result'" (m.outputs.head?.map (·.name) == some "result")

  -- Non-empty Verilog generation
  let verilog := toVerilog m
  check "dynamic: generates non-empty Verilog" (verilog.length > 100)

  -- Module name
  check "dynamic: module named DynamicBitLinear_4" (m.name == "DynamicBitLinear_4")

-- ============================================================================
-- 3. HardwiredUnrolled SoC Tests
-- ============================================================================

def testHardwiredSoC : IO Unit := do
  IO.println "--- HardwiredUnrolled SoC Tests ---"

  let m := SoC.buildBitNetSoC testSoCConfigHW testLayerWeights testLayerScales testGenCfg

  -- Module generates without error
  check "hw: module generates" (m.name.length > 0)

  -- Module name contains "HW"
  check "hw: name contains HW" (m.name == "BitNet_SoC_HW_2L_4d")

  -- Has x_in input
  let hasXin := m.inputs.any (fun p => p.name == "x_in")
  check "hw: has x_in input" hasXin

  -- Has y_out output
  let hasYout := m.outputs.any (fun p => p.name == "y_out")
  check "hw: has y_out output" hasYout

  -- Has clk/rst inputs
  let hasClk := m.inputs.any (fun p => p.name == "clk")
  let hasRst := m.inputs.any (fun p => p.name == "rst")
  check "hw: has clk input" hasClk
  check "hw: has rst input" hasRst

  -- Has done output
  let hasDone := m.outputs.any (fun p => p.name == "done")
  check "hw: has done output" hasDone

  -- Non-empty Verilog
  let verilog := toVerilog m
  check "hw: generates non-empty Verilog" (verilog.length > 100)

  IO.println ""
  IO.println "  --- HardwiredUnrolled SoC Verilog (truncated) ---"
  let truncated := if verilog.length > 1500 then (verilog.take 1500).toString ++ "\n  ... (truncated)" else verilog
  IO.println truncated

-- ============================================================================
-- 4. TimeMultiplexed SoC Tests
-- ============================================================================

def testTimeMultiplexedSoC : IO Unit := do
  IO.println "--- TimeMultiplexed SoC Tests ---"

  let m := SoC.buildBitNetSoC testSoCConfigTM testLayerWeights testLayerScales testGenCfg

  -- Module generates without error
  check "tm: module generates" (m.name.length > 0)

  -- Module name contains "TM"
  check "tm: name contains TM" (m.name == "BitNet_SoC_TM_2L_4d")

  -- Has x_in input
  let hasXin := m.inputs.any (fun p => p.name == "x_in")
  check "tm: has x_in input" hasXin

  -- Has y_out output
  let hasYout := m.outputs.any (fun p => p.name == "y_out")
  check "tm: has y_out output" hasYout

  -- Has clk/rst inputs
  let hasClk := m.inputs.any (fun p => p.name == "clk")
  let hasRst := m.inputs.any (fun p => p.name == "rst")
  check "tm: has clk input" hasClk
  check "tm: has rst input" hasRst

  -- Has done output
  let hasDone := m.outputs.any (fun p => p.name == "done")
  check "tm: has done output" hasDone

  -- Has FSM registers (state register)
  let regCount := m.body.foldl (fun acc s =>
    match s with
    | .register .. => acc + 1
    | _ => acc) 0
  check "tm: has FSM registers" (regCount ≥ 3)  -- state, layer_idx, act_reg

  -- Non-empty Verilog
  let verilog := toVerilog m
  check "tm: generates non-empty Verilog" (verilog.length > 100)

  IO.println ""
  IO.println "  --- TimeMultiplexed SoC Verilog (truncated) ---"
  let truncated := if verilog.length > 1500 then (verilog.take 1500).toString ++ "\n  ... (truncated)" else verilog
  IO.println truncated

-- ============================================================================
-- 5. Cross-Architecture Comparison Tests
-- ============================================================================

def testComparison : IO Unit := do
  IO.println "--- Cross-Architecture Comparison Tests ---"

  let hwMod := SoC.buildBitNetSoC testSoCConfigHW testLayerWeights testLayerScales testGenCfg
  let tmMod := SoC.buildBitNetSoC testSoCConfigTM testLayerWeights testLayerScales testGenCfg

  let hwVerilog := toVerilog hwMod
  let tmVerilog := toVerilog tmMod

  -- Both generate valid Verilog
  check "compare: both generate valid Verilog"
    (hwVerilog.length > 100 && tmVerilog.length > 100)

  -- Both have the same I/O interface (x_in, y_out, clk, rst, done)
  let hwHasXin := hwMod.inputs.any (fun p => p.name == "x_in")
  let tmHasXin := tmMod.inputs.any (fun p => p.name == "x_in")
  check "compare: both have x_in" (hwHasXin && tmHasXin)

  let hwHasYout := hwMod.outputs.any (fun p => p.name == "y_out")
  let tmHasYout := tmMod.outputs.any (fun p => p.name == "y_out")
  check "compare: both have y_out" (hwHasYout && tmHasYout)

  -- Module names differ
  check "compare: different module names" (hwMod.name != tmMod.name)

def runAll : IO Unit := do
  IO.println "=== SoC Tests ==="
  IO.println ""
  testArchMode
  IO.println ""
  testDynamicBitLinear
  IO.println ""
  testHardwiredSoC
  IO.println ""
  testTimeMultiplexedSoC
  IO.println ""
  testComparison
  IO.println ""
  IO.println "=== All SoC tests complete ==="

end Sparkle.Examples.BitNet.Tests.SoC
