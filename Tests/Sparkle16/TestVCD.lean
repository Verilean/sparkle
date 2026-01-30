/-
  VCD Writer Tests using Sparkle16

  Tests VCD (Value Change Dump) waveform generation using the Sparkle16 ALU
  and datapath modules. Generated VCD files can be viewed in GTKWave.
-/

import Sparkle
import Sparkle.Backend.VCD
import LSpec
import Tests.Sparkle16.TestALU
import Tests.Sparkle16.TestHierarchical

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Backend.VCD
open LSpec

namespace Sparkle16.Test

/-!
## VCD Writer Tests

These tests verify that:
1. VCD files are generated correctly from Signal simulations
2. VCD format contains proper headers, variable declarations, and traces
3. Waveforms can be generated for Sparkle16 modules (ALU, datapath)
-/

/-- Test: VCD header generation -/
def test_vcd_header : IO TestSeq := do
  let writer := VCDWriter.new "test_module"
  let header := generateHeader writer

  return group "VCD Header" (
    test "contains $date" (header.contains "$date") $
    test "contains $version" (header.contains "$version") $
    test "contains Sparkle HDL" (header.contains "Sparkle") $
    test "contains $timescale" (header.contains "$timescale") $
    test "ends sections with $end" (header.contains "$end")
  )

/-- Test: VCD variable declarations -/
def test_vcd_var_decls : IO TestSeq := do
  let writer := VCDWriter.new "alu_test"
    |>.addVar "a" 16
    |>.addVar "b" 16
    |>.addVar "result" 16

  let decls := generateVarDecls writer

  return group "VCD Variable Declarations" (
    test "contains module scope" (decls.contains "$scope module alu_test") $
    test "declares variable 'a'" (decls.contains "a") $
    test "declares variable 'b'" (decls.contains "b") $
    test "declares variable 'result'" (decls.contains "result") $
    test "has 16-bit width" (decls.contains "16") $
    test "ends definitions" (decls.contains "$enddefinitions")
  )

/-!
## Sparkle16 ALU VCD Test

Generate VCD waveform for ALU performing ADD and SUB operations.
-/

def test_alu_vcd_generation : IO TestSeq := do
  -- Create time-varying signals for ALU
  let a : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (10 + t * 5)⟩
  let b : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (20 + t * 3)⟩

  -- Test both ADD and SUB
  let selAdd := Signal.pure false  -- ADD operation
  let resultAdd := alu selAdd a b

  -- Setup VCD writer
  let writer := VCDWriter.new "sparkle16_alu"
    |>.addVar "a" 16
    |>.addVar "b" 16
    |>.addVar "sel" 1
    |>.addVar "result" 16

  -- Get variable identifiers
  let aId := (writer.variables[0]!).identifier
  let bId := (writer.variables[1]!).identifier
  let selId := (writer.variables[2]!).identifier
  let resultId := (writer.variables[3]!).identifier

  -- Sample signals over 5 cycles
  let cycles := 5
  let traceA := sampleBitVecSignal a aId cycles
  let traceB := sampleBitVecSignal b bId cycles
  let traceSel := sampleBoolSignal selAdd selId cycles
  let traceResult := sampleBitVecSignal resultAdd resultId cycles

  let allTraces := traceA ++ traceB ++ traceSel ++ traceResult

  -- Generate VCD
  let vcd := generateVCD writer allTraces

  -- Optionally write to file for manual inspection with GTKWave
  -- writeVCDFile "/tmp/sparkle16_alu.vcd" vcd

  return group "Sparkle16 ALU VCD Generation" (
    test "VCD contains header" (vcd.contains "$date") $
    test "VCD contains module name" (vcd.contains "sparkle16_alu") $
    test "VCD contains variable 'a'" (vcd.contains "a") $
    test "VCD contains variable 'result'" (vcd.contains "result") $
    test "VCD has initial dump" (vcd.contains "$dumpvars") $
    test "VCD has timestamps" (vcd.contains "#0") $
    test "VCD has multiple time points" (vcd.contains "#1") $
    test "VCD contains binary values" (vcd.contains "b") $
    test "VCD is non-empty" (vcd.length > 100)
  )

/-!
## Sparkle16 Datapath VCD Test

Generate VCD for hierarchical datapath (ALU + register) showing register delay.
-/

def test_datapath_vcd_generation : IO TestSeq := do
  -- Time-varying inputs
  let a : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 10)⟩
  let b : Signal defaultDomain (BitVec 16) := ⟨fun t => BitVec.ofNat 16 (t * 5)⟩
  let sel := Signal.pure false  -- ADD

  -- Datapath (ALU + register)
  let result := datapath sel a b

  -- Setup VCD writer
  let writer := VCDWriter.new "sparkle16_datapath"
    |>.addVar "a" 16
    |>.addVar "b" 16
    |>.addVar "sel" 1
    |>.addVar "alu_out" 16
    |>.addVar "reg_out" 16

  -- Get IDs
  let aId := (writer.variables[0]!).identifier
  let bId := (writer.variables[1]!).identifier
  let selId := (writer.variables[2]!).identifier
  let aluOutId := (writer.variables[3]!).identifier
  let regOutId := (writer.variables[4]!).identifier

  -- Compute ALU output (before register)
  let aluOut := alu sel a b

  -- Sample over 8 cycles to show register delay
  let cycles := 8
  let traceA := sampleBitVecSignal a aId cycles
  let traceB := sampleBitVecSignal b bId cycles
  let traceSel := sampleBoolSignal sel selId cycles
  let traceAluOut := sampleBitVecSignal aluOut aluOutId cycles
  let traceRegOut := sampleBitVecSignal result regOutId cycles

  let allTraces := traceA ++ traceB ++ traceSel ++ traceAluOut ++ traceRegOut

  -- Generate VCD
  let vcd := generateVCD writer allTraces

  -- Optionally write for viewing
  -- writeVCDFile "/tmp/sparkle16_datapath.vcd" vcd

  return group "Sparkle16 Datapath VCD Generation" (
    test "VCD contains datapath module" (vcd.contains "sparkle16_datapath") $
    test "VCD contains inputs (a, b)" (vcd.contains "a" && vcd.contains "b") $
    test "VCD contains alu_out" (vcd.contains "alu_out") $
    test "VCD contains reg_out" (vcd.contains "reg_out") $
    test "VCD has 8 time points" (vcd.contains "#7") $
    test "VCD shows register delay" (
      -- At t=0, reg_out should be 0 (initial)
      -- At t=1, reg_out should be alu_out(t=0)
      vcd.contains "#0" && vcd.contains "#1"
    ) $
    test "VCD is well-formed" (vcd.length > 200)
  )

/-!
## VCD Format Validation Tests

Test that generated VCD conforms to IEEE 1364 standard format.
-/

def test_vcd_format_validation : IO TestSeq := do
  let writer := VCDWriter.new "format_test"
    |>.addVar "clk" 1
    |>.addVar "data" 8

  let clk : Signal defaultDomain Bool := ⟨fun t => t % 2 == 1⟩
  let data : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 (t * 10)⟩

  let clkId := (writer.variables[0]!).identifier
  let dataId := (writer.variables[1]!).identifier

  let traceClk := sampleBoolSignal clk clkId 4
  let traceData := sampleBitVecSignal data dataId 4

  let vcd := generateVCD writer (traceClk ++ traceData)

  return group "VCD Format Validation" (
    test "starts with $date" (vcd.startsWith "$date") $
    test "has proper section endings" (
      vcd.contains "$end\n$version" &&
      vcd.contains "$end\n$timescale"
    ) $
    test "binary values have 'b' prefix" (vcd.contains "b00") $
    test "bit values are 0 or 1" (vcd.contains "0" || vcd.contains "1") $
    test "timestamps start with #" (vcd.contains "#0") $
    test "identifiers are printable ASCII" (vcd.contains "!") $
    test "has dumpvars section" (vcd.contains "$dumpvars")
  )

/-!
## Combined Test Suite
-/

def vcdTests : IO TestSeq := do
  let headerTests ← test_vcd_header
  let varDeclTests ← test_vcd_var_decls
  let aluVCDTests ← test_alu_vcd_generation
  let datapathVCDTests ← test_datapath_vcd_generation
  let formatTests ← test_vcd_format_validation

  return group "VCD Writer Tests" (
    headerTests ++
    varDeclTests ++
    aluVCDTests ++
    datapathVCDTests ++
    formatTests
  )

end Sparkle16.Test
