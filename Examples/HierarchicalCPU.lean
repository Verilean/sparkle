import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

-- ============================================================================
-- LEVEL 3: Leaf Modules (Basic Operations)
-- ============================================================================

-- 16-bit Adder Module
def adder16 (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· + ·) <$> a <*> b

-- 16-bit Logic Unit (AND, OR, XOR)
def logicUnit16 (op : Signal Domain (BitVec 2)) (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  let andResult := (· &&& ·) <$> a <*> b
  let orResult := (· ||| ·) <$> a <*> b
  let xorResult := (· ^^^ ·) <$> a <*> b

  -- Mux based on op: 00=AND, 01=OR, 10=XOR, 11=AND (default)
  let sel0 := Signal.map (fun x => x.getLsbD 0) op
  let sel1 := Signal.map (fun x => x.getLsbD 1) op

  let mux01 := Signal.mux sel0 orResult andResult
  let mux23 := Signal.mux sel0 andResult xorResult
  Signal.mux sel1 mux23 mux01

-- ============================================================================
-- LEVEL 2: ALU Module (Combines Basic Operations)
-- ============================================================================

-- ALU Operation Encoding:
-- 000: ADD
-- 001: SUB
-- 010: AND
-- 011: OR
-- 100: XOR
-- 101-111: Reserved (returns ADD result)
def alu16 (op : Signal Domain (BitVec 3)) (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  -- Arithmetic operations
  let addResult := adder16 a b
  let subResult := adder16 a (Signal.map (· ^^^ 0xFFFF) b)  -- a + (~b) for subtraction approximation

  -- Logic operations - extract lower 2 bits for logic unit
  let logicOp := Signal.map (fun x => x.truncate 2) op
  let logicResult := logicUnit16 logicOp a b

  -- Main mux tree based on op[2:1]
  let isArith := Signal.map (fun x => !x.getLsbD 2) op  -- op[2] == 0
  let isAdd := Signal.map (fun x => !x.getLsbD 0) op    -- op[0] == 0

  let arithResult := Signal.mux isAdd addResult subResult
  Signal.mux isArith arithResult logicResult

-- ============================================================================
-- LEVEL 2: Register File Module
-- ============================================================================

-- Simplified 2-register file for demonstration
-- This shows how sub-modules can combine multiple signals
-- sel: which register to read (0 or 1)
-- val0, val1: two input values to choose from
-- Returns: selected value
def registerFile2
    (sel : Signal Domain Bool)
    (val0 val1 : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=

  -- Simple multiplexer: select between val0 and val1
  Signal.mux sel val1 val0

-- ============================================================================
-- LEVEL 1: Simple CPU Core (Top-level - Instantiates ALU and RegisterFile)
-- ============================================================================

-- Instruction format (16-bit):
-- [15:13] opcode (3 bits)
-- [12:11] rs1 (2 bits)
-- [10:9]  rs2 (2 bits)
-- [8:7]   rd (2 bits)
-- [6:0]   immediate (7 bits, unused in this simple example)

def simpleCPU (instruction : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  -- Decode instruction fields using shift and mask operations
  let opcode := Signal.map (fun (i : BitVec 16) => ((i >>> 13) &&& 0b111).truncate 3) instruction  -- bits [15:13]
  let sel := Signal.map (fun (i : BitVec 16) => i.getLsbD 12) instruction  -- bit 12 for register select

  -- ALU instantiation (LEVEL 2 MODULE, which internally uses LEVEL 3 modules)
  -- Using simple constant operands for demonstration
  let operand1 := Signal.pure (42 : BitVec 16)
  let operand2 := Signal.pure (17 : BitVec 16)
  let aluResult := alu16 opcode operand1 operand2

  -- Create two different values to demonstrate register file selection
  let val0 := aluResult
  let val1 := Signal.map (fun x => x * 2) aluResult

  -- Register file instantiation (LEVEL 2 MODULE) - acts as a mux selector
  let regValue := registerFile2 sel val0 val1

  -- Output: the selected value
  regValue

-- ============================================================================
-- Synthesis Commands
-- ============================================================================

-- Test Level 3: Individual leaf modules
#synthesizeVerilog adder16
-- #synthesizeVerilog logicUnit16  -- TODO: Fix truncate issue

-- Test Level 2: ALU (should instantiate adder16 and logicUnit16)
-- #synthesizeVerilogDesign alu16  -- TODO: Fix after logicUnit16 is fixed

-- Test Level 2: Register file (WORKING!)
#synthesizeVerilogDesign registerFile2

-- Test Level 1: Complete CPU (should instantiate alu16 and registerFile2)
-- This creates a 3-level hierarchy:
--   simpleCPU -> alu16 -> adder16, logicUnit16
--   simpleCPU -> registerFile2
-- #synthesizeVerilogDesign simpleCPU  -- TODO: Fix after alu16 is fixed

-- ============================================================================
-- Simpler Working Example: 2-level hierarchy
-- ============================================================================

-- Demonstrates working hierarchical synthesis with two adders composed
def twoStageAdder (a b c : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  let sum1 := adder16 a b        -- First adder instance (LEVEL 2)
  adder16 sum1 c                 -- Second adder instance (LEVEL 2)

-- Test hierarchical synthesis: twoStageAdder instantiates adder16 twice
#synthesizeVerilogDesign twoStageAdder
