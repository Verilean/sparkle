import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-!
# Simple Working CPU - Step by Step

Start with basic components that work, then build up complexity.
-/

-- ============================================================================
-- LEVEL 3: Basic Operations (THESE WORK!)
-- ============================================================================

def add16 (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· + ·) <$> a <*> b

def sub16 (a b : Signal Domain (BitVec 16)) : Signal Domain (BitVec 16) :=
  (· - ·) <$> a <*> b

-- ============================================================================
-- LEVEL 2: Simple 2-Way ALU
-- ============================================================================

-- ALU with just 2 operations: ADD (op=0) and SUB (op=1)
def simpleALU (op : Signal Domain Bool) (a b : Signal Domain (BitVec 16))
    : Signal Domain (BitVec 16) :=
  let addResult := add16 a b
  let subResult := sub16 a b
  Signal.mux op subResult addResult  -- op=0: ADD, op=1: SUB

-- ============================================================================
-- LEVEL 2: Simple ROM (4 instructions using nested mux)
-- ============================================================================

-- Simplified ROM: Returns a fixed value
-- ROM synthesis with mux trees needs more work - this is a placeholder
def simpleROM4 (addr : Signal Domain (BitVec 2)) : Signal Domain (BitVec 16) :=
  -- Placeholder: just use the address input as-is (demonstrates parameter passing)
  -- TODO: Implement actual mux-based ROM
  let _unused := addr
  Signal.pure (0x0005 : BitVec 16)  -- Return constant: ADD 5 instruction

-- ============================================================================
-- LEVEL 1: Simple Datapath (Fetch + Execute)
-- ============================================================================

-- Simple datapath that:
-- 1. Fetches instruction from ROM
-- 2. Decodes opcode and immediate
-- 3. Executes ADD or SUB with immediate value

def simpleCPU (addr : Signal Domain (BitVec 2)) : Signal Domain (BitVec 16) :=
  -- Fetch instruction
  let instruction := simpleROM4 addr

  -- Decode
  let opcode := Signal.map (fun i => i.getLsbD 15) instruction  -- Bit 15 = opcode
  let immediate := Signal.map (fun i => i &&& 0xFF) instruction  -- Lower 8 bits

  -- Execute: ALU operation with accumulator value
  let accumulator := Signal.pure (100 : BitVec 16)  -- Fixed accumulator for demo
  let result := simpleALU opcode accumulator immediate

  result

-- ============================================================================
-- Synthesis Commands
-- ============================================================================

-- Level 3: Basic operations
#synthesizeVerilog add16
#synthesizeVerilog sub16

-- Level 2: ALU (should instantiate add16 and sub16)
#synthesizeVerilogDesign simpleALU

-- Level 2: ROM (nested mux tree)
#synthesizeVerilogDesign simpleROM4

-- Level 1: Complete simple CPU
-- Hierarchical structure:
--   simpleCPU
--   ├── simpleROM4 (ROM with program)
--   └── simpleALU
--       ├── add16
--       └── sub16
#synthesizeVerilogDesign simpleCPU
