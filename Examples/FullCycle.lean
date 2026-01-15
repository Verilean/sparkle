/-
  Full Cycle Example: Multiply-Accumulate (MAC) Unit

  Demonstrates Phase 4 complete functionality:
  - Sequential logic with registers
  - Arithmetic operations (multiply, add)
  - Clock and reset handling
  - State accumulation

  A MAC unit computes: acc' = acc + (a * b)
-/

import Sparkle.IR.Builder
import Sparkle.Backend.Verilog

open Sparkle.IR.Type
open Sparkle.IR.AST
open Sparkle.IR.Builder
open Sparkle.Backend.Verilog
open CircuitM

/--
  MAC Unit: Multiply-Accumulate

  Inputs:
  - clk: Clock signal
  - rst: Reset signal
  - a: First operand (8-bit)
  - b: Second operand (8-bit)
  - en: Enable signal

  Output:
  - acc: Accumulated result (16-bit to prevent overflow)

  Operation: when enabled, acc' = acc + (a * b)
-/
def macUnit : Module :=
  runModule "MAC" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "en" .bit
    addInput "a" (.bitVector 8)
    addInput "b" (.bitVector 8)

    -- Multiply a * b
    let product ← makeWire "product" (.bitVector 16)
    -- Extend operands to 16-bit for multiplication
    let aExt ← makeWire "a_ext" (.bitVector 16)
    let bExt ← makeWire "b_ext" (.bitVector 16)

    -- Zero-extend 8-bit to 16-bit (concatenate with zeros)
    emitAssign aExt (.ref "a")  -- Simplified: in real HW would need proper extension
    emitAssign bExt (.ref "b")
    emitAssign product (.op .mul [.ref aExt, .ref bExt])

    -- Compute next accumulator value
    let accNext ← makeWire "acc_next" (.bitVector 16)
    let accCurrent ← emitRegister "acc_reg" "clk" "rst" (.ref accNext) 0 (.bitVector 16)

    -- Add product to accumulator
    let sum ← makeWire "sum" (.bitVector 16)
    emitAssign sum (.op .add [.ref accCurrent, .ref product])

    -- Mux: if enabled, update with sum, else keep current value
    emitAssign accNext (.op .mux [.ref "en", .ref sum, .ref accCurrent])

    -- Output
    addOutput "acc" (.bitVector 16)
    emitAssign "acc" (.ref accCurrent)

/--
  FIR Filter (Finite Impulse Response) - 3-tap

  Implements: y[n] = c0*x[n] + c1*x[n-1] + c2*x[n-2]

  This is a simple 3-tap FIR filter with fixed coefficients.
-/
def firFilter3Tap : Module :=
  runModule "FIR3Tap" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "x" (.bitVector 8)  -- Input sample

    -- Coefficients (hardcoded for this example)
    let c0 := 2  -- Coefficient for current sample
    let c1 := 3  -- Coefficient for 1-sample delay
    let c2 := 1  -- Coefficient for 2-sample delay

    -- Delay line: x[n-1] and x[n-2]
    let xn1 ← emitRegister "x_n1" "clk" "rst" (.ref "x") 0 (.bitVector 8)
    let xn2 ← emitRegister "x_n2" "clk" "rst" (.ref xn1) 0 (.bitVector 8)

    -- Multiply by coefficients
    let term0 ← makeWire "term0" (.bitVector 8)
    emitAssign term0 (.op .mul [.ref "x", .const c0 8])

    let term1 ← makeWire "term1" (.bitVector 8)
    emitAssign term1 (.op .mul [.ref xn1, .const c1 8])

    let term2 ← makeWire "term2" (.bitVector 8)
    emitAssign term2 (.op .mul [.ref xn2, .const c2 8])

    -- Sum all terms
    let sum01 ← makeWire "sum01" (.bitVector 8)
    emitAssign sum01 (.op .add [.ref term0, .ref term1])

    let result ← makeWire "result" (.bitVector 8)
    emitAssign result (.op .add [.ref sum01, .ref term2])

    -- Output
    addOutput "y" (.bitVector 8)
    emitAssign "y" (.ref result)

/--
  State Machine: Simple Traffic Light Controller

  States:
  - 00: Red
  - 01: Red+Yellow
  - 10: Green
  - 11: Yellow

  Transitions every N cycles (simplified with counter)
-/
def trafficLight : Module :=
  runModule "TrafficLight" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit

    -- State register (2 bits for 4 states)
    let stateNext ← makeWire "state_next" (.bitVector 2)
    let stateCurrent ← emitRegister "state" "clk" "rst" (.ref stateNext) 0 (.bitVector 2)

    -- Next state logic (increment state, wrap around)
    let stateInc ← makeWire "state_inc" (.bitVector 2)
    emitAssign stateInc (.op .add [.ref stateCurrent, .const 1 2])

    -- Check if we've reached state 3 (11), then wrap to 0
    let isState3 ← makeWire "is_state3" .bit
    emitAssign isState3 (.op .eq [.ref stateCurrent, .const 3 2])

    emitAssign stateNext (.op .mux [.ref isState3, .const 0 2, .ref stateInc])

    -- Decode state to outputs
    let isRed ← makeWire "is_red" .bit
    emitAssign isRed (.op .or [
      .op .eq [.ref stateCurrent, .const 0 2],
      .op .eq [.ref stateCurrent, .const 1 2]
    ])

    let isYellow ← makeWire "is_yellow" .bit
    emitAssign isYellow (.op .or [
      .op .eq [.ref stateCurrent, .const 1 2],
      .op .eq [.ref stateCurrent, .const 3 2]
    ])

    let isGreen ← makeWire "is_green" .bit
    emitAssign isGreen (.op .eq [.ref stateCurrent, .const 2 2])

    -- Outputs
    addOutput "red" .bit
    emitAssign "red" (.ref isRed)

    addOutput "yellow" .bit
    emitAssign "yellow" (.ref isYellow)

    addOutput "green" .bit
    emitAssign "green" (.ref isGreen)

/--
  Shift Register: Serial to Parallel Converter

  Shifts data in serially and outputs 8 bits in parallel.
-/
def shiftRegister8 : Module :=
  runModule "ShiftRegister8" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "serial_in" .bit
    addInput "shift_en" .bit

    -- 8-bit shift register
    let srNext ← makeWire "sr_next" (.bitVector 8)
    let srCurrent ← emitRegister "sr" "clk" "rst" (.ref srNext) 0 (.bitVector 8)

    -- Shift left, insert serial_in at LSB
    let shifted ← makeWire "shifted" (.bitVector 8)
    emitAssign shifted (.op .shl [.ref srCurrent, .const 1 8])

    let withInput ← makeWire "with_input" (.bitVector 8)
    emitAssign withInput (.op .or [.ref shifted, .ref "serial_in"])

    -- If shift enabled, use new value, else keep current
    emitAssign srNext (.op .mux [.ref "shift_en", .ref withInput, .ref srCurrent])

    -- Output
    addOutput "parallel_out" (.bitVector 8)
    emitAssign "parallel_out" (.ref srCurrent)

/--
  FIFO Buffer (simplified, 4 entries)

  A simple circular buffer with write and read pointers.
-/
def fifo4 : Module :=
  runModule "FIFO4" do
    -- Inputs
    addInput "clk" .bit
    addInput "rst" .bit
    addInput "wr_en" .bit
    addInput "rd_en" .bit
    addInput "din" (.bitVector 8)

    -- Write pointer (2-bit, counts 0-3)
    let wrPtrNext ← makeWire "wr_ptr_next" (.bitVector 2)
    let wrPtrCurrent ← emitRegister "wr_ptr" "clk" "rst" (.ref wrPtrNext) 0 (.bitVector 2)

    -- Read pointer (2-bit, counts 0-3)
    let rdPtrNext ← makeWire "rd_ptr_next" (.bitVector 2)
    let rdPtrCurrent ← emitRegister "rd_ptr" "clk" "rst" (.ref rdPtrNext) 0 (.bitVector 2)

    -- Increment pointers when enabled
    let wrPtrInc ← makeWire "wr_ptr_inc" (.bitVector 2)
    emitAssign wrPtrInc (.op .add [.ref wrPtrCurrent, .const 1 2])
    emitAssign wrPtrNext (.op .mux [.ref "wr_en", .ref wrPtrInc, .ref wrPtrCurrent])

    let rdPtrInc ← makeWire "rd_ptr_inc" (.bitVector 2)
    emitAssign rdPtrInc (.op .add [.ref rdPtrCurrent, .const 1 2])
    emitAssign rdPtrNext (.op .mux [.ref "rd_en", .ref rdPtrInc, .ref rdPtrCurrent])

    -- Count (tracks number of elements)
    let countNext ← makeWire "count_next" (.bitVector 3)
    let countCurrent ← emitRegister "count" "clk" "rst" (.ref countNext) 0 (.bitVector 3)

    -- Update count based on write/read
    let bothOps ← makeWire "both_ops" .bit
    emitAssign bothOps (.op .and [.ref "wr_en", .ref "rd_en"])

    let onlyWr ← makeWire "only_wr" .bit
    emitAssign onlyWr (.op .and [.ref "wr_en", .op .not [.ref "rd_en"]])

    let onlyRd ← makeWire "only_rd" .bit
    emitAssign onlyRd (.op .and [.ref "rd_en", .op .not [.ref "wr_en"]])

    let countInc ← makeWire "count_inc" (.bitVector 3)
    emitAssign countInc (.op .add [.ref countCurrent, .const 1 3])

    let countDec ← makeWire "count_dec" (.bitVector 3)
    emitAssign countDec (.op .sub [.ref countCurrent, .const 1 3])

    -- Mux for count update
    let countTemp ← makeWire "count_temp" (.bitVector 3)
    emitAssign countTemp (.op .mux [.ref onlyWr, .ref countInc,
                          .op .mux [.ref onlyRd, .ref countDec, .ref countCurrent]])
    emitAssign countNext (.ref countTemp)

    -- Status outputs
    let isEmpty ← makeWire "is_empty" .bit
    emitAssign isEmpty (.op .eq [.ref countCurrent, .const 0 3])

    let isFull ← makeWire "is_full" .bit
    emitAssign isFull (.op .eq [.ref countCurrent, .const 4 3])

    addOutput "empty" .bit
    emitAssign "empty" (.ref isEmpty)

    addOutput "full" .bit
    emitAssign "full" (.ref isFull)

    -- For simplicity, output current data (real FIFO would need memory)
    addOutput "dout" (.bitVector 8)
    emitAssign "dout" (.ref "din")  -- Simplified

/-- Main: Generate all advanced examples -/
def main : IO Unit := do
  IO.println "=== Sparkle Phase 4: Advanced Examples ===\n"

  IO.println "1. MAC (Multiply-Accumulate) Unit:"
  let macV := toVerilog macUnit
  IO.println macV
  writeVerilogFile macUnit "MAC.sv"
  IO.println ""

  IO.println "2. FIR Filter (3-tap):"
  let firV := toVerilog firFilter3Tap
  IO.println firV
  writeVerilogFile firFilter3Tap "FIR3Tap.sv"
  IO.println ""

  IO.println "3. Traffic Light Controller:"
  let trafficV := toVerilog trafficLight
  IO.println trafficV
  writeVerilogFile trafficLight "TrafficLight.sv"
  IO.println ""

  IO.println "4. Shift Register (8-bit):"
  let shiftV := toVerilog shiftRegister8
  IO.println shiftV
  writeVerilogFile shiftRegister8 "ShiftRegister8.sv"
  IO.println ""

  IO.println "5. FIFO Buffer (4 entries):"
  let fifoV := toVerilog fifo4
  IO.println fifoV
  writeVerilogFile fifo4 "FIFO4.sv"
  IO.println ""

  IO.println "✓ Phase 4 advanced examples complete!"
  IO.println "✓ Generated comprehensive SystemVerilog modules"

#eval main
