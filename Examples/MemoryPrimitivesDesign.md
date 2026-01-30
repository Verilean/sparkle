# Memory Primitives Design Document

## Overview

This document outlines the design for SRAM/BRAM memory primitives in Sparkle HDL.

## Goals

1. **Simple synchronous RAM** - Single-port read/write memory
2. **Dual-port RAM** - Simultaneous read/write to different addresses
3. **Register files** - Small, fast memories for CPU registers
4. **Clean Verilog generation** - Synthesizable to FPGA BRAM or ASIC SRAM

## Design Approach

### Memory Model

Memory is modeled as a stateful component with:
- **Address space**: 2^addrWidth locations
- **Data width**: Width of each memory word
- **Synchronous writes**: Write on clock edge when write-enable is high
- **Combinational or synchronous reads**: Configurable

### Signal-Level API

Since Signals are pure functional streams, we model memory as:

```lean
-- Memory state: a function from address to data
-- This is a Signal of the entire memory contents
def MemoryState (addrWidth dataWidth : Nat) : Type :=
  BitVec addrWidth → BitVec dataWidth

-- Memory primitive: creates a memory with read/write ports
def Signal.memory
    {d : DomainConfig}
    (addrWidth : Nat)   -- Address width (size = 2^addrWidth)
    (dataWidth : Nat)   -- Data width
    (writeAddr : Signal d (BitVec addrWidth))   -- Write address
    (writeData : Signal d (BitVec dataWidth))   -- Write data
    (writeEnable : Signal d Bool)               -- Write enable
    (readAddr : Signal d (BitVec addrWidth))    -- Read address
    : Signal d (BitVec dataWidth)               -- Read data
```

#### Behavior:

1. **Write Operation** (synchronous):
   ```
   At each clock cycle t:
   if writeEnable.atTime t then
     memory[writeAddr.atTime t] := writeData.atTime t
   ```

2. **Read Operation** (synchronous):
   ```
   readData.atTime (t+1) = memory[readAddr.atTime t]
   ```

   Note: Read is registered (1-cycle latency), matching FPGA BRAM behavior.

#### Alternative: Combinational Read

For asynchronous/combinational reads:

```lean
def Signal.memoryComb
    (addrWidth dataWidth : Nat)
    (writeAddr : Signal d (BitVec addrWidth))
    (writeData : Signal d (BitVec dataWidth))
    (writeEnable : Signal d Bool)
    (readAddr : Signal d (BitVec addrWidth))
    : Signal d (BitVec dataWidth)

-- Read is combinational: readData.atTime t = memory[readAddr.atTime t]
```

### IR-Level Support

Add new IR constructs:

```lean
-- Memory declaration statement
inductive Stmt where
  | ...
  | memory
      (name : String)          -- Memory instance name
      (addrWidth : Nat)        -- Address width
      (dataWidth : Nat)        -- Data width
      (clock : String)         -- Clock signal
      (writeAddr : Expr)       -- Write address port
      (writeData : Expr)       -- Write data port
      (writeEnable : Expr)     -- Write enable port
      (readAddr : Expr)        -- Read address port
      (readData : String)      -- Read data output wire
      : Stmt
```

### Verilog Generation

The memory IR should generate clean Verilog:

```systemverilog
// Synchronous memory with registered read
logic [7:0] mem [0:255];  // 256 x 8-bit memory
logic [7:0] read_data;

always_ff @(posedge clk) begin
  if (write_enable) begin
    mem[write_addr] <= write_data;
  end
  read_data <= mem[read_addr];  // Registered read
end
```

For combinational reads:

```systemverilog
// Synchronous write, combinational read
logic [7:0] mem [0:255];

always_ff @(posedge clk) begin
  if (write_enable) begin
    mem[write_addr] <= write_data;
  end
end

assign read_data = mem[read_addr];  // Combinational read
```

## Usage Examples

### Example 1: Simple RAM

```lean
-- 256-byte memory (8-bit address, 8-bit data)
def simpleRAM
    (writeAddr : Signal d (BitVec 8))
    (writeData : Signal d (BitVec 8))
    (writeEnable : Signal d Bool)
    (readAddr : Signal d (BitVec 8))
    : Signal d (BitVec 8) :=
  Signal.memory 8 8 writeAddr writeData writeEnable readAddr
```

### Example 2: Register File (CPU Registers)

```lean
-- 8 registers, 16-bit each (3-bit address, 16-bit data)
def registerFile
    (writeReg : Signal d (BitVec 3))   -- R0-R7
    (writeData : Signal d (BitVec 16))
    (writeEnable : Signal d Bool)
    (readReg : Signal d (BitVec 3))
    : Signal d (BitVec 16) :=
  Signal.memory 3 16 writeReg writeData writeEnable readReg
```

### Example 3: Dual-Port RAM

For true dual-port (simultaneous read/write to different addresses):

```lean
-- Two separate memory primitives sharing state (advanced, future work)
-- OR use synthesis-level primitive module for vendor BRAM
def dualPortRAM : Module :=
  Module.primitive "DUAL_PORT_RAM"
    [ ("clk", .bit)
    , ("we_a", .bit)
    , ("addr_a", .bitVector 8)
    , ("din_a", .bitVector 8)
    , ("dout_a", .bitVector 8)
    , ("we_b", .bit)
    , ("addr_b", .bitVector 8)
    , ("din_b", .bitVector 8)
    , ("dout_b", .bitVector 8)
    ]
    [ ]
```

## Implementation Plan

1. ✓ Design document (this file)
2. Add `Stmt.memory` to IR AST
3. Implement `Signal.memory` in Signal.lean
4. Update Verilog backend to emit memory declarations
5. Add memory synthesis support to Compiler/Elab.lean
6. Create examples (SimpleRAM, RegisterFile)
7. Write comprehensive tests
8. Update README and documentation

## Constraints and Limitations

### Initial Implementation:

- **Single-port only**: One read port, one write port
- **Synchronous writes**: Writes happen on clock edge
- **Registered reads**: 1-cycle read latency (matches FPGA BRAM)
- **No initialization**: Memory contents undefined at start (can be added later)
- **Fixed size**: Size determined at compile time (2^addrWidth)

### Future Enhancements:

- Combinational read option (async SRAM)
- Memory initialization from file/array
- Dual-port RAM support
- Vendor-specific BRAM primitives
- Read-modify-write operations
- Byte-enable for partial writes

## Verification Strategy

### Simulation Tests:

1. **Write-then-read**: Write data, then read it back
2. **Multiple locations**: Write to different addresses
3. **Read latency**: Verify registered read behavior
4. **Write enable**: Verify writes only occur when enabled
5. **Address wrapping**: Test boundary conditions

### Verilog Generation Tests:

1. Verify correct `logic` array declaration
2. Verify `always_ff` block for writes
3. Verify registered read assignment
4. Verify write-enable condition

### Co-simulation:

1. Compare Lean simulation vs Verilator execution
2. Verify bit-accurate memory behavior
3. Test with realistic memory access patterns

## Design Rationale

**Why registered reads?**
- Matches FPGA Block RAM (BRAM) behavior
- Better timing (pipelined memory access)
- More synthesizable across different targets

**Why single-port first?**
- Simpler to implement and verify
- Covers 80% of use cases
- Can be extended to dual-port later

**Why no initialization?**
- Keep initial implementation simple
- Can add via optional parameter later
- Most use cases write before read anyway

**Why synchronous writes only?**
- Matches standard hardware memory behavior
- Easier to reason about timing
- All modern memories are synchronous

## Summary

This design provides a clean, functional API for memory primitives that:
- Integrates naturally with Signal monad
- Generates synthesizable Verilog
- Supports common memory use cases
- Can be extended for advanced features

The registered-read, synchronous-write model matches FPGA BRAM behavior and provides a solid foundation for hardware design with memories.
