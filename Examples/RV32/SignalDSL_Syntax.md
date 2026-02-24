# Signal DSL Syntax Reference for RV32 Rewrite

This document provides a side-by-side comparison of **CircuitM** (manual IR builder) and **Signal DSL** (recommended) patterns, specifically for the RV32I core rewrite.

**Rule: Use Signal DSL for everything. Only fall back to CircuitM for vendor blackbox instantiation.**

---

## Wire / Constant

```lean
-- CircuitM (manual)
let w ← makeWire "result" (.bitVector 32)
emitAssign w (.const 42 32)

-- Signal DSL (recommended)
let w : Signal dom (BitVec 32) := Signal.pure 42#32
```

## Arithmetic

```lean
-- CircuitM
let sum ← makeWire "sum" (.bitVector 32)
emitAssign sum (.op .add [.ref "a", .ref "b"])

-- Signal DSL
let sum := (· + ·) <$> a <*> b
```

## Multiplexer

```lean
-- CircuitM
let result ← makeWire "result" (.bitVector 32)
emitAssign result (.op .mux [.ref "sel", .ref "thenVal", .ref "elseVal"])

-- Signal DSL
let result := Signal.mux sel thenVal elseVal
```

## Register (D Flip-Flop)

```lean
-- CircuitM
let nextVal ← makeWire "next_val" (.bitVector 32)
emitAssign nextVal (.op .add [.ref regOut, .const 1 32])
let regOut ← emitRegister "counter" "clk" "rst" (.ref nextVal) 0 (.bitVector 32)

-- Signal DSL
let rec counter := Signal.register 0#32 (counter.map (· + 1))
```

## Memory (BRAM)

```lean
-- CircuitM
let rdata ← emitMemory "dmem" 14 32 "clk"
  (.ref writeAddr) (.ref writeData) (.ref writeEn) (.ref readAddr)

-- Signal DSL
let rdata := Signal.memory writeAddr writeData writeEn readAddr
```

## Bit Slice (extract field)

```lean
-- CircuitM
let opcode ← makeWire "opcode" (.bitVector 7)
emitAssign opcode (.slice (.ref "inst") 6 0)

-- Signal DSL (requires compiler extension for extractLsb')
let opcode := inst.map (BitVec.extractLsb' 0 7 ·)
```

## Concatenation

```lean
-- CircuitM
let sext ← makeWire "sext" (.bitVector 32)
emitAssign sext (.concat [.const 0 20, .ref "imm12"])

-- Signal DSL (requires compiler extension for BitVec.append)
let sext := (BitVec.append · ·) <$> (Signal.pure 0#20) <*> imm12
```

## Comparison

```lean
-- CircuitM
let isEq ← makeWire "is_eq" .bit
emitAssign isEq (.op .eq [.ref "a", .ref "b"])

-- Signal DSL
let isEq := (· == ·) <$> a <*> b
-- or: (BEq.beq · ·) <$> a <*> b
```

## Feedback Loop (state machine)

```lean
-- CircuitM
let nextState ← makeWire "next_state" (.bitVector 8)
let stateReg ← emitRegister "state" "clk" "rst" (.ref nextState) 0 (.bitVector 8)
emitAssign nextState (.op .mux [.ref "condition",
  .op .add [.ref stateReg, .const 1 8], .ref stateReg])

-- Signal DSL
let state := Signal.loop fun s =>
  let prev := Signal.register 0#8 s
  let next := Signal.mux condition (prev.map (· + 1)) prev
  next
```

## Combinational Logic (pure function + map)

```lean
-- CircuitM (must manually create wires for each step)
let isLui ← makeWire "is_lui" .bit
emitAssign isLui (.op .eq [.ref "opcode", .const 0b0110111 7])
let isAuipc ← makeWire "is_auipc" .bit
emitAssign isAuipc (.op .eq [.ref "opcode", .const 0b0010111 7])
let isUtype ← makeWire "is_utype" .bit
emitAssign isUtype (.op .or [.ref isLui, .ref isAuipc])

-- Signal DSL (pure function, auto-synthesized)
def isUtype (opcode : BitVec 7) : Bool :=
  opcode == 0b0110111 || opcode == 0b0010111

let isUtypeSig := inst.map (fun i => isUtype (i.extractLsb' 0 7))
```

## Hierarchical Module Instantiation

```lean
-- CircuitM
emitInstance "ALU" "alu_inst" [
  ("alu_op", .ref "op"), ("alu_a", .ref "a"), ("alu_b", .ref "b")]

-- Signal DSL (just function call, auto-hierarchical)
let aluResult := aluSignal op a b
```

## Simulation (why Signal DSL wins)

```lean
-- CircuitM: NO Lean-native simulation possible
-- Must generate Verilog → iverilog → vvp (slow, hangs)

-- Signal DSL: Direct Lean evaluation
let value := myCircuit.atTime 100  -- Get output at cycle 100
let trace := List.range 1000 |>.map myCircuit.atTime  -- Full trace
-- Runs in milliseconds, not minutes
```

---

## When to Use What

| Use Case | Recommended | Why |
|----------|------------|-----|
| New RTL design | **Signal DSL** | Simulatable, verifiable, synthesizable |
| Combinational logic | **Signal DSL** (pure function + map) | Clean, provable, reusable |
| Sequential logic | **Signal DSL** (register + loop) | Lean-native simulation |
| Testbenches | **Signal DSL** (Signal.atTime) | Fast, no external tools |
| Vendor primitives | CircuitM (via emitInstance) | For blackbox instantiation only |
| Legacy integration | CircuitM | When wrapping external IP |

---

## Compiler Extensions Required for RV32

The following operations need compiler support (Step 1 of the rewrite plan):

| Operation | Lean Function | IR Support | Compiler Status |
|-----------|--------------|------------|-----------------|
| Bit slice | `BitVec.extractLsb'` | `Expr.slice` exists | **Needs compiler handler** |
| Concatenation | `BitVec.append` | `Expr.concat` exists | **Needs compiler handler** |
| Shift left | `BitVec.shiftLeft` | `Operator.shl` exists | **Needs primitive registry entry** |
| Shift right | `BitVec.ushiftRight` | `Operator.shr` exists | **Needs primitive registry entry** |
| Arith shift right | `BitVec.sshiftRight` | `Operator.asr` exists | **Needs primitive registry entry** |
| Negation | `BitVec.neg` | `Operator.neg` exists | **Needs primitive registry entry** |
| Greater than (unsigned) | `BitVec.ugt` | `Operator.gt_u` exists | **Needs primitive registry entry** |
| Greater or equal (unsigned) | `BitVec.uge` | `Operator.ge_u` exists | **Needs primitive registry entry** |
| Greater than (signed) | `BitVec.sgt` | `Operator.gt_s` exists | **Needs primitive registry entry** |
| Greater or equal (signed) | `BitVec.sge` | `Operator.ge_s` exists | **Needs primitive registry entry** |
| Register with enable | `Signal.registerWithEnable` | register + mux | **Needs compiler handler** |

---

## RV32 Rewrite Patterns

### ALU (combinational → pure function + Signal.map)

```lean
-- Pure reference model
def aluCompute (op : ALUOp) (a b : BitVec 32) : BitVec 32 := ...

-- Signal wrapper using nested mux tree
def aluSignal (op : Signal dom (BitVec 4)) (a b : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let isAdd := op.map (· == ALUOp.ADD.toBitVec4)
  let addResult := (· + ·) <$> a <*> b
  let isSub := op.map (· == ALUOp.SUB.toBitVec4)
  let subResult := (· - ·) <$> a <*> b
  ...
  Signal.mux isAdd addResult (Signal.mux isSub subResult ...)
```

### Decoder (combinational → pure function)

```lean
structure DecoderOutput where
  opcode : BitVec 7
  rd     : BitVec 5
  funct3 : BitVec 3
  rs1    : BitVec 5
  rs2    : BitVec 5
  funct7 : BitVec 7
  imm    : BitVec 32
  aluOp  : BitVec 4

def decode (inst : BitVec 32) : DecoderOutput :=
  let opcode := inst.extractLsb' 0 7
  let rd := inst.extractLsb' 7 5
  ...
```

### Pipeline (sequential → Signal.loop)

```lean
def rv32iCore
    (imemRdata : Signal dom (BitVec 32))
    (dmemRdata : Signal dom (BitVec 32))
    : Signal dom CoreOutputs :=
  Signal.loop fun state =>
    let prevState := Signal.register initPipelineState state
    -- IF stage: PC logic
    -- ID stage: decode + register file read
    -- EX stage: ALU + branch evaluation
    -- WB stage: register file write
    -- Compute next state
    ...
```

### Register File (memory)

```lean
def regFile
    (rs1Addr rs2Addr : Signal dom (BitVec 5))
    (wrAddr : Signal dom (BitVec 5))
    (wrData : Signal dom (BitVec 32))
    (wrEn : Signal dom Bool)
    : Signal dom (BitVec 32 × BitVec 32) :=
  let rs1Data := Signal.memory wrAddr wrData wrEn rs1Addr
  let rs2Data := Signal.memory wrAddr wrData wrEn rs2Addr
  Signal.bundle2 rs1Data rs2Data
```

### CLINT (sequential → Signal.loop)

```lean
def clint (busAddr : Signal dom (BitVec 32))
          (busWdata : Signal dom (BitVec 32))
          (busWe : Signal dom Bool)
    : Signal dom (BitVec 32 × Bool × Bool) :=
  Signal.loop fun state =>
    let prev := Signal.register clintInitState state
    let mtimeLo := prev.map (·.mtimeLo)
    -- auto-increment, write handling, irq comparison...
```

### Lean-Native Testbench

```lean
def testSoC : IO Unit := do
  let firmware ← loadHex "firmware/firmware.hex"
  let soc := rv32iSoCWithFirmware firmware
  for cycle in [:100000] do
    let debugPc := soc.debugPc.atTime cycle
    let uartWe := soc.uartWe.atTime cycle
    let uartData := soc.uartData.atTime cycle
    if uartWe then
      IO.println s!"[UART @ cycle {cycle}] 0x{uartData.toHex}"
```
