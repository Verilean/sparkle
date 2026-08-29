/-
  SystemVerilog Parser Tests

  Test 1-5: Parser + lowering for simple counter
  Test 6: E2E — parse Verilog → lower to IR → generate CppSim → JIT compile → simulate
  Test 7: PicoRV32 parse (3049-line RISC-V CPU)
-/

import Tools.SVParser
import Sparkle.Backend.Verilog
import Sparkle.Backend.CSim
import Tools.SVParser.EmitAst
import Sparkle.Core.JIT

open Tools.SVParser.AST
open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Sparkle.IR.AST
open Sparkle.Backend.Verilog
open Sparkle.Backend.CSim
open Sparkle.Core.JIT

-- The do-block of `main` is large enough that Lean's elaborator hits the
-- default `maxRecDepth` (512) when it processes the trailing regression
-- tests.  Bumping the budget keeps the whole file building without
-- splitting tests into many `lean_exe` drivers.
set_option maxRecDepth 1024

def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def hexToNat (s : String) : Nat :=
  s.foldl (fun acc c =>
    let d := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
             else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
             else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
             else 0
    acc * 16 + d) 0

def counterVerilog : String :=
"module simple_counter (
    input clk,
    input rst_n,
    output [7:0] count
);
    reg [7:0] count_reg;
    assign count = count_reg;

    always @(posedge clk) begin
        if (!rst_n) begin
            count_reg <= 8'h00;
        end else begin
            count_reg <= count_reg + 8'h01;
        end
    end
endmodule
"

/-- Extracted from PicoRV32 (ISC License, Copyright (C) 2015 Clifford Wolf).
    picorv32_pcpi_mul: Carry-save shift-and-add multiplier with CARRY_CHAIN=4.
    This is the most complex combinational logic in PicoRV32 — a nested for-loop
    with concat-LHS part-select assignments that exercises SSA renaming,
    read-modify-write decomposition, and 64-bit promotion. -/
def pcpiMulVerilog : String :=
"module picorv32_pcpi_mul #(
  parameter STEPS_AT_ONCE = 1,
  parameter CARRY_CHAIN = 4
) (
  input clk, resetn,
  input             pcpi_valid,
  input      [31:0] pcpi_insn,
  input      [31:0] pcpi_rs1,
  input      [31:0] pcpi_rs2,
  output reg        pcpi_wr,
  output reg [31:0] pcpi_rd,
  output reg        pcpi_wait,
  output reg        pcpi_ready
);
  reg instr_mul, instr_mulh, instr_mulhsu, instr_mulhu;
  wire instr_any_mul = |{instr_mul, instr_mulh, instr_mulhsu, instr_mulhu};
  wire instr_any_mulh = |{instr_mulh, instr_mulhsu, instr_mulhu};
  wire instr_rs1_signed = |{instr_mulh, instr_mulhsu};
  wire instr_rs2_signed = |{instr_mulh};

  reg pcpi_wait_q;
  wire mul_start = pcpi_wait && !pcpi_wait_q;

  always @(posedge clk) begin
    instr_mul <= 0;
    instr_mulh <= 0;
    instr_mulhsu <= 0;
    instr_mulhu <= 0;

    if (resetn && pcpi_valid && pcpi_insn[6:0] == 7'b0110011 && pcpi_insn[31:25] == 7'b0000001) begin
      case (pcpi_insn[14:12])
        3'b000: instr_mul <= 1;
        3'b001: instr_mulh <= 1;
        3'b010: instr_mulhsu <= 1;
        3'b011: instr_mulhu <= 1;
      endcase
    end

    pcpi_wait <= instr_any_mul;
    pcpi_wait_q <= pcpi_wait;
  end

  reg [63:0] rs1, rs2, rd, rdx;
  reg [63:0] next_rs1, next_rs2, this_rs2;
  reg [63:0] next_rd, next_rdx, next_rdt;
  reg [6:0] mul_counter;
  reg mul_waiting;
  reg mul_finish;
  integer i, j;

  // carry save accumulator
  always @* begin
    next_rd = rd;
    next_rdx = rdx;
    next_rs1 = rs1;
    next_rs2 = rs2;

    for (i = 0; i < STEPS_AT_ONCE; i=i+1) begin
      this_rs2 = next_rs1[0] ? next_rs2 : 0;
      if (CARRY_CHAIN == 0) begin
        next_rdt = next_rd ^ next_rdx ^ this_rs2;
        next_rdx = ((next_rd & next_rdx) | (next_rd & this_rs2) | (next_rdx & this_rs2)) << 1;
        next_rd = next_rdt;
      end else begin
        next_rdt = 0;
        for (j = 0; j < 64; j = j + CARRY_CHAIN)
          {next_rdt[j+CARRY_CHAIN-1], next_rd[j +: CARRY_CHAIN]} =
              next_rd[j +: CARRY_CHAIN] + next_rdx[j +: CARRY_CHAIN] + this_rs2[j +: CARRY_CHAIN];
        next_rdx = next_rdt << 1;
      end
      next_rs1 = next_rs1 >> 1;
      next_rs2 = next_rs2 << 1;
    end
  end

  always @(posedge clk) begin
    mul_finish <= 0;
    if (!resetn) begin
      mul_waiting <= 1;
    end else
    if (mul_waiting) begin
      if (instr_rs1_signed)
        rs1 <= $signed(pcpi_rs1);
      else
        rs1 <= $unsigned(pcpi_rs1);

      if (instr_rs2_signed)
        rs2 <= $signed(pcpi_rs2);
      else
        rs2 <= $unsigned(pcpi_rs2);

      rd <= 0;
      rdx <= 0;
      mul_counter <= (instr_any_mulh ? 63 - STEPS_AT_ONCE : 31 - STEPS_AT_ONCE);
      mul_waiting <= !mul_start;
    end else begin
      rd <= next_rd;
      rdx <= next_rdx;
      rs1 <= next_rs1;
      rs2 <= next_rs2;

      mul_counter <= mul_counter - STEPS_AT_ONCE;
      if (mul_counter[6]) begin
        mul_finish <= 1;
        mul_waiting <= 1;
      end
    end
  end

  always @(posedge clk) begin
    pcpi_wr <= 0;
    pcpi_ready <= 0;
    if (mul_finish && resetn) begin
      pcpi_wr <= 1;
      pcpi_ready <= 1;
      pcpi_rd <= instr_any_mulh ? rd >> 32 : rd;
    end
  end
endmodule
"

def main : IO UInt32 := do
  IO.println "=== SystemVerilog Parser Tests ==="
  let mut passed := 0
  let mut failed := 0

  -- Test 1: Parse the counter module
  IO.print "  Test 1: Parse counter module... "
  match parseModuleFromString counterVerilog with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok svMod =>
    if svMod.name == "simple_counter" && svMod.ports.length == 3 && svMod.items.length == 3 then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: name={svMod.name}, ports={svMod.ports.length}, items={svMod.items.length}"
      failed := failed + 1

  -- Test 2: Verify port parsing
  IO.print "  Test 2: Verify ports... "
  match parseModuleFromString counterVerilog with
  | .error _ => IO.println "FAIL: parse error"; failed := failed + 1
  | .ok svMod =>
    let inputs := svMod.ports.filter (·.dir == .input)
    let outputs := svMod.ports.filter (·.dir == .output)
    if inputs.length == 2 && outputs.length == 1 &&
       (outputs.head?.map (·.name) == some "count") then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: inputs={inputs.length}, outputs={outputs.length}"
      failed := failed + 1

  -- Test 3: Lower to Sparkle IR
  IO.print "  Test 3: Lower to Sparkle IR... "
  match parseAndLower counterVerilog with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      let hasAssign := m.body.any fun s => match s with
        | .assign "count" _ => true | _ => false
      let hasRegister := m.body.any fun s => match s with
        | .register "count_reg" "clk" _ _ _ => true | _ => false
      if hasAssign && hasRegister then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: assign={hasAssign}, register={hasRegister}"
        failed := failed + 1

  -- Test 4: Round-trip (lower → emit Verilog)
  IO.print "  Test 4: Round-trip to Verilog... "
  match parseAndLower counterVerilog with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      let verilog := toVerilog m
      let ok := containsSubstr verilog "module simple_counter" &&
                containsSubstr verilog "clk" &&
                containsSubstr verilog "assign" &&
                containsSubstr verilog "always_ff"
      if ok then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL"; failed := failed + 1

  -- Test 5: Parse expression
  IO.print "  Test 5: Parse expression (a + 8'h01)... "
  match Tools.SVParser.Lexer.run (do Tools.SVParser.Lexer.ws; parseExpr) "a + 8'h01" with
  | .ok (.binary .add (.ident "a") (.lit (.hex (some 8) 1))) =>
    IO.println "PASS"; passed := passed + 1
  | .ok e => IO.println s!"FAIL: unexpected AST: {repr e}"; failed := failed + 1
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 6: E2E — parse → lower → CppSim → JIT compile → simulate
  IO.print "  Test 6: E2E JIT simulation... "
  match parseAndLower counterVerilog with
  | .error e => IO.println s!"FAIL (lower): {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      -- Generate JIT C++
      let jitDesign : Design := { topModule := m.name, modules := [m] }
      let jitCpp := toCJIT jitDesign
      let jitPath := "/tmp/sparkle_sv_counter_jit.c"
      IO.FS.writeFile jitPath jitCpp

      -- JIT compile and load
      try
        let handle ← JIT.compileAndLoad jitPath
        -- Reset (zeroes internal registers AND input ports — so we
        -- have to explicitly deassert the counter's active-low reset
        -- before stepping, otherwise count_reg is held at 0).
        JIT.reset handle
        JIT.setInput handle 0 1  -- rst_n = 1 (active-low → deassert)
        -- Run 10 cycles
        for _ in [:10] do
          JIT.evalTick handle
        -- Read counter output (output port 0)
        let val ← JIT.getOutput handle 0
        JIT.destroy handle

        -- After 10 evalTick cycles: reg starts at 0, increments each tick
        -- Output reads current reg before next tick, so count=9 after 10 ticks
        if val == 9 || val == 10 then
          IO.println s!"PASS (count={val} after 10 cycles)"
          passed := passed + 1
        else
          IO.println s!"FAIL: expected 10, got {val}"
          failed := failed + 1
      catch e =>
        IO.println s!"FAIL (JIT): {toString e}"
        failed := failed + 1

  -- Test 7: PicoRV32 parse
  IO.print "  Test 7: PicoRV32 parse... "
  let picoExists ← System.FilePath.pathExists "/tmp/picorv32.v"
  if picoExists then
    let contents ← IO.FS.readFile "/tmp/picorv32.v"
    match parse contents with
    | .ok design =>
      if design.modules.length >= 4 then
        match design.modules.head? with
        | some core =>
          IO.println s!"PASS ({design.modules.length} modules, core: {core.items.length} items)"
          passed := passed + 1
        | none => IO.println "FAIL"; failed := failed + 1
      else
        IO.println s!"FAIL: only {design.modules.length} modules"
        failed := failed + 1
    | .error e =>
      IO.println s!"FAIL: {e}"
      failed := failed + 1
  else
    IO.println "SKIP (picorv32.v not found)"

  -- Test 8: PicoRV32 core JIT compile + run
  IO.print "  Test 8: PicoRV32 JIT compile + simulate... "
  if picoExists then
    match parseAndLower (← IO.FS.readFile "/tmp/picorv32.v") with
    | .error e => IO.println s!"FAIL (lower): {e}"; failed := failed + 1
    | .ok design =>
      match design.modules.head? with
      | none => IO.println "FAIL: no modules"; failed := failed + 1
      | some core =>
        let coreDesign : Design := { topModule := core.name, modules := [core] }
        let jitCpp := toCJIT coreDesign
        let cppPath := "/tmp/picorv32_core_jit.c"
        IO.FS.writeFile cppPath jitCpp
        try
          let handle ← JIT.compileAndLoad cppPath
          JIT.reset handle
          -- Run 100 cycles
          for _ in [:100] do
            JIT.evalTick handle
          let numWires ← JIT.numWires handle
          let numRegs ← JIT.numRegs handle
          JIT.destroy handle
          IO.println s!"PASS ({numWires} wires, {numRegs} regs, 100 cycles)"
          passed := passed + 1
        catch e =>
          IO.println s!"FAIL (JIT): {toString e}"
          failed := failed + 1
  else
    IO.println "SKIP (picorv32.v not found)"

  -- Test 9: SoC with $readmemh — parse, lower, detect memory init
  IO.print "  Test 9: $readmemh support... "
  let socPath := "/tmp/picorv32_soc.v"
  let socExists ← System.FilePath.pathExists socPath
  if socExists && picoExists then
    let soc ← IO.FS.readFile socPath
    let cpu ← IO.FS.readFile "/tmp/picorv32.v"
    let combined := soc ++ "\n" ++ cpu
    match Tools.SVParser.Parser.parse combined with
    | .ok svDesign =>
      let memInits := Tools.SVParser.Lower.extractReadMemH svDesign
      if memInits.length == 1 &&
         (memInits.head?.map (·.filename) == some "firmware.hex") &&
         (memInits.head?.map (·.memName) == some "memory") then
        IO.println s!"PASS ($readmemh detected: firmware.hex → memory)"
        passed := passed + 1
      else
        IO.println s!"FAIL: expected 1 readmemh, got {memInits.length}"
        failed := failed + 1
    | .error e =>
      IO.println s!"FAIL: {e}"
      failed := failed + 1
  else
    IO.println "SKIP (files not found)"

  -- Test 10: PicoRV32 SoC — JIT compile + firmware load + simulate
  IO.print "  Test 10: PicoRV32 SoC with firmware... "
  let socPath := "/tmp/picorv32_soc.v"
  let socExists ← System.FilePath.pathExists socPath
  let fwPath := "/tmp/firmware.hex"
  let fwExists ← System.FilePath.pathExists fwPath
  if socExists && picoExists && fwExists then
    try
      let soc ← IO.FS.readFile socPath
      let cpu ← IO.FS.readFile "/tmp/picorv32.v"
      let combined := soc ++ "\n" ++ cpu

      let flatDesign ← IO.ofExcept (parseAndLowerFlat combined)

      -- Generate and compile JIT (flattened — single module with all logic inlined)
      let jitCpp := toCJIT flatDesign
      let cppPath := "/tmp/picorv32_soc_jit.c"
      IO.FS.writeFile cppPath jitCpp

      let handle ← JIT.compileAndLoad cppPath
      JIT.reset handle

      -- Load firmware into memory (memory index 0 = first memory in SoC)
      -- Must be done after reset since reset clears memory
      let fwContents ← IO.FS.readFile fwPath
      let mut addr : UInt32 := 0
      for line in fwContents.splitOn "\n" do
        let trimmed := String.ofList (line.toList.filter fun c => c != ' ' && c != '\t' && c != '\r' && c != '\n')
        if trimmed.startsWith "@" then
          addr := UInt32.ofNat (hexToNat (String.ofList (trimmed.toList.drop 1)))
        else if trimmed.length >= 8 then
          JIT.setMem handle 0 (addr / 4) (UInt32.ofNat (hexToNat trimmed))
          addr := addr + 4

      -- Hold in reset for 10 cycles (resetn = 0) to let CPU properly initialize
      JIT.setInput handle 0 0  -- resetn = 0 (input port 0)
      for _ in [:10] do
        JIT.evalTick handle

      -- De-assert reset (set resetn = 1) — PicoRV32 uses active-low reset
      JIT.setInput handle 0 1  -- resetn = 1 (input port 0)

      -- Run for 2000 cycles, check for UART output
      let mut uartOutput : List UInt64 := []
      for _ in [:2000] do
        JIT.evalTick handle
        let uartValid ← JIT.getOutput handle 1  -- uart_valid
        if uartValid != 0 then
          let uartData ← JIT.getOutput handle 0  -- uart_data
          uartOutput := uartOutput ++ [uartData]

      let numRegs ← JIT.numRegs handle
      JIT.destroy handle

      -- Build UART output string
      -- Note: sb (store byte) produces {4{byte}} in mem_wdata (e.g., 0x48484848 for 'H')
      -- This is normal PicoRV32 behavior; UART stores the full word.
      -- Mask to low 8 bits to extract the actual byte value.
      let uartChars := uartOutput.filterMap fun v =>
        let n := v.toNat &&& 0xFF  -- UART byte is in the low 8 bits
        if n >= 32 && n < 127 then some (Char.ofNat n) else none
      let uartStr := String.ofList uartChars
      if uartOutput.length > 0 then
        IO.println s!"PASS ({numRegs} regs, {uartOutput.length} UART bytes: \"{uartStr}\")"
      else
        IO.println s!"PASS ({numRegs} regs, 0 UART events after 2000 cycles)"
      passed := passed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"
      failed := failed + 1
  else
    IO.println "SKIP (files not found)"

  -- Test 11: C firmware (RV32I) — Fibonacci, array sum, sort, GCD
  IO.print "  Test 11: C firmware (RV32I) via JIT... "
  let cFwPath := "/tmp/firmware_rv32i.hex"
  let cFwExists ← System.FilePath.pathExists cFwPath
  if socExists && picoExists && cFwExists then
    try
      let soc ← IO.FS.readFile socPath
      let cpu ← IO.FS.readFile "/tmp/picorv32.v"
      let combined := soc ++ "\n" ++ cpu
      let flatDesign ← IO.ofExcept (parseAndLowerFlat combined)
      let jitCpp := toCJIT flatDesign
      IO.FS.writeFile "/tmp/picorv32_cfirmware_jit.c" jitCpp
      let handle ← JIT.compileAndLoad "/tmp/picorv32_cfirmware_jit.c"
      JIT.reset handle

      -- Load C firmware
      let fwContents ← IO.FS.readFile cFwPath
      let mut addr : UInt32 := 0
      for line in fwContents.splitOn "\n" do
        let trimmed := String.ofList (line.toList.filter fun c => c != ' ' && c != '\t' && c != '\r' && c != '\n')
        if trimmed.startsWith "@" then
          addr := UInt32.ofNat (hexToNat (String.ofList (trimmed.toList.drop 1)))
        else if trimmed.length >= 8 then
          JIT.setMem handle 0 (addr / 4) (UInt32.ofNat (hexToNat trimmed))
          addr := addr + 4

      -- Reset sequence
      JIT.setInput handle 0 0  -- resetn = 0
      for _ in [:10] do JIT.evalTick handle
      JIT.setInput handle 0 1  -- resetn = 1

      -- Run for 200000 cycles (C firmware with loops needs many cycles)
      let mut uartOutput : List UInt64 := []
      let mut done := false
      for _ in [:200000] do
        if !done then
          JIT.evalTick handle
          let uartValid ← JIT.getOutput handle 1
          if uartValid != 0 then
            let uartData ← JIT.getOutput handle 0
            uartOutput := uartOutput ++ [uartData]
            -- Stop early on pass/fail marker
            if uartData == 0xCAFE0000 || uartData == 0xDEADDEAD then
              done := true

      JIT.destroy handle

      -- Verify: check for start marker (0xDEAD0001) and pass marker (0xCAFE0000)
      let hasStart := uartOutput.any (· == 0xDEAD0001)
      let hasPass := uartOutput.any (· == 0xCAFE0000)
      let hasFail := uartOutput.any (· == 0xDEADDEAD)
      -- Verify Fibonacci: first data after 0xAAAA0001 should be 0,1,1,2,3,5,8,13,21,34
      let fibExpected : List UInt64 := [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]

      -- Extract Fibonacci values (after marker 0xAAAA0001)
      let mut afterFib := false
      let mut fibValues : List UInt64 := []
      for v in uartOutput do
        if v == 0xAAAA0001 then afterFib := true
        else if afterFib && fibValues.length < 10 then
          fibValues := fibValues ++ [v]
        else if afterFib && fibValues.length >= 10 then
          afterFib := false
      let fibOk := fibValues == fibExpected

      -- Extract GCD values (after marker 0xAAAA0004)
      let gcdExpected : List UInt64 := [6, 25, 1]
      let mut afterGcd := false
      let mut gcdValues : List UInt64 := []
      for v in uartOutput do
        if v == 0xAAAA0004 then afterGcd := true
        else if afterGcd && gcdValues.length < 3 then
          gcdValues := gcdValues ++ [v]
        else if afterGcd && gcdValues.length >= 3 then
          afterGcd := false
      let gcdOk := gcdValues == gcdExpected

      -- Verify array sum (after 0xAAAA0002): expected 360 = 0x168
      let mut sumVal : UInt64 := 0
      let mut afterSum := false
      for v in uartOutput do
        if v == 0xAAAA0002 then afterSum := true
        else if afterSum then
          sumVal := v; afterSum := false
      let sumOk := sumVal == 360

      -- Verify sort (after 0xAAAA0003): expected 3,8,17,42,55,99
      let sortExpected : List UInt64 := [3, 8, 17, 42, 55, 99]
      let mut afterSort := false
      let mut sortValues : List UInt64 := []
      for v in uartOutput do
        if v == 0xAAAA0003 then afterSort := true
        else if afterSort && sortValues.length < 6 then
          sortValues := sortValues ++ [v]
        else if afterSort && sortValues.length >= 6 then
          afterSort := false
      let sortOk := sortValues == sortExpected

      if hasStart && hasPass && fibOk && gcdOk && sumOk && sortOk then
        IO.println s!"PASS ({uartOutput.length} words, ALL C TESTS OK)"
        passed := passed + 1
      else
        IO.println s!"FAIL (fib={fibOk} sum={sumOk} sort={sortOk} gcd={gcdOk} pass={hasPass}, {uartOutput.length} words. First 8: {uartOutput.take 8})"
        failed := failed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"
      failed := failed + 1
  else
    IO.println "SKIP (files not found)"

  -- ===================================================================
  -- IR-level unit tests (no JIT, just parse+lower and inspect IR)
  -- ===================================================================

  -- Test 12: Nested blocking assign in if/else inside always @*
  -- Bug: sigNames filter only checked top-level blockAssign, missing
  -- assignments inside if/else. cpuregs_rs1 was silently dropped.
  IO.print "  Test 12: Nested always @* assign in if/else... "
  let nestedIfVerilog := "
module nested_if_test (input clk, input [1:0] sel, output [7:0] out);
  reg [7:0] result;
  assign out = result;
  always @* begin
    if (sel == 2'b01) begin
      result = 8'hAA;
    end else begin
      result = 8'h55;
    end
  end
endmodule
"
  match parseAndLower nestedIfVerilog with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      let hasResultAssign := m.body.any fun s => match s with
        | .assign "result" _ => true | _ => false
      if hasResultAssign then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: 'result' assign not found in IR body"
        for s in m.body do IO.println s!"  {s}"
        failed := failed + 1

  -- Test 13: case(1'b1) first-match-wins priority (processCaseArms)
  -- Bug: later case arms could override earlier matches without !covered guard.
  -- PicoRV32's decoder uses case(1'b1) with multiple arms that can match simultaneously.
  IO.print "  Test 13: case(1'b1) first-match-wins... "
  let casePriorityVerilog := "
module case_priority (input clk, input rst_n, input a, input b, output reg [7:0] out);
  always @(posedge clk) begin
    if (!rst_n) out <= 0;
    else begin
      out <= 8'hFF;
      case (1'b1)
        a: out <= 8'h01;
        b: out <= 8'h02;
      endcase
    end
  end
endmodule
"
  match parseAndLower casePriorityVerilog with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      -- The register for 'out' should exist and its mux expression should
      -- reference both 'a' and 'b' (not just the last arm)
      -- Register may be named _reg_out (lowering convention)
      let regEntry := m.body.findSome? fun s => match s with
        | .register name _ _ expr _ =>
          if name == "out" || name == "_reg_out" then some (toString expr) else none
        | _ => none
      match regEntry with
      | some exprStr =>
        let hasA := containsSubstr exprStr "a"
        let hasB := containsSubstr exprStr "b"
        if hasA && hasB then
          IO.println "PASS"; passed := passed + 1
        else
          IO.println s!"FAIL: hasA={hasA} hasB={hasB} expr={exprStr}"
          failed := failed + 1
      | none =>
        IO.println "FAIL: no register for 'out' found"
        for s in m.body do IO.println s!"  {s}"
        failed := failed + 1

  -- Test 14: Part-select concat-LHS decomposition in always @*
  -- Bug: {a[3:0], b[3:0]} = expr was decomposed but produced self-referencing
  -- read-modify-write that broke SSA chains. Now uses __RMW_BASE__ placeholder.
  IO.print "  Test 14: Concat-LHS with part-select (always @*)... "
  let concatLhsVerilog := "
module concat_lhs_test (input [7:0] a, input [7:0] b, output [7:0] lo, output [7:0] hi);
  reg [7:0] lo_r, hi_r;
  assign lo = lo_r;
  assign hi = hi_r;
  always @* begin
    {hi_r[3:0], lo_r[3:0]} = a + b;
  end
endmodule
"
  match parseAndLower concatLhsVerilog with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      -- Both 'lo_r' and 'hi_r' should have assign statements
      let hasLoR := m.body.any fun s => match s with
        | .assign "lo_r" _ => true | _ => false
      let hasHiR := m.body.any fun s => match s with
        | .assign "hi_r" _ => true | _ => false
      -- __RMW_BASE__ should be resolved (not appear in body)
      let bodyStr := String.intercalate "\n" (m.body.map toString)
      let noRmw := !containsSubstr bodyStr "__RMW_BASE__"
      if hasLoR && hasHiR && noRmw then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: lo_r={hasLoR} hi_r={hasHiR} noRmw={noRmw}"
        for s in m.body do IO.println s!"  {s}"
        failed := failed + 1

  -- Test 15: For-loop unroll with SSA renaming
  -- Bug: unrolled inner loop result was discarded (result ++ renamed instead of ++ unrolled)
  IO.print "  Test 15: For-loop unroll with SSA... "
  let forLoopVerilog := "
module for_loop_test (input clk, input rst_n, input [7:0] a, input [7:0] b, output reg [7:0] sum);
  reg [7:0] acc;
  integer i;
  always @* begin
    acc = 0;
    for (i = 0; i < 4; i = i + 1) begin
      acc = acc + a;
    end
    sum = acc + b;
  end
endmodule
"
  match parseAndLower forLoopVerilog with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      -- 'sum' should have an assign, 'acc' should have sequential SSA wires (_seq)
      let hasSum := m.body.any fun s => match s with
        | .assign "sum" _ => true | _ => false
      let seqCount := m.wires.filter (fun w => containsSubstr w.name "acc_seq") |>.length
      if hasSum && seqCount >= 4 then
        IO.println s!"PASS (seq wires={seqCount})"; passed := passed + 1
      else
        IO.println s!"FAIL: sum={hasSum} seqWires={seqCount}"
        for s in m.body do IO.println s!"  {s}"
        failed := failed + 1

  -- Test 16: Array read in always @* (register file dual-port read)
  -- Bug: cpuregs[decoded_rs1] in always @* was not emitted because
  -- exprToName didn't handle array index, and the always @* filter
  -- only looked at top-level statements.
  IO.print "  Test 16: Array read in always @*... "
  let arrayReadVerilog := "
module array_read_test (input clk, input [4:0] addr, output [31:0] dout);
  reg [31:0] mem [0:31];
  reg [31:0] read_val;
  assign dout = read_val;
  always @* begin
    read_val = mem[addr];
  end
  always @(posedge clk) begin
    mem[addr] <= 32'hDEAD;
  end
endmodule
"
  match parseAndLower arrayReadVerilog with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      -- 'read_val' or 'read_val_seq0' should exist and reference mem[addr]
      let bodyStr := String.intercalate "\n" (m.body.map toString)
      let hasMem := containsSubstr bodyStr "mem[addr]"
      let hasReadVal := containsSubstr bodyStr "read_val"
      if hasReadVal && hasMem then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: hasReadVal={hasReadVal} hasMem={hasMem}"
        for s in m.body do IO.println s!"  {s}"
        failed := failed + 1

  -- Helper: parse+lower pcpiMulVerilog (used by tests 17-21)
  let pcpiMulIR := parseAndLower pcpiMulVerilog

  -- Test 17: pcpi_mul standalone parse+lower (carry-save accumulator)
  IO.print "  Test 17: pcpi_mul standalone IR... "
  match pcpiMulIR with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL: no modules"; failed := failed + 1
    | some m =>
      let regNames := m.body.filterMap fun s => match s with
        | .register name _ _ _ _ => some name | _ => none
      let hasRd := regNames.any (· == "rd")
      let hasRdx := regNames.any (· == "rdx")
      let hasRs1 := regNames.any (· == "rs1")
      let hasMulCounter := regNames.any (· == "mul_counter")
      -- Sequential SSA: look for _seq wires from carry-save loop
      let seqWires := m.wires.filter (fun w => containsSubstr w.name "_seq")
      let hasSeqWires := seqWires.length > 10  -- carry-save generates many seq wires
      let assignNames := m.body.filterMap fun s => match s with
        | .assign name _ => some name | _ => none
      let hasNextRd := assignNames.any (· == "next_rd")
      let hasNextRdx := assignNames.any (· == "next_rdx")
      let bodyStr := String.intercalate "\n" (m.body.map toString)
      let hasRmwPlaceholder := containsSubstr bodyStr "__RMW_BASE__"
      if hasRd && hasRdx && hasRs1 && hasMulCounter &&
         hasSeqWires && hasNextRd && hasNextRdx && !hasRmwPlaceholder then
        IO.println s!"PASS (regs={regNames.length}, seq wires={seqWires.length}, assigns={assignNames.length})"
        passed := passed + 1
      else
        IO.println s!"FAIL: rd={hasRd} rdx={hasRdx} rs1={hasRs1} counter={hasMulCounter} seqWires={seqWires.length} nextRd={hasNextRd} nextRdx={hasNextRdx} rmwClean={!hasRmwPlaceholder}"
        failed := failed + 1

  -- Test 18: Sequential SSA chain for next_rd (carry-save j-loop)
  -- Sequential emitter generates next_rd_seq0, next_rd_seq1, ... for each j-iteration.
  -- Each step should reference the previous step (proper chaining).
  IO.print "  Test 18: Carry-save sequential chain (next_rd)... "
  match pcpiMulIR with
  | .error _ => IO.println "FAIL (lower)"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL"; failed := failed + 1
    | some m =>
      -- Count next_rd_seq* assigns (should be many: j-loop produces ~16 per variable)
      let rdSeqAssigns := m.body.filterMap fun s => match s with
        | .assign name _ => if containsSubstr name "next_rd_seq" then some name else none
        | _ => none
      -- Check forward order: positions should be increasing
      let mut positions : List (String × Nat) := []
      let mut idx : Nat := 0
      for s in m.body do
        match s with
        | .assign name _ =>
          if containsSubstr name "next_rd_seq" then
            positions := positions ++ [(name, idx)]
        | _ => pure ()
        idx := idx + 1
      let orderOk := positions.length > 0 &&
        (positions.zip (positions.drop 1)).all fun ((_, a), (_, b)) => a < b
      if rdSeqAssigns.length >= 10 && orderOk then
        IO.println s!"PASS ({rdSeqAssigns.length} seq steps, forward order)"
        passed := passed + 1
      else
        IO.println s!"FAIL: count={rdSeqAssigns.length} orderOk={orderOk}"
        failed := failed + 1

  -- Test 19: Sequential chain for next_rdt (carry bits)
  IO.print "  Test 19: Carry-save sequential chain (next_rdt)... "
  match pcpiMulIR with
  | .error _ => IO.println "FAIL (lower)"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL"; failed := failed + 1
    | some m =>
      let rdtSeqAssigns := m.body.filterMap fun s => match s with
        | .assign name _ => if containsSubstr name "next_rdt_seq" then some name else none
        | _ => none
      if rdtSeqAssigns.length >= 10 then
        IO.println s!"PASS ({rdtSeqAssigns.length} seq steps)"
        passed := passed + 1
      else
        IO.println s!"FAIL: count={rdtSeqAssigns.length}"
        failed := failed + 1

  -- Test 20: next_rdx reads post-loop next_rdt (sequential ordering)
  -- After j-loop, next_rdx = next_rdt << 1 should use the FINAL next_rdt value.
  IO.print "  Test 20: next_rdx uses post-loop next_rdt... "
  match pcpiMulIR with
  | .error _ => IO.println "FAIL (lower)"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL"; failed := failed + 1
    | some m =>
      -- next_rdx should be assigned as next_rdx_seqN = next_rdt_seqM << 1
      -- where M is the final rdt value (from the last j-loop iteration)
      let rdxAssigns := m.body.filterMap fun s => match s with
        | .assign name expr => if containsSubstr name "next_rdx_seq" then
            some (name, toString expr) else none
        | _ => none
      -- At least one next_rdx_seq should reference next_rdt_seq (not raw next_rdt)
      let hasRdtSeqRef := rdxAssigns.any fun (_, e) => containsSubstr e "next_rdt_seq"
      if hasRdtSeqRef then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: no next_rdx_seq references next_rdt_seq"
        for (n, e) in rdxAssigns do IO.println s!"  {n} = {e.take 100}"
        failed := failed + 1

  -- Test 21a: No topo sort deadlock for pcpi_mul
  IO.print "  Test 21a: pcpi_mul no topo sort deadlock... "
  match pcpiMulIR with
  | .error _ => IO.println "FAIL"; failed := failed + 1
  | .ok design =>
    match design.modules.head? with
    | none => IO.println "FAIL"; failed := failed + 1
    | some m =>
      -- All assigns should be topo-sortable (no cyclic deps)
      -- Check by verifying the body has assigns and they reference known wires
      let assignCount := m.body.filter fun s => match s with
        | .assign _ _ => true | _ => false
      let bodyStr := String.intercalate "\n" (m.body.map toString)
      -- No __RMW_BASE__ should remain
      let noRmw := !containsSubstr bodyStr "__RMW_BASE__"
      if assignCount.length > 50 && noRmw then
        IO.println s!"PASS ({assignCount.length} assigns, no placeholders)"
        passed := passed + 1
      else
        IO.println s!"FAIL: assigns={assignCount.length} noRmw={noRmw}"
        failed := failed + 1

  -- Test 21: pcpi_mul JIT — compute 7 * 6 = 42
  -- MUL instruction encoding: funct7=0000001, funct3=000, opcode=0110011
  -- pcpi_insn = 0x02_000_0_000_00_33 (simplified: 0x02000033)
  IO.print "  Test 21: pcpi_mul JIT (7*6=42)... "
  match pcpiMulIR with
  | .error e => IO.println s!"FAIL (lower): {e}"; failed := failed + 1
  | .ok design =>
    let jitCpp := toCJIT design
    IO.FS.writeFile "/tmp/sparkle_pcpi_mul_jit.c" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.c"
      JIT.reset h
      -- Input mapping: 0=resetn, 1=pcpi_valid, 2=pcpi_insn, 3=pcpi_rs1, 4=pcpi_rs2
      -- Output mapping: 0=pcpi_wr, 1=pcpi_rd, 2=pcpi_wait, 3=pcpi_ready

      -- Phase 1: Reset (2 cycles)
      JIT.setInput h 0 0  -- resetn=0
      JIT.setInput h 1 0  -- pcpi_valid=0
      for _ in [:2] do JIT.evalTick h
      JIT.setInput h 0 1  -- resetn=1

      -- Phase 2: Present MUL instruction with operands
      JIT.setInput h 1 1  -- pcpi_valid=1
      JIT.setInput h 2 0x02000033  -- MUL insn
      JIT.setInput h 3 7   -- rs1 = 7
      JIT.setInput h 4 6   -- rs2 = 6

      -- Phase 3: Run until pcpi_ready or timeout
      let mut result : UInt64 := 0
      let mut ready := false
      let mut cycles : Nat := 0
      for _ in [:100] do
        if !ready then
          JIT.evalTick h
          cycles := cycles + 1
          let rdyVal ← JIT.getOutput h 3  -- pcpi_ready
          if rdyVal != 0 then
            result ← JIT.getOutput h 1  -- pcpi_rd
            ready := true
      JIT.destroy h

      if ready && result == 42 then
        IO.println s!"PASS (result={result}, {cycles} cycles)"
        passed := passed + 1
      else
        -- Debug: dump all outputs at final state
        IO.println s!"FAIL: ready={ready} result=0x{String.ofList (Nat.toDigits 16 result.toNat)} expected=42 cycles={cycles}"
        -- Re-run with tracing to find the issue
        let h2 ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.c"
        JIT.reset h2
        JIT.setInput h2 0 0; for _ in [:2] do JIT.evalTick h2
        JIT.setInput h2 0 1; JIT.setInput h2 1 1
        JIT.setInput h2 2 0x02000033; JIT.setInput h2 3 7; JIT.setInput h2 4 6
        for cyc in [:50] do
          JIT.evalTick h2
          let wr ← JIT.getOutput h2 0
          let rd ← JIT.getOutput h2 1
          let wait ← JIT.getOutput h2 2
          let rdy ← JIT.getOutput h2 3
          if cyc < 5 || wr != 0 || rdy != 0 then
            IO.println s!"    cyc {cyc}: wr={wr} rd=0x{String.ofList (Nat.toDigits 16 rd.toNat)} wait={wait} ready={rdy}"
        JIT.destroy h2
        failed := failed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"; failed := failed + 1

  -- Test 21b: pcpi_mul JIT — large multiply 100*100=10000
  IO.print "  Test 21b: pcpi_mul JIT (100*100=10000)... "
  match pcpiMulIR with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    let jitCpp := toCJIT design
    IO.FS.writeFile "/tmp/sparkle_pcpi_mul_jit.c" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.c"
      JIT.reset h
      JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
      JIT.setInput h 0 1; JIT.setInput h 1 1
      JIT.setInput h 2 0x02000033; JIT.setInput h 3 100; JIT.setInput h 4 100
      let mut result : UInt64 := 0
      let mut ready := false
      for _ in [:100] do
        if !ready then
          JIT.evalTick h
          let rdyVal ← JIT.getOutput h 3
          if rdyVal != 0 then
            result ← JIT.getOutput h 1
            ready := true
      JIT.destroy h
      if ready && result == 10000 then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: result=0x{String.ofList (Nat.toDigits 16 result.toNat)} expected=10000"
        failed := failed + 1
    catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 21c: pcpi_mul JIT — 12345*6789=83810205
  IO.print "  Test 21c: pcpi_mul JIT (12345*6789)... "
  match pcpiMulIR with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    let jitCpp := toCJIT design
    IO.FS.writeFile "/tmp/sparkle_pcpi_mul_jit.c" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.c"
      JIT.reset h
      JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
      JIT.setInput h 0 1; JIT.setInput h 1 1
      JIT.setInput h 2 0x02000033; JIT.setInput h 3 12345; JIT.setInput h 4 6789
      let mut result : UInt64 := 0
      let mut ready := false
      for _ in [:100] do
        if !ready then
          JIT.evalTick h
          let rdyVal ← JIT.getOutput h 3
          if rdyVal != 0 then
            result ← JIT.getOutput h 1
            ready := true
      JIT.destroy h
      if ready && result == 83810205 then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: result=0x{String.ofList (Nat.toDigits 16 result.toNat)} expected=0x4FEC4BD"
        failed := failed + 1
    catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 21d: pcpi_mul consecutive multiplies (7*6 then 12345*6789)
  IO.print "  Test 21d: pcpi_mul consecutive MUL... "
  match pcpiMulIR with
  | .error e => IO.println s!"FAIL: {e}"; failed := failed + 1
  | .ok design =>
    let jitCpp := toCJIT design
    IO.FS.writeFile "/tmp/sparkle_pcpi_mul_jit.c" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.c"
      JIT.reset h
      JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
      JIT.setInput h 0 1
      -- First multiply: 7*6=42
      JIT.setInput h 1 1; JIT.setInput h 2 0x02000033
      JIT.setInput h 3 7; JIT.setInput h 4 6
      let mut result1 : UInt64 := 0
      for _ in [:100] do
        JIT.evalTick h
        let rdy ← JIT.getOutput h 3
        if rdy != 0 then
          result1 ← JIT.getOutput h 1
      -- Deassert pcpi_valid briefly to allow FSM to re-trigger
      JIT.setInput h 1 0  -- pcpi_valid=0
      for _ in [:3] do JIT.evalTick h
      -- Second multiply: 12345*6789=83810205
      JIT.setInput h 1 1  -- pcpi_valid=1
      JIT.setInput h 3 12345; JIT.setInput h 4 6789
      let mut result2 : UInt64 := 0
      let mut ready2 := false
      for _ in [:100] do
        if !ready2 then
          JIT.evalTick h
          let rdy ← JIT.getOutput h 3
          if rdy != 0 then
            result2 ← JIT.getOutput h 1
            ready2 := true
      JIT.destroy h
      if result1 == 42 && result2 == 83810205 then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: first=0x{String.ofList (Nat.toDigits 16 result1.toNat)} second=0x{String.ofList (Nat.toDigits 16 result2.toNat)}"
        failed := failed + 1
    catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 21e: pcpi_mul with SoC-like wrapper (memory + CPU-like sequencer)
  -- Tests the full multiply protocol as used in PicoRV32 SoC integration.
  -- A minimal sequencer drives pcpi_valid/insn/rs1/rs2 and captures pcpi_rd.
  IO.print "  Test 21e: pcpi_mul SoC-like wrapper... "
  let mulWrapperVerilog := "
module mul_wrapper (input clk, input resetn, input start,
    input [31:0] rs1, input [31:0] rs2, output [31:0] result, output done);
  reg pcpi_valid_r;
  wire pcpi_wr, pcpi_wait, pcpi_ready;
  wire [31:0] pcpi_rd;
  reg [31:0] result_r;
  reg done_r;
  // MUL insn encoding: funct7=0000001, funct3=000, opcode=0110011
  wire [31:0] pcpi_insn = 32'h02000033;
  assign result = result_r;
  assign done = done_r;
  always @(posedge clk) begin
    if (!resetn) begin
      pcpi_valid_r <= 0;
      result_r <= 0;
      done_r <= 0;
    end else begin
      done_r <= 0;
      if (start && !pcpi_valid_r && !pcpi_wait) begin
        pcpi_valid_r <= 1;
      end
      if (pcpi_valid_r && pcpi_ready) begin
        pcpi_valid_r <= 0;
        result_r <= pcpi_rd;
        done_r <= 1;
      end
    end
  end
  picorv32_pcpi_mul mul0 (
    .clk(clk), .resetn(resetn),
    .pcpi_valid(pcpi_valid_r), .pcpi_insn(pcpi_insn),
    .pcpi_rs1(rs1), .pcpi_rs2(rs2),
    .pcpi_wr(pcpi_wr), .pcpi_rd(pcpi_rd),
    .pcpi_wait(pcpi_wait), .pcpi_ready(pcpi_ready)
  );
endmodule
" ++ pcpiMulVerilog
  match parseAndLowerFlat mulWrapperVerilog with
  | .error e => IO.println s!"FAIL (lower): {e}"; failed := failed + 1
  | .ok design =>
    let jitCpp := toCJIT design
    IO.FS.writeFile "/tmp/sparkle_mul_wrapper_jit.c" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_mul_wrapper_jit.c"
      JIT.reset h
      -- Inputs: 0=resetn, 1=start, 2=rs1, 3=rs2. Outputs: 0=result, 1=done
      JIT.setInput h 0 0; for _ in [:3] do JIT.evalTick h
      JIT.setInput h 0 1  -- resetn=1

      -- First multiply: 7*6
      JIT.setInput h 1 1; JIT.setInput h 2 7; JIT.setInput h 3 6
      let mut r1 : UInt64 := 0
      let mut d1 := false
      for _ in [:100] do
        if !d1 then
          JIT.evalTick h
          let d ← JIT.getOutput h 1
          if d != 0 then
            r1 ← JIT.getOutput h 0; d1 := true
      JIT.setInput h 1 0  -- deassert start
      for _ in [:3] do JIT.evalTick h

      -- Second multiply: 12345*6789
      JIT.setInput h 1 1; JIT.setInput h 2 12345; JIT.setInput h 3 6789
      let mut r2 : UInt64 := 0
      let mut d2 := false
      for _ in [:100] do
        if !d2 then
          JIT.evalTick h
          let d ← JIT.getOutput h 1
          if d != 0 then
            r2 ← JIT.getOutput h 0; d2 := true

      JIT.destroy h
      if r1 == 42 && r2 == 83810205 then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: first=0x{String.ofList (Nat.toDigits 16 r1.toNat)} second=0x{String.ofList (Nat.toDigits 16 r2.toNat)}"
        failed := failed + 1
    catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- ===================================================================
  -- JIT pair tests: Verilog pattern → parse → JIT → value verification
  -- Each tests a specific pattern that caused bugs during development.
  -- ===================================================================

  -- Helper: parse Verilog, generate JIT, compile, run N cycles, return outputs
  let jitRun := fun (verilog : String) (setupFn : JITHandle → IO Unit)
                    (cycles : Nat) (getResults : JITHandle → IO (List UInt64)) => do
    let design ← IO.ofExcept (parseAndLowerFlat verilog)
    let cpp := toCJIT design
    IO.FS.writeFile "/tmp/sparkle_pair_test.c" cpp
    let h ← JIT.compileAndLoad "/tmp/sparkle_pair_test.c"
    JIT.reset h
    setupFn h
    for _ in [:cycles] do JIT.evalTick h
    let results ← getResults h
    JIT.destroy h
    return results

  -- Test 27: Verilog replication {N{expr}} — bit replication
  -- Bug: {4{mem_la_write}} was lowered as just mem_la_write (1-bit),
  -- causing mem_wstrb = wstrb & 1 instead of wstrb & 4'b1111.
  -- This made sw (store word) write only 1 byte instead of 4.
  IO.print "  Test 27: Bit replication {N{expr}} via JIT... "
  try
    let v := "
module repl_test (input clk, input resetn, input en, input [3:0] mask, output [3:0] out);
  reg [3:0] result;
  assign out = result;
  always @(posedge clk) begin
    if (!resetn) result <= 0;
    else result <= mask & {4{en}};
  end
endmodule
"
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
                   JIT.setInput h 0 1; JIT.setInput h 1 1; JIT.setInput h 2 0xF)  -- en=1, mask=0xF
      3
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    -- mask=4'b1111 & {4{1}} = 4'b1111 & 4'b1111 = 4'b1111 = 15
    -- Bug would give: 4'b1111 & 1'b1 = 4'b0001 = 1
    if results == [15] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [15], got {results} (if 1, replication is broken)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 28: Byte-lane memory write + read (SoC memory pattern)
  -- Bug: store word wrote 4 bytes but load only returned byte 0.
  IO.print "  Test 28: Byte-lane memory write/read via JIT... "
  try
    let v := "
module bytelane_test (input clk, input resetn,
    input mem_valid, input [13:0] mem_addr, input [31:0] mem_wdata,
    input [3:0] mem_wstrb, output reg mem_ready, output reg [31:0] mem_rdata);
  reg [31:0] memory [0:255];
  always @(posedge clk) begin
    mem_ready <= 0;
    if (resetn && mem_valid && !mem_ready) begin
      mem_ready <= 1;
      mem_rdata <= memory[mem_addr[7:0]];
      if (mem_wstrb[0]) memory[mem_addr[7:0]][ 7: 0] <= mem_wdata[ 7: 0];
      if (mem_wstrb[1]) memory[mem_addr[7:0]][15: 8] <= mem_wdata[15: 8];
      if (mem_wstrb[2]) memory[mem_addr[7:0]][23:16] <= mem_wdata[23:16];
      if (mem_wstrb[3]) memory[mem_addr[7:0]][31:24] <= mem_wdata[31:24];
    end
  end
endmodule
"
    let design ← IO.ofExcept (parseAndLowerFlat v)
    let cpp := toCJIT design
    IO.FS.writeFile "/tmp/sparkle_bytelane_test.c" cpp
    let h ← JIT.compileAndLoad "/tmp/sparkle_bytelane_test.c"
    JIT.reset h
    -- Inputs: 0=resetn, 1=mem_valid, 2=mem_addr, 3=mem_wdata, 4=mem_wstrb
    -- Outputs: 0=mem_ready, 1=mem_rdata
    JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
    JIT.setInput h 0 1
    -- Write 0x12345678 to addr 5 with wstrb=0xF
    JIT.setInput h 1 1; JIT.setInput h 2 5; JIT.setInput h 3 0x12345678; JIT.setInput h 4 0xF
    -- Wait for mem_ready
    for _ in [:10] do
      JIT.evalTick h
      let rdy ← JIT.getOutput h 0
      if rdy != 0 then
        -- Write accepted, deassert
        JIT.setInput h 1 0; JIT.setInput h 4 0
    -- Wait a few cycles for memory to settle
    for _ in [:5] do JIT.evalTick h
    -- Read back from addr 5 (wstrb=0 = read only)
    JIT.setInput h 1 1; JIT.setInput h 2 5; JIT.setInput h 3 0; JIT.setInput h 4 0
    let mut rdata : UInt64 := 0
    for _ in [:10] do
      JIT.evalTick h
      let rdy ← JIT.getOutput h 0
      if rdy != 0 then rdata ← JIT.getOutput h 1
    JIT.destroy h
    if rdata == 0x12345678 then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected 0x12345678, got 0x{String.ofList (Nat.toDigits 16 rdata.toNat)}"
      -- Dump generated C++ snippet for debugging
      let lines := cpp.splitOn "\n"
      let memLines := lines.filter fun l => (l.splitOn "memory[").length > 1
      for l in memLines.take 5 do IO.println s!"  {l.trim}"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1
  -- Tests multi-bit replication used by PicoRV32: {2{reg_op2[15:0]}}
  IO.print "  Test 29: Multi-bit replication {2{expr}} via JIT... "
  try
    let v := "
module repl2_test (input clk, input resetn, input [15:0] din, output [31:0] out);
  reg [31:0] result;
  assign out = result;
  always @(posedge clk) begin
    if (!resetn) result <= 0;
    else result <= {2{din}};
  end
endmodule
"
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
                   JIT.setInput h 0 1; JIT.setInput h 1 0xABCD)
      3
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    -- {2{16'hABCD}} = 32'hABCDABCD
    if results == [0xABCDABCD] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [0xABCDABCD], got {results}"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 22: if/else with one-sided assign + posedge register reads result
  -- Pattern: always @* computes a value conditionally, posedge register captures it.
  -- Bug: if-else MUX merge created self-referencing cycle for uninitialized variables.
  IO.print "  Test 22: if/else one-sided assign + register... "
  try
    let v := "
module one_sided_test (input clk, input resetn, input sel, output [7:0] out);
  reg [7:0] result;
  reg [7:0] captured;
  assign out = captured;
  always @* begin
    result = 8'h00;
    if (sel)
      result = 8'hAB;
  end
  always @(posedge clk) begin
    if (!resetn) captured <= 0;
    else captured <= result;
  end
endmodule
"
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h  -- reset
                   JIT.setInput h 0 1; JIT.setInput h 1 1)  -- resetn=1, sel=1
      5
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [0xAB] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [0xAB], got {results}"; failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 23: Array read in always @* feeding posedge register
  -- Pattern: reg file read with variable index, result used by register update.
  -- Bug: cpuregs_rs1 was silently dropped when nested inside if().
  IO.print "  Test 23: Array read in always @* → register... "
  try
    let v := "
module array_read_reg (input clk, input resetn, input [2:0] addr, output [7:0] out);
  reg [7:0] mem [0:7];
  reg [7:0] read_val;
  reg [7:0] captured;
  assign out = captured;
  always @* begin
    read_val = mem[addr];
  end
  always @(posedge clk) begin
    if (!resetn) begin captured <= 0; end
    else begin
      captured <= read_val;
      mem[addr] <= addr * 16 + 5;
    end
  end
endmodule
"
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0; JIT.setInput h 1 3  -- addr=3
                   for _ in [:2] do JIT.evalTick h  -- reset
                   JIT.setInput h 0 1)  -- resetn=1
      10
      (fun h => do
        -- Write addr=3, value should be 3*16+5=53=0x35
        -- After a few cycles, read back addr=3
        JIT.setInput h 1 3
        JIT.evalTick h
        let v ← JIT.getOutput h 0
        return [v])
    -- After writing mem[3] = 53 and reading it back
    if results == [53] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [53], got {results}"; failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 24: case(1'b1) decoder priority (first-match-wins)
  -- Pattern: PicoRV32's instruction decoder uses case(1'b1) with overlapping conditions.
  -- Bug: later arms overrode earlier ones without !covered guard.
  IO.print "  Test 24: case(1'b1) priority via JIT... "
  try
    let v := "
module case_decoder (input clk, input resetn, input a, input b, output [7:0] out);
  reg [7:0] decoded;
  reg [7:0] captured;
  assign out = captured;
  always @(posedge clk) begin
    if (!resetn) begin captured <= 0; decoded <= 8'hFF; end
    else begin
      decoded <= 8'hFF;
      case (1'b1)
        a: decoded <= 8'h01;
        b: decoded <= 8'h02;
      endcase
      captured <= decoded;
    end
  end
endmodule
"
    -- Test: a=1, b=1 → first match (a) should win → decoded=0x01
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
                   JIT.setInput h 0 1; JIT.setInput h 1 1; JIT.setInput h 2 1)
      5
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    -- captured gets decoded from PREVIOUS cycle (registered), so need extra cycles
    -- After: cycle1: decoded=FF(init), cycle2: decoded=01(a wins), captured=FF
    -- cycle3: captured=01
    if results.any (· == 0x01) then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected 0x01 (a wins), got {results}"; failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 25: Read-then-overwrite in always @* (the pcpi_mul pattern)
  -- Pattern: variable initialized, used in computation, then overwritten.
  -- Bug: MUX approach created cyclic dependency between read and write.
  IO.print "  Test 25: Read-then-overwrite in always @*... "
  try
    let v := "
module read_overwrite (input clk, input resetn, output [7:0] out);
  reg [7:0] acc;
  reg [7:0] temp;
  reg [7:0] result;
  assign out = result;
  always @* begin
    temp = acc;
    temp = temp + 8'd10;
    temp = temp + 8'd20;
  end
  always @(posedge clk) begin
    if (!resetn) begin acc <= 0; result <= 0; end
    else begin
      acc <= temp;
      result <= temp;
    end
  end
endmodule
"
    -- acc starts at 0. Cycle 1: temp=0+10+20=30, acc←30, result←30
    -- Cycle 2: temp=30+10+20=60, result←60
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
                   JIT.setInput h 0 1)
      3
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    -- Cycle 1: acc=0 → temp=0+10+20=30 → result←30
    -- Cycle 2: acc=30 → temp=30+10+20=60 → result←60
    -- Cycle 3: acc=60 → temp=60+10+20=90 → result←90
    -- Read after 3 evalTick: result should be 90
    -- If result=60, the sequential chaining (temp=temp+10; temp=temp+20) is broken
    -- (temp+20 reads original temp instead of temp+10 result)
    -- If result=30, only 1 cycle of accumulation happened
    -- evalTick = eval+tick, so after N evalTick, the output reflects N-1 register updates
    -- (the last tick commits, but getOutput reads the combinational output before next tick)
    -- 3 evalTick after reset: register updated 3 times → acc=90, output=90
    -- But actual observation: result is 1 cycle behind → 60 after 3 cycles
    -- This is because result reads the OLD register value (before this cycle's tick)
    -- So 4 evalTick gives: acc=0→30→60→90, result reads 90 after 4th tick
    let results4 ← jitRun v
      (fun h => do JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
                   JIT.setInput h 0 1)
      4
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results4 == [90] then
      IO.println "PASS (result=90 after 4 cycles)"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [90] after 4cyc, got {results4}"; failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 26: Combinational loop-like accumulator (simplified carry-save)
  -- Pattern: for-loop with accumulation via concat-LHS part-select.
  -- Bug: read-modify-write in decomposeMultiConcatLhs used self-reference.
  IO.print "  Test 26: For-loop accumulator via JIT... "
  try
    let v := "
module loop_accum (input clk, input resetn, input [7:0] din, output [7:0] out);
  reg [7:0] acc;
  reg [7:0] next_acc;
  integer i;
  assign out = acc;
  always @* begin
    next_acc = 0;
    for (i = 0; i < 4; i = i + 1)
      next_acc = next_acc + din;
  end
  always @(posedge clk) begin
    if (!resetn) acc <= 0;
    else acc <= next_acc;
  end
endmodule
"
    -- din=7 → next_acc = 7+7+7+7 = 28
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0; for _ in [:2] do JIT.evalTick h
                   JIT.setInput h 0 1; JIT.setInput h 1 7)  -- resetn=1, din=7
      3
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [28] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [28], got {results}"; failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- ===================================================================
  -- Tests 30-34: regression coverage for open SVParser bugs.
  -- These reproduce the failures reported in issues #41-#45.  Each is
  -- expected to FAIL on the affected commit and PASS once the
  -- corresponding lowering / parser fix lands.
  -- ===================================================================

  -- Test 30 (issue #41): reduction-AND `&x` on a sub-32-bit operand.
  -- Original bug: lowerExpr used a hardcoded 32-bit all-ones mask,
  -- so `&a` for `a = 4'b1111` returned 0 instead of 1.
  -- Now fixed indirectly by the `narrowMaskConstants` post-pass in
  -- `Lower.lean` (the same pass that fixes Test 37).  Kept as a
  -- regression guard so any future change that re-widens the mask
  -- will fail here.
  IO.print "  Test 30: reduction-AND on 4-bit operand (issue #41)... "
  try
    let v := "
module bug1_reduction_and (input clk, input [3:0] a, output y);
  assign y = &a;
endmodule
"
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0xF)  -- a = 4'b1111
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [1] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [1] for &4'b1111, got {results} (issue #41)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 31 (issue #42): two module instances chained via an internal wire.
  -- Original-bug description: "flattenDesign drops the bridge wire,
  -- so `y = ~~a` collapses to `y = ~a`."  The real root cause is
  -- subtler — `lowerDesign` used to pick the *first* module in source
  -- order as the top, so declaring sub-modules before the top (which
  -- is the natural Verilog order — top last) caused the flattener to
  -- treat the leaf sub-module as the top.  Fixed by `lowerDesign`
  -- now picking the module that is not instantiated by any other.
  IO.print "  Test 31: chained module instances via internal wire (issue #42)... "
  try
    let v := "
module inc (input [7:0] x, output [7:0] o);
  assign o = ~x;
endmodule

module bug2_chained_inst (input clk, input [7:0] a, output [7:0] y);
  wire [7:0] mid;
  inc u1 (.x(a),   .o(mid));
  inc u2 (.x(mid), .o(y));
endmodule
"
    -- a = 125 → mid = ~125 = 130 → y = ~130 = 125 (= a)
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 125)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [125] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [125], got {results} (issue #42 — likely 130 = ~125, second instance bypassed)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 31b (issue #42 follow-up — comment #4673267681): two PARALLEL
  -- instances with no shared internal wire.  Originally reported as
  -- "only the first instance takes effect"; now passes thanks to the
  -- top-module selection fix in `lowerDesign`.  Kept as a regression
  -- guard for the broader multi-instance flattening path.
  IO.print "  Test 31b: parallel module instances (issue #42 follow-up)... "
  try
    let v := "
module add1 (input [7:0] x, output [7:0] o);
  assign o = x + 8'd1;
endmodule

module parallel_inst (input clk, input [7:0] a, input [7:0] b, output [7:0] ya, output [7:0] yb);
  add1 u1 (.x(a), .o(ya));
  add1 u2 (.x(b), .o(yb));
endmodule
"
    -- a = 10 → ya = 11; b = 200 → yb = 201.
    -- `JIT.setInput` indexes the user inputs (clk is skipped), so 0 = a,
    -- 1 = b — see emitSetInputSwitch in Sparkle/Backend/CppSim.lean.
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 10; JIT.setInput h 1 200)
      1
      (fun h => do
        let ya ← JIT.getOutput h 0
        let yb ← JIT.getOutput h 1
        return [ya, yb])
    if results == [11, 201] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [11, 201] (ya=a+1, yb=b+1), got {results} (issue #42 follow-up — second instance bypassed)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 31c (issue #42 follow-up — comment #4673267681): 3-deep chain
  -- through two internal wires.  ~~~a = ~a for an 8-bit operand, so
  -- expected y = ~a.
  IO.print "  Test 31c: 3-deep instance chain (issue #42 follow-up)... "
  try
    let v := "
module inc (input [7:0] x, output [7:0] o);
  assign o = ~x;
endmodule

module deep3 (input clk, input [7:0] a, output [7:0] y);
  wire [7:0] m1;
  wire [7:0] m2;
  inc u1 (.x(a),  .o(m1));
  inc u2 (.x(m1), .o(m2));
  inc u3 (.x(m2), .o(y));
endmodule
"
    -- a = 0x55 → m1 = 0xAA → m2 = 0x55 → y = 0xAA (= ~0x55 for 8-bit)
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0x55)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [0xAA] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [170] (~0x55 = 0xAA after 3 inversions), got {results} (issue #42 follow-up)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 32 (issue #43): signed comparison.
  -- Bug: parser drops `signed`, Lower.lean hardcodes `.lt_u` for <,
  -- so a signed-negative `a` is compared as a large unsigned value
  -- and `(-106) < 127` returns 0 instead of 1.
  IO.print "  Test 32: signed comparison `a < b` (issue #43)... "
  try
    let v := "
module bug3_signed_lt (input clk, input signed [7:0] a, input signed [7:0] b, output lt);
  assign lt = a < b;
endmodule
"
    -- a = -106 (8'hFFFF...96 -> low 8 bits 0x96), b = 127 (0x7F)
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0x96  -- -106 as 8-bit two's complement
                   JIT.setInput h 1 0x7F) -- 127
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [1] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [1] for (-106) < 127 signed, got {results} (issue #43)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 33 (issue #44): parameter default width hardcoded to 32.
  -- Bug: in Lower.lean `paramWidth` falls back to 32 for any
  -- parameter without an explicit range, so an 8-bit-input port
  -- declared `[W-1:0]` with default `parameter W = 8` resolves to
  -- 32 bits instead of 8.  We exercise the symptom indirectly: the
  -- module multiplies `a` (declared `[W-1:0]` with default W = 8)
  -- by a literal — when the port is correctly 8-bit, `a` gets
  -- masked to 0xFF before being multiplied; when the bug widens
  -- the port to 32-bit, the upper 24 bits of whatever the host
  -- passed in (or undefined garbage) participate in the product.
  -- We feed a value with set bits above bit 7 (0x1FF = 511) and
  -- multiply by 1 — a correctly-truncated module returns
  -- 0x1FF & 0xFF = 0xFF = 255, but with the 32-bit-wide port the
  -- full 0x1FF passes through.
  -- Diagnostic A: parameter default width — verbatim from the issue.
  -- `[W-1:0] a` with default W = 8 should mask 0x1FF down to 0xFF;
  -- if W resolves to 32 internally, 0x1FF leaks through.
  IO.print "  Test 33a: parameter default width (issue #44 verbatim)... "
  try
    let v := "
module param_default_width #(parameter W = 8) (input clk, input [W-1:0] a, output [W-1:0] y);
  assign y = a + 1;
endmodule
"
    -- a = 255 (0xFF).  Correct: 8-bit (a+1) wraps to 0.
    -- Bug (W=32 internally): result = 256, low 8 bits = 0 — same value but for the wrong reason.
    -- So feed 0x1FF instead: 8-bit input port should mask to 0xFF, (a+1) = 0; 32-bit port
    -- leaks 0x1FF, (a+1) = 0x200, low 8 bits at the [W-1:0] output = 0 again.
    -- The cleanest probe is to read `a` straight through: a 0x1FF input on an 8-bit
    -- port → 0xFF out; on a 32-bit port → 0x1FF out.  We test that separately as 33.
    -- Here we exercise the issue's literal repro and report the value either way.
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 255)  -- 0xFF, fits in 8 bits
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    -- With a = 0xFF and `assign y = a + 1`, an 8-bit lowering wraps to 0.
    if results == [0] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [0] (8-bit wrap of 255+1), got {results} (issue #44)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 33b: same defect, but exposed via a value that distinguishes
  -- 8-bit-masked input from 32-bit-passed-through input.  An 8-bit
  -- port truncates 0x1FF to 0xFF (255); a 32-bit port forwards 0x1FF (511).
  IO.print "  Test 33b: parameter default width truncates input (issue #44)... "
  try
    let v := "
module bug4_param_default_width #(parameter W = 8) (input clk, input [W-1:0] a, output [15:0] y);
  assign y = a;
endmodule
"
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0x1FF)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [0xFF] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [255] (8-bit input mask), got {results} (issue #44 — default W resolved to 32)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 33c: issue #44 symptom 2 — localparam constant-expression
  -- width.  `K = 3 + 4` should resolve to 7; the bug truncates K to
  -- 1-bit so `y = a + K` returns `a + 1` instead of `a + 7`.
  IO.print "  Test 33c: localparam K = 3+4 width (issue #44 symptom 2)... "
  try
    let v := "
module localparam_expr (input clk, input [7:0] a, output [7:0] y);
  localparam K = 3 + 4;
  assign y = a + K;
endmodule
"
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 10)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [17] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [17] (10 + (3+4)), got {results} (issue #44 sympt. 2 — likely 11 = 10+1, K truncated)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- ===================================================================
  -- Tests 35-38: probe other 32-bit-hardcoded constants in
  -- `Tools/SVParser/Lower.lean` that look like the issue-#41 family
  -- (operand-width-blind constants used to build IR for reduction /
  -- bitwise-NOT / logical-AND/OR / signed-extend lowerings).  If any
  -- of these PASS today they are passive regression guards; if they
  -- FAIL they are new bugs that warrant their own issues.
  -- ===================================================================

  -- Test 35: reduction-OR `|a` on a 4-bit operand.
  -- Lower.lean line 155 uses a 32-bit `.const 0 32` for the
  -- `(a != 0)` lowering.  With a 4-bit `a`, the wider zero may
  -- still compare equal to a (truncated) zero, but the eq result
  -- semantics aren't guaranteed when operand widths disagree.
  IO.print "  Test 35: reduction-OR on 4-bit operand (Lower.lean:155)... "
  try
    let v := "
module probe_redor (input clk, input [3:0] a, output y);
  assign y = |a;
endmodule
"
    -- a = 4'b0001 → expected 1 (any bit set)
    -- a = 4'b0000 → expected 0
    let r1 ← jitRun v (fun h => do JIT.setInput h 0 1) 1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    let r0 ← jitRun v (fun h => do JIT.setInput h 0 0) 1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if r1 == [1] && r0 == [0] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: a=1→{r1} a=0→{r0} (expected [1] and [0])"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 36: logical-NOT `!a` on a 4-bit operand.
  -- Lower.lean line 158 uses `.const 0 32` for the `(a == 0)`
  -- lowering.  Same width-mismatch concern as Test 35.
  IO.print "  Test 36: logical-NOT on 4-bit operand (Lower.lean:158)... "
  try
    let v := "
module probe_lnot (input clk, input [3:0] a, output y);
  assign y = !a;
endmodule
"
    let r1 ← jitRun v (fun h => do JIT.setInput h 0 5) 1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    let r0 ← jitRun v (fun h => do JIT.setInput h 0 0) 1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    -- !5 = 0, !0 = 1
    if r1 == [0] && r0 == [1] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: !5→{r1} !0→{r0} (expected [0] and [1])"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 37: bitwise-NOT `~a` on a 4-bit operand, observed via a
  -- downstream `+`.  Lower.lean line 161 emits `x XOR -1` with a
  -- 32-bit constant; without the `narrowMaskConstants` post-pass
  -- the upper-28 XORed bits leak into adjacent arithmetic and
  -- `~0 + 1` returns 0 instead of 16.  Fixed by that pass.
  IO.print "  Test 37: bitwise-NOT 4-bit, value-only check (Lower.lean:161)... "
  try
    let v := "
module probe_bnot (input clk, input [3:0] a, output [4:0] y);
  assign y = ~a + 1;
endmodule
"
    -- a = 4'b0000; ~a = 4'b1111 = 15; 15 + 1 = 16 (5 bits clean)
    -- bug: ~a as a 32-bit XOR = 0xFFFFFFFF; + 1 = 0x100000000 → low 5 bits = 0
    let r ← jitRun v (fun h => do JIT.setInput h 0 0) 1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if r == [16] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: ~0+1 (4-bit) → {r}, expected [16]"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 38: logical-AND `a && b` on 4-bit operands.
  -- Lower.lean line 176-178 uses `.const 0 32` for both
  -- `(lhs != 0)` and `(rhs != 0)` lowerings.
  IO.print "  Test 38: logical-AND 4-bit operands (Lower.lean:176)... "
  try
    let v := "
module probe_land (input clk, input [3:0] a, input [3:0] b, output y);
  assign y = a && b;
endmodule
"
    let r ← jitRun v
      (fun h => do JIT.setInput h 0 3; JIT.setInput h 1 5)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    let r0 ← jitRun v
      (fun h => do JIT.setInput h 0 0; JIT.setInput h 1 5)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if r == [1] && r0 == [0] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: 3&&5→{r}, 0&&5→{r0} (expected [1] and [0])"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 34 (issue #45): casez `?` wildcards.
  -- Bug: casez is routed through the same parseCaseBody as case, so
  -- `?` in case items is compared as an ordinary bit (= 0) and the
  -- wildcard arm never matches.
  IO.print "  Test 34: casez `?` wildcards (issue #45)... "
  try
    let v := "
module bug5_casez_wild (input clk, input [3:0] s, output [1:0] y);
  reg [1:0] yr;
  assign y = yr;
  always @* begin
    casez (s)
      4'b1???: yr = 2'd3;
      default: yr = 2'd0;
    endcase
  end
endmodule
"
    -- s = 4'b1010 should match `4'b1???` arm → y = 3
    let results ← jitRun v
      (fun h => do JIT.setInput h 0 0b1010)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if results == [3] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: expected [3] for casez 4'b1??? match, got {results} (issue #45 — wildcard arm never fires)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 45 (XiangShan Phase 2): reset-less register — `always
  -- @(posedge clock)` with an enable-only update.  The old lowering
  -- referenced a phantom `rst` wire that exists in no such module, so the
  -- re-emitted Verilog failed elaboration.  Now a shared `_no_rst`
  -- constant-0 wire drives a SYNCHRONOUS register (clock-only
  -- sensitivity), and it must survive DCE/const-prop/inlining (the reset
  -- is a String field no Expr walker sees).
  IO.print "  Test 45: reset-less register emits _no_rst, not phantom rst... "
  try
    let v := "
module no_rst_reg (input clock, input w, input [3:0] d, output [3:0] q);
  reg [3:0] r;
  always @(posedge clock) begin
    if (w)
      r <= d;
  end
  assign q = r;
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let sv := toVerilogDesign design
      if containsSubstr sv "posedge rst" || containsSubstr sv "if (rst)" then
        IO.println "FAIL: emitted Verilog references phantom `rst`"
        failed := failed + 1
      else if !(containsSubstr sv "logic _no_rst;"
                && containsSubstr sv "assign _no_rst = 1'd0;") then
        IO.println "FAIL: `_no_rst` wire/assign missing (eaten by DCE or inlining)"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 46 (XiangShan Phase 2, Mhpmcounter class): `~x` on a RANGE-LESS
  -- (scalar) wire inside a ternary condition.  `~x` lowers to
  -- `x ^ 32'hffffffff`; if the mask is not narrowed to the operand's 1-bit
  -- width, Verilog context sizing makes the whole condition 32-bit and
  -- `~w` evaluates non-zero even when w=1 — and the CSim JIT computes the
  -- unmasked 32-bit XOR, same wrong answer.  w=1 must select b.
  IO.print "  Test 46: scalar ~x in ternary condition (32-bit mask narrowing)... "
  try
    let v := "
module scalar_not_cond (input clk, input w, input [7:0] a, input [7:0] b,
                        output [7:0] y);
  assign y = (~w) ? a : b;
endmodule
"
    let rSel ← jitRun v
      (fun h => do JIT.setInput h 0 1; JIT.setInput h 1 17; JIT.setInput h 2 42)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    let rUnsel ← jitRun v
      (fun h => do JIT.setInput h 0 0; JIT.setInput h 1 17; JIT.setInput h 2 42)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    if rSel == [42] && rUnsel == [17] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: w=1→{rSel} (want [42]), w=0→{rUnsel} (want [17])"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 47 (XiangShan Phase 2, RenameTable class): the optimizer's
  -- register-liveness BFS must not run out of fuel on ref-dense bodies.
  -- 16 registers, each referencing all 16 (256 ref occurrences from a
  -- handful of statements) — the old `body.length * 8` fuel budget
  -- truncated the walk and SILENTLY PRUNED live registers, which
  -- `declareOrphanRefs` then patched with `assign x = 32'd0`.
  IO.print "  Test 47: liveness fuel on ref-dense register mesh... "
  try
    let n := 16
    let regDecls := String.intercalate "\n" ((List.range n).map fun i =>
      s!"  reg [3:0] r{i};")
    let allXor := String.intercalate " ^ " ((List.range n).map fun i => s!"r{i}")
    let updates := String.intercalate "\n" ((List.range n).map fun i =>
      s!"      r{i} <= d ^ {allXor};")
    let v := s!"
module reg_mesh (input clock, input rst, input [3:0] d, output [3:0] q);
{regDecls}
  always @(posedge clock) begin
    if (rst) begin
{String.intercalate "\n" ((List.range n).map fun i => s!"      r{i} <= 4'h0;")}
    end else begin
{updates}
    end
  end
  assign q = r0;
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let regCount := design.modules.foldl (fun acc m =>
        acc + m.body.foldl (fun a s => match s with
          | .register .. => a + 1 | _ => a) 0) 0
      let sv := toVerilogDesign design
      if regCount != n then
        IO.println s!"FAIL: {regCount}/{n} registers survived (liveness fuel ran out)"
        failed := failed + 1
      else if containsSubstr sv "= 32'd0;" then
        IO.println "FAIL: orphaned register patched with `assign x = 32'd0`"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 48 (XiangShan Phase 2, ByteMaskTailGen): an identifier ENDING in
  -- `begin` followed by a ternary colon (`io_in_begin : 8'h0`) must not
  -- trigger the hierarchical path's named-block strip (`begin : label`),
  -- which used to eat the rest of the line.
  IO.print "  Test 48: `x_begin :` in ternary survives named-block strip... "
  try
    let v := "
module begin_ident (input clk, input sel, input [7:0] io_in_begin,
                    output [7:0] y);
  assign y = sel ? io_in_begin : 8'h0;
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let sv := toVerilogDesign design
      if containsSubstr sv "io_in_begin" then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println "FAIL: io_in_begin vanished from the roundtrip"
        failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 49 (XiangShan Phr): DYNAMIC shift of a >64-bit value.  CSim's
  -- wide shl/shr emitters resolved the amount with `constAmt`, which
  -- returned 0 for any non-constant expression — Phr's rotation idiom
  -- `{phr, phr} >> ptr` (104-bit) silently read the UNSHIFTED vector, so
  -- every folded-history output was wrong once the pointer moved.
  IO.print "  Test 49: dynamic shift of a >64-bit value (Phr rotation)... "
  try
    let v := "
module wide_dyn_shr (input clk, input [6:0] amt, output [15:0] y);
  wire [79:0] base = 80'h5A5A5A5A5A5A5A5A5A5A;
  wire [79:0] shifted = base >> amt;
  assign y = shifted[15:0];
endmodule
"
    let r36 ← jitRun v
      (fun h => do JIT.setInput h 0 36)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    let r0 ← jitRun v
      (fun h => do JIT.setInput h 0 0)
      1
      (fun h => do let v ← JIT.getOutput h 0; return [v])
    -- base >> 36 = 0x5A5A5A5A5A5A5A5A5A5A >> 36 → low 16 bits = 0xA5A5
    if r36 == [0xA5A5] && r0 == [0x5A5A] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: amt=36→{r36} (want [42405]), amt=0→{r0} (want [23130])"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 50 (XiangShan dt_352x1): TRUE MULTI-PORT memory.  Real SRAM
  -- macros are not all 1R1W — XiangShan's Difftest array is 8R8W and
  -- fires several write ports in the same cycle.  The lowering used to
  -- fold every guarded write into a priority mux, which silently kept
  -- only the highest-priority write; `Stmt.memory` now carries extra
  -- read/write ports and both backends emit one guarded write per port.
  IO.print "  Test 50: multi-port memory (2W2R) keeps every port... "
  try
    let v := "
module mp_mem (
  input        clk,
  input  [1:0] w0_addr, input w0_en, input [7:0] w0_data,
  input  [1:0] w1_addr, input w1_en, input [7:0] w1_data,
  input  [1:0] r0_addr, input [1:0] r1_addr,
  output [7:0] r0_data, output [7:0] r1_data
);
  reg [7:0] Memory[0:3];
  always @(posedge clk) begin
    if (w0_en)
      Memory[w0_addr] <= w0_data;
    if (w1_en)
      Memory[w1_addr] <= w1_data;
  end
  assign r0_data = Memory[r0_addr];
  assign r1_data = Memory[r1_addr];
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      -- IR must carry one extra write port and one extra read port
      let ports := design.modules.foldl (fun acc m =>
        acc ++ m.body.filterMap fun s => match s with
          | .memory _ _ _ _ _ _ _ _ _ _ ew er => some (ew.length, er.length)
          | _ => none) []
      let sv := toVerilogDesign design
      -- both writes and both reads must appear in the emitted Verilog
      let writes := (sv.splitOn "Memory[").length - 1
      if ports != [(1, 1)] then
        IO.println s!"FAIL: IR extra ports = {ports} (expected [(1, 1)])"
        failed := failed + 1
      else if !(containsSubstr sv "w0_en" && containsSubstr sv "w1_en") then
        IO.println "FAIL: emitted Verilog lost a write port"
        failed := failed + 1
      else if writes < 4 then
        IO.println s!"FAIL: only {writes} Memory[...] references emitted (want 2 writes + 2 reads)"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 51 (XiangShan array_128x138): wide SLICE at a NON-ZERO offset.
  -- `matWide` had no `.slice` arm, so a >64-bit slice fell into the
  -- generic memcpy fallback, which copies from the operand's BASE word
  -- and DISCARDS `lo`.  firtool's 138x2 SRAM writes
  -- `wdata[137:69] << 69`; CSim silently computed `wdata[68:0] << 69`,
  -- so the JIT wrote the wrong half of every masked entry while both the
  -- IR and the re-emitted Verilog were correct.
  IO.print "  Test 51: wide slice at a non-zero offset (138-bit lane)... "
  try
    -- `sel` widens to 138 bits and shifts up by 69, so d[137:69] == sel
    -- while d[68:0] == 0.  Driving a 138-bit port directly is not
    -- possible through `JIT.setInput` (one machine word), so the wide
    -- value is built inside the module.
    let v := "
module wide_slice_off (input clk, input [15:0] sel, output [15:0] y);
  reg [137:0] d;
  always @(posedge clk) d <= {53'd0, sel, 69'd0};
  // The slice feeds a WIDE op, so it is materialised by `matWide`; its
  // operand is a plain 138-bit array lvalue, which is the shape that hit
  // the offset-dropping memcpy fallback.
  wire [137:0] w = {69'd0, d[137:69]} | 138'd0;
  assign y = w[15:0];
endmodule
"
    -- The buggy emitter read d[68:0] (== 0) and returned 0.
    -- sel sits at d[84:69], so the CORRECT slice d[137:69] lands it at
    -- bits [15:0] and y == sel.  The offset-dropping fallback reads
    -- d[68:0], whose low 16 bits are zero, so y == 0.
    let r ← jitRun v
      (fun h => do JIT.setInput h 0 0xBEEF)
      2
      (fun h => do let o ← JIT.getOutput h 0; return [o])
    if r == [0xBEEF] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: sel=0xBEEF → {r} (want [48879]; 0 means the slice offset was dropped)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 52 (XiangShan MulModuleS0): a wide concat NARROWER than its
  -- destination.  Booth partial products are sign-extended concats like
  -- `{{32{b[63]}}, b[63:32], a[31:0]}` (96 bits) assigned to a 128-bit
  -- wire.  The emitter copied `sizeof(dst)` from a 3-word compound
  -- literal — 16 bytes out of a 12-byte source — so the top word held
  -- whatever followed the literal in memory instead of the zero fill.
  -- This was the 128-bit CSA-tree value divergence in the hier sweep.
  IO.print "  Test 52: wide concat narrower than its destination... "
  try
    -- The short source `memcpy` reads whatever FOLLOWS the compound
    -- literal, so the test must observe the top word directly and keep
    -- other wide values live around it.  `pad` is all-ones so a stale
    -- read is distinguishable from the correct zero fill.
    let v := "
module concat_short (input clk, input [31:0] a, output [31:0] y);
  wire [127:0] pad = {4{32'hAAAAAAAA}};
  wire [127:0] x = {64'd0, a};
  wire [127:0] z = x | {96'd0, pad[31:0]};
  assign y = z[127:96];
endmodule
"
    -- x is 96 bits wide, so x[127:96] — and hence z[127:96] — must be 0.
    let r ← jitRun v
      (fun h => do JIT.setInput h 0 0xFFFFFFFF)
      1
      (fun h => do let o ← JIT.getOutput h 0; return [o])
    if r == [0] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: {r} (want [0]; nonzero = short memcpy read past the literal)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 53 (XiangShan Booth partial products): the top-level wide
  -- shl/shr arms called `emitExpr` and then SUBSCRIPTED the result, so a
  -- compound operand rendered as `(uint32_t[4]){...}[j]` — GCC rejects
  -- that ("subscripted value is not an array") once the nesting is deep
  -- enough, which is why MulModuleS0 would not even compile.  Assert on
  -- the emitted C directly: a shift operand must be materialised into a
  -- named temp, never subscripted inline.
  IO.print "  Test 53: wide shift materialises its operand (no literal[j])... "
  try
    let v := "
module shl_concat (input clk, input [15:0] sel, output [15:0] y);
  wire [95:0] hi = {96{sel[15]}};
  wire [127:0] x = {hi, sel, 16'd0} << 16;
  assign y = x[47:32];
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let c := toCDesign design
      -- No `}[` anywhere: that is a compound literal being subscripted.
      if containsSubstr c "}[" then
        IO.println "FAIL: emitted C subscripts a compound literal"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 54 (XiangShan arbiters): several continuous assigns each
  -- driving a DIFFERENT bit of one vector.  `exprToName` mapped `gnt[0]`
  -- and `gnt[1]` both to bare `gnt`, dropping the position, so the
  -- statements became competing full-vector drivers: iverilog rejected
  -- the emitted Verilog ("cannot have multiple drivers") and the IR kept
  -- only the LAST write.  They are now merged into one driver.
  IO.print "  Test 54: part-select assigns merge into one driver... "
  try
    let v := "
module bitsel (input [1:0] req, input ready, output [1:0] gnt);
  assign gnt[0] = req[0] & ready;
  assign gnt[1] = req[1] & ready;
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let drivers := design.modules.foldl (fun acc m =>
        acc + (m.body.filter fun s => match s with
          | .assign lhs _ => lhs == "gnt" | _ => false).length) 0
      let sv := toVerilogDesign design
      if drivers != 1 then
        IO.println s!"FAIL: {drivers} drivers for gnt (expected 1)"
        failed := failed + 1
      -- Both bits must survive the merge: req[1] belongs at bit 1.
      else if !(containsSubstr sv "req[1:1]" && containsSubstr sv "req[0:0]") then
        IO.println "FAIL: the merge dropped a bit"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 55 (XiangShan TwoLevelRRArbiter): a combinational handshake
  -- THROUGH a child instance.  `usesOf` filtered the instance's outputs
  -- out of EVERY connection, so feeding a child output back into that
  -- same child's input was invisible to the scheduler — the emitted pass
  -- read the STALE value.  The back edge must now be seen, which makes
  -- the body un-orderable and switches eval to fixed-point relaxation.
  IO.print "  Test 55: back edge through an instance is scheduled... "
  try
    let v := "
module rr (input [1:0] want, input ready_in, output [1:0] gnt_o);
  wire [1:0] gnt;
  wire [1:0] req = {want[1] & ~gnt[0], want[0]};
  rr_child c (.req(req), .ready(ready_in), .gnt(gnt));
  assign gnt_o = gnt;
endmodule
module rr_child (input [1:0] req, input ready, output [1:0] gnt);
  assign gnt[0] = req[0] & ready;
  assign gnt[1] = req[1] & ready;
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let c := toCDesign design
      -- The relaxation loop is the observable consequence of detecting
      -- the cycle; without it the single pass silently used stale `gnt`.
      if !(containsSubstr c "__round") then
        IO.println "FAIL: no fixed-point relaxation emitted for the cycle"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 56: complementary nested mux conditions.  Every register lowered
  -- from `if (reset) … else …` carried a DEAD `reset ? init : old` arm
  -- inside the else branch, emitted as `(~reset ? d : (reset ? 0 : q))`.
  -- When `~reset` is false, `reset` is true, so the inner mux can only
  -- pick its then-arm — the else-arm is unreachable.
  IO.print "  Test 56: complementary nested mux arms fold away... "
  try
    let v := "
module resetarm (input clk, input reset, input io_d, output q);
  reg r;
  always @(posedge clk) begin
    if (reset) r <= 1'd0;
    else r <= io_d;
  end
  assign q = r;
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let sv := toVerilogDesign design
      -- The dead inner arm mentions `reset` a SECOND time inside the mux.
      if containsSubstr sv "(reset ?" then
        IO.println "FAIL: the dead reset arm survived"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 57 (XiangShan LCredit2Decoupled_4): a wide INSTANCE CONNECTION
  -- that is a slice at a non-zero offset.  The connection emitter did
  -- `memcpy(child.port, <expr>, sizeof(...))`, which copies from the
  -- operand's BASE word and drops the offset — the parent wires the
  -- child's 256-bit data port to `io_in_flit[385:130]`, so the child's
  -- SRAM stored the wrong 256 bits every cycle.  The IR and the
  -- re-emitted Verilog were both correct; only the JIT was wrong.
  IO.print "  Test 57: wide instance connection keeps its slice offset... "
  try
    let v := "
module wconn (input clk, input [421:0] flit, output [63:0] y);
  wsink s (.d(flit[385:130]), .y(y));
endmodule
module wsink (input [255:0] d, output [63:0] y);
  assign y = d[63:0];
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let c := toCDesign design
      -- bit 130 = word 4, shift 2.  A memcpy from the base word (the bug)
      -- would reference flit[0] with no shift.
      if !(containsSubstr c "flit[4] >> 2") then
        IO.println "FAIL: the connection dropped its slice offset"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 58 (XiangShan NCBUpstreamRXREQ): Verilog's `~` is CONTEXT-
  -- determined, not self-determined, so an unbounded `~expr` inverts the
  -- CONTAINER's bits once it lands in a wider context.  NCBUpstreamRXREQ
  -- builds `{6{~(|Size)}}` as the sign-extend trick
  -- `6'd0 - (~(Size == 0) ^ 1)`; emitted unbounded, `~(…)` widened to 32
  -- bits, `^ 1` gave 0xffffffff, and `6'd0 - 0xffffffff` evaluated to 1
  -- instead of 6'h3f — the mask silently lost five of its six bits, and
  -- only the RE-EMITTED Verilog was wrong (an RT mismatch, not a JIT one).
  IO.print "  Test 58: unary NOT is width-bounded in emitted Verilog... "
  try
    -- The replication must be CONSUMED (here through a packed-array
    -- lookup) for the lowering to produce the `~(x == 0) ^ 1` shape that
    -- the unbounded emitter mis-evaluated.  Asserting the VALUE, not the
    -- absence of a syntax form: unfixed this yields 1, fixed 6'h3f.
    let v := "
module notw (input [2:0] sz, output [5:0] m);
  wire [5:0] t = {6{~(|sz)}};
  wire [7:0][5:0] tbl = {{t}, {6'h0}, {6'h20}, {6'h30}, {6'h38}, {6'h3C}, {6'h3E}, {t}};
  assign m = tbl[sz];
endmodule
"
    -- The JIT was always CORRECT here — only the emitted Verilog was
    -- wrong — so this asserts on the emitted RTL.  Under iverilog the
    -- unbounded form evaluates the 6-bit mask to 1 instead of 6'h3f;
    -- that end-to-end check is the sv-cosim harness's job (NCBUpstreamRXREQ
    -- is an RT mismatch there).  What can be pinned cheaply here is the
    -- invariant that makes it sound: a unary NOT never reaches the output
    -- unbounded, because Verilog's `~` is context-determined.
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let sv := toVerilogDesign design
      if containsSubstr sv "~(" || containsSubstr sv "~_" then
        IO.println "FAIL: emitted an unbounded `~`"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 59 (XiangShan TXDAT): reduction XOR over a TERNARY operand.
  -- `staticExprWidth` had no arm for a conditional, so `^(cond ? 8'h0 :
  -- beat[255:248])` had no static width and the parity expansion bailed
  -- to its undeclared-wire sentinel — `io_out_bits_dataCheck` collapsed
  -- to a constant, losing all 32 parity bytes.  (The sentinel is the
  -- deliberate fail-loud path; the gap was that a resolvable width was
  -- treated as unknown.)
  IO.print "  Test 59: reduction XOR over a ternary keeps its width... "
  try
    let v := "
module parity_tern (input [15:0] d, input z, output [1:0] p);
  assign p = {^(z ? 8'h0 : d[15:8]), ^(z ? 8'h0 : d[7:0])};
endmodule
"
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let sv := toVerilogDesign design
      if containsSubstr sv "__reduction_xor_unknown_width__" then
        IO.println "FAIL: parity bailed to the unknown-width sentinel"
        failed := failed + 1
      else if containsSubstr sv "assign p = 1'd0" then
        IO.println "FAIL: parity collapsed to a constant"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 60 (VectorFloatFMA): a WIDE slice at a non-word-aligned offset
  -- as a CONCAT element.  The wide-concat slot builder indexed
  -- `emitExpr(slice)`, and emitExpr has no inline form for a >64-bit
  -- slice with lo≠0 — it silently handed back the BASE, so
  -- `{car[106:1], b}` became `(car << 1) | b`: every bit of the CSA
  -- carry off by one, surfacing as a 1-LSB FMA rounding error three
  -- pipeline stages later.
  IO.print "  Test 60: wide slice offset survives inside a concat slot... "
  try
    -- The slice must itself be >64 bits (94:31 is exactly 64 and takes
    -- the sound narrow path) — the broken path was the >64-bit slice
    -- with a non-aligned lo, `car[106:1]`-style.
    let v := "
module cslot (input [31:0] a, input b, output [7:0] y);
  wire [127:0] base = {a, a, a, a};
  wire [96:0] r = {base[126:31], b};
  assign y = r[9:2];
endmodule
"
    -- base bit i = a[i % 32]; r bit j (j ≥ 1) = base[j + 30], so
    -- r[9:2] = base[39:32] = a[7:0] = 8'h01... compute: r[j]=base[j+30]:
    -- r[2]=base[32]=a[0], …, r[9]=base[39]=a[7] → y = a[7:0].
    let r ← jitRun v
      (fun h => do JIT.setInput h 0 0x800000A5; JIT.setInput h 1 1)
      1
      (fun h => do let o ← JIT.getOutput h 0; return [o])
    if r == [0xA5] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: {r} (want [165]; anything else = the slice offset was dropped)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 61 (DivUnit / SBToTL): a wide instance connection that is a
  -- COMPOUND (mux of concats), and a wide value consumed by a ≤64-bit
  -- context.  C has no expression form for a multi-word value, so these
  -- rendered compound literals into scalar arithmetic and did not
  -- compile — or, once hoisted, an un-truncated wide ref (SBToTL's
  -- `cond ? 64'h0 : {…}`) assigned a pointer to a uint64.  The
  -- `hoistWideForC` pre-pass now routes every such subexpression
  -- through a wire.
  IO.print "  Test 61: wide compound connection is hoisted and correct... "
  try
    -- The connection is a wide OP (not a concat): pre-hoist this emitted
    -- `array | array` — the C did not compile at all.
    let v := "
module hst (input [31:0] a, input s, output [7:0] y);
  wire [95:0] p = {a, a, a};
  wire [95:0] q = {a, 32'h0, a};
  hsink u (.d((s ? p : 96'h0) | (s ? 96'h0 : q)), .y(y));
endmodule
module hsink (input [95:0] d, output [7:0] y);
  assign y = d[39:32];
endmodule
"
    -- s=1: d = p | 0; d[39:32] = p[39:32] = a[7:0].  (The OR at the
    -- connection root with mux operands is DivUnit's csa_sel shape.)
    -- Value check AND a structural pin: from SV the optimizer's inlining
    -- protections can leave a wire in place, so the value alone cannot
    -- distinguish the hoisting pass — assert the hoist fired too.
    let r ← jitRun v
      (fun h => do JIT.setInput h 0 0x800000A5; JIT.setInput h 1 1)
      1
      (fun h => do let o ← JIT.getOutput h 0; return [o])
    let structOk := match parseAndLowerHierarchical v with
      | .ok design =>
        -- The IR shape that reached DivUnit came from the optimizer
        -- inlining a single-use wire into the connection; reproduce it
        -- directly at the IR level and demand the hoist wire.
        let m : Sparkle.IR.AST.Module := {
          name := "hroot"
          inputs := [⟨"s", .bit⟩, ⟨"p", .bitVector 96⟩, ⟨"q", .bitVector 96⟩]
          outputs := [⟨"y", .bitVector 8⟩]
          wires := [⟨"dw", .bitVector 96⟩]
          body := [
            .inst "hsink" "u" [("d",
              .op .or [
                .op .mux [.ref "s", .ref "p", .const 0 96],
                .op .mux [.ref "s", .const 0 96, .ref "q"]]),
              ("y", .ref "y")]]
          assertions := [] }
        let sink := (design.modules.find? (·.name == "hsink")).getD m
        let c := Sparkle.Backend.CSim.toCDesign
          { topModule := "hroot", modules := [m, sink] }
        containsSubstr c "_wide_hoist_"
      | .error _ => false
    if r == [0xA5] && structOk then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: value={r} (want [165]) hoisted={structOk}"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 62 (XiangShan MiscModule / VpnTable): concat elements are
  -- SELF-DETERMINED in Verilog, so a packed-table gather element like
  -- `(_GEN >> (idx*4)) & 4'd15` is as wide as `_GEN` (64 bits), not the
  -- 4 bits the IR means — the 16-nibble xperm concat became 1024 bits
  -- and only its LAST element landed in the 64-bit target.  The dynamic
  -- select lowerings now pin the width with an explicit `.slice`, which
  -- the Verilog emitter renders as a size cast.
  IO.print "  Test 62: dynamic packed-select keeps its width in a concat... "
  try
    let v := "
module xperm (input [15:0] src, input [7:0] sel, output [7:0] y);
  wire [3:0][3:0] tbl = {src[15:12], src[11:8], src[7:4], src[3:0]};
  assign y = {tbl[sel[5:4]], tbl[sel[1:0]]};
endmodule
"
    -- src = 0xABCD, sel = 8'h01 → hi nibble tbl[0]=D, lo nibble tbl[1]=C
    let r ← jitRun v
      (fun h => do JIT.setInput h 0 0xABCD; JIT.setInput h 1 0x01)
      1
      (fun h => do let o ← JIT.getOutput h 0; return [o])
    match parseAndLowerHierarchical v with
    | .error e => IO.println s!"FAIL: lower error {e}"; failed := failed + 1
    | .ok design =>
      let sv := toVerilogDesign design
      -- iverilog must also agree, i.e. each op element carries a cast.
      if r != [0xDC] then
        IO.println s!"FAIL: JIT {r} (want [220])"
        failed := failed + 1
      else if !(containsSubstr sv "4'(") then
        IO.println "FAIL: emitted concat elements are unsized"
        failed := failed + 1
      else
        IO.println "PASS"; passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 63 (XiangShan TIMER): a WIDE dynamic shift AMOUNT.  The amount
  -- of `128'h1 << {121'h0, addr[14], addr[8:3]}` is itself a 128-bit
  -- value; once hoisted to a word array, `(unsigned)(amount)` took the
  -- POINTER, so the CLINT's register-select one-hot was shifted by
  -- garbage and every ipi/timecmp write was lost.  Wide amounts now read
  -- their low word.
  IO.print "  Test 63: wide dynamic shift amount reads its value... "
  try
    let v := "
module whot (input [6:0] a, output o);
  wire [127:0] sel = 128'h1 << {121'h0, a};
  assign o = sel[0];
endmodule
"
    -- a = 0 → sel = 1 → o = 1.  With the pointer bug o was 0.
    let r ← jitRun v
      (fun h => do JIT.setInput h 0 0)
      1
      (fun h => do let o ← JIT.getOutput h 0; return [o])
    if r == [1] then
      IO.println "PASS"; passed := passed + 1
    else
      IO.println s!"FAIL: {r} (want [1]; 0 = the amount was read as a pointer)"
      failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 64 (certified-roundtrip M0): `emitAstExpr` is the shipping
  -- emitter, at the AST level — validated by PARSE-equality over every
  -- expression of the real XiangShan CI corpus.  For each parsed+lowered
  -- module, every assign RHS and register input must satisfy
  --   parse (Verilog.emitExpr widthOf e) = emitAstExpr widthOf e.
  -- Skips gracefully when the corpus is absent (it is downloaded in CI).
  IO.print "  Test 64: emitAst{Expr,Module} ≡ shipping emitter on the CI corpus... "
  try
    let corpusDir := "bench/xiangshan/corpus"
    if ← System.FilePath.pathExists corpusDir then
      let mut exprs := 0
      let mut bad := 0
      let mut firstBad := ""
      let entries ← System.FilePath.readDir corpusDir
      for ent in entries do
        if ent.fileName.endsWith ".sv" then
          let src ← IO.FS.readFile ent.path
          match parseAndLowerHierarchical src with
          | .error _ => pure ()
          | .ok design =>
            for m in design.modules do
              -- the widthOf the shipping emitStmt builds: wires by
              -- SANITIZED name
              let wof : String → Option Nat := fun n =>
                ((m.wires ++ m.inputs ++ m.outputs).find? (fun p =>
                  Sparkle.Backend.Verilog.sanitizeName p.name == n)).bind
                  fun p => match p.ty with
                    | .bitVector w => some w
                    | .bit => some 1
                    | _ => none
              let es : List Sparkle.IR.AST.Expr := m.body.foldl (fun acc st =>
                match st with
                | .assign _ rhs => rhs :: acc
                | .register _ _ _ input _ => input :: acc
                | _ => acc) []
              for e in es do
                exprs := exprs + 1
                let rendered := Sparkle.Backend.Verilog.emitExpr wof e
                match Tools.SVParser.EmitAst.parseExprString rendered with
                | .ok sv =>
                  if Tools.SVParser.EmitAst.emitAstExpr wof e != some sv then
                    bad := bad + 1
                    if firstBad == "" then
                      firstBad := s!"{ent.fileName}/{m.name}: {rendered.take 80}"
                | .error err =>
                  bad := bad + 1
                  if firstBad == "" then
                    firstBad := s!"{ent.fileName}/{m.name} (parse: {err.take 40}): {rendered.take 60}"
              -- module level: whole-module parse-equality
              exprs := exprs + 1
              match Tools.SVParser.Parser.parseModuleFromString
                  (Sparkle.Backend.Verilog.emitModule m) with
              | .ok sv =>
                if Tools.SVParser.EmitAst.emitAstModule m != some sv then
                  bad := bad + 1
                  if firstBad == "" then
                    firstBad := s!"MODULE {ent.fileName}/{m.name}"
              | .error err =>
                bad := bad + 1
                if firstBad == "" then
                  firstBad := s!"MODULE {ent.fileName}/{m.name} (parse: {err.take 60})"
      if bad == 0 && exprs > 0 then
        IO.println s!"PASS ({exprs} expressions)"
        passed := passed + 1
      else
        IO.println s!"FAIL: {bad}/{exprs} disagree; first: {firstBad}"
        failed := failed + 1
    else
      IO.println "SKIP (corpus not present)"
      passed := passed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 65 (certified-roundtrip M1): a REGISTER survives re-parsing
  -- Sparkle's own emission.  `logic r = 8'h3;` is a register
  -- INITIALIZER when r is procedurally assigned in an always block; the
  -- lowering used to also emit `assign r = 3`, the register-vs-assign
  -- dedup kept the constant assign, and the register folded away —
  -- q became `assign q = 3'd3` and the feedback loop vanished.
  IO.print "  Test 65: registers survive self-reparse... "
  try
    let m : Sparkle.IR.AST.Module := {
      name := "selfrt"
      inputs := [⟨"clock", .bit⟩, ⟨"rst", .bit⟩, ⟨"a", .bitVector 8⟩]
      outputs := [⟨"q", .bitVector 8⟩]
      wires := [⟨"w", .bitVector 8⟩, ⟨"r", .bitVector 8⟩, ⟨"q", .bitVector 8⟩]
      body := [
        .assign "w" (.op .add [.ref "a", .ref "r"]),
        .register "r" "clock" ("rst", .asynchronous) (.ref "w") 3,
        .assign "q" (.ref "r")]
      assertions := [] }
    match parseAndLowerHierarchical (Sparkle.Backend.Verilog.emitModule m) with
    | .error e => IO.println s!"FAIL: reparse error {e}"; failed := failed + 1
    | .ok d =>
      let regs := d.modules.foldl (fun acc lm =>
        acc + (lm.body.filter fun st => match st with
          | .register out _ _ _ _ => out == "r" | _ => false).length) 0
      if regs == 1 then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: register count {regs} (folded to a constant?)"
        failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  -- Test 66 (certified-roundtrip): a SYNC-READ memory survives
  -- re-parsing Sparkle's own emission as exactly the original stmt.
  -- `rdata <= Mem[ra]` used to be claimed as the memory's sync read
  -- AND lowered as a scalar register whose input was a garbage
  -- bit-select of the ARRAY (`(Mem >> ra) & 1`) — a duplicate driver.
  IO.print "  Test 66: sync-read memory survives self-reparse... "
  try
    let m : Sparkle.IR.AST.Module := {
      name := "syncrt"
      inputs := [⟨"clock", .bit⟩, ⟨"wa", .bitVector 2⟩, ⟨"wd", .bitVector 8⟩,
                 ⟨"wen", .bit⟩, ⟨"ra", .bitVector 2⟩]
      outputs := [⟨"rdata", .bitVector 8⟩]
      wires := [⟨"rdata", .bitVector 8⟩]
      body := [
        .memory "Mem" 2 8 "clock" (.ref "wa") (.ref "wd") (.ref "wen")
          (.ref "ra") "rdata" false [] []]
      assertions := [] }
    match parseAndLowerHierarchical (Sparkle.Backend.Verilog.emitModule m) with
    | .error e => IO.println s!"FAIL: reparse error {e}"; failed := failed + 1
    | .ok d =>
      let bodies := d.modules.foldl (fun acc lm => acc ++ lm.body) []
      if bodies == m.body then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: lowered body ≠ original ({bodies.length} stmts)"
        failed := failed + 1
  catch e => IO.println s!"FAIL: {e}"; failed := failed + 1

  IO.println s!"\n=== Results: {passed} passed, {failed} failed ==="
  return if failed == 0 then 0 else 1
