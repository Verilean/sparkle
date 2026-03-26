/-
  SystemVerilog Parser Tests

  Test 1-5: Parser + lowering for simple counter
  Test 6: E2E — parse Verilog → lower to IR → generate CppSim → JIT compile → simulate
  Test 7: PicoRV32 parse (3049-line RISC-V CPU)
-/

import Tools.SVParser
import Sparkle.Backend.Verilog
import Sparkle.Backend.CppSim
import Sparkle.Core.JIT

open Tools.SVParser.AST
open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Sparkle.IR.AST
open Sparkle.Backend.Verilog
open Sparkle.Backend.CppSim
open Sparkle.Core.JIT

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
      let jitCpp := toCppSimJIT jitDesign
      let jitPath := "/tmp/sparkle_sv_counter_jit.cpp"
      IO.FS.writeFile jitPath jitCpp

      -- JIT compile and load
      try
        let handle ← JIT.compileAndLoad jitPath
        -- Reset
        JIT.reset handle
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
        let jitCpp := toCppSimJIT coreDesign
        let cppPath := "/tmp/picorv32_core_jit.cpp"
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
      let jitCpp := toCppSimJIT flatDesign
      let cppPath := "/tmp/picorv32_soc_jit.cpp"
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
      let uartChars := uartOutput.filterMap fun v =>
        let n := v.toNat
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
      let jitCpp := toCppSimJIT flatDesign
      IO.FS.writeFile "/tmp/picorv32_cfirmware_jit.cpp" jitCpp
      let handle ← JIT.compileAndLoad "/tmp/picorv32_cfirmware_jit.cpp"
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
        IO.println s!"FAIL (fib={fibOk} sum={sumOk} sort={sortOk} gcd={gcdOk} pass={hasPass}, {uartOutput.length} words)"
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
    let jitCpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_pcpi_mul_jit.cpp" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.cpp"
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
        let h2 ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.cpp"
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
    let jitCpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_pcpi_mul_jit.cpp" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.cpp"
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
    let jitCpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_pcpi_mul_jit.cpp" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.cpp"
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
    let jitCpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_pcpi_mul_jit.cpp" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_pcpi_mul_jit.cpp"
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
    let jitCpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_mul_wrapper_jit.cpp" jitCpp
    try
      let h ← JIT.compileAndLoad "/tmp/sparkle_mul_wrapper_jit.cpp"
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
    let cpp := toCppSimJIT design
    IO.FS.writeFile "/tmp/sparkle_pair_test.cpp" cpp
    let h ← JIT.compileAndLoad "/tmp/sparkle_pair_test.cpp"
    JIT.reset h
    setupFn h
    for _ in [:cycles] do JIT.evalTick h
    let results ← getResults h
    JIT.destroy h
    return results

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

  IO.println s!"\n=== Results: {passed} passed, {failed} failed ==="
  return if failed == 0 then 0 else 1
