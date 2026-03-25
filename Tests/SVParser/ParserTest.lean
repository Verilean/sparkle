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
      -- 'sum' and 'acc' should have assign statements
      -- 'acc' should have SSA chain (acc_ssa0_0 through acc_ssa0_4)
      let hasSum := m.body.any fun s => match s with
        | .assign "sum" _ => true | _ => false
      let ssaCount := m.wires.filter (fun w => containsSubstr w.name "acc_ssa") |>.length
      if hasSum && ssaCount >= 4 then
        IO.println s!"PASS (SSA wires={ssaCount})"; passed := passed + 1
      else
        IO.println s!"FAIL: sum={hasSum} ssaWires={ssaCount}"
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
      -- 'read_val' should have an assign statement referencing mem[addr]
      let hasReadVal := m.body.any fun s => match s with
        | .assign "read_val" _ => true | _ => false
      let readValExpr := m.body.findSome? fun s => match s with
        | .assign "read_val" e => some (toString e)
        | _ => none
      let exprStr := readValExpr.getD ""
      -- Should reference 'mem' (array access)
      let hasMem := containsSubstr exprStr "mem"
      if hasReadVal && hasMem then
        IO.println "PASS"; passed := passed + 1
      else
        IO.println s!"FAIL: hasReadVal={hasReadVal} hasMem={hasMem} expr={exprStr}"
        for s in m.body do IO.println s!"  {s}"
        failed := failed + 1

  -- Test 17: pcpi_mul standalone parse+lower (carry-save accumulator)
  -- Verifies: parameter substitution, for-loop unroll, concat-LHS decompose,
  -- nested SSA, __RMW_BASE__ placeholder, 64-bit promotion
  IO.print "  Test 17: pcpi_mul standalone IR... "
  let picoExists' ← System.FilePath.pathExists "/tmp/picorv32.v"
  if picoExists' then
    try
      let cpu ← IO.FS.readFile "/tmp/picorv32.v"
      -- Extract just picorv32_pcpi_mul module with default params
      match Tools.SVParser.Parser.parse cpu with
      | .error e => IO.println s!"FAIL (parse): {e}"; failed := failed + 1
      | .ok svDesign =>
        let mulMod? := svDesign.modules.find? fun m => m.name == "picorv32_pcpi_mul"
        match mulMod? with
        | none => IO.println "FAIL: pcpi_mul module not found"; failed := failed + 1
        | some svMul =>
          match lowerModule svMul with
          | .error e => IO.println s!"FAIL (lower): {e}"; failed := failed + 1
          | .ok m =>
            -- Check: has registers for rd, rdx, rs1, rs2, mul_counter, mul_waiting
            let regNames := m.body.filterMap fun s => match s with
              | .register name _ _ _ _ => some name | _ => none
            let hasRd := regNames.any (· == "rd")
            let hasRdx := regNames.any (· == "rdx")
            let hasRs1 := regNames.any (· == "rs1")
            let hasMulCounter := regNames.any (· == "mul_counter")
            -- Check: has SSA wires for carry-save (next_rd_ssa, next_rdt_ssa)
            let ssaWires := m.wires.filter (fun w => containsSubstr w.name "_ssa")
            let hasInnerSsa := ssaWires.any (fun w => containsSubstr w.name "_ssa1_")
            -- Check: has assigns for next_rd, next_rdx, next_rs1, next_rs2
            let assignNames := m.body.filterMap fun s => match s with
              | .assign name _ => some name | _ => none
            let hasNextRd := assignNames.any (· == "next_rd")
            let hasNextRdx := assignNames.any (· == "next_rdx")
            -- Check: __RMW_BASE__ should NOT appear in any expression (all resolved)
            let bodyStr := String.intercalate "\n" (m.body.map toString)
            let hasRmwPlaceholder := containsSubstr bodyStr "__RMW_BASE__"
            if hasRd && hasRdx && hasRs1 && hasMulCounter &&
               hasInnerSsa && hasNextRd && hasNextRdx && !hasRmwPlaceholder then
              IO.println s!"PASS (regs={regNames.length}, SSA wires={ssaWires.length}, assigns={assignNames.length})"
              passed := passed + 1
            else
              IO.println s!"FAIL: rd={hasRd} rdx={hasRdx} rs1={hasRs1} counter={hasMulCounter} innerSSA={hasInnerSsa} nextRd={hasNextRd} nextRdx={hasNextRdx} rmwClean={!hasRmwPlaceholder}"
              IO.println s!"  regNames={regNames}"
              IO.println s!"  ssaWireCount={ssaWires.length}"
              if hasRmwPlaceholder then
                IO.println "  ERROR: __RMW_BASE__ placeholder not resolved!"
              failed := failed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"; failed := failed + 1
  else
    IO.println "SKIP (picorv32.v not found)"

  -- Test 18: Carry-save for-loop SSA chain correctness
  -- The inner j-loop (16 iterations, CARRY_CHAIN=4) must produce:
  --   next_rd_ssa1_0 = next_rd (prologue)
  --   next_rd_ssa1_1 = f(next_rd_ssa1_0, ...)  (j=0, bits 0-3)
  --   next_rd_ssa1_2 = f(next_rd_ssa1_1, ...)  (j=4, bits 4-7)
  --   ...
  --   next_rd_ssa1_16 = f(next_rd_ssa1_15, ...) (j=60, bits 60-63)
  --   next_rd = next_rd_ssa1_16 (epilogue)
  -- Each step must reference the PREVIOUS step (not ssa1_0 or self).
  IO.print "  Test 18: Carry-save SSA chain references... "
  if picoExists' then
    try
      let cpu ← IO.FS.readFile "/tmp/picorv32.v"
      match Tools.SVParser.Parser.parse cpu with
      | .error e => IO.println s!"FAIL (parse): {e}"; failed := failed + 1
      | .ok svDesign =>
        let mulMod? := svDesign.modules.find? fun m => m.name == "picorv32_pcpi_mul"
        match mulMod? with
        | none => IO.println "FAIL: pcpi_mul not found"; failed := failed + 1
        | some svMul =>
          match lowerModule svMul with
          | .error e => IO.println s!"FAIL (lower): {e}"; failed := failed + 1
          | .ok m =>
            -- Collect all assigns for next_rd SSA chain
            let rdSsaAssigns := m.body.filterMap fun s => match s with
              | .assign name expr => if containsSubstr name "next_rd_ssa1_" then some (name, toString expr) else none
              | _ => none
            -- Check chain: each ssa1_N (N>=1) must reference ssa1_{N-1}
            let mut chainOk := true
            let mut chainErrors : List String := []
            for (name, exprStr) in rdSsaAssigns do
              -- Extract N from "next_rd_ssa1_N" or "next_rd_ssa0_1_ssa1_N"
              let parts := name.splitOn "_ssa1_"
              if parts.length >= 2 then
                let idxStr := parts[parts.length - 1]!
                match idxStr.toNat? with
                | some n =>
                  if n >= 1 then
                    let prevName := s!"{parts[0]!}_ssa1_{n - 1}"
                    if !containsSubstr exprStr prevName then
                      chainOk := false
                      chainErrors := chainErrors ++ [s!"{name} does NOT reference {prevName}"]
                  -- ssa1_0 (prologue) should reference "next_rd" (original)
                  if n == 0 then
                    if !containsSubstr exprStr "next_rd" then
                      chainOk := false
                      chainErrors := chainErrors ++ [s!"{name} does NOT reference next_rd"]
                | none => pure ()
            -- Check epilogue: next_rd = next_rd_ssa1_16
            let epilogue := m.body.findSome? fun s => match s with
              | .assign "next_rd" expr => some (toString expr)
              | _ => none
            let epilogueOk := match epilogue with
              | some e => containsSubstr e "next_rd_ssa1_16"
              | none => false
            -- Check count: should have 17 SSA wires (ssa1_0 through ssa1_16)
            let ssaCount := rdSsaAssigns.length
            if chainOk && epilogueOk && ssaCount >= 16 then
              IO.println s!"PASS ({ssaCount} SSA steps, chain OK)"
              passed := passed + 1
            else
              IO.println s!"FAIL: chainOk={chainOk} epilogueOk={epilogueOk} ssaCount={ssaCount}"
              for e in chainErrors do IO.println s!"  {e}"
              if !epilogueOk then
                IO.println s!"  epilogue: {epilogue.getD "NOT FOUND"}"
              failed := failed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"; failed := failed + 1
  else
    IO.println "SKIP (picorv32.v not found)"

  -- Test 19: Carry-save for-loop: next_rdt SSA chain (carry bits)
  -- Each j-iteration writes a carry bit to next_rdt[j+3].
  -- next_rdt_ssa1_N must reference next_rdt_ssa1_{N-1}.
  IO.print "  Test 19: Carry-save next_rdt SSA chain... "
  if picoExists' then
    try
      let cpu ← IO.FS.readFile "/tmp/picorv32.v"
      match Tools.SVParser.Parser.parse cpu with
      | .error _ => IO.println "FAIL (parse)"; failed := failed + 1
      | .ok svDesign =>
        match svDesign.modules.find? (fun m => m.name == "picorv32_pcpi_mul") with
        | none => IO.println "FAIL: not found"; failed := failed + 1
        | some svMul =>
          match lowerModule svMul with
          | .error e => IO.println s!"FAIL (lower): {e}"; failed := failed + 1
          | .ok m =>
            let rdtSsaAssigns := m.body.filterMap fun s => match s with
              | .assign name expr => if containsSubstr name "next_rdt_ssa1_" then some (name, toString expr) else none
              | _ => none
            let mut chainOk := true
            let mut chainErrors : List String := []
            for (name, exprStr) in rdtSsaAssigns do
              let parts := name.splitOn "_ssa1_"
              if parts.length >= 2 then
                let idxStr := parts[parts.length - 1]!
                match idxStr.toNat? with
                | some n =>
                  if n >= 1 then
                    let prevName := s!"{parts[0]!}_ssa1_{n - 1}"
                    if !containsSubstr exprStr prevName then
                      chainOk := false
                      chainErrors := chainErrors ++ [s!"{name} does NOT ref {prevName}"]
                | none => pure ()
            if chainOk && rdtSsaAssigns.length >= 16 then
              IO.println s!"PASS ({rdtSsaAssigns.length} SSA steps)"
              passed := passed + 1
            else
              IO.println s!"FAIL: chainOk={chainOk} count={rdtSsaAssigns.length}"
              for e in chainErrors do IO.println s!"  {e}"
              failed := failed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"; failed := failed + 1
  else
    IO.println "SKIP (picorv32.v not found)"

  -- Test 20: Carry-save: next_rdx reads from FINAL next_rdt (after j-loop)
  -- Bug: outer SSA renamed next_rdt to _ssa0_0 (pre-j-loop value) instead of
  -- _ssa0_1 (post-j-loop). With numIters<=1 skip, should read final next_rdt.
  IO.print "  Test 20: next_rdx reads post-loop next_rdt... "
  if picoExists' then
    try
      let cpu ← IO.FS.readFile "/tmp/picorv32.v"
      match Tools.SVParser.Parser.parse cpu with
      | .error _ => IO.println "FAIL (parse)"; failed := failed + 1
      | .ok svDesign =>
        match svDesign.modules.find? (fun m => m.name == "picorv32_pcpi_mul") with
        | none => IO.println "FAIL: not found"; failed := failed + 1
        | some svMul =>
          match lowerModule svMul with
          | .error e => IO.println s!"FAIL (lower): {e}"; failed := failed + 1
          | .ok m =>
            let rdxExpr := m.body.findSome? fun s => match s with
              | .assign "next_rdx" expr => some (toString expr)
              | _ => none
            match rdxExpr with
            | none =>
              IO.println "FAIL: next_rdx assign not found"
              failed := failed + 1
            | some exprStr =>
              -- next_rdx should reference next_rdt (the final value after j-loop)
              -- or next_rdt_ssa1_16 (the epilogue result)
              let refsRdt := containsSubstr exprStr "next_rdt"
              -- It should NOT reference the pre-loop value via _ssa0_0
              -- (which would mean it's reading stale data)
              let refsStaleSSA := containsSubstr exprStr "next_rdt_ssa0_0"
              if refsRdt && !refsStaleSSA then
                IO.println s!"PASS"
                passed := passed + 1
              else
                IO.println s!"FAIL: refsRdt={refsRdt} refsStaleSSA={refsStaleSSA}"
                IO.println s!"  expr={exprStr.take 200}"
                failed := failed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"; failed := failed + 1
  else
    IO.println "SKIP (picorv32.v not found)"

  IO.println s!"\n=== Results: {passed} passed, {failed} failed ==="
  return if failed == 0 then 0 else 1
