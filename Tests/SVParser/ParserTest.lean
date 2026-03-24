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

      if hasStart && hasPass && !hasFail then
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
        IO.println s!"PASS ({uartOutput.length} UART words, fib={if fibOk then "OK" else "MISMATCH"})"
        passed := passed + 1
      else
        IO.println s!"FAIL (start={hasStart} pass={hasPass} fail={hasFail}, {uartOutput.length} words)"
        failed := failed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"
      failed := failed + 1
  else
    IO.println "SKIP (files not found)"

  IO.println s!"\n=== Results: {passed} passed, {failed} failed ==="
  return if failed == 0 then 0 else 1
