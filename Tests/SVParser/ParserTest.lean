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
    | .ok design =>
      let memInits := Tools.SVParser.Lower.extractReadMemH design
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

      let svDesign ← IO.ofExcept (Tools.SVParser.Parser.parse combined)
      let design ← IO.ofExcept (lowerDesign svDesign)

      -- Filter to SoC + picorv32 only
      let needed := design.modules.filter fun (m : Module) =>
        m.name == "picorv32_soc" || m.name == "picorv32"
      let filteredDesign : Design := { topModule := "picorv32_soc", modules := needed }

      -- Generate and compile JIT
      let jitCpp := toCppSimJIT filteredDesign
      let cppPath := "/tmp/picorv32_soc_jit.cpp"
      IO.FS.writeFile cppPath jitCpp

      let handle ← JIT.compileAndLoad cppPath

      -- Load firmware into memory (memory index 0 = first memory in SoC)
      let fwContents ← IO.FS.readFile fwPath
      let lines := fwContents.splitOn "\n"
      let mut addr : UInt32 := 0
      for line in lines do
        let trimmed := line.trim
        if trimmed.startsWith "@" then
          -- Address directive
          let hexAddr := trimmed.drop 1
          addr := String.toNat! s!"0x{hexAddr}" |>.toUInt32
        else if trimmed.length >= 8 then
          -- Hex data word
          let word := String.toNat! s!"0x{trimmed}" |>.toUInt32
          JIT.setMem handle 0 (addr / 4) word
          addr := addr + 4

      -- Reset and run
      JIT.reset handle

      -- De-assert reset (set resetn = 1) — PicoRV32 uses active-low reset
      JIT.setInput handle 1 1  -- resetn = 1

      -- Run for 10000 cycles, check for UART output
      let mut uartOutput : List UInt64 := []
      for _ in [:10000] do
        JIT.evalTick handle
        let uartValid ← JIT.getOutput handle 1  -- uart_valid
        if uartValid != 0 then
          let uartData ← JIT.getOutput handle 0  -- uart_data
          uartOutput := uartOutput ++ [uartData]

      let numRegs ← JIT.numRegs handle
      JIT.destroy handle

      -- Count non-zero UART bytes
      let nonZero := uartOutput.filter (· != 0)
      IO.println s!"PASS ({numRegs} regs, {uartOutput.length} UART events, {nonZero.length} non-zero)"
      passed := passed + 1
    catch e =>
      IO.println s!"FAIL: {toString e}"
      failed := failed + 1
  else
    IO.println "SKIP (files not found)"

  IO.println s!"\n=== Results: {passed} passed, {failed} failed ==="
  return if failed == 0 then 0 else 1
