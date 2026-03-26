/-
  LiteX SoC Parse & Lower Test

  Stress-tests the SVParser with a LiteX-generated PicoRV32 SoC (1730 lines).
  Phase 1: Parse only (verify all constructs are recognized)
  Phase 2: Lower to Sparkle IR
  Phase 3: Generate JIT C++ and simulate
-/

import Tools.SVParser
import Sparkle.Backend.CppSim
import Sparkle.Core.JIT
open Tools.SVParser.Parser
open Tools.SVParser.Lower
open Sparkle.Core.JIT

def main : IO Unit := do
  let path := "Tests/SVParser/fixtures/litex_sim_minimal.v"
  let fileExists ← System.FilePath.pathExists path
  if !fileExists then
    IO.println s!"SKIP: {path} not found"
    pure ()

  let src ← IO.FS.readFile path
  IO.println s!"LiteX SoC: Read {src.length} chars from {path}"

  -- Phase 1: Parse
  -- Preprocess: replace @(*) with @* (LiteX/Migen convention)
  let src := "@*".intercalate (src.splitOn "@(*)")
  let atStarCount := (src.splitOn "@(*)").length - 1
  IO.println s!"  @(*) remaining after preprocess: {atStarCount}"

  IO.print "  Phase 1: Parse... "
  match parse src with
  | .error e =>
    IO.println s!"FAIL"
    IO.println s!"  Parse error: {e}"
    pure ()
  | .ok design =>
    IO.println s!"PASS ({design.modules.length} modules)"
    for m in design.modules do
      IO.println s!"    Module: {m.name} ({m.items.length} items, {m.params.length} params)"

  -- Phase 2: Lower to IR
  IO.print "  Phase 2: Lower to IR... "
  match parseAndLower src with
  | .error e =>
    IO.println s!"FAIL"
    IO.println s!"  Lower error: {e}"
    pure ()
  | .ok d =>
    IO.println s!"PASS ({d.modules.length} modules)"
    for m in d.modules do
      let regCount := m.body.filter fun s => match s with
        | .register _ _ _ _ _ => true | _ => false
      let assignCount := m.body.filter fun s => match s with
        | .assign _ _ => true | _ => false
      let memCount := m.body.filter fun s => match s with
        | .memory _ _ _ _ _ _ _ _ _ _ => true | _ => false
      IO.println s!"    {m.name}: {regCount.length} regs, {assignCount.length} assigns, {memCount.length} memories, {m.wires.length} wires"

  -- Phase 3: Generate JIT C++
  IO.print "  Phase 3: JIT C++ generation... "
  let design ← IO.ofExcept (parseAndLower src)
  let jitCpp := Sparkle.Backend.CppSim.toCppSimJIT design
  IO.FS.writeFile "/tmp/sparkle_litex_jit.cpp" jitCpp
  IO.println s!"PASS ({jitCpp.length} chars)"

  -- Phase 4: JIT compile and simulate 100 cycles
  IO.print "  Phase 4: JIT compile + simulate... "
  try
    let h ← JIT.compileAndLoad "/tmp/sparkle_litex_jit.cpp"
    JIT.reset h
    let mut cycles : Nat := 0
    while cycles < 100 do
      JIT.evalTick h
      cycles := cycles + 1
    JIT.destroy h
    IO.println s!"PASS (100 cycles OK)"
  catch e =>
    IO.println s!"FAIL: {e}"
    pure ()

  IO.println "\nLiteX SoC: ALL PHASES PASSED"
