import Sparkle.Core.JIT
import Tools.SVParser.Lower
import Sparkle.Backend.CppSim
open Sparkle.Core.JIT
open Tools.SVParser.Lower
def hexToNat (s : String) : Nat :=
  s.foldl (fun acc c =>
    let d := if c.isDigit then c.toNat - '0'.toNat
             else if c >= 'a' && c <= 'f' then c.toNat - 'a'.toNat + 10
             else if c >= 'A' && c <= 'F' then c.toNat - 'A'.toNat + 10
             else 0
    acc * 16 + d) 0

def runFirmware (h : JITHandle) (fwPath : String) (maxCycles : Nat := 200000)
    : IO (List UInt64) := do
  JIT.reset h
  let fwContents ← IO.FS.readFile fwPath
  let mut addr : UInt32 := 0
  for line in fwContents.splitOn "\n" do
    let trimmed := String.ofList (line.toList.filter fun c =>
      c != ' ' && c != '\t' && c != '\r' && c != '\n')
    if trimmed.startsWith "@" then
      addr := UInt32.ofNat (hexToNat (String.ofList (trimmed.toList.drop 1)))
    else if trimmed.length >= 8 then
      JIT.setMem h 0 (addr / 4) (UInt32.ofNat (hexToNat trimmed))
      addr := addr + 4
  JIT.setInput h 0 0
  for _ in [:10] do JIT.evalTick h
  JIT.setInput h 0 1
  let mut uartOutput : List UInt64 := []
  let mut done := false
  for _ in [:maxCycles] do
    if !done then
      JIT.evalTick h
      let uartValid ← JIT.getOutput h 1
      if uartValid != 0 then
        let uartData ← JIT.getOutput h 0
        uartOutput := uartOutput ++ [uartData]
        if uartData == 0xCAFE0000 || uartData == 0xDEADDEAD then done := true
  return uartOutput

def main : IO Unit := do
  let soc ← IO.FS.readFile "/tmp/picorv32_soc_m.v"
  let cpu ← IO.FS.readFile "/tmp/picorv32.v"
  let design ← IO.ofExcept (parseAndLowerFlat (soc ++ "\n" ++ cpu))
  IO.FS.writeFile "/tmp/picorv32_mext_jit.cpp" (Sparkle.Backend.CppSim.toCppSimJIT design)
  let h ← JIT.compileAndLoad "/tmp/picorv32_mext_jit.cpp"

  -- Test 1: RV32I firmware on M-ext SoC
  IO.print "  RV32I on M-ext SoC... "
  let rv32iOut ← runFirmware h "/tmp/firmware_rv32i.hex"
  let rv32iPass := rv32iOut.any (· == 0xCAFE0000)
  IO.println s!"{if rv32iPass then "PASS" else "FAIL"} ({rv32iOut.length} words)"

  -- Test 2: RV32IM firmware (MUL/DIV/REM) on M-ext SoC
  let mextFwExists ← System.FilePath.pathExists "/tmp/firmware_rv32im.hex"
  if mextFwExists then
    IO.print "  RV32IM (MUL/DIV) on M-ext SoC... "
    let mextOut ← runFirmware h "/tmp/firmware_rv32im.hex"
    let mextPass := mextOut.any (· == 0xCAFE0000)
    IO.println s!"{if mextPass then "PASS" else "FAIL"} ({mextOut.length} words)"
    for v in mextOut do
      IO.println s!"    0x{String.ofList (Nat.toDigits 16 v.toNat)}"
  else
    IO.println "  RV32IM test: SKIP (firmware_rv32im.hex not found)"

  -- Test 3: Simple MUL test (runtime mul only)
  let mulTestExists ← System.FilePath.pathExists "/tmp/firmware_multest.hex"
  if mulTestExists then
    IO.print "  Simple MUL test... "
    let mulOut ← runFirmware h "/tmp/firmware_multest.hex"
    let mulPass := mulOut.any (· == 0xCAFE0000)
    IO.println s!"{if mulPass then "PASS" else "FAIL"} ({mulOut.length} words)"
    for v in mulOut do
      IO.println s!"    0x{String.ofList (Nat.toDigits 16 v.toNat)}"
  else
    IO.println "  Simple MUL test: SKIP"

  -- Test 4: Store/Load test with wstrb tracing
  let slTestExists ← System.FilePath.pathExists "/tmp/firmware_storeload.hex"
  if slTestExists then
    IO.print "  Store/Load test... "
    JIT.reset h
    let fwContents ← IO.FS.readFile "/tmp/firmware_storeload.hex"
    let mut addr : UInt32 := 0
    for line in fwContents.splitOn "\n" do
      let trimmed := String.ofList (line.toList.filter fun c =>
        c != ' ' && c != '\t' && c != '\r' && c != '\n')
      if trimmed.startsWith "@" then
        addr := UInt32.ofNat (hexToNat (String.ofList (trimmed.toList.drop 1)))
      else if trimmed.length >= 8 then
        JIT.setMem h 0 (addr / 4) (UInt32.ofNat (hexToNat trimmed))
        addr := addr + 4
    JIT.setInput h 0 0
    for _ in [:10] do JIT.evalTick h
    JIT.setInput h 0 1
    let mut uartOutput : List UInt64 := []
    let mut done := false
    for i in [:10000] do
      if !done then
        JIT.evalTick h
        let uartValid ← JIT.getOutput h 1
        if uartValid != 0 then
          let uartData ← JIT.getOutput h 0
          uartOutput := uartOutput ++ [uartData]
          if uartData == 0xCAFE0000 || uartData == 0xDEADDEAD then done := true
        -- Trace wstrb for first few SW instructions
        if i > 30 && i < 300 then
          let wstrb ← JIT.getWire h 4  -- _gen_mem_wstrb
          let wdata ← JIT.getWire h 3  -- _gen_mem_wdata
          let maddr ← JIT.getWire h 2   -- _gen_mem_addr
          if wstrb != 0 then
            IO.println s!"    cycle {i}: wstrb=0x{String.ofList (Nat.toDigits 16 wstrb.toNat)} wdata=0x{String.ofList (Nat.toDigits 16 wdata.toNat)} addr=0x{String.ofList (Nat.toDigits 16 maddr.toNat)}"
    let slPass := uartOutput.any (· == 0xCAFE0000)
    IO.println s!"{if slPass then "PASS" else "FAIL"} ({uartOutput.length} words)"
    for v in uartOutput do
      IO.println s!"    0x{String.ofList (Nat.toDigits 16 v.toNat)}"
  else
    IO.println "  Store/Load test: SKIP"

  JIT.destroy h
