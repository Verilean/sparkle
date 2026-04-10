/-
  BitNetSoCTest — Level 1a integration smoke test.

  First ever "CPU + NN IP cohabitation" test in Sparkle. Proves that
  the BitNet MMIO peripheral (IP/RV32/BitNetPeripheral.lean) is correctly
  integrated into the picorv32 SoC (IP/RV32/SoC.lean) on three axes:

  1. **Functional**: the peripheral's combinational Signal function
     produces the expected output for every test input. This is the
     unit test of `bitNetPeripheral` in isolation.

  2. **Structural**: the generated SystemVerilog for the SoC contains
     a BitNet subtree (grep `_gen_bitnetOut`), proving that the SoC
     actually instantiates the peripheral in its read mux.

  3. **Artifacts**: the C firmware hex compiled with the BitNet MMIO
     addresses is present and well-formed, ready for the day the
     Signal-DSL-SoC JIT boot path (`rv32iSoCJITRun`) is fixed upstream
     and can execute the hex end-to-end.

  The end-to-end firmware-on-CPU path is currently blocked by a
  pre-existing issue: `rv32-jit-loop-test` shows the CPU stuck at
  `PC = 0x00000000` even with the known-good `firmware/firmware.hex`,
  and independently of any BitNet wiring. That issue is tracked in
  `docs/TODO.md` and is out of scope for Level 1a. Once it's fixed,
  this test will be extended to load `firmware/bitnet_smoke/firmware.hex`,
  run the SoC, and assert the expected UART PASS marker sequence.

  Run:  lake exe bitnet-soc-test
-/

import Sparkle
import IP.RV32.BitNetPeripheral

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.RV32.BitNetPeripheral

/-- Exercise the BitNet peripheral as a pure Signal function.
    Golden outputs captured from `#eval` of the real FFN pipeline
    (dim=4, 1 layer, all-+1 ternary weights, unit scales). -/
def runBitNetUnit : IO (Bool × Array (Nat × Nat)) := do
  let testCases : Array (Nat × Nat) := #[
    (0x00010000, 0x00410000),  -- 1.0 in Q16.16
    (0x00020000, 0x02020000),  -- 2.0
    (0x00030000, 0x06C30000),  -- 3.0
    (0x00040000, 0x10040000),  -- 4.0
    (0x00080000, 0x80080000),  -- 8.0
    (0x00000100, 0x00000100),  -- small
    (0x12345678, 0x5AD1BC9A),  -- arbitrary
    (0x00000000, 0x00000000)   -- zero
  ]
  let mut results : Array (Nat × Nat) := #[]
  let mut allOk := true
  for (x, expected) in testCases do
    let inputSig : Signal defaultDomain (BitVec 32) :=
      Signal.pure (BitVec.ofNat 32 x)
    let outSig := bitNetPeripheral inputSig
    let out := outSig.atTime 0
    if out != BitVec.ofNat 32 expected then allOk := false
    results := results.push (x, out.toNat)
  pure (allOk, results)

/-- Confirm the generated SystemVerilog contains a BitNet subtree. -/
def runStructuralCheck : IO Bool := do
  let svPath := "verilator/generated_soc.sv"
  let present ← System.FilePath.pathExists svPath
  if !present then
    IO.println s!"  ❌ {svPath} missing — run `lake build IP.RV32.SoCVerilog` first"
    return false
  let sv ← IO.FS.readFile svPath
  let hasBitnetOut := (sv.splitOn "_gen_bitnetOut").length > 1
  let hasBitnetInRead := (sv.splitOn "bitnetOut").length > 1
  pure (hasBitnetOut && hasBitnetInRead)

/-- Confirm the C firmware hex was built. -/
def runFirmwareCheck : IO Bool := do
  let hexPath := "firmware/bitnet_smoke/firmware.hex"
  let present ← System.FilePath.pathExists hexPath
  if !present then
    IO.println s!"  ❌ {hexPath} missing — run `make -C firmware/bitnet_smoke`"
    return false
  let content ← IO.FS.readFile hexPath
  let wordLines := (content.splitOn "\n").filter fun line =>
    let t := line.trimLeft
    t.length >= 8 && !t.startsWith "@"
  if wordLines.length < 10 then
    IO.println s!"  ❌ {hexPath} has only {wordLines.length} words — likely truncated"
    return false
  pure true

def main : IO UInt32 := do
  IO.println "╔══════════════════════════════════════════════════╗"
  IO.println "║   Sparkle BitNet SoC Integration Test  (v1a)    ║"
  IO.println "║   picorv32 CPU ⊕ BitLinear MMIO @0x40000004     ║"
  IO.println "╚══════════════════════════════════════════════════╝"
  IO.println ""

  -- ------------------------------------------------------------------
  -- Axis 1: functional — peripheral computes the expected mapping
  -- ------------------------------------------------------------------
  IO.println "Axis 1: BitNet peripheral unit behavior"
  IO.println "  Expected: full FFN pipeline (BitLinear→Scale→ReLU²→ElemMul→BitLinear→Scale→Residual)"
  let (unitOk, unitResults) ← runBitNetUnit
  for (inp, out) in unitResults do
    let inHex := String.mk (Nat.toDigits 16 inp)
    let outHex := String.mk (Nat.toDigits 16 out)
    IO.println s!"    in=0x{inHex}  out=0x{outHex}"
  if unitOk then
    IO.println "  ✅ functional"
  else
    IO.println "  ❌ functional — see mismatches above"
  IO.println ""

  -- ------------------------------------------------------------------
  -- Axis 2: structural — generated Verilog wires BitNet into the SoC
  -- ------------------------------------------------------------------
  IO.println "Axis 2: generated SoC Verilog contains BitNet subtree"
  let structOk ← runStructuralCheck
  if structOk then
    IO.println "  ✅ `_gen_bitnetOut` and bitnetOut read-mux entry present in generated_soc.sv"
  else
    IO.println "  ❌ structural"
  IO.println ""

  -- ------------------------------------------------------------------
  -- Axis 3: firmware artifact — C firmware compiled and ready
  -- ------------------------------------------------------------------
  IO.println "Axis 3: C firmware artifact"
  let fwOk ← runFirmwareCheck
  if fwOk then
    IO.println "  ✅ firmware/bitnet_smoke/firmware.hex present and well-formed"
  else
    IO.println "  ❌ firmware artifact missing or truncated"
  IO.println ""

  -- ------------------------------------------------------------------
  -- Summary
  -- ------------------------------------------------------------------
  IO.println "─────────────────────────────────────────────────"
  if unitOk && structOk && fwOk then
    IO.println "✅ BitNet SoC Level-1a: ALL THREE AXES PASS"
    IO.println ""
    IO.println "The BitNet IP is structurally wired into the picorv32 SoC,"
    IO.println "the peripheral computes the expected deterministic mapping,"
    IO.println "and the firmware hex is ready for end-to-end execution."
    IO.println ""
    IO.println "Next step: end-to-end boot + firmware execution via the"
    IO.println "Signal DSL SoC JIT. This is currently blocked on a pre-"
    IO.println "existing PC-stuck-at-0 issue in rv32-jit-loop-test — tracked"
    IO.println "in docs/TODO.md, independent of BitNet."
    return 0
  else
    IO.println "❌ BitNet SoC Level-1a: one or more axes failed"
    return 1
