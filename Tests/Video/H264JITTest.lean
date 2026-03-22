/-
  H.264 JIT End-to-End Test

  Tests the quant/dequant roundtrip module via JIT compilation:
  1. Compiles the generated CppSim JIT wrapper to a shared library
  2. Loads test coefficients into input memory via JIT.setMem
  3. Runs the FSM (assert start → process 16 coefficients → done)
  4. Reads output memory via JIT.getMem
  5. Compares results with pure Lean reference function

  Usage:
    lake exe h264-jit-test
-/

import Sparkle.Core.JIT
import IP.Video.H264.QuantRoundtripSynth

open Sparkle.Core.JIT
open Sparkle.IP.Video.H264.QuantRoundtripSynth

/-- Convert signed Int to 16-bit 2's complement (as UInt32 for JIT.setMem) -/
def intToU16 (v : Int) : UInt32 :=
  if v >= 0 then v.toNat.toUInt32
  else (65536 + v).toNat.toUInt32

/-- Convert 16-bit 2's complement UInt32 back to signed Int -/
def u16ToInt (v : UInt32) : Int :=
  let n := v.toNat % 65536
  if n >= 32768 then (n : Int) - 65536 else (n : Int)

/-- Resolve a wire index by name, throwing if not found -/
def resolveWire (handle : JITHandle) (name : String) : IO UInt32 := do
  match ← JIT.findWire handle name with
  | some idx => return idx
  | none => throw (IO.userError s!"JIT: wire '{name}' not found")

/-- Run FSM: assert start, wait for done.
    Returns true if done was seen within maxCycles. -/
def runFSM (handle : JITHandle) (doneIdx : UInt32) (maxCycles : Nat := 25) : IO Bool := do
  -- Assert start for one cycle
  JIT.setInput handle 0 1  -- start = true
  JIT.eval handle
  JIT.tick handle

  -- Deassert start
  JIT.setInput handle 0 0  -- start = false

  -- Run until done or timeout
  for _ in [:maxCycles] do
    JIT.eval handle
    let doneVal ← JIT.getWire handle doneIdx
    if doneVal == 1 then return true
    JIT.tick handle

  return false

/-- Test: all-zero coefficients should give all-zero output -/
def testZeroBlock (handle : JITHandle) (doneIdx : UInt32) : IO Bool := do
  IO.println "  Test 1: Zero block..."

  JIT.reset handle

  -- Load 16 zeros into input memory (mem index 0)
  for i in [:16] do
    JIT.setMem handle 0 i.toUInt32 0

  let done ← runFSM handle doneIdx
  if !done then
    IO.println "    FAIL: FSM not done"
    return false

  -- Read output memory and verify all zeros
  let mut pass := true
  for i in [:16] do
    let val ← JIT.getMem handle 1 i.toUInt32
    if val != 0 then
      IO.println s!"    FAIL: output[{i}] = {val}, expected 0"
      pass := false

  if pass then IO.println "    PASS: all zeros"
  return pass

/-- Test: known DCT coefficients through quant/dequant roundtrip -/
def testDCTCoeffs (handle : JITHandle) (doneIdx : UInt32) : IO Bool := do
  IO.println "  Test 2: DCT coefficients..."

  -- Test coefficients (from forward DCT of sequential block 1..16)
  let testCoeffs : Array Int := #[136, -28, 0, -4, -112, 0, 0, 0,
                                    0, 0, 0, 0, -16, 0, 0, 0]

  JIT.reset handle

  -- Load coefficients into input memory (mem index 0)
  for i in [:16] do
    let coeff := if h : i < testCoeffs.size then testCoeffs[i] else 0
    JIT.setMem handle 0 i.toUInt32 (intToU16 coeff)

  let done ← runFSM handle doneIdx
  if !done then
    IO.println "    FAIL: FSM not done"
    return false

  -- Read output memory and compare with pure Lean reference
  let mut pass := true
  let mut maxErr : Nat := 0
  for i in [:16] do
    let jitVal ← JIT.getMem handle 1 i.toUInt32
    let jitInt := u16ToInt jitVal
    let coeff := if h : i < testCoeffs.size then testCoeffs[i] else 0
    let expected := quantDequantRef coeff
    let err := (jitInt - expected).natAbs
    if err > maxErr then maxErr := err
    if jitInt != expected then
      IO.println s!"    coeff[{i}]: input={coeff}, JIT={jitInt}, expected={expected}, err={err}"
      pass := false

  if pass then
    IO.println s!"    PASS: all 16 coefficients match (max error = {maxErr})"
  else
    IO.println s!"    FAIL: max error = {maxErr}"

  return pass

/-- Test: single large positive coefficient -/
def testSingleCoeff (handle : JITHandle) (doneIdx : UInt32) : IO Bool := do
  IO.println "  Test 3: Single large coefficient..."

  JIT.reset handle

  -- Load: only position 0 = 200, rest = 0
  JIT.setMem handle 0 0 200
  for i in [1:16] do
    JIT.setMem handle 0 i.toUInt32 0

  let done ← runFSM handle doneIdx
  if !done then
    IO.println "    FAIL: FSM not done"
    return false

  let jitVal ← JIT.getMem handle 1 0
  let jitInt := u16ToInt jitVal
  let expected := quantDequantRef 200

  IO.println s!"    input=200, JIT={jitInt}, expected={expected}"
  if jitInt == expected then
    IO.println "    PASS"
    return true
  else
    IO.println s!"    FAIL: mismatch"
    return false

/-- Test: negative coefficients -/
def testNegativeCoeffs (handle : JITHandle) (doneIdx : UInt32) : IO Bool := do
  IO.println "  Test 4: Negative coefficients..."

  JIT.reset handle

  let testCoeffs : Array Int := #[-50, -100, -200, -500, 0, 0, 0, 0,
                                     0, 0, 0, 0, 0, 0, 0, 0]

  for i in [:16] do
    let coeff := if h : i < testCoeffs.size then testCoeffs[i] else 0
    JIT.setMem handle 0 i.toUInt32 (intToU16 coeff)

  let done ← runFSM handle doneIdx
  if !done then
    IO.println "    FAIL: FSM not done"
    return false

  let mut pass := true
  for i in [:4] do
    let jitVal ← JIT.getMem handle 1 i.toUInt32
    let jitInt := u16ToInt jitVal
    let coeff := if h : i < testCoeffs.size then testCoeffs[i] else 0
    let expected := quantDequantRef coeff
    IO.println s!"    coeff[{i}]: input={coeff}, JIT={jitInt}, expected={expected}"
    if jitInt != expected then
      pass := false

  if pass then IO.println "    PASS"
  else IO.println "    FAIL"
  return pass

def main : IO UInt32 := do
  let jitPath := ".lake/build/gen/h264/quant_roundtrip_jit.cpp"

  IO.println "=== H.264 JIT End-to-End Test ==="
  IO.println s!"JIT: Compiling {jitPath}..."

  let handle ← JIT.compileAndLoad jitPath
  IO.println "JIT: Loaded shared library"

  -- Resolve wire indices
  let doneIdx ← resolveWire handle "_gen_done"
  let numWires ← JIT.numWires handle
  IO.println s!"JIT: 4 inputs, {numWires} wires, 2 memories (done wire={doneIdx})"

  -- Run all tests
  let mut allPass := true

  let pass1 ← testZeroBlock handle doneIdx
  if !pass1 then allPass := false

  let pass2 ← testDCTCoeffs handle doneIdx
  if !pass2 then allPass := false

  let pass3 ← testSingleCoeff handle doneIdx
  if !pass3 then allPass := false

  let pass4 ← testNegativeCoeffs handle doneIdx
  if !pass4 then allPass := false

  JIT.destroy handle

  IO.println ""
  if allPass then
    IO.println "*** ALL H.264 JIT TESTS PASSED ***"
    return 0
  else
    IO.println "*** SOME H.264 JIT TESTS FAILED ***"
    return 1
