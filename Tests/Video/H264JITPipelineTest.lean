/-
  H.264 JIT Pipeline End-to-End Tests

  Tests both decoder and encoder pipelines via JIT FFI:
    1. Decoder QP=20: load quantized levels + prediction → run FSM → verify output vs pure Lean
    2. Encoder QP=20: load original pixels + prediction → run FSM → verify output vs pure Lean
    3. Roundtrip QP=20: encoder output → decoder input → verify pixels in [0, 255]
    4. Roundtrip QP=10: encoder QP=10 → decoder QP=10 → cross-validate against parameterized ref

  Usage:
    lake exe h264-jit-pipeline-test
-/

import Sparkle.Core.JIT
import IP.Video.H264.Quant
import IP.Video.H264.DecoderSynth
import IP.Video.H264.EncoderSynth
import IP.Video.H264.CAVLCSynth
import IP.Video.H264.VLCTables
import IP.Video.H264.CAVLC

open Sparkle.Core.JIT
open Sparkle.IP.Video.H264.Quant
open Sparkle.IP.Video.H264.DecoderSynth
open Sparkle.IP.Video.H264.EncoderSynth
open Sparkle.IP.Video.H264.VLCTables
open Sparkle.IP.Video.H264.CAVLC
open Sparkle.IP.Video.H264.CAVLCSynth

/-- Resolve a wire index by name, throwing if not found -/
def resolveWire (handle : JITHandle) (name : String) : IO UInt32 := do
  match ← JIT.findWire handle name with
  | some idx => return idx
  | none => throw (IO.userError s!"JIT: wire '{name}' not found")

/-- Convert signed Int to unsigned 16-bit representation (2's complement) -/
def intToU16 (v : Int) : UInt32 :=
  if v < 0 then (65536 + v).toNat.toUInt32
  else v.toNat.toUInt32

/-- Convert unsigned 16-bit value back to signed Int -/
def u16ToInt (val : UInt32) : Int :=
  if val.toNat >= 32768 then (val.toNat : Int) - 65536
  else (val.toNat : Int)

-- ============================================================================
-- QP input helpers
-- ============================================================================

/-- Set decoder QP inputs (vscale0/1/2) on input ports 7/8/9 -/
def setDecoderQP (handle : JITHandle) (qp : Nat) : IO Unit := do
  let (vs0, vs1, vs2) := dequantScales qp
  JIT.setInput handle 7 vs0.toUInt64
  JIT.setInput handle 8 vs1.toUInt64
  JIT.setInput handle 9 vs2.toUInt64

/-- Set encoder QP inputs (quantMF0/1/2, quantF, quantShift) on input ports 7-11 -/
def setEncoderQP (handle : JITHandle) (qp : Nat) : IO Unit := do
  let (mf0, mf1, mf2, f, qbits) := quantParams qp
  JIT.setInput handle 7 mf0.toUInt64
  JIT.setInput handle 8 mf1.toUInt64
  JIT.setInput handle 9 mf2.toUInt64
  JIT.setInput handle 10 f.toUInt64
  JIT.setInput handle 11 qbits.toUInt64

-- ============================================================================
-- Test data
-- ============================================================================

def testQuantLevels : Array Int := #[10, -2, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0]
def testPredicted : Array Nat := Array.replicate 16 128
def testOriginal : Array Nat := #[129, 130, 131, 132, 133, 134, 135, 136,
                                    137, 138, 139, 140, 141, 142, 143, 144]

-- ============================================================================
-- Test 1: Decoder JIT (QP=20)
-- ============================================================================

def testDecoderJIT : IO Bool := do
  IO.println "\n=== Test 1: Decoder JIT Pipeline (QP=20) ==="

  -- Compile and load
  IO.println "  Compiling decoder_pipeline_jit.cpp..."
  let handle ← JIT.compileAndLoad ".lake/build/gen/h264/decoder_pipeline_jit.cpp"
  IO.println "  Loaded decoder JIT module"

  -- Resolve done wire
  let doneIdx ← resolveWire handle "_gen_done"
  IO.println s!"  Wire _gen_done = index {doneIdx}"

  -- Set QP=20 dequant parameters
  setDecoderQP handle 20

  -- Load quantized levels into memIdx=0 (_gen_inputLevel)
  for i in [:16] do
    let val := if h : i < testQuantLevels.size then testQuantLevels[i] else 0
    JIT.setMem handle 0 i.toUInt32 (intToU16 val)

  -- Load prediction (128) into memIdx=5 (_gen_predVal)
  for i in [:16] do
    let val := if h : i < testPredicted.size then testPredicted[i] else 0
    JIT.setMem handle 5 i.toUInt32 val.toUInt32

  -- Assert start for 1 cycle
  JIT.setInput handle 0 1
  JIT.eval handle
  JIT.tick handle
  JIT.setInput handle 0 0

  -- Run FSM until done (max 200 cycles)
  let mut doneCycle := 0
  for cycle in [:200] do
    JIT.eval handle
    let doneVal ← JIT.getWire handle doneIdx
    if doneVal != 0 then
      doneCycle := cycle + 1  -- +1 for the start cycle
      break
    JIT.tick handle

  if doneCycle == 0 then
    IO.eprintln "  FAIL: Decoder did not complete within 200 cycles"
    JIT.destroy handle
    return false

  IO.println s!"  Decoder completed in {doneCycle} cycles"

  -- Read output from memIdx=6 (_gen__outMem)
  let mut jitOutput : Array Nat := #[]
  for i in [:16] do
    let val ← JIT.getMem handle 6 i.toUInt32
    jitOutput := jitOutput.push val.toNat

  -- Compute reference
  let refOutput := decoderPipelineRef testQuantLevels testPredicted (qp := 20)

  IO.println s!"  JIT output: {jitOutput}"
  IO.println s!"  Ref output: {refOutput}"

  -- Compare
  let mut pass := true
  for i in [:16] do
    let jv := if h : i < jitOutput.size then jitOutput[i] else 0
    let rv := if h : i < refOutput.size then refOutput[i] else 0
    if jv != rv then
      IO.eprintln s!"  MISMATCH at index {i}: JIT={jv} ref={rv}"
      pass := false

  JIT.destroy handle

  if pass then
    IO.println "  PASS: Decoder JIT matches reference"
  else
    IO.eprintln "  FAIL: Decoder JIT output differs from reference"
  return pass

-- ============================================================================
-- Test 2: Encoder JIT (QP=20)
-- ============================================================================

def testEncoderJIT : IO Bool := do
  IO.println "\n=== Test 2: Encoder JIT Pipeline (QP=20) ==="

  -- Compile and load
  IO.println "  Compiling encoder_pipeline_jit.cpp..."
  let handle ← JIT.compileAndLoad ".lake/build/gen/h264/encoder_pipeline_jit.cpp"
  IO.println "  Loaded encoder JIT module"

  -- Resolve done wire
  let doneIdx ← resolveWire handle "_gen_done"
  IO.println s!"  Wire _gen_done = index {doneIdx}"

  -- Set QP=20 quant parameters
  setEncoderQP handle 20

  -- Load original pixels into memIdx=0 (_gen_origVal)
  for i in [:16] do
    let val := if h : i < testOriginal.size then testOriginal[i] else 0
    JIT.setMem handle 0 i.toUInt32 val.toUInt32

  -- Load prediction (128) into memIdx=1 (_gen_predVal)
  for i in [:16] do
    let val := if h : i < testPredicted.size then testPredicted[i] else 0
    JIT.setMem handle 1 i.toUInt32 val.toUInt32

  -- Assert start for 1 cycle
  JIT.setInput handle 0 1
  JIT.eval handle
  JIT.tick handle
  JIT.setInput handle 0 0

  -- Run FSM until done (max 200 cycles)
  let mut doneCycle := 0
  for cycle in [:200] do
    JIT.eval handle
    let doneVal ← JIT.getWire handle doneIdx
    if doneVal != 0 then
      doneCycle := cycle + 1
      break
    JIT.tick handle

  if doneCycle == 0 then
    IO.eprintln "  FAIL: Encoder did not complete within 200 cycles"
    JIT.destroy handle
    return false

  IO.println s!"  Encoder completed in {doneCycle} cycles"

  -- Read output from memIdx=6 (_gen__outMem)
  let mut jitOutput : Array Int := #[]
  for i in [:16] do
    let val ← JIT.getMem handle 6 i.toUInt32
    jitOutput := jitOutput.push (u16ToInt val)

  -- Compute reference
  let refOutput := encoderPipelineRef testOriginal testPredicted (qp := 20)

  IO.println s!"  JIT output: {jitOutput}"
  IO.println s!"  Ref output: {refOutput}"

  -- Compare
  let mut pass := true
  for i in [:16] do
    let jv := if h : i < jitOutput.size then jitOutput[i] else 0
    let rv := if h : i < refOutput.size then refOutput[i] else 0
    if jv != rv then
      IO.eprintln s!"  MISMATCH at index {i}: JIT={jv} ref={rv}"
      pass := false

  JIT.destroy handle

  if pass then
    IO.println "  PASS: Encoder JIT matches reference"
  else
    IO.eprintln "  FAIL: Encoder JIT output differs from reference"
  return pass

-- ============================================================================
-- Test 3: Encoder→Decoder roundtrip (QP=20)
-- ============================================================================

def testRoundtrip : IO Bool := do
  IO.println "\n=== Test 3: Encoder→Decoder Roundtrip (QP=20) ==="

  -- Step 1: Encode
  IO.println "  Running encoder..."
  let encHandle ← JIT.compileAndLoad ".lake/build/gen/h264/encoder_pipeline_jit.cpp"
  let encDoneIdx ← resolveWire encHandle "_gen_done"

  setEncoderQP encHandle 20

  for i in [:16] do
    let val := if h : i < testOriginal.size then testOriginal[i] else 0
    JIT.setMem encHandle 0 i.toUInt32 val.toUInt32
  for i in [:16] do
    let val := if h : i < testPredicted.size then testPredicted[i] else 0
    JIT.setMem encHandle 1 i.toUInt32 val.toUInt32

  JIT.setInput encHandle 0 1
  JIT.eval encHandle
  JIT.tick encHandle
  JIT.setInput encHandle 0 0

  for _ in [:200] do
    JIT.eval encHandle
    let doneVal ← JIT.getWire encHandle encDoneIdx
    if doneVal != 0 then break
    JIT.tick encHandle

  -- Read encoder output (quantized levels)
  let mut encodedLevels : Array Int := #[]
  for i in [:16] do
    let val ← JIT.getMem encHandle 6 i.toUInt32
    encodedLevels := encodedLevels.push (u16ToInt val)

  JIT.destroy encHandle
  IO.println s!"  Encoded levels: {encodedLevels}"

  -- Step 2: Decode using encoder output
  IO.println "  Running decoder with encoder output..."
  let decHandle ← JIT.compileAndLoad ".lake/build/gen/h264/decoder_pipeline_jit.cpp"
  let decDoneIdx ← resolveWire decHandle "_gen_done"

  setDecoderQP decHandle 20

  for i in [:16] do
    let val := if h : i < encodedLevels.size then encodedLevels[i] else 0
    JIT.setMem decHandle 0 i.toUInt32 (intToU16 val)
  for i in [:16] do
    let val := if h : i < testPredicted.size then testPredicted[i] else 0
    JIT.setMem decHandle 5 i.toUInt32 val.toUInt32

  JIT.setInput decHandle 0 1
  JIT.eval decHandle
  JIT.tick decHandle
  JIT.setInput decHandle 0 0

  for _ in [:200] do
    JIT.eval decHandle
    let doneVal ← JIT.getWire decHandle decDoneIdx
    if doneVal != 0 then break
    JIT.tick decHandle

  -- Read decoder output (reconstructed pixels)
  let mut decoded : Array Nat := #[]
  for i in [:16] do
    let val ← JIT.getMem decHandle 6 i.toUInt32
    decoded := decoded.push val.toNat

  JIT.destroy decHandle

  IO.println s!"  Original:    {testOriginal}"
  IO.println s!"  Decoded:     {decoded}"

  -- Verify all pixels are in [0, 255]
  let mut pass := true
  for i in [:16] do
    let v := if h : i < decoded.size then decoded[i] else 0
    if v > 255 then
      IO.eprintln s!"  FAIL: pixel {i} = {v} out of range [0, 255]"
      pass := false

  if pass then
    IO.println "  PASS: All decoded pixels in [0, 255]"
  else
    IO.eprintln "  FAIL: Some pixels out of range"
  return pass

-- ============================================================================
-- Test 4: Encoder→Decoder roundtrip at QP=10 (cross-validation)
-- ============================================================================

def testRoundtripQP10 : IO Bool := do
  IO.println "\n=== Test 4: Encoder→Decoder Roundtrip (QP=10) ==="
  let qp := 10

  -- Step 1: Encode at QP=10
  IO.println s!"  Running encoder at QP={qp}..."
  let encHandle ← JIT.compileAndLoad ".lake/build/gen/h264/encoder_pipeline_jit.cpp"
  let encDoneIdx ← resolveWire encHandle "_gen_done"

  setEncoderQP encHandle qp

  for i in [:16] do
    let val := if h : i < testOriginal.size then testOriginal[i] else 0
    JIT.setMem encHandle 0 i.toUInt32 val.toUInt32
  for i in [:16] do
    let val := if h : i < testPredicted.size then testPredicted[i] else 0
    JIT.setMem encHandle 1 i.toUInt32 val.toUInt32

  JIT.setInput encHandle 0 1
  JIT.eval encHandle
  JIT.tick encHandle
  JIT.setInput encHandle 0 0

  for _ in [:200] do
    JIT.eval encHandle
    let doneVal ← JIT.getWire encHandle encDoneIdx
    if doneVal != 0 then break
    JIT.tick encHandle

  -- Read encoder output (quantized levels)
  let mut jitEncodedLevels : Array Int := #[]
  for i in [:16] do
    let val ← JIT.getMem encHandle 6 i.toUInt32
    jitEncodedLevels := jitEncodedLevels.push (u16ToInt val)

  JIT.destroy encHandle

  -- Cross-validate encoder output against parameterized reference
  let refEncodedLevels := encoderPipelineRef testOriginal testPredicted (qp := qp)
  IO.println s!"  JIT encoded:  {jitEncodedLevels}"
  IO.println s!"  Ref encoded:  {refEncodedLevels}"

  let mut encPass := true
  for i in [:16] do
    let jv := if h : i < jitEncodedLevels.size then jitEncodedLevels[i] else 0
    let rv := if h : i < refEncodedLevels.size then refEncodedLevels[i] else 0
    if jv != rv then
      IO.eprintln s!"  ENCODER MISMATCH at index {i}: JIT={jv} ref={rv}"
      encPass := false

  if encPass then
    IO.println s!"  Encoder QP={qp} matches reference"
  else
    IO.eprintln s!"  FAIL: Encoder QP={qp} output differs from reference"

  -- Step 2: Decode at QP=10
  IO.println s!"  Running decoder at QP={qp} with encoder output..."
  let decHandle ← JIT.compileAndLoad ".lake/build/gen/h264/decoder_pipeline_jit.cpp"
  let decDoneIdx ← resolveWire decHandle "_gen_done"

  setDecoderQP decHandle qp

  for i in [:16] do
    let val := if h : i < jitEncodedLevels.size then jitEncodedLevels[i] else 0
    JIT.setMem decHandle 0 i.toUInt32 (intToU16 val)
  for i in [:16] do
    let val := if h : i < testPredicted.size then testPredicted[i] else 0
    JIT.setMem decHandle 5 i.toUInt32 val.toUInt32

  JIT.setInput decHandle 0 1
  JIT.eval decHandle
  JIT.tick decHandle
  JIT.setInput decHandle 0 0

  for _ in [:200] do
    JIT.eval decHandle
    let doneVal ← JIT.getWire decHandle decDoneIdx
    if doneVal != 0 then break
    JIT.tick decHandle

  -- Read decoder output (reconstructed pixels)
  let mut jitDecoded : Array Nat := #[]
  for i in [:16] do
    let val ← JIT.getMem decHandle 6 i.toUInt32
    jitDecoded := jitDecoded.push val.toNat

  JIT.destroy decHandle

  -- Cross-validate decoder output against parameterized reference
  let refDecoded := decoderPipelineRef jitEncodedLevels testPredicted (qp := qp)

  IO.println s!"  JIT decoded: {jitDecoded}"
  IO.println s!"  Ref decoded: {refDecoded}"

  let mut decPass := true
  for i in [:16] do
    let jv := if h : i < jitDecoded.size then jitDecoded[i] else 0
    let rv := if h : i < refDecoded.size then refDecoded[i] else 0
    if jv != rv then
      IO.eprintln s!"  DECODER MISMATCH at index {i}: JIT={jv} ref={rv}"
      decPass := false

  -- Also verify all pixels are in [0, 255]
  let mut rangePass := true
  for i in [:16] do
    let v := if h : i < jitDecoded.size then jitDecoded[i] else 0
    if v > 255 then
      IO.eprintln s!"  FAIL: pixel {i} = {v} out of range [0, 255]"
      rangePass := false

  let pass := encPass && decPass && rangePass
  if pass then
    IO.println s!"  PASS: QP={qp} roundtrip matches reference, pixels in [0, 255]"
  else
    IO.eprintln s!"  FAIL: QP={qp} roundtrip validation failed"
  return pass

-- ============================================================================
-- Test 5: CAVLC Synth JIT
-- ============================================================================

def testCAVLCSynthJIT : IO Bool := do
  IO.println "\n=== Test 5: CAVLC Synth JIT ==="

  -- Compile and load
  IO.println "  Compiling cavlc_synth_jit.cpp..."
  let handle ← JIT.compileAndLoad ".lake/build/gen/h264/cavlc_synth_jit.cpp"
  IO.println "  Loaded CAVLC synth JIT module"

  -- Resolve done wire
  let doneIdx ← resolveWire handle "_gen_done"
  IO.println s!"  Wire _gen_done = index {doneIdx}"

  -- Load VLC tables and data into correct JIT memory indices:
  --   memIdx 0 = _gen_zzData (zigzag table, 16 entries)
  --   memIdx 1 = _gen_coeffReadData (coefficients, 16 entries)
  --   memIdx 2 = _gen_ctTableData (coeff_token VLC, 128 entries)
  --   memIdx 3 = _gen_tzTableData (total_zeros VLC, 128 entries)
  --   memIdx 4 = _gen_rbTableData (run_before VLC, 64 entries)
  --   memIdx 5 = _gen_levelReadData (internal, written by FSM)
  --   memIdx 6 = _gen_posReadData (internal, written by FSM)
  IO.println "  Loading VLC tables..."

  -- Load zig-zag table into memIdx 0
  let zzTable := zigzagTable
  for i in [:zzTable.size] do
    if h : i < zzTable.size then
      JIT.setMem handle 0 i.toUInt32 zzTable[i]

  let ctTable := buildCoeffTokenTable
  for i in [:ctTable.size] do
    if h : i < ctTable.size then
      JIT.setMem handle 2 i.toUInt32 ctTable[i]

  let tzTable := buildTotalZerosTable
  for i in [:tzTable.size] do
    if h : i < tzTable.size then
      JIT.setMem handle 3 i.toUInt32 tzTable[i]

  let rbTable := buildRunBeforeTable
  for i in [:rbTable.size] do
    if h : i < rbTable.size then
      JIT.setMem handle 4 i.toUInt32 rbTable[i]

  -- Load test coefficients into memIdx 1
  let testCoeffs : Array Int := #[0, 3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  IO.println "  Loading coefficients into memory..."
  for i in [:16] do
    let val := if h : i < testCoeffs.size then testCoeffs[i] else 0
    JIT.setMem handle 1 i.toUInt32 (intToU16 val)

  -- Assert start for 1 cycle, nCTableSelect=0 (port 1)
  JIT.setInput handle 0 1  -- start
  JIT.setInput handle 1 0  -- nCTableSelect = 0
  JIT.eval handle
  JIT.tick handle
  JIT.setInput handle 0 0

  -- Run FSM until done (max 200 cycles)
  let mut doneCycle := 0
  for cycle in [:200] do
    JIT.eval handle
    let doneVal ← JIT.getWire handle doneIdx
    if doneVal != 0 then
      doneCycle := cycle + 1
      break
    JIT.tick handle

  if doneCycle == 0 then
    IO.eprintln "  FAIL: CAVLC synth did not complete within 200 cycles"
    JIT.destroy handle
    return false

  IO.println s!"  CAVLC synth completed in {doneCycle} cycles"

  -- Read output: bitstream data and bit length
  let bsIdx ← resolveWire handle "_gen_bitBuffer"
  let bpIdx ← resolveWire handle "_gen_bitPos"
  let bsData ← JIT.getWire handle bsIdx
  let bpData ← JIT.getWire handle bpIdx

  IO.println s!"  Bitstream: 0x{String.ofList (Nat.toDigits 16 bsData.toNat)}"
  IO.println s!"  Bit length: {bpData}"

  -- Compare with pure reference (nC=0)
  let (refBits, refLen) := cavlcEncodeFull testCoeffs
  IO.println s!"  Reference: 0x{String.ofList (Nat.toDigits 16 refBits.toNat)} ({refLen} bits)"

  let pass := bsData.toNat == refBits.toNat && bpData.toNat == refLen
  JIT.destroy handle

  if pass then
    IO.println "  PASS: CAVLC synth JIT matches reference"
  else
    IO.eprintln "  FAIL: CAVLC synth JIT output differs from reference"
  return pass

-- ============================================================================
-- Main
-- ============================================================================

def main : IO UInt32 := do
  IO.println "H.264 JIT Pipeline Tests"
  IO.println "========================"

  let r1 ← testDecoderJIT
  let r2 ← testEncoderJIT
  let r3 ← testRoundtrip
  let r4 ← testRoundtripQP10
  let r5 ← testCAVLCSynthJIT

  IO.println "\n========================"
  if r1 && r2 && r3 && r4 && r5 then
    IO.println "ALL TESTS PASSED"
    return 0
  else
    IO.eprintln "SOME TESTS FAILED"
    return 1
