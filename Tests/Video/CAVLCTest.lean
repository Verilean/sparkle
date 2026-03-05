/-
  Test: CAVLC Encoder
  Verifies CAVLC encoding against C++ golden reference output.

  Test block (raster order): {0, 3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  Expected output: 0x1E6E8000 (17 bits)
-/

import LSpec
import IP.Video.H264.CAVLC

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Video.H264.CAVLC

namespace Sparkle.Tests.Video.CAVLCTest

-- Golden reference values from C++ generate_cavlc_golden
private def goldenBitstream64 : BitVec 64 := 0x1E6E800000000000#64
private def goldenBitstream32 : BitVec 32 := 0x1E6E8000#32
private def goldenBitLen    : Nat := 17

/-- Test the pure CAVLC encoding function against golden reference -/
def testPureEncoding : IO LSpec.TestSeq := do
  let coeffs : Array Int := #[0, 3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let (bitstream, bitLen) := cavlcEncodeFull coeffs
  IO.println s!"  Pure encoding: 0x{String.ofList (Nat.toDigits 16 bitstream.toNat)} ({bitLen} bits)"
  IO.println s!"  Golden:        0x{String.ofList (Nat.toDigits 16 goldenBitstream64.toNat)} ({goldenBitLen} bits)"
  pure $ LSpec.group "Pure CAVLC Encoding" (
    LSpec.test "bitstream matches golden" (bitstream == goldenBitstream64) ++
    LSpec.test "bit length matches golden" (bitLen == goldenBitLen)
  )

/-- Test the Signal-level CAVLC encoder FSM against golden reference -/
def testFSMEncoding : IO LSpec.TestSeq := do
  -- Test block coefficients in raster order
  let coeffData : Array (BitVec 16) := #[
    0#16,      -- raster[0] = 0
    3#16,      -- raster[1] = 3
    0xFFFF#16, -- raster[2] = -1 (two's complement 16-bit)
    0#16,      -- raster[3] = 0
    0#16,      -- raster[4] = 0
    0xFFFF#16, -- raster[5] = -1
    0#16, 0#16, 0#16, 0#16, 0#16, 0#16, 0#16, 0#16, 0#16, 0#16
  ]

  -- Write coefficients into memory during cycles 0-15
  let writeEn : Signal defaultDomain Bool := ⟨fun t => t < 16⟩
  let writeAddr : Signal defaultDomain (BitVec 4) := ⟨fun t =>
    BitVec.ofNat 4 t⟩
  let writeData : Signal defaultDomain (BitVec 16) := ⟨fun t =>
    if h : t < coeffData.size then coeffData[t] else 0#16⟩

  -- Assert start at cycle 16 (after all coefficients written)
  let start : Signal defaultDomain Bool := ⟨fun t => t == 16⟩

  -- Run simulation
  let output ← cavlcEncoderSimulate start writeEn writeAddr writeData

  -- Extract outputs
  let validOut := output.map (·.1)
  let bitstreamData := output.map (·.2.1)
  let bitLen := output.map (·.2.2.1)
  let done := output.map (·.2.2.2)

  -- FSM timeline:
  -- t=0-15: write coefficients to memory
  -- t=16: start=1, FSM transitions IDLE→SCAN
  -- t=17: SCAN begins (scanIdx=0, issue first read)
  -- t=17-33: SCAN (17 cycles: scanIdx 0-16, processing positions 0-15)
  -- t=34: ENCODE (compute bitstream)
  -- t=35: OUTPUT (validOut=1)
  -- t=36: DONE (done=1)

  IO.println s!"  FSM encoding:"
  -- Sample output at key cycles
  for t in [33, 34, 35, 36, 37] do
    let v := validOut.atTime t
    let bs := bitstreamData.atTime t
    let bl := bitLen.atTime t
    let d := done.atTime t
    IO.println s!"    t={t}: valid={v} bitstream=0x{String.ofList (Nat.toDigits 16 bs.toNat)} bitLen={bl.toNat} done={d}"

  -- Check the OUTPUT cycle (when validOut is true)
  -- Find the first cycle where validOut is true
  let mut outputCycle := 0
  for t in [30:45] do
    if validOut.atTime t then
      outputCycle := t
      break

  IO.println s!"  Output at cycle {outputCycle}"
  let bsAtOutput := bitstreamData.atTime outputCycle
  let blAtOutput := bitLen.atTime outputCycle

  pure $ LSpec.group "FSM CAVLC Encoding" (
    LSpec.test "validOut asserts" (outputCycle > 0) ++
    LSpec.test "bitstream matches golden" (bsAtOutput == goldenBitstream32) ++
    LSpec.test "bit length matches golden" (blAtOutput == BitVec.ofNat 6 goldenBitLen)
  )

/-- Test that done signal asserts after encoding -/
def testDoneSignal : IO LSpec.TestSeq := do
  let coeffData : Array (BitVec 16) := #[
    0#16, 3#16, 0xFFFF#16, 0#16, 0#16, 0xFFFF#16,
    0#16, 0#16, 0#16, 0#16, 0#16, 0#16, 0#16, 0#16, 0#16, 0#16
  ]

  let writeEn : Signal defaultDomain Bool := ⟨fun t => t < 16⟩
  let writeAddr : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 t⟩
  let writeData : Signal defaultDomain (BitVec 16) := ⟨fun t =>
    if h : t < coeffData.size then coeffData[t] else 0#16⟩
  let start : Signal defaultDomain Bool := ⟨fun t => t == 16⟩

  let output ← cavlcEncoderSimulate start writeEn writeAddr writeData
  let done := output.map (·.2.2.2)

  -- Find first cycle where done is true
  let mut doneCycle := 0
  for t in [30:50] do
    if done.atTime t then
      doneCycle := t
      break

  IO.println s!"  Done signal at cycle {doneCycle}"

  pure $ LSpec.group "CAVLC Done Signal" (
    LSpec.test "done not at t=0" (done.atTime 0 == false) ++
    LSpec.test "done asserts eventually" (doneCycle > 0)
  )

def allTests : IO LSpec.TestSeq := do
  IO.println "--- CAVLC Encoder Tests ---"
  let t1 ← testPureEncoding
  let t2 ← testFSMEncoding
  let t3 ← testDoneSignal
  return LSpec.group "CAVLC Encoder" (t1 ++ t2 ++ t3)

end Sparkle.Tests.Video.CAVLCTest
