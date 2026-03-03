/-
  Test: DRAM Interface
  Verifies pure DRAM model and simulation model.
-/

import LSpec
import IP.Video.H264.DRAMInterface

open Sparkle.IP.Video.H264.DRAMInterface

namespace Sparkle.Tests.Video.DRAMTest

def testPureModel : IO LSpec.TestSeq := do
  -- Read-after-write
  let s0 := DRAMState.empty
  let s1 := s0.write 0x100#24 0xDEADBEEF#32
  let v := s1.read 0x100#24

  -- Read different address returns 0
  let v2 := s1.read 0x200#24

  -- Write-write same address
  let s2 := s1.write 0x100#24 0xCAFEBABE#32
  let v3 := s2.read 0x100#24

  pure $ LSpec.group "Pure DRAM Model" (
    LSpec.test "read-after-write" (v == 0xDEADBEEF#32) ++
    LSpec.test "read unwritten returns 0" (v2 == 0#32) ++
    LSpec.test "write-write same addr" (v3 == 0xCAFEBABE#32) ++
    LSpec.test "read empty returns 0" (DRAMState.empty.read 0#24 == 0#32)
  )

def testSimModel : IO LSpec.TestSeq := do
  let sim ← DRAMSim.new

  -- Write and read back
  sim.write 0x000#24 0x12345678#32
  let v1 ← sim.read 0x000#24

  -- Read unwritten
  let v2 ← sim.read 0x001#24

  -- Bulk load and read
  sim.loadBlock 0x100#24 #[0xAA#32, 0xBB#32, 0xCC#32, 0xDD#32]
  let block ← sim.readBlock 0x100#24 4

  pure $ LSpec.group "DRAM Simulation Model" (
    LSpec.test "write/read" (v1 == 0x12345678#32) ++
    LSpec.test "read unwritten" (v2 == 0#32) ++
    LSpec.test "bulk load/read[0]" (block[0]! == 0xAA#32) ++
    LSpec.test "bulk load/read[3]" (block[3]! == 0xDD#32)
  )

def allTests : IO LSpec.TestSeq := do
  IO.println "--- DRAM Interface Tests ---"
  let t1 ← testPureModel
  let t2 ← testSimModel
  return LSpec.group "DRAM Interface" (t1 ++ t2)

end Sparkle.Tests.Video.DRAMTest
