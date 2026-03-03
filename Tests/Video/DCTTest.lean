/-
  Test: DCT / IDCT
  Verifies forward and inverse DCT against C++ golden values.
-/

import LSpec
import IP.Video.H264.DCT

open Sparkle.IP.Video.H264.DCT

namespace Sparkle.Tests.Video.DCTTest

private def testBlock1 : Block4x4 :=
  #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

private def goldenDCT1 : Block4x4 :=
  #[136, -28, 0, -4, -112, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0]

private def testBlock2 : Block4x4 :=
  #[3, -1, 0, 2, -2, 4, -3, 1, 0, 1, -1, 0, 1, -2, 3, -4]

private def goldenDCT2 : Block4x4 :=
  #[2, 9, 0, -3, 12, -9, 18, -37, 2, 3, 4, 39, 6, -2, 14, 14]

def testForwardDCT : IO LSpec.TestSeq := do
  let dct1 := forwardDCT testBlock1
  let dct2 := forwardDCT testBlock2
  let dct3 := forwardDCT (Array.replicate 16 (0 : Int))

  pure $ LSpec.group "Forward DCT" (
    LSpec.test "block1 matches golden" (dct1 == goldenDCT1) ++
    LSpec.test "block2 matches golden" (dct2 == goldenDCT2) ++
    LSpec.test "zero block produces zeros" (dct3 == Array.replicate 16 (0 : Int))
  )

def testInverseDCT : IO LSpec.TestSeq := do
  let idct0 := inverseDCT (Array.replicate 16 (0 : Int))

  -- Roundtrip: compute max error
  let rt2 := inverseDCT (forwardDCT testBlock2)
  let mut maxErr : Nat := 0
  for i in [:16] do
    if h1 : i < rt2.size then
      if h2 : i < testBlock2.size then
        let err := (rt2[i] - testBlock2[i]).natAbs
        if err > maxErr then maxErr := err

  pure $ LSpec.group "Inverse DCT" (
    LSpec.test "zero block roundtrip" (idct0 == Array.replicate 16 (0 : Int)) ++
    LSpec.test "block2 roundtrip error ≤ 5" (maxErr <= 5)
  )

def allTests : IO LSpec.TestSeq := do
  IO.println "--- DCT/IDCT Tests ---"
  let t1 ← testForwardDCT
  let t2 ← testInverseDCT
  return LSpec.group "DCT/IDCT" (t1 ++ t2)

end Sparkle.Tests.Video.DCTTest
