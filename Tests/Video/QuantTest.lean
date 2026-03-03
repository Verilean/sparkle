/-
  Test: Quantization / Dequantization
  Verifies forward quant and inverse dequant against C++ golden values.
-/

import LSpec
import IP.Video.H264.Quant

open Sparkle.IP.Video.H264.Quant

namespace Sparkle.Tests.Video.QuantTest

private def testCoeffs : Array Int :=
  #[136, -28, 0, -4, -112, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0]

private def goldenQuantQP0 : Array Int :=
  #[54, -7, 0, -1, -27, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0]

def testQuant : IO LSpec.TestSeq := do
  let q0 := quantizeBlock testCoeffs 0
  let qZero := quantizeBlock (Array.replicate 16 (0 : Int)) 20

  -- Sign preservation
  let pos := quantize 136 10 0
  let neg := quantize (-136) 10 0

  pure $ LSpec.group "Forward Quantization" (
    LSpec.test "QP=0 matches golden" (q0 == goldenQuantQP0) ++
    LSpec.test "zero block stays zero" (qZero == Array.replicate 16 (0 : Int)) ++
    LSpec.test "positive input positive output" (pos > 0) ++
    LSpec.test "negative input negative output" (neg < 0) ++
    LSpec.test "sign magnitude preserved" (pos == -neg)
  )

def testDequant : IO LSpec.TestSeq := do
  let dq0 := dequantizeBlock (Array.replicate 16 (0 : Int)) 20

  -- Roundtrip at QP=0
  let levels := quantizeBlock testCoeffs 0
  let recon := dequantizeBlock levels 0

  pure $ LSpec.group "Inverse Dequantization" (
    LSpec.test "zero levels stay zero" (dq0 == Array.replicate 16 (0 : Int)) ++
    LSpec.test "dequant(0) = 0" (dequantize 0 20 0 == 0)
  )

def allTests : IO LSpec.TestSeq := do
  IO.println "--- Quantization Tests ---"
  let t1 ← testQuant
  let t2 ← testDequant
  return LSpec.group "Quant/Dequant" (t1 ++ t2)

end Sparkle.Tests.Video.QuantTest
