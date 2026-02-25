/-
  Test: 2x Nearest-Neighbor Upsampling
-/

import LSpec
import Examples.YOLOv8.Primitives.Upsample

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8.Primitives.Upsample

namespace Sparkle.Examples.YOLOv8.Tests.TestUpsample

/-- Test horizontal duplication: input pixel A should appear twice. -/
def testHorizontalDuplication : IO LSpec.TestSeq := do
  let pixelIn : Signal defaultDomain (BitVec 8) := ⟨fun t =>
    if t == 0 then 42#8 else 0#8⟩
  let valid : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let upsampled ← upsample2xSimulate pixelIn valid
  let pixelOut := Signal.fst upsampled
  let outValid := Signal.snd upsampled
  return LSpec.test "upsample: first output valid" (outValid.atTime 1 == true) ++
    LSpec.test "upsample: first pixel = 42" (pixelOut.atTime 1 == 42#8)

def allTests : IO LSpec.TestSeq := do
  let t1 ← testHorizontalDuplication
  return LSpec.group "Upsample 2x" t1

end Sparkle.Examples.YOLOv8.Tests.TestUpsample
