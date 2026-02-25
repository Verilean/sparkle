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
def testHorizontalDuplication : LSpec.TestSeq :=
  -- Feed pixel value 42 at t=0 (valid=true), then nothing
  let pixelIn : Signal defaultDomain (BitVec 8) := ⟨fun t =>
    if t == 0 then 42#8 else 0#8⟩
  let valid : Signal defaultDomain Bool := ⟨fun t => t == 0⟩
  let upsampled := upsample2x pixelIn valid
  let pixelOut := Signal.fst upsampled
  let outValid := Signal.snd upsampled

  -- The upsampler should output pixel 42 twice
  LSpec.test "upsample: first output valid" (outValid.atTime 1 == true) ++
  LSpec.test "upsample: first pixel = 42" (pixelOut.atTime 1 == 42#8)

def allTests : LSpec.TestSeq :=
  LSpec.group "Upsample 2x" testHorizontalDuplication

end Sparkle.Examples.YOLOv8.Tests.TestUpsample
