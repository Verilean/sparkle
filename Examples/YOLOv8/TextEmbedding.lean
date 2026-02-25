/-
  Text Embedding — Signal DSL

  Pre-computed CLIP text embeddings stored as INT8 in ROM.
  Classification = dot product between visual features and text embeddings.

  For YOLOv8-WorldV2, the text encoder runs offline in Python.
  The embeddings are quantized to INT8 and stored in Signal.memoryWithInit.
  At runtime, we compute: score[cls] = dot(visual_features, text_embed[cls])
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.YOLOv8.Config
import Examples.YOLOv8.Types
import Examples.YOLOv8.Primitives.Dequant

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.YOLOv8.TextEmbedding

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.YOLOv8.Primitives.Dequant

/-- INT8 dot product engine.

    Computes dot product of two INT8 vectors sequentially (one element per cycle).
    Uses Signal.loop with accumulator.

    State registers (4 total):
      0: accumulator (BitVec 32) — running dot product sum
      1: counter     (BitVec 16) — remaining elements
      2: fsmState    (BitVec 2)  — IDLE/ACCUMULATE/OUTPUT
      3: doneFlag    (Bool)

    Inputs:
      - vecA:    INT8 element from visual features
      - vecB:    INT8 element from text embedding
      - start:   begin new dot product
      - length:  vector length

    Outputs:
      - result:  INT32 dot product
      - done:    result valid pulse
-/
def dotProductEngine {dom : DomainConfig}
    (vecA : Signal dom (BitVec 8))
    (vecB : Signal dom (BitVec 8))
    (start : Signal dom Bool)
    (length : Signal dom (BitVec 16))
    : Signal dom (BitVec 32 × Bool) :=
  let loopState := Signal.loop fun state =>
    let accReg     := projN! state 4 0  -- BitVec 32
    let counterReg := projN! state 4 1  -- BitVec 16
    let fsmReg     := projN! state 4 2  -- BitVec 2
    let doneReg    := projN! state 4 3  -- Bool

    let isIdle := (· == ·) <$> fsmReg <*> Signal.pure 0#2
    let isAcc  := (· == ·) <$> fsmReg <*> Signal.pure 1#2
    let isOut  := (· == ·) <$> fsmReg <*> Signal.pure 2#2

    let startAndIdle := (· && ·) <$> start <*> isIdle

    -- MAC: sign-extend both to 32 bits, multiply, accumulate
    let aExt := extendInt8ToInt32 vecA
    let bExt := extendInt8ToInt32 vecB
    let product := (· * ·) <$> aExt <*> bExt
    let accPlus := (· + ·) <$> accReg <*> product

    -- Counter
    let counterDec := (· - ·) <$> counterReg <*> Signal.pure 1#16
    let counterIsOne := (· == ·) <$> counterReg <*> Signal.pure 1#16
    let accDone := (· && ·) <$> isAcc <*> counterIsOne

    -- FSM
    let fsmNext :=
      Signal.mux startAndIdle (Signal.pure 1#2)
        (Signal.mux accDone (Signal.pure 2#2)
          (Signal.mux isOut (Signal.pure 0#2)
            fsmReg))

    let accNext :=
      Signal.mux startAndIdle (Signal.pure 0#32)
        (Signal.mux isAcc accPlus
          accReg)

    let counterNext :=
      Signal.mux startAndIdle length
        (Signal.mux isAcc counterDec
          counterReg)

    let doneNext := isOut

    bundleAll! [
      Signal.register 0#32 accNext,
      Signal.register 0#16 counterNext,
      Signal.register 0#2 fsmNext,
      Signal.register false doneNext
    ]

  let accOut := projN! loopState 4 0
  let doneOut := projN! loopState 4 3
  bundle2 accOut doneOut

#synthesizeVerilog dotProductEngine

end Sparkle.Examples.YOLOv8.TextEmbedding
