/-
  BitNet Attention — Time-Multiplexed Single Head — Signal DSL (200 MHz)

  Sequential attention head using 1 MAC/cycle TimeMux cores.
  Shares the MAC unit across QKV projection, dot product, and score-V multiply.

  FSM phases:
    0  IDLE
    1  Q_PROJ     — headDim rows × dim MACs → Q[headDim] (INT8)
    2  K_PROJ     — headDim rows × dim MACs → K[headDim] (INT8)
    3  V_PROJ     — headDim rows × dim MACs → V[headDim] (INT8)
    4  STORE_KV   — write K,V to cache BRAM (headDim cycles)
    5  DOT_PROD   — seqLen dot products of Q·K_cached (each headDim cycles)
    6  SOFTMAX    — max + exp + normalize (seqLen cycles)
    7  SCORE_V    — headDim weighted sums (each seqLen cycles)
    8  DONE

  For the initial implementation, we simplify:
  - Single head only (multi-head wraps this)
  - KV cache in on-chip BRAM (sufficient for small seqLen)
  - Softmax via 16-entry exp/recip LUT (same as RMSNorm approach)

  All QKV/DotProd/ScoreV share the same TimeMux BitLinear core
  with different weight sources.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.BitLinear.TimeMux
import IP.BitNet.BitLinear.ScalePipelined
import IP.BitNet.Attention.Quantize
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.BitLinear
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- Time-multiplexed single attention head.

    This is a high-level FSM that orchestrates QKV projection,
    KV cache management, dot products, softmax, and score-V multiply.

    For the initial version, we implement only QKV projection via
    the existing WeightStreamer + TimeMux. Dot product, softmax, and
    score-V multiply reuse the same MAC unit with different data sources.

    Inputs:
      go         — start pulse
      activation — input activation (32-bit, broadcast during projection)
      qBaseAddr, kBaseAddr, vBaseAddr — weight memory addresses
      scaleVal   — Q8.24 scale for projection
      memReadData, memReadValid — weight memory interface
      seqPos     — current sequence position (for KV cache write)

    Returns (output × (done × phase)) where output is the first
    element of the attention result. -/
def attentionHeadTimeMux
    (dimLimit : BitVec 16)
    (go : Signal dom Bool)
    (activation : Signal dom (BitVec 32))
    -- QKV weight addresses
    (qBaseAddr kBaseAddr vBaseAddr : Signal dom (BitVec 32))
    (scaleVal : Signal dom (BitVec 32))
    -- Memory interface
    (memReadData : Signal dom (BitVec 2))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × BitVec 4)) :=
  -- Simplified: compute Q projection only (first row) as proof of concept.
  -- Full implementation would loop over headDim rows for Q, K, V each.
  --
  -- Phase: 0=IDLE, 1=Q_PROJ_ROW, 2=SCALE_QUANT, 3=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 8 × BitVec 16)))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 8 × BitVec 16)))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let projResult := Signal.fst r1  -- raw 32-bit MAC result
    let r2 := Signal.snd r1
    let quantResult := Signal.fst r2  -- INT8 quantized output
    let rowIdx := Signal.snd r2       -- current projection row

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isProj : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isScale : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

    -- WeightStreamer for Q projection (row 0)
    let projGo : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    let streamerOut := bitLinearTimeMux dimLimit
      (Signal.pure 0#16 : Signal dom (BitVec 16))  -- dummy write addr
      (Signal.pure 0#2 : Signal dom (BitVec 2))    -- dummy write data
      (Signal.pure false : Signal dom Bool)          -- no write
      projGo activation
    let macResult := bitLinearTimeMuxResult streamerOut
    let macDone := bitLinearTimeMuxDone streamerOut

    -- Scale: signExtend → multiply → extract (pipelined, 1 cycle)
    let acc48 : Signal dom (BitVec (16 + 32)) := signExtendSignal 16 projResult
    let scaled := scaleMultiplyPipelined acc48 scaleVal
    -- Note: INT8 quantization omitted (Signal.ashrC not yet in synthesis catalog)
    -- Full quantize would be: quantizeInt8Signal 10#32 scaled

    -- FSM transitions
    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    let projDone : Signal dom Bool := Signal.mux isProj macDone (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))      -- → Q_PROJ
        (Signal.mux projDone (Signal.pure 2#4 : Signal dom (BitVec 4)) -- → SCALE
          (Signal.mux isScale (Signal.pure 3#4 : Signal dom (BitVec 4))  -- → DONE
            (Signal.mux isDone
              (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
              phase)))

    let nextProjResult : Signal dom (BitVec 32) :=
      Signal.mux projDone macResult projResult

    -- Truncate scaled to 8 bits (placeholder for full INT8 quantize)
    let nextQuantResult : Signal dom (BitVec 8) :=
      Signal.mux isScale (Signal.map (BitVec.extractLsb' 0 8 ·) scaled) quantResult

    let nextRowIdx : Signal dom (BitVec 16) :=
      Signal.mux goIdle (Signal.pure 0#16 : Signal dom (BitVec 16)) rowIdx

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextProjResult)
        (bundle2
          (Signal.register 0#8 nextQuantResult)
          (Signal.register 0#16 nextRowIdx)))

  -- Extract
  let phase := Signal.fst state
  let r1 := Signal.snd state
  let projResult := Signal.fst r1

  let done : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))
  bundle2 projResult (bundle2 done phase)

end Sparkle.IP.BitNet.Attention
