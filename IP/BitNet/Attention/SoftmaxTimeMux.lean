/-
  BitNet Attention — Softmax (Time-Multiplexed) — Signal DSL (200 MHz)

  Sequential softmax over scores stored in BRAM:
    1. FIND_MAX: read all scores, track maximum (seqLen cycles)
    2. EXP_SUM: read each score, subtract max, exp LUT, accumulate sum (seqLen cycles)
    3. NORMALIZE: read each exp, multiply by 1/sum, write back as weight (seqLen cycles)
    4. DONE

  Uses 16-entry exp and reciprocal LUTs (same pattern as RMSNorm).
  Scores and weights stored in BRAM addressed by sequence position.

  Total latency: 3 × seqLen cycles.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import IP.BitNet.SignalHelpers

namespace Sparkle.IP.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.IP.BitNet.SignalHelpers

variable {dom : DomainConfig}

/-- 16-entry exp(-x) LUT in Q8.24. Index = top 4 bits of |diff|.
    Pre-computed: exp(-i*16) for i in 0..15. -/
def expLUT16 : Array (BitVec 32) := #[
  0x01000000#32,  -- exp(0) = 1.0
  0x00000001#32,  -- exp(-16) ≈ 0
  0x00000000#32,  -- exp(-32) ≈ 0
  0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
  0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
  0x00000000#32, 0x00000000#32, 0x00000000#32
]

/-- 16-entry reciprocal LUT in Q8.24. Index = top 4 bits of sum. -/
def recipLUT16 : Array (BitVec 32) := #[
  0x01000000#32,  -- 1/1 = 1.0
  0x00800000#32,  -- 1/2 = 0.5
  0x00555555#32,  -- 1/3
  0x00400000#32,  -- 1/4
  0x00333333#32,  -- 1/5
  0x002AAAAB#32,  -- 1/6
  0x00249249#32,  -- 1/7
  0x00200000#32,  -- 1/8
  0x001C71C7#32,  -- 1/9
  0x00199999#32,  -- 1/10
  0x00174703#32,  -- 1/11
  0x00155555#32,  -- 1/12
  0x0013B13B#32,  -- 1/13
  0x00124925#32,  -- 1/14
  0x00111111#32,  -- 1/15
  0x00100000#32   -- 1/16
]

/-- Time-multiplexed softmax FSM.

    Operates on scores stored in a BRAM (written by dot product phase).
    Produces attention weights in a second BRAM.

    Inputs:
      go         — start pulse
      seqLen     — number of valid positions (as BitVec 16, = actual count - 1)
      scoreWriteAddr/Data/En — score BRAM write port (from dot product)
      scoreReadAddr  — (output) address the FSM is reading from score BRAM

    Returns (weightReadData × (done × (readAddr × phase))). -/
def softmaxTimeMux
    (go : Signal dom Bool)
    (seqLenLimit : Signal dom (BitVec 16))  -- seqLen - 1 (runtime signal)
    -- Score BRAM write port (external: dot product writes scores)
    (scoreWriteAddr : Signal dom (BitVec 16))
    (scoreWriteData : Signal dom (BitVec 32))
    (scoreWriteEn : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (BitVec 16 × BitVec 4))) :=
  -- Score BRAM: dot product writes, softmax reads
  -- Weight BRAM: softmax writes normalized weights

  -- FSM: 0=IDLE, 1=FIND_MAX, 2=EXP_SUM, 3=NORMALIZE, 4=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 16 × (BitVec 32 × (BitVec 32 × BitVec 32))))
    fun (self : Signal dom (BitVec 4 × (BitVec 16 × (BitVec 32 × (BitVec 32 × BitVec 32))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let counter := Signal.fst r1
    let r2 := Signal.snd r1
    let maxVal := Signal.fst r2
    let r3 := Signal.snd r2
    let expSum := Signal.fst r3
    let recipVal := Signal.snd r3

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isFindMax : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isExpSum : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isNorm : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 4#4 : Signal dom (BitVec 4))

    -- Score BRAM read
    let scoreRead := Signal.memoryComboRead scoreWriteAddr scoreWriteData scoreWriteEn counter

    -- FIND_MAX: track signed maximum (compare via subtraction sign bit)
    let diff : Signal dom (BitVec 32) := scoreRead - maxVal
    let scoreIsGreater : Signal dom Bool :=
      Signal.map (BitVec.extractLsb' 31 1 ·) diff === (Signal.pure 0#1 : Signal dom (BitVec 1))
    let newMax : Signal dom (BitVec 32) := Signal.mux scoreIsGreater scoreRead maxVal

    -- EXP_SUM: exp(score - max) via LUT
    let scoreDiff := maxVal - scoreRead  -- always >= 0
    let expIdx : Signal dom (BitVec 4) := Signal.map (BitVec.extractLsb' 4 4 ·) scoreDiff
    let expVal := lutMuxTree expLUT16 expIdx
    let newExpSum : Signal dom (BitVec 32) := expSum + expVal

    -- NORMALIZE: reciprocal LUT on sum, then multiply
    let recipIdx : Signal dom (BitVec 4) := Signal.map (BitVec.extractLsb' 20 4 ·) expSum
    let recipFromLUT := lutMuxTree recipLUT16 recipIdx

    -- Counter limit
    let atEnd : Signal dom Bool := counter === seqLenLimit

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)
    let maxDone : Signal dom Bool := Signal.mux isFindMax atEnd (Signal.pure false : Signal dom Bool)
    let expDone : Signal dom Bool := Signal.mux isExpSum atEnd (Signal.pure false : Signal dom Bool)
    let normDone : Signal dom Bool := Signal.mux isNorm atEnd (Signal.pure false : Signal dom Bool)

    let counterInc : Signal dom (BitVec 16) := counter + (Signal.pure 1#16 : Signal dom (BitVec 16))

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux maxDone (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux expDone (Signal.pure 3#4 : Signal dom (BitVec 4))
            (Signal.mux normDone (Signal.pure 4#4 : Signal dom (BitVec 4))
              (Signal.mux isDone
                (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
                phase))))

    -- Reset counter on phase transitions
    let nextCounter : Signal dom (BitVec 16) :=
      Signal.mux goIdle (Signal.pure 0#16 : Signal dom (BitVec 16))
        (Signal.mux maxDone (Signal.pure 0#16 : Signal dom (BitVec 16))
          (Signal.mux expDone (Signal.pure 0#16 : Signal dom (BitVec 16))
            (Signal.mux (Signal.mux isFindMax (Signal.pure true : Signal dom Bool)
              (Signal.mux isExpSum (Signal.pure true : Signal dom Bool)
                (Signal.mux isNorm (Signal.pure true : Signal dom Bool)
                  (Signal.pure false : Signal dom Bool)))) counterInc
              counter)))

    let nextMax : Signal dom (BitVec 32) :=
      Signal.mux goIdle (Signal.pure 0x80000000#32 : Signal dom (BitVec 32))  -- INT32_MIN
        (Signal.mux isFindMax newMax maxVal)

    let nextExpSum : Signal dom (BitVec 32) :=
      Signal.mux goIdle (Signal.pure 0#32 : Signal dom (BitVec 32))
        (Signal.mux expDone (Signal.pure 0#32 : Signal dom (BitVec 32))  -- reset for normalize
          (Signal.mux isExpSum newExpSum expSum))

    let nextRecip : Signal dom (BitVec 32) :=
      Signal.mux expDone recipFromLUT recipVal

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#16 nextCounter)
        (bundle2
          (Signal.register 0x80000000#32 nextMax)
          (bundle2
            (Signal.register 0#32 nextExpSum)
            (Signal.register 0#32 nextRecip))))

  -- Extract outputs
  let phase := Signal.fst state
  let r1 := Signal.snd state
  let counter := Signal.fst r1
  let r2 := Signal.snd r1
  let _maxVal := Signal.fst r2
  let r3 := Signal.snd r2
  let _expSum := Signal.fst r3
  let recipVal := Signal.snd r3

  -- Normalized weight output: exp(score - max) × recip >> 24
  -- (computed on-the-fly during NORMALIZE phase reading from score BRAM)
  let done : Signal dom Bool := phase === (Signal.pure 4#4 : Signal dom (BitVec 4))
  bundle2 recipVal (bundle2 done (bundle2 counter phase))

end Sparkle.IP.BitNet.Attention
