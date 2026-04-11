/-
  BitNet Layers — HBM Embedding Lookup — Signal DSL (200 MHz)

  Reads embedding vector from HBM for a given token ID.
  Layout: embeddingBaseAddr + tokenId * dim * 4 (byte-addressed)

  FSM: IDLE → READ_BEATS (dim words via AXI burst) → DONE

  For dim=2048, one embedding = 2048 × 4 bytes = 8 KB.
  With 256-bit HBM bus: 8192 / 32 = 256 beats.
  With 32-bit simplified bus: 2048 beats.

  Output: per-beat activation value + valid signal.
  Downstream consumer (transformer layer) receives one activation
  per cycle during READ_BEATS phase.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.BitNet.Layers

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- HBM embedding lookup FSM.
    Computes address = embeddingBase + tokenId * dimStride,
    then reads dim words sequentially from memory.

    Inputs:
      go             — start lookup
      tokenId        — token ID (16-bit)
      embeddingBase  — HBM base address of embedding table
      dimStrideBV    — dim * 4 as BitVec 32 (bytes per embedding)
      dimLimit       — dim - 1 (BitVec 16)
      memReadData    — data from memory
      memReadValid   — memory data valid

    Returns (activation × (actValid × (memReadAddr × (done × phase)))) -/
def embeddingHBMLookup
    (go : Signal dom Bool)
    (tokenId : Signal dom (BitVec 16))
    (embeddingBase : Signal dom (BitVec 32))
    (dimStrideBV : BitVec 32)
    (dimLimit : BitVec 16)
    -- Memory response
    (memReadData : Signal dom (BitVec 32))
    (memReadValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × (BitVec 32 × (Bool × BitVec 4)))) :=
  -- FSM: 0=IDLE, 1=READ_BEATS, 2=DONE
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 32 × (BitVec 16 × BitVec 32)))
    fun (self : Signal dom (BitVec 4 × (BitVec 32 × (BitVec 16 × BitVec 32)))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let baseAddr := Signal.fst r1
    let r2 := Signal.snd r1
    let beatCounter := Signal.fst r2
    let lastData := Signal.snd r2

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isReading : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- Compute embedding address: base + tokenId * dimStride
    let tokenIdExt : Signal dom (BitVec 32) :=
      tokenId ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
    let embAddr : Signal dom (BitVec 32) :=
      embeddingBase + tokenIdExt * (Signal.pure dimStrideBV : Signal dom (BitVec 32))

    -- Beat counter: increment on valid read
    let beatInc : Signal dom Bool :=
      Signal.mux isReading memReadValid (Signal.pure false : Signal dom Bool)
    let atLastBeat : Signal dom Bool :=
      Signal.mux beatInc
        (beatCounter === (Signal.pure dimLimit : Signal dom (BitVec 16)))
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux atLastBeat (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux isDone
            (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
            phase))

    let nextBaseAddr : Signal dom (BitVec 32) :=
      Signal.mux goIdle embAddr baseAddr

    let nextBeatCounter : Signal dom (BitVec 16) :=
      Signal.mux goIdle (Signal.pure 0#16 : Signal dom (BitVec 16))
        (Signal.mux beatInc
          (beatCounter + (Signal.pure 1#16 : Signal dom (BitVec 16)))
          beatCounter)

    let nextLastData : Signal dom (BitVec 32) :=
      Signal.mux beatInc memReadData lastData

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#32 nextBaseAddr)
        (bundle2
          (Signal.register 0#16 nextBeatCounter)
          (Signal.register 0#32 nextLastData)))

  let phase := Signal.fst state
  let r1 := Signal.snd state
  let baseAddr := Signal.fst r1
  let r2 := Signal.snd r1
  let beatCounter := Signal.fst r2
  let _lastData := Signal.snd r2

  let isReading : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
  let isDone : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))

  -- Memory read address: baseAddr + beatCounter * 4
  let beatCounterExt : Signal dom (BitVec 32) :=
    beatCounter ++ (Signal.pure 0#16 : Signal dom (BitVec 16))
  let readAddr : Signal dom (BitVec 32) :=
    baseAddr + beatCounterExt * (Signal.pure 4#32 : Signal dom (BitVec 32))

  -- Output: forward memory data as activation when valid during READ
  let actValid : Signal dom Bool :=
    Signal.mux isReading memReadValid (Signal.pure false : Signal dom Bool)

  bundle2 memReadData (bundle2 actValid (bundle2 readAddr (bundle2 isDone phase)))

end Sparkle.IP.BitNet.Layers
