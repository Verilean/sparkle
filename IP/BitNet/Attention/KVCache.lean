/-
  BitNet Attention — KV Cache — Signal DSL (200 MHz)

  BRAM-based Key/Value cache for autoregressive attention.

  Stores K and V projection results (32-bit per element) indexed by
  sequence position. During attention computation, past K/V values
  are read out for dot product and score-V multiply.

  Two BRAM instances: one for K cache, one for V cache.
  Address = seqPos (write) or readIdx (read during dot/scoreV).

  Interface:
    writeEn    — store K/V at current seqPos
    writeData  — K or V value to store
    writePos   — sequence position to write at
    readAddr   — address to read (cycled through during dot/scoreV)
    readData   — output: cached K or V value
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.BitNet.Attention

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Single KV cache BRAM.
    Stores 32-bit values indexed by 16-bit sequence position.
    Supports simultaneous write (at writePos) and read (at readAddr). -/
def kvCacheBRAM
    (writePos : Signal dom (BitVec 16))
    (writeData : Signal dom (BitVec 32))
    (writeEn : Signal dom Bool)
    (readAddr : Signal dom (BitVec 16))
    : Signal dom (BitVec 32) :=
  Signal.memoryComboRead writePos writeData writeEn readAddr

/-- KV Cache pair (K cache + V cache).
    Returns (kReadData × vReadData). -/
def kvCachePair
    (writePos : Signal dom (BitVec 16))
    (kWriteData vWriteData : Signal dom (BitVec 32))
    (writeEn : Signal dom Bool)
    (readAddr : Signal dom (BitVec 16))
    : Signal dom (BitVec 32 × BitVec 32) :=
  let kRead := kvCacheBRAM writePos kWriteData writeEn readAddr
  let vRead := kvCacheBRAM writePos vWriteData writeEn readAddr
  bundle2 kRead vRead

end Sparkle.IP.BitNet.Attention
