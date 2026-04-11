/-
  Joint Encoder Reader — SPI Multi-Axis — Signal DSL

  Reads absolute position encoders via SPI (AS5047P / AS5600 compatible).
  Supports sequential polling of up to 30 encoders on a shared SPI bus
  with individual chip selects.

  AS5047P protocol:
    - SPI Mode 1 (CPOL=0, CPHA=1), 10 MHz max
    - 16-bit frame: [1-bit parity][1-bit EF][14-bit angle]
    - Read: send 0xFFFF, receive angle on MISO
    - Resolution: 14-bit = 16384 counts/revolution

  FSM: IDLE → SELECT_CH → TRANSFER → STORE → next channel → DONE

  At 200 MHz: SPI clock ~6 MHz (divider=32), 16 bits per transfer
  16 bits × 32 cycles/bit = 512 cycles per encoder
  30 encoders × 512 = 15,360 cycles = 76.8 μs total read time
  → 13 kHz update rate (exceeds 10 kHz control loop)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Humanoid

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Single SPI encoder transfer.
    Sends 16 clock pulses, receives 14-bit angle on MISO.
    Returns (angle × (done × (sck × mosi))). -/
def encoderTransfer
    (go : Signal dom Bool)
    (miso : Signal dom Bool)
    : Signal dom (BitVec 14 × (Bool × (Bool × Bool))) :=
  -- State: phase(4) × bitCount(8) × sckDiv(8) × rxShift(16)
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 8 × (BitVec 8 × BitVec 16)))
    fun (self : Signal dom (BitVec 4 × (BitVec 8 × (BitVec 8 × BitVec 16)))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let bitCount := Signal.fst r1
    let r2 := Signal.snd r1
    let sckDiv := Signal.fst r2
    let rxShift := Signal.snd r2

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isTransfer : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- SPI clock divider (÷32 → ~6.25 MHz)
    let divLimit : Signal dom (BitVec 8) := (Signal.pure 31#8 : Signal dom (BitVec 8))
    let sckToggle : Signal dom Bool :=
      Signal.mux isTransfer (sckDiv === divLimit) (Signal.pure false : Signal dom Bool)

    -- Sample MISO on rising edge (divider = 15 → middle of half-period)
    let samplePoint : Signal dom Bool :=
      Signal.mux isTransfer (sckDiv === (Signal.pure 15#8 : Signal dom (BitVec 8)))
        (Signal.pure false : Signal dom Bool)

    -- Shift in MISO bit
    let misoBit : Signal dom (BitVec 16) :=
      Signal.mux miso (Signal.pure 1#16 : Signal dom (BitVec 16)) (Signal.pure 0#16 : Signal dom (BitVec 16))
    let shiftedRx : Signal dom (BitVec 16) :=
      (rxShift <<< (Signal.pure 1#16 : Signal dom (BitVec 16))) ||| misoBit

    -- Bit counter
    let bitDone : Signal dom Bool :=
      Signal.mux sckToggle (bitCount === (Signal.pure 15#8 : Signal dom (BitVec 8)))
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux bitDone (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux isDone
            (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
            phase))

    let nextBitCount : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux sckToggle
          (bitCount + (Signal.pure 1#8 : Signal dom (BitVec 8)))
          bitCount)

    let nextSckDiv : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux sckToggle (Signal.pure 0#8 : Signal dom (BitVec 8))
          (Signal.mux isTransfer
            (sckDiv + (Signal.pure 1#8 : Signal dom (BitVec 8)))
            sckDiv))

    let nextRxShift : Signal dom (BitVec 16) :=
      Signal.mux samplePoint shiftedRx rxShift

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#8 nextBitCount)
        (bundle2
          (Signal.register 0#8 nextSckDiv)
          (Signal.register 0#16 nextRxShift)))

  let phase := Signal.fst state
  let r1 := Signal.snd state
  let _bitCount := Signal.fst r1
  let r2 := Signal.snd r1
  let sckDiv := Signal.fst r2
  let rxShift := Signal.snd r2

  let isTransfer : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
  let isDone : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))

  -- SCK output: high when sckDiv >= 16 (half of 32-cycle period)
  let sckOut : Signal dom Bool :=
    Signal.mux isTransfer
      (Signal.map (BitVec.extractLsb' 4 1 ·) sckDiv === (Signal.pure 1#1 : Signal dom (BitVec 1)))
      (Signal.pure false : Signal dom Bool)

  -- MOSI: always high (0xFFFF read command)
  let mosiOut : Signal dom Bool :=
    Signal.mux isTransfer (Signal.pure true : Signal dom Bool) (Signal.pure false : Signal dom Bool)

  -- Extract 14-bit angle from received 16-bit frame (bits [13:0])
  let angle : Signal dom (BitVec 14) := Signal.map (BitVec.extractLsb' 0 14 ·) rxShift

  bundle2 angle (bundle2 isDone (bundle2 sckOut mosiOut))

/-- Multi-channel encoder reader.
    Sequentially polls `nChannels` encoders on shared SPI bus.
    Each encoder has its own CS line (active low).

    Inputs:
      go   — start reading all channels
      miso — shared MISO line
      nChannels — number of encoders - 1 (BitVec 8)

    Returns (currentAngle × (channelIdx × (done × (sck × (mosi × csActive))))). -/
def multiEncoderReader
    (nChannels : BitVec 8)  -- number of channels - 1
    (go : Signal dom Bool)
    (miso : Signal dom Bool)
    : Signal dom (BitVec 14 × (BitVec 8 × (Bool × (Bool × (Bool × Bool))))) :=
  -- Master FSM: cycles through channels
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 8 × (BitVec 14 × Bool)))
    fun (self : Signal dom (BitVec 4 × (BitVec 8 × (BitVec 14 × Bool)))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let channelIdx := Signal.fst r1
    let r2 := Signal.snd r1
    let lastAngle := Signal.fst r2
    let xferStart := Signal.snd r2

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isReading : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- Single encoder transfer
    let xferOut := encoderTransfer xferStart miso
    let xferAngle := Signal.fst xferOut
    let xferDone : Signal dom Bool :=
      Signal.mux isReading (Signal.fst (Signal.snd xferOut)) (Signal.pure false : Signal dom Bool)

    -- Channel done → next or all done
    let atLastChannel : Signal dom Bool :=
      channelIdx === (Signal.pure nChannels : Signal dom (BitVec 8))
    let allDone : Signal dom Bool :=
      Signal.mux xferDone atLastChannel (Signal.pure false : Signal dom Bool)
    let nextChannel : Signal dom Bool :=
      Signal.mux xferDone
        (Signal.mux atLastChannel (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux allDone (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux isDone
            (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
            phase))

    let nextChannelIdx : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux nextChannel
          (channelIdx + (Signal.pure 1#8 : Signal dom (BitVec 8)))
          channelIdx)

    let nextAngle : Signal dom (BitVec 14) :=
      Signal.mux xferDone xferAngle lastAngle

    -- Start transfer: on go (first channel) or next channel
    let nextXferStart : Signal dom Bool :=
      Signal.mux goIdle (Signal.pure true : Signal dom Bool)
        (Signal.mux nextChannel (Signal.pure true : Signal dom Bool)
          (Signal.pure false : Signal dom Bool))

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#8 nextChannelIdx)
        (bundle2
          (Signal.register 0#14 nextAngle)
          (Signal.register false nextXferStart)))

  let phase := Signal.fst state
  let r1 := Signal.snd state
  let channelIdx := Signal.fst r1
  let r2 := Signal.snd r1
  let lastAngle := Signal.fst r2

  let isDone : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
  let isReading : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))

  -- SPI signals: from the xferOut already computed inside the loop
  -- For output, we regenerate (combinational — same inputs produce same outputs)
  let xferStart2 := Signal.snd r2
  let xferOut2 := encoderTransfer xferStart2 miso
  let sckOut := Signal.fst (Signal.snd (Signal.snd xferOut2))
  let mosiOut := Signal.snd (Signal.snd (Signal.snd xferOut2))
  let csActive := isReading

  bundle2 lastAngle (bundle2 channelIdx (bundle2 isDone (bundle2 sckOut (bundle2 mosiOut csActive))))

end Sparkle.IP.Humanoid
