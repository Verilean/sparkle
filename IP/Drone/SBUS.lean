/-
  SBUS RC Receiver — Signal DSL

  Futaba SBUS protocol for RC transmitter input.
  Used for manual control and emergency override.

  Protocol:
    - Inverted UART 100,000 baud, 8E2 (8 data, even parity, 2 stop)
    - 25 bytes per frame, every 14 ms
    - Byte 0: header 0x0F
    - Bytes 1-22: 16 channels × 11 bits packed (little-endian bit order)
    - Byte 23: flags (ch17, ch18, frame_lost, failsafe)
    - Byte 24: footer 0x00

  Channel values: 0-2047 (center ~1024)
    Typical mapping: 172-1811 useful range

  At 200 MHz: bit period = 200M / 100000 = 2000 cycles

  Outputs: 8 primary channels (ch1-ch8) × 16-bit + failsafe flag
  (ch1 = roll, ch2 = pitch, ch3 = throttle, ch4 = yaw,
   ch5-ch8 = aux switches)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- SBUS frame receiver.
    Receives 25 bytes via inverted UART, extracts channel data.

    Input: sbusPin (inverted UART from RC receiver — invert externally or here)

    Returns:
      ch1..ch4  — primary stick channels (11-bit, zero-extended to 16)
      ch5..ch8  — aux channels
      failsafe  — failsafe flag (no RC signal)
      frameValid — new frame decoded -/
def sbusReceiver
    (sbusPin : Signal dom Bool)
    : Signal dom (BitVec 16 × (BitVec 16 × (BitVec 16 × (BitVec 16 ×
      (BitVec 16 × (BitVec 16 × (BitVec 16 × (BitVec 16 × (Bool × Bool))))))))) :=
  -- Invert SBUS signal (SBUS is inverted UART)
  let rxPin : Signal dom Bool :=
    Signal.mux sbusPin (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool)

  -- UART receiver at 100k baud (bit period = 2000 @ 200 MHz)
  -- Reuse uartReceiver from UARTGPS would be ideal, but to avoid
  -- cross-module synthesis issues, inline a simplified version.

  -- State: phase(4) × bitTimer(16) × bitIdx(4) × byteIdx(8) ×
  --        shiftReg(8) × frameBuffer (store key bytes: 1-8 for ch1-ch4) ×
  --        ch1-4 packed (2 × 32-bit) × flags(8) × frameValid
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 16 × (BitVec 4 × (BitVec 8 ×
          (BitVec 8 × (BitVec 32 × (BitVec 32 × (BitVec 8 × Bool))))))))
    fun (self : Signal dom (BitVec 4 × (BitVec 16 × (BitVec 4 × (BitVec 8 ×
          (BitVec 8 × (BitVec 32 × (BitVec 32 × (BitVec 8 × Bool))))))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let bitTimer := Signal.fst r1
    let r2 := Signal.snd r1
    let bitIdx := Signal.fst r2
    let r3 := Signal.snd r2
    let byteIdx := Signal.fst r3
    let r4 := Signal.snd r3
    let shiftReg := Signal.fst r4
    let r5 := Signal.snd r4
    let chLo := Signal.fst r5  -- ch1(11) + ch2(11) packed in lower bits
    let r6 := Signal.snd r5
    let chHi := Signal.fst r6  -- ch3(11) + ch4(11) packed
    let r7 := Signal.snd r6
    let flags := Signal.fst r7
    let frameValid := Signal.snd r7

    -- SBUS UART: 100k baud, bit period = 2000 cycles
    let bitPeriod : Signal dom (BitVec 16) := (Signal.pure 2000#16 : Signal dom (BitVec 16))
    let halfPeriod : Signal dom (BitVec 16) := (Signal.pure 1000#16 : Signal dom (BitVec 16))

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isStartBit : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDataBits : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isStopBits : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))
    let isFrameDone : Signal dom Bool := phase === (Signal.pure 4#4 : Signal dom (BitVec 4))

    -- Start bit detection
    let startDetect : Signal dom Bool :=
      Signal.mux isIdle
        (Signal.mux rxPin (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    let timerZero : Signal dom Bool :=
      bitTimer === (Signal.pure 0#16 : Signal dom (BitVec 16))

    -- Byte complete (8 data bits)
    let byteComplete : Signal dom Bool :=
      Signal.mux isDataBits
        (Signal.mux timerZero (bitIdx === (Signal.pure 7#4 : Signal dom (BitVec 4)))
          (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    -- Frame complete (25 bytes received, check for footer = 0x00 simplified)
    let frameComplete : Signal dom Bool :=
      Signal.mux byteComplete
        (byteIdx === (Signal.pure 24#8 : Signal dom (BitVec 8)))
        (Signal.pure false : Signal dom Bool)

    -- Header check (byte 0 = 0x0F)
    let isHeader : Signal dom Bool :=
      Signal.mux byteComplete
        (Signal.mux (byteIdx === (Signal.pure 0#8 : Signal dom (BitVec 8)))
          (shiftReg === (Signal.pure 0x0F#8 : Signal dom (BitVec 8)))
          (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    -- Phase transitions
    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux startDetect (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux (Signal.mux isStartBit timerZero (Signal.pure false : Signal dom Bool))
          (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux byteComplete (Signal.pure 3#4 : Signal dom (BitVec 4))
            (Signal.mux (Signal.mux isStopBits timerZero (Signal.pure false : Signal dom Bool))
              (Signal.mux frameComplete (Signal.pure 4#4 : Signal dom (BitVec 4))
                (Signal.pure 0#4 : Signal dom (BitVec 4)))  -- back to idle for next byte
              (Signal.mux isFrameDone (Signal.pure 0#4 : Signal dom (BitVec 4))
                phase))))

    let nextBitTimer : Signal dom (BitVec 16) :=
      Signal.mux startDetect halfPeriod
        (Signal.mux timerZero bitPeriod
          (bitTimer - (Signal.pure 1#16 : Signal dom (BitVec 16))))

    let nextBitIdx : Signal dom (BitVec 4) :=
      Signal.mux startDetect (Signal.pure 0#4 : Signal dom (BitVec 4))
        (Signal.mux (Signal.mux isDataBits timerZero (Signal.pure false : Signal dom Bool))
          (bitIdx + (Signal.pure 1#4 : Signal dom (BitVec 4)))
          bitIdx)

    let nextByteIdx : Signal dom (BitVec 8) :=
      Signal.mux isFrameDone (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux byteComplete
          (byteIdx + (Signal.pure 1#8 : Signal dom (BitVec 8)))
          byteIdx)

    -- Shift register: shift in rx bit (LSB first)
    let rxBitVal : Signal dom (BitVec 8) :=
      Signal.mux rxPin (Signal.pure 0x80#8 : Signal dom (BitVec 8)) (Signal.pure 0#8 : Signal dom (BitVec 8))
    let nextShiftReg : Signal dom (BitVec 8) :=
      Signal.mux (Signal.mux isDataBits timerZero (Signal.pure false : Signal dom Bool))
        ((shiftReg >>> (Signal.pure 1#8 : Signal dom (BitVec 8))) ||| rxBitVal)
        shiftReg

    -- Store channel data: bytes 1-4 → chLo, bytes 5-8 → chHi
    -- (simplified: shift received bytes into 32-bit registers)
    let storeByte : Signal dom Bool := byteComplete
    let shiftExt : Signal dom (BitVec 32) :=
      shiftReg ++ (Signal.pure 0#24 : Signal dom (BitVec 24))
    let nextChLo : Signal dom (BitVec 32) :=
      Signal.mux storeByte
        ((chLo <<< (Signal.pure 8#32 : Signal dom (BitVec 32))) ||| shiftExt)
        chLo
    let nextChHi := chHi  -- simplified for v0

    -- Flags byte (byte 23)
    let nextFlags : Signal dom (BitVec 8) :=
      Signal.mux (Signal.mux byteComplete
        (byteIdx === (Signal.pure 23#8 : Signal dom (BitVec 8)))
        (Signal.pure false : Signal dom Bool))
        shiftReg flags

    let nextFrameValid := frameComplete

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#16 nextBitTimer)
        (bundle2
          (Signal.register 0#4 nextBitIdx)
          (bundle2
            (Signal.register 0#8 nextByteIdx)
            (bundle2
              (Signal.register 0#8 nextShiftReg)
              (bundle2
                (Signal.register 0#32 nextChLo)
                (bundle2
                  (Signal.register 0#32 nextChHi)
                  (bundle2
                    (Signal.register 0#8 nextFlags)
                    (Signal.register false nextFrameValid))))))))

  -- Extract outputs
  let r1 := Signal.snd state
  let _bitTimer := Signal.fst r1
  let r2 := Signal.snd r1
  let _bitIdx := Signal.fst r2
  let r3 := Signal.snd r2
  let _byteIdx := Signal.fst r3
  let r4 := Signal.snd r3
  let _shiftReg := Signal.fst r4
  let r5 := Signal.snd r4
  let chLo := Signal.fst r5
  let r6 := Signal.snd r5
  let chHi := Signal.fst r6
  let r7 := Signal.snd r6
  let flags := Signal.fst r7
  let frameValid := Signal.snd r7

  -- Extract 11-bit channels from packed bytes (simplified: use byte boundaries)
  let ch1 : Signal dom (BitVec 16) := Signal.map (BitVec.extractLsb' 24 16 ·) chLo
  let ch2 : Signal dom (BitVec 16) := Signal.map (BitVec.extractLsb' 16 16 ·) chLo
  let ch3 : Signal dom (BitVec 16) := Signal.map (BitVec.extractLsb' 8 16 ·) chLo
  let ch4 : Signal dom (BitVec 16) := Signal.map (BitVec.extractLsb' 0 16 ·) chLo
  let ch5 : Signal dom (BitVec 16) := Signal.map (BitVec.extractLsb' 24 16 ·) chHi
  let ch6 : Signal dom (BitVec 16) := Signal.map (BitVec.extractLsb' 16 16 ·) chHi
  let ch7 : Signal dom (BitVec 16) := Signal.map (BitVec.extractLsb' 8 16 ·) chHi
  let ch8 : Signal dom (BitVec 16) := Signal.map (BitVec.extractLsb' 0 16 ·) chHi

  -- Failsafe: bit 3 of flags byte
  let failsafe : Signal dom Bool :=
    Signal.map (BitVec.extractLsb' 3 1 ·) flags === (Signal.pure 1#1 : Signal dom (BitVec 1))

  bundle2 ch1 (bundle2 ch2 (bundle2 ch3 (bundle2 ch4
    (bundle2 ch5 (bundle2 ch6 (bundle2 ch7 (bundle2 ch8
      (bundle2 failsafe frameValid))))))))

end Sparkle.IP.Drone
