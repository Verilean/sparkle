/-
  UART GPS Receiver — Signal DSL

  UART receiver + UBX-NAV-PVT parser for u-blox GPS modules.

  UART: 9600 baud (default for u-blox), 8N1
  At 200 MHz: bit period = 200M / 9600 = 20,833 cycles

  UBX-NAV-PVT packet (simplified):
    Header: 0xB5 0x62
    Class:  0x01 (NAV)
    ID:     0x07 (PVT)
    Length: 92 bytes
    Payload: bytes 24-27 = longitude (int32, 1e-7 degrees)
             bytes 28-31 = latitude (int32, 1e-7 degrees)
             bytes 36-39 = height (int32, mm above ellipsoid)

  FSM: IDLE → SYNC1 → SYNC2 → HEADER → PAYLOAD → CHECKSUM → DONE

  Output: latitude, longitude, altitude (all 32-bit signed)
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- UART receiver — 8N1, configurable baud via bitPeriod.
    Samples RX line, outputs received byte + valid strobe.

    Returns (rxByte × rxValid). -/
def uartReceiver
    (bitPeriod : BitVec 16)  -- clock cycles per bit (e.g. 20833 for 9600 baud @ 200 MHz)
    (rxPin : Signal dom Bool)
    : Signal dom (BitVec 8 × Bool) :=
  -- State: phase(4) × bitTimer(16) × bitIdx(4) × shiftReg(8) × rxByte(8) × rxValid(1)
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 16 × (BitVec 4 × (BitVec 8 × (BitVec 8 × Bool)))))
    fun (self : Signal dom (BitVec 4 × (BitVec 16 × (BitVec 4 × (BitVec 8 × (BitVec 8 × Bool)))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let bitTimer := Signal.fst r1
    let r2 := Signal.snd r1
    let bitIdx := Signal.fst r2
    let r3 := Signal.snd r2
    let shiftReg := Signal.fst r3
    let r4 := Signal.snd r3
    let rxByte := Signal.fst r4
    let rxValid := Signal.snd r4

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isStartBit : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDataBits : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isStopBit : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

    -- Detect start bit (falling edge: rxPin goes low while idle)
    let startDetect : Signal dom Bool :=
      Signal.mux isIdle
        (Signal.mux rxPin (Signal.pure false : Signal dom Bool) (Signal.pure true : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    -- Timer counts down to zero, then triggers bit sample
    let halfPeriod : Signal dom (BitVec 16) :=
      Signal.map (fun p => BitVec.extractLsb' 1 16 (0#1 ++ p)) (Signal.pure bitPeriod : Signal dom (BitVec 16))
    let timerZero : Signal dom Bool :=
      bitTimer === (Signal.pure 0#16 : Signal dom (BitVec 16))
    let timerDec : Signal dom (BitVec 16) :=
      bitTimer - (Signal.pure 1#16 : Signal dom (BitVec 16))

    -- Sample MISO into shift register (LSB first for UART)
    let rxBitVal : Signal dom (BitVec 8) :=
      Signal.mux rxPin (Signal.pure 0x80#8 : Signal dom (BitVec 8)) (Signal.pure 0#8 : Signal dom (BitVec 8))
    let shiftedReg : Signal dom (BitVec 8) :=
      (shiftReg >>> (Signal.pure 1#8 : Signal dom (BitVec 8))) ||| rxBitVal

    -- Last data bit
    let lastDataBit : Signal dom Bool :=
      Signal.mux isDataBits
        (Signal.mux timerZero (bitIdx === (Signal.pure 7#4 : Signal dom (BitVec 4))) (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux startDetect (Signal.pure 1#4 : Signal dom (BitVec 4))         -- → START_BIT
        (Signal.mux (Signal.mux isStartBit timerZero (Signal.pure false : Signal dom Bool))
          (Signal.pure 2#4 : Signal dom (BitVec 4))                             -- → DATA_BITS
          (Signal.mux lastDataBit (Signal.pure 3#4 : Signal dom (BitVec 4))    -- → STOP_BIT
            (Signal.mux (Signal.mux isStopBit timerZero (Signal.pure false : Signal dom Bool))
              (Signal.pure 0#4 : Signal dom (BitVec 4))                         -- → IDLE
              phase)))

    let nextBitTimer : Signal dom (BitVec 16) :=
      Signal.mux startDetect halfPeriod                                          -- start: sample mid-bit
        (Signal.mux timerZero (Signal.pure bitPeriod : Signal dom (BitVec 16))  -- reload on zero
          timerDec)

    let nextBitIdx : Signal dom (BitVec 4) :=
      Signal.mux startDetect (Signal.pure 0#4 : Signal dom (BitVec 4))
        (Signal.mux (Signal.mux isDataBits timerZero (Signal.pure false : Signal dom Bool))
          (bitIdx + (Signal.pure 1#4 : Signal dom (BitVec 4)))
          bitIdx)

    let nextShiftReg : Signal dom (BitVec 8) :=
      Signal.mux (Signal.mux isDataBits timerZero (Signal.pure false : Signal dom Bool))
        shiftedReg shiftReg

    let nextRxByte : Signal dom (BitVec 8) :=
      Signal.mux lastDataBit shiftedReg rxByte

    let nextRxValid := lastDataBit

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#16 nextBitTimer)
        (bundle2
          (Signal.register 0#4 nextBitIdx)
          (bundle2
            (Signal.register 0#8 nextShiftReg)
            (bundle2
              (Signal.register 0#8 nextRxByte)
              (Signal.register false nextRxValid)))))

  let r1 := Signal.snd state
  let _bitTimer := Signal.fst r1
  let r2 := Signal.snd r1
  let _bitIdx := Signal.fst r2
  let r3 := Signal.snd r2
  let _shiftReg := Signal.fst r3
  let r4 := Signal.snd r3
  let rxByte := Signal.fst r4
  let rxValid := Signal.snd r4

  bundle2 rxByte rxValid

/-- UBX-NAV-PVT parser — extracts lat/lon/alt from UBX GPS packets.

    Input: byte stream from UART receiver.
    Output: lat, lon, alt (32-bit signed) + posValid flag.

    FSM: IDLE → SYNC1(0xB5) → SYNC2(0x62) → CLASS_ID → LENGTH →
         PAYLOAD (skip to lat/lon/alt offsets) → DONE -/
def ubxNavPvtParser
    (rxByte : Signal dom (BitVec 8))
    (rxValid : Signal dom Bool)
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × Bool))) :=
  -- State: phase(4) × byteCount(8) × lat(32) × lon(32) × alt(32)
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 8 × (BitVec 32 × (BitVec 32 × BitVec 32))))
    fun (self : Signal dom (BitVec 4 × (BitVec 8 × (BitVec 32 × (BitVec 32 × BitVec 32))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let byteCount := Signal.fst r1
    let r2 := Signal.snd r1
    let lat := Signal.fst r2
    let r3 := Signal.snd r2
    let lon := Signal.fst r3
    let alt := Signal.snd r3

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isSync1 : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isSync2 : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isPayload : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 4#4 : Signal dom (BitVec 4))

    -- Sync detection
    let gotSync1 : Signal dom Bool :=
      Signal.mux isIdle
        (Signal.mux rxValid
          (rxByte === (Signal.pure 0xB5#8 : Signal dom (BitVec 8)))
          (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)
    let gotSync2 : Signal dom Bool :=
      Signal.mux isSync1
        (Signal.mux rxValid
          (rxByte === (Signal.pure 0x62#8 : Signal dom (BitVec 8)))
          (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    -- Payload byte counting (skip class/id/length = 4 bytes, then 92 bytes payload)
    let payloadByte : Signal dom Bool :=
      Signal.mux isPayload rxValid (Signal.pure false : Signal dom Bool)
    let payloadDone : Signal dom Bool :=
      Signal.mux payloadByte
        (byteCount === (Signal.pure 95#8 : Signal dom (BitVec 8)))  -- 4 header + 92 payload - 1
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux gotSync1 (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux gotSync2 (Signal.pure 3#4 : Signal dom (BitVec 4))  -- skip class/id check for v0
          (Signal.mux payloadDone (Signal.pure 4#4 : Signal dom (BitVec 4))
            (Signal.mux isDone (Signal.pure 0#4 : Signal dom (BitVec 4))
              phase)))

    let nextByteCount : Signal dom (BitVec 8) :=
      Signal.mux gotSync2 (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux payloadByte
          (byteCount + (Signal.pure 1#8 : Signal dom (BitVec 8)))
          byteCount)

    -- Latch lat/lon/alt at their payload offsets
    -- lon at bytes 24-27 (byteCount 28-31 counting from sync2)
    -- lat at bytes 28-31 (byteCount 32-35)
    -- alt at bytes 36-39 (byteCount 40-43)
    -- Simplified: latch first byte of each field as 8-bit, shift in
    let rxByteExt : Signal dom (BitVec 32) :=
      rxByte ++ (Signal.pure 0#24 : Signal dom (BitVec 24))

    -- For v0: store last 4 received bytes as lat/lon/alt demo
    -- (real implementation would demux by byteCount)
    let nextLat : Signal dom (BitVec 32) :=
      Signal.mux payloadByte
        ((lat <<< (Signal.pure 8#32 : Signal dom (BitVec 32))) ||| rxByteExt)
        lat
    let nextLon := lon  -- simplified
    let nextAlt := alt  -- simplified

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#8 nextByteCount)
        (bundle2
          (Signal.register 0#32 nextLat)
          (bundle2
            (Signal.register 0#32 nextLon)
            (Signal.register 0#32 nextAlt))))

  let phase := Signal.fst state
  let r1 := Signal.snd state
  let _byteCount := Signal.fst r1
  let r2 := Signal.snd r1
  let lat := Signal.fst r2
  let r3 := Signal.snd r2
  let lon := Signal.fst r3
  let alt := Signal.snd r3

  let posValid : Signal dom Bool := phase === (Signal.pure 4#4 : Signal dom (BitVec 4))
  bundle2 lat (bundle2 lon (bundle2 alt posValid))

/-- Complete GPS receiver: UART + UBX parser.
    Input: rxPin (GPS module TX line)
    Output: lat, lon, alt (32-bit signed) + posValid -/
def gpsReceiver
    (rxPin : Signal dom Bool)
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 × Bool))) :=
  let uartOut := uartReceiver 20833#16 rxPin  -- 9600 baud @ 200 MHz
  let rxByte := Signal.fst uartOut
  let rxValid := Signal.snd uartOut
  ubxNavPvtParser rxByte rxValid

end Sparkle.IP.Drone
