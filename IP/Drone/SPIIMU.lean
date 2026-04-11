/-
  SPI IMU Driver — Signal DSL

  SPI master for reading IMU sensor data (MPU6050 / ICM-42688 compatible).
  Burst-reads 12 bytes: accel X/Y/Z (6 bytes) + gyro X/Y/Z (6 bytes).

  SPI Mode 0 (CPOL=0, CPHA=0):
    - SCK idle low
    - Data sampled on rising edge, shifted on falling edge
    - MSB first

  SPI clock: 200 MHz / 20 = 10 MHz (divider = 10)

  FSM: IDLE → SEND_ADDR → READ_DATA (12 bytes) → DONE

  Output: 6 × 16-bit signed sensor values (Q8.8 or raw counts)
    accelX, accelY, accelZ, gyroX, gyroY, gyroZ
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- SPI master for IMU burst read.

    Inputs:
      go       — start a sensor read
      miso     — SPI MISO (data from IMU)

    Outputs:
      sck      — SPI clock
      mosi     — SPI MOSI (command to IMU)
      cs_n     — chip select (active low)
      accelX/Y/Z, gyroX/Y/Z — 16-bit sensor values
      done     — read complete, data valid

    Reads from register 0x3B (ACCEL_XOUT_H on MPU6050).
    Burst reads 12 bytes = 6 × 16-bit values. -/
def spiIMUDriver
    (go : Signal dom Bool)
    (miso : Signal dom Bool)
    : Signal dom (
        Bool ×          -- sck
        (Bool ×         -- mosi
        (Bool ×         -- cs_n (active low)
        (BitVec 16 ×    -- accelX
        (BitVec 16 ×    -- accelY
        (BitVec 16 ×    -- accelZ
        (BitVec 16 ×    -- gyroX
        (BitVec 16 ×    -- gyroY
        (BitVec 16 ×    -- gyroZ
        Bool             -- done
        ))))))))) :=
  -- State: phase(4) × bitCount(8) × byteCount(4) × sckDiv(8) ×
  --        txShiftReg(8) × rxShiftReg(8) × sensorRegs(6 × 16-bit packed as 3 × 32-bit)
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 8 × (BitVec 4 × (BitVec 8 ×
          (BitVec 8 × (BitVec 8 × (BitVec 32 × (BitVec 32 × BitVec 32))))))))
    fun (self : Signal dom (BitVec 4 × (BitVec 8 × (BitVec 4 × (BitVec 8 ×
          (BitVec 8 × (BitVec 8 × (BitVec 32 × (BitVec 32 × BitVec 32))))))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let bitCount := Signal.fst r1
    let r2 := Signal.snd r1
    let byteCount := Signal.fst r2
    let r3 := Signal.snd r2
    let sckDiv := Signal.fst r3
    let r4 := Signal.snd r3
    let txShift := Signal.fst r4
    let r5 := Signal.snd r4
    let rxShift := Signal.fst r5
    let r6 := Signal.snd r5
    let sensorLo := Signal.fst r6   -- accelX(16) + accelY(16)
    let r7 := Signal.snd r6
    let sensorMid := Signal.fst r7  -- accelZ(16) + gyroX(16)
    let sensorHi := Signal.snd r7   -- gyroY(16) + gyroZ(16)

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isSendAddr : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isReadData : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- SPI clock divider: toggle SCK every 10 cycles (200MHz / 20 = 10MHz)
    let divLimit : Signal dom (BitVec 8) := (Signal.pure 9#8 : Signal dom (BitVec 8))
    let sckToggle : Signal dom Bool :=
      Signal.mux (Signal.mux isSendAddr (Signal.pure true : Signal dom Bool)
        (Signal.mux isReadData (Signal.pure true : Signal dom Bool) (Signal.pure false : Signal dom Bool)))
        (sckDiv === divLimit)
        (Signal.pure false : Signal dom Bool)

    -- SCK generation: toggle on divider overflow
    -- For simplicity: sckDiv[3] as SCK (divide by 16 approximation → ~6.25 MHz)
    let sckOut : Signal dom Bool :=
      Signal.map (BitVec.extractLsb' 3 1 ·) sckDiv === (Signal.pure 1#1 : Signal dom (BitVec 1))

    -- Bit count: 0-7 per byte, increment on SCK rising edge
    let sckRising := sckToggle  -- simplified: count on divider overflow

    -- Address byte: 0x80 | 0x3B = 0xBB (read bit + register address)
    -- 0xBB = 10111011
    let addrByte : Signal dom (BitVec 8) := (Signal.pure 0xBB#8 : Signal dom (BitVec 8))

    -- MOSI: MSB of txShift during SEND_ADDR, 0 during READ_DATA
    let mosiOut : Signal dom Bool :=
      Signal.mux isSendAddr
        (Signal.map (BitVec.extractLsb' 7 1 ·) txShift === (Signal.pure 1#1 : Signal dom (BitVec 1)))
        (Signal.pure false : Signal dom Bool)

    -- RX: shift in MISO on rising edge during READ_DATA
    let rxBitIn : Signal dom (BitVec 8) :=
      Signal.mux miso
        ((rxShift <<< (Signal.pure 1#8 : Signal dom (BitVec 8))) ||| (Signal.pure 1#8 : Signal dom (BitVec 8)))
        (rxShift <<< (Signal.pure 1#8 : Signal dom (BitVec 8)))

    -- Byte complete: 8 bits shifted
    let byteComplete : Signal dom Bool :=
      Signal.mux sckRising
        (bitCount === (Signal.pure 7#8 : Signal dom (BitVec 8)))
        (Signal.pure false : Signal dom Bool)

    -- All 12 bytes + 1 addr byte = 13 bytes
    let addrDone : Signal dom Bool :=
      Signal.mux isSendAddr byteComplete (Signal.pure false : Signal dom Bool)
    let allBytesRead : Signal dom Bool :=
      Signal.mux isReadData
        (Signal.mux byteComplete
          (byteCount === (Signal.pure 11#4 : Signal dom (BitVec 4)))
          (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)

    -- Phase transitions
    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux addrDone (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux allBytesRead (Signal.pure 3#4 : Signal dom (BitVec 4))
            (Signal.mux isDone
              (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
              phase)))

    let nextSckDiv : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux sckToggle (Signal.pure 0#8 : Signal dom (BitVec 8))
          (Signal.mux (Signal.mux isSendAddr (Signal.pure true : Signal dom Bool)
            (Signal.mux isReadData (Signal.pure true : Signal dom Bool) (Signal.pure false : Signal dom Bool)))
            (sckDiv + (Signal.pure 1#8 : Signal dom (BitVec 8)))
            sckDiv))

    let nextBitCount : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux byteComplete (Signal.pure 0#8 : Signal dom (BitVec 8))
          (Signal.mux sckRising
            (bitCount + (Signal.pure 1#8 : Signal dom (BitVec 8)))
            bitCount))

    let nextByteCount : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 0#4 : Signal dom (BitVec 4))
        (Signal.mux (Signal.mux isReadData byteComplete (Signal.pure false : Signal dom Bool))
          (byteCount + (Signal.pure 1#4 : Signal dom (BitVec 4)))
          byteCount)

    let nextTxShift : Signal dom (BitVec 8) :=
      Signal.mux goIdle addrByte
        (Signal.mux sckRising
          (txShift <<< (Signal.pure 1#8 : Signal dom (BitVec 8)))
          txShift)

    let nextRxShift : Signal dom (BitVec 8) :=
      Signal.mux goIdle (Signal.pure 0#8 : Signal dom (BitVec 8))
        (Signal.mux (Signal.mux isReadData sckRising (Signal.pure false : Signal dom Bool))
          rxBitIn rxShift)

    -- Store received bytes into sensor registers
    -- Bytes 0-1: accelX, 2-3: accelY, 4-5: accelZ,
    -- 6-7: gyroX, 8-9: gyroY, 10-11: gyroZ
    -- Pack into 3 × 32-bit: Lo=[accelX,accelY], Mid=[accelZ,gyroX], Hi=[gyroY,gyroZ]
    let storeComplete : Signal dom Bool :=
      Signal.mux isReadData byteComplete (Signal.pure false : Signal dom Bool)
    -- Simplified: latch rxShift into sensor regs based on byteCount
    -- For now, accumulate into Lo/Mid/Hi (full implementation would
    -- demux by byteCount)
    let nextSensorLo : Signal dom (BitVec 32) :=
      Signal.mux storeComplete
        ((sensorLo <<< (Signal.pure 8#32 : Signal dom (BitVec 32))) |||
          (rxShift ++ (Signal.pure 0#24 : Signal dom (BitVec 24))))
        sensorLo
    let nextSensorMid := sensorMid  -- simplified for v0
    let nextSensorHi := sensorHi    -- simplified for v0

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#8 nextBitCount)
        (bundle2
          (Signal.register 0#4 nextByteCount)
          (bundle2
            (Signal.register 0#8 nextSckDiv)
            (bundle2
              (Signal.register 0#8 nextTxShift)
              (bundle2
                (Signal.register 0#8 nextRxShift)
                (bundle2
                  (Signal.register 0#32 nextSensorLo)
                  (bundle2
                    (Signal.register 0#32 nextSensorMid)
                    (Signal.register 0#32 nextSensorHi))))))))

  -- Extract outputs
  let phase := Signal.fst state
  let r1 := Signal.snd state
  let _bitCount := Signal.fst r1
  let r2 := Signal.snd r1
  let _byteCount := Signal.fst r2
  let r3 := Signal.snd r2
  let sckDiv := Signal.fst r3
  let r4 := Signal.snd r3
  let txShift := Signal.fst r4
  let r5 := Signal.snd r4
  let _rxShift := Signal.fst r5
  let r6 := Signal.snd r5
  let sensorLo := Signal.fst r6
  let r7 := Signal.snd r6
  let sensorMid := Signal.fst r7
  let sensorHi := Signal.snd r7

  let isSendAddr : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
  let isReadData : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))
  let isDone : Signal dom Bool := phase === (Signal.pure 3#4 : Signal dom (BitVec 4))

  -- SPI outputs
  let sckOut : Signal dom Bool :=
    Signal.mux (Signal.mux isSendAddr (Signal.pure true : Signal dom Bool)
      (Signal.mux isReadData (Signal.pure true : Signal dom Bool) (Signal.pure false : Signal dom Bool)))
      (Signal.map (BitVec.extractLsb' 3 1 ·) sckDiv === (Signal.pure 1#1 : Signal dom (BitVec 1)))
      (Signal.pure false : Signal dom Bool)
  let mosiOut : Signal dom Bool :=
    Signal.mux isSendAddr
      (Signal.map (BitVec.extractLsb' 7 1 ·) txShift === (Signal.pure 1#1 : Signal dom (BitVec 1)))
      (Signal.pure false : Signal dom Bool)
  let csN : Signal dom Bool :=
    Signal.mux (Signal.mux isSendAddr (Signal.pure true : Signal dom Bool)
      (Signal.mux isReadData (Signal.pure true : Signal dom Bool) (Signal.pure false : Signal dom Bool)))
      (Signal.pure false : Signal dom Bool)   -- CS active (low) during transfer
      (Signal.pure true : Signal dom Bool)    -- CS idle (high)

  -- Sensor values (16-bit from 32-bit packed registers)
  let accelX := Signal.map (BitVec.extractLsb' 16 16 ·) sensorLo
  let accelY := Signal.map (BitVec.extractLsb' 0 16 ·) sensorLo
  let accelZ := Signal.map (BitVec.extractLsb' 16 16 ·) sensorMid
  let gyroX := Signal.map (BitVec.extractLsb' 0 16 ·) sensorMid
  let gyroY := Signal.map (BitVec.extractLsb' 16 16 ·) sensorHi
  let gyroZ := Signal.map (BitVec.extractLsb' 0 16 ·) sensorHi

  bundle2 sckOut (bundle2 mosiOut (bundle2 csN
    (bundle2 accelX (bundle2 accelY (bundle2 accelZ
      (bundle2 gyroX (bundle2 gyroY (bundle2 gyroZ isDone))))))))

end Sparkle.IP.Drone
