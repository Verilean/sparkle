/-
  DShot ESC Protocol — Signal DSL

  Digital motor control protocol for brushless ESCs.
  Sends 16-bit frames: [11-bit throttle][1-bit telemetry][4-bit CRC]

  Bit encoding (DShot600 @ 600 kbit/s):
    Bit period = 1.67 μs
    Bit '0': high for 625 ns, low for 1045 ns  (37.5% duty)
    Bit '1': high for 1250 ns, low for 420 ns  (74.8% duty)

  At 200 MHz clock: 1 cycle = 5 ns
    Bit period = 334 cycles
    Bit '0': high for 125 cycles, low for 209 cycles
    Bit '1': high for 250 cycles, low for 84 cycles

  Frame: 16 bits × 334 cycles = 5,344 cycles = 26.7 μs
  Repeat rate: ~37.5 kHz (one frame every 26.7 μs)

  Interface:
    throttle (11 bit): 0 = disarmed, 48-2047 = min-max thrust
    telemetryReq (1 bit): request telemetry from ESC
    go: pulse to send one frame
    dshotOut: the DShot signal wire (to ESC)
    busy: high while transmitting
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.Drone

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

-- DShot600 timing constants @ 200 MHz
-- Bit period: 334 cycles
-- Bit 0 high: 125 cycles
-- Bit 1 high: 250 cycles

/-- Compute DShot CRC (XOR of nibbles).
    CRC = (frame >> 8) XOR (frame >> 4) XOR frame, lower 4 bits. -/
@[reducible] def dshotCRC (throttle : BitVec 11) (telem : BitVec 1)
    : BitVec 4 :=
  let frame12 : BitVec 12 := throttle ++ telem
  let n2 := frame12.extractLsb' 8 4
  let n1 := frame12.extractLsb' 4 4
  let n0 := frame12.extractLsb' 0 4
  n2 ^^^ n1 ^^^ n0

/-- DShot600 transmitter FSM.

    Sends one 16-bit frame when `go` is pulsed.
    Output `dshotOut` is the DShot signal wire.

    Returns (dshotOut × (busy × phase)). -/
def dshotTransmitter
    (go : Signal dom Bool)
    (throttle : Signal dom (BitVec 11))
    (telemetryReq : Signal dom Bool)
    : Signal dom (Bool × (Bool × BitVec 4)) :=
  -- State: phase(4) × bitIdx(4) × cycleCount(16) × frame(16) × outputReg(1)
  let state := Signal.loop (dom := dom)
    (α := BitVec 4 × (BitVec 4 × (BitVec 16 × (BitVec 16 × Bool))))
    fun (self : Signal dom (BitVec 4 × (BitVec 4 × (BitVec 16 × (BitVec 16 × Bool))))) =>
    let phase := Signal.fst self
    let r1 := Signal.snd self
    let bitIdx := Signal.fst r1
    let r2 := Signal.snd r1
    let cycleCount := Signal.fst r2
    let r3 := Signal.snd r2
    let frame := Signal.fst r3
    let outputReg := Signal.snd r3

    let isIdle : Signal dom Bool := phase === (Signal.pure 0#4 : Signal dom (BitVec 4))
    let isSending : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
    let isDone : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))

    let goIdle : Signal dom Bool := Signal.mux isIdle go (Signal.pure false : Signal dom Bool)

    -- Build 16-bit frame: [throttle(11)][telem(1)][crc(4)]
    let telemBit : Signal dom (BitVec 1) :=
      Signal.mux telemetryReq (Signal.pure 1#1 : Signal dom (BitVec 1)) (Signal.pure 0#1 : Signal dom (BitVec 1))
    let frame12 : Signal dom (BitVec 12) := throttle ++ telemBit
    -- CRC = nibble2 XOR nibble1 XOR nibble0 (Signal-level XOR)
    let n2 : Signal dom (BitVec 4) := Signal.map (BitVec.extractLsb' 8 4 ·) frame12
    let n1 : Signal dom (BitVec 4) := Signal.map (BitVec.extractLsb' 4 4 ·) frame12
    let n0 : Signal dom (BitVec 4) := Signal.map (BitVec.extractLsb' 0 4 ·) frame12
    let crcVal : Signal dom (BitVec 4) := n2 ^^^ n1 ^^^ n0
    let fullFrame : Signal dom (BitVec 16) := frame12 ++ crcVal

    -- Current bit: extract from frame using bitIdx (MSB first)
    -- bit 15 sent first, bit 0 sent last
    -- Simplified: check if bit at position (15 - bitIdx) is 1
    -- For synthesis: use XOR of frame shifted right by (15-bitIdx)
    let bitIdxExt : Signal dom (BitVec 16) := bitIdx ++ (Signal.pure 0#12 : Signal dom (BitVec 12))
    let fifteenMinusIdx : Signal dom (BitVec 16) :=
      (Signal.pure 15#16 : Signal dom (BitVec 16)) - bitIdxExt
    let shiftedFrame : Signal dom (BitVec 16) := frame >>> fifteenMinusIdx
    let currentBit : Signal dom Bool :=
      Signal.map (BitVec.extractLsb' 0 1 ·) shiftedFrame === (Signal.pure 1#1 : Signal dom (BitVec 1))

    -- DShot bit timing: high duration depends on bit value
    -- Bit '0': high for 125 cycles (of 334)
    -- Bit '1': high for 250 cycles (of 334)
    let highDuration : Signal dom (BitVec 16) :=
      Signal.mux currentBit (Signal.pure 250#16 : Signal dom (BitVec 16))
                             (Signal.pure 125#16 : Signal dom (BitVec 16))
    let bitPeriod : Signal dom (BitVec 16) := (Signal.pure 334#16 : Signal dom (BitVec 16))

    -- Output: high when cycleCount < highDuration
    let isHigh : Signal dom Bool := Signal.mux isSending
      -- Compare cycle count < high duration
      (Signal.map (BitVec.extractLsb' 15 1 ·) (cycleCount - highDuration)
        === (Signal.pure 1#1 : Signal dom (BitVec 1)))  -- negative = count < duration
      (Signal.pure false : Signal dom Bool)

    -- Cycle counter: increment each cycle during SENDING
    let atBitEnd : Signal dom Bool :=
      Signal.mux isSending (cycleCount === (bitPeriod - (Signal.pure 1#16 : Signal dom (BitVec 16))))
        (Signal.pure false : Signal dom Bool)
    -- Last bit
    let atLastBit : Signal dom Bool :=
      Signal.mux atBitEnd (bitIdx === (Signal.pure 15#4 : Signal dom (BitVec 4)))
        (Signal.pure false : Signal dom Bool)

    let nextPhase : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 1#4 : Signal dom (BitVec 4))
        (Signal.mux atLastBit (Signal.pure 2#4 : Signal dom (BitVec 4))
          (Signal.mux isDone
            (Signal.mux go (Signal.pure 1#4 : Signal dom (BitVec 4)) phase)
            phase))

    let nextBitIdx : Signal dom (BitVec 4) :=
      Signal.mux goIdle (Signal.pure 0#4 : Signal dom (BitVec 4))
        (Signal.mux atBitEnd
          (bitIdx + (Signal.pure 1#4 : Signal dom (BitVec 4)))
          bitIdx)

    let nextCycleCount : Signal dom (BitVec 16) :=
      Signal.mux goIdle (Signal.pure 0#16 : Signal dom (BitVec 16))
        (Signal.mux atBitEnd (Signal.pure 0#16 : Signal dom (BitVec 16))
          (Signal.mux isSending
            (cycleCount + (Signal.pure 1#16 : Signal dom (BitVec 16)))
            cycleCount))

    let nextFrame : Signal dom (BitVec 16) :=
      Signal.mux goIdle fullFrame frame

    let nextOutput := isHigh

    bundle2
      (Signal.register 0#4 nextPhase)
      (bundle2
        (Signal.register 0#4 nextBitIdx)
        (bundle2
          (Signal.register 0#16 nextCycleCount)
          (bundle2
            (Signal.register 0#16 nextFrame)
            (Signal.register false nextOutput))))

  let phase := Signal.fst state
  let r1 := Signal.snd state
  let _bitIdx := Signal.fst r1
  let r2 := Signal.snd r1
  let _cycleCount := Signal.fst r2
  let r3 := Signal.snd r2
  let _frame := Signal.fst r3
  let outputReg := Signal.snd r3

  let isSending : Signal dom Bool := phase === (Signal.pure 1#4 : Signal dom (BitVec 4))
  let isDone : Signal dom Bool := phase === (Signal.pure 2#4 : Signal dom (BitVec 4))

  bundle2 outputReg (bundle2 isSending phase)

/-- 4-channel DShot output (one per motor).
    Each channel has its own transmitter FSM. -/
def dshotQuad
    (go : Signal dom Bool)
    (throttle1 throttle2 throttle3 throttle4 : Signal dom (BitVec 11))
    : Signal dom (Bool × (Bool × (Bool × (Bool × Bool)))) :=
  let ch1 := dshotTransmitter go throttle1 (Signal.pure false : Signal dom Bool)
  let ch2 := dshotTransmitter go throttle2 (Signal.pure false : Signal dom Bool)
  let ch3 := dshotTransmitter go throttle3 (Signal.pure false : Signal dom Bool)
  let ch4 := dshotTransmitter go throttle4 (Signal.pure false : Signal dom Bool)
  let out1 := Signal.fst ch1
  let out2 := Signal.fst ch2
  let out3 := Signal.fst ch3
  let out4 := Signal.fst ch4
  let busy := Signal.fst (Signal.snd ch1)
  bundle2 out1 (bundle2 out2 (bundle2 out3 (bundle2 out4 busy)))

end Sparkle.IP.Drone
