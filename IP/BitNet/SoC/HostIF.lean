/-
  BitNet SoC — PCIe Host Interface — Signal DSL

  Register-mapped control/status interface for the BitNet accelerator.
  Connects to the host PC via AXI4-Lite (downstream of Xilinx XDMA IP).

  Register Map (32-bit, byte-addressed):
    0x00  CTRL     W   [0]=go, [1]=reset
    0x04  STATUS   R   [0]=done, [1]=busy, [31:16]=layerIdx
    0x08  TOKEN_IN W   token activation input (Q16.16)
    0x0C  SEQ_POS  W   current sequence position
    0x10  RESULT   R   inference output (32-bit)
    0x14  WEIGHT_BASE W  HBM weight base address
    0x18  PERF_CYCLES R  cycle counter (for benchmarking)

  The host writes TOKEN_IN, SEQ_POS, WEIGHT_BASE, then pulses CTRL.go.
  The accelerator runs the full forward pass and sets STATUS.done.
  The host reads RESULT.

  On real hardware: XDMA IP → AXI4-Lite → this register file → FullModel.
  For simulation: direct register writes via testbench.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain

namespace Sparkle.IP.BitNet.SoC

open Sparkle.Core.Signal
open Sparkle.Core.Domain

variable {dom : DomainConfig}

/-- Host interface register file + control logic.

    Inputs:
      -- AXI4-Lite write port (from XDMA / testbench)
      regWriteAddr  — register address (4-bit, word-aligned)
      regWriteData  — write data
      regWriteEn    — write strobe
      -- Accelerator status (from FullModel)
      accelDone     — inference complete
      accelResult   — output value
      accelLayerIdx — current layer being processed
      accelBusy     — accelerator is running

    Returns (go × (tokenIn × (seqPos × (weightBase × (result × (perfCycles × status)))))) -/
def hostInterface
    -- Register write port
    (regWriteAddr : Signal dom (BitVec 4))
    (regWriteData : Signal dom (BitVec 32))
    (regWriteEn : Signal dom Bool)
    -- Register read port
    (regReadAddr : Signal dom (BitVec 4))
    -- Accelerator feedback
    (accelDone : Signal dom Bool)
    (accelResult : Signal dom (BitVec 32))
    (accelLayerIdx : Signal dom (BitVec 8))
    (accelBusy : Signal dom Bool)
    : Signal dom (Bool × (BitVec 32 × (BitVec 16 × (BitVec 32 × (BitVec 32 × (BitVec 32 × BitVec 32)))))) :=
  -- Register file via Signal.loop
  let state := Signal.loop (dom := dom)
    (α := BitVec 32 × (BitVec 16 × (BitVec 32 × (BitVec 32 × (Bool × BitVec 32)))))
    fun (self : Signal dom (BitVec 32 × (BitVec 16 × (BitVec 32 × (BitVec 32 × (Bool × BitVec 32)))))) =>
    let tokenIn := Signal.fst self
    let r1 := Signal.snd self
    let seqPos := Signal.fst r1
    let r2 := Signal.snd r1
    let weightBase := Signal.fst r2
    let r3 := Signal.snd r2
    let perfCycles := Signal.fst r3
    let r4 := Signal.snd r3
    let goPulse := Signal.fst r4
    let resultLatch := Signal.snd r4

    -- Address decode
    let isCtrl : Signal dom Bool := regWriteAddr === (Signal.pure 0x0#4 : Signal dom (BitVec 4))
    let isTokenIn : Signal dom Bool := regWriteAddr === (Signal.pure 0x2#4 : Signal dom (BitVec 4))
    let isSeqPos : Signal dom Bool := regWriteAddr === (Signal.pure 0x3#4 : Signal dom (BitVec 4))
    let isWeightBase : Signal dom Bool := regWriteAddr === (Signal.pure 0x5#4 : Signal dom (BitVec 4))

    -- Write logic
    let ctrlWrite : Signal dom Bool :=
      Signal.mux regWriteEn
        (Signal.mux isCtrl (Signal.pure true : Signal dom Bool) (Signal.pure false : Signal dom Bool))
        (Signal.pure false : Signal dom Bool)
    let goWrite : Signal dom Bool :=
      Signal.mux ctrlWrite
        -- bit 0 of write data = go
        (Signal.map (fun d => d.extractLsb' 0 1 == 1#1) regWriteData)
        (Signal.pure false : Signal dom Bool)

    let nextTokenIn : Signal dom (BitVec 32) :=
      Signal.mux (Signal.mux regWriteEn isTokenIn (Signal.pure false : Signal dom Bool))
        regWriteData tokenIn

    let nextSeqPos : Signal dom (BitVec 16) :=
      Signal.mux (Signal.mux regWriteEn isSeqPos (Signal.pure false : Signal dom Bool))
        (Signal.map (BitVec.extractLsb' 0 16 ·) regWriteData) seqPos

    let nextWeightBase : Signal dom (BitVec 32) :=
      Signal.mux (Signal.mux regWriteEn isWeightBase (Signal.pure false : Signal dom Bool))
        regWriteData weightBase

    -- Performance counter: increment every cycle while busy
    let nextPerfCycles : Signal dom (BitVec 32) :=
      Signal.mux goWrite (Signal.pure 0#32 : Signal dom (BitVec 32))  -- reset on go
        (Signal.mux accelBusy
          (perfCycles + (Signal.pure 1#32 : Signal dom (BitVec 32)))
          perfCycles)

    -- Go pulse: high for 1 cycle on CTRL write with bit 0 set
    let nextGo := goWrite

    -- Latch result when done
    let nextResult : Signal dom (BitVec 32) :=
      Signal.mux accelDone accelResult resultLatch

    bundle2
      (Signal.register 0#32 nextTokenIn)
      (bundle2
        (Signal.register 0#16 nextSeqPos)
        (bundle2
          (Signal.register 0#32 nextWeightBase)
          (bundle2
            (Signal.register 0#32 nextPerfCycles)
            (bundle2
              (Signal.register false nextGo)
              (Signal.register 0#32 nextResult)))))

  -- Extract registers
  let tokenIn := Signal.fst state
  let r1 := Signal.snd state
  let seqPos := Signal.fst r1
  let r2 := Signal.snd r1
  let weightBase := Signal.fst r2
  let r3 := Signal.snd r2
  let perfCycles := Signal.fst r3
  let r4 := Signal.snd r3
  let goPulse := Signal.fst r4
  let resultLatch := Signal.snd r4

  -- Read mux: STATUS register composition
  let layerIdxExt : Signal dom (BitVec 32) :=
    accelLayerIdx ++ (Signal.pure 0#24 : Signal dom (BitVec 24))
  let layerShifted : Signal dom (BitVec 32) :=
    layerIdxExt <<< (Signal.pure 16#32 : Signal dom (BitVec 32))
  let doneExt : Signal dom (BitVec 32) :=
    Signal.mux accelDone (Signal.pure 1#32 : Signal dom (BitVec 32)) (Signal.pure 0#32 : Signal dom (BitVec 32))
  let busyExt : Signal dom (BitVec 32) :=
    Signal.mux accelBusy (Signal.pure 2#32 : Signal dom (BitVec 32)) (Signal.pure 0#32 : Signal dom (BitVec 32))
  let statusReg : Signal dom (BitVec 32) := layerShifted ||| doneExt ||| busyExt

  -- Read mux by address
  let readData : Signal dom (BitVec 32) :=
    Signal.mux (regReadAddr === (Signal.pure 0x1#4 : Signal dom (BitVec 4))) statusReg
      (Signal.mux (regReadAddr === (Signal.pure 0x4#4 : Signal dom (BitVec 4))) resultLatch
        (Signal.mux (regReadAddr === (Signal.pure 0x6#4 : Signal dom (BitVec 4))) perfCycles
          (Signal.pure 0#32 : Signal dom (BitVec 32))))

  bundle2 goPulse (bundle2 tokenIn (bundle2 seqPos (bundle2 weightBase
    (bundle2 resultLatch (bundle2 perfCycles statusReg)))))

end Sparkle.IP.BitNet.SoC
