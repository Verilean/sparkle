/-
  CLINT (Core Local Interruptor) — Signal DSL

  Memory-mapped timer and software interrupt controller.
  Uses Signal.loop with 5 registers: msip, mtimeLo, mtimeHi, mtimecmpLo, mtimecmpHi.

  Register Map:
    0x0000       MSIP        - Software interrupt pending (bit 0)
    0x4000-4004  MTIMECMP    - Timer compare (64-bit)
    0xBFF8-BFFC  MTIME       - Timer counter (64-bit)
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.RV32.CSR.Types

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.CLINT

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32.CSR

/-- CLINT — Signal DSL.

    Inputs:
      bus_addr[15:0]     - Bus address (offset from CLINT base)
      bus_wdata[31:0]    - Bus write data
      bus_we             - Bus write enable

    Output:
      (bus_rdata[31:0] × timer_irq × sw_irq) -/
def clintSignal {dom : DomainConfig}
    (busAddr : Signal dom (BitVec 16))
    (busWdata : Signal dom (BitVec 32))
    (busWE : Signal dom Bool)
    : Signal dom (BitVec 32 × (Bool × Bool)) :=
  let clint := Signal.loop fun state =>
    let msipReg       := projN! state 5 0  -- BitVec 32
    let mtimeLoReg    := projN! state 5 1  -- BitVec 32
    let mtimeHiReg    := projN! state 5 2  -- BitVec 32
    let mtimecmpLoReg := projN! state 5 3  -- BitVec 32
    let mtimecmpHiReg := projN! state 5 4  -- BitVec 32

    -- Address matching
    let msipMatch     := busAddr === (BitVec.ofNat 16 clintMSIP)
    let mtimeLoMatch  := busAddr === (BitVec.ofNat 16 clintMTIME_LO)
    let mtimeHiMatch  := busAddr === (BitVec.ofNat 16 clintMTIME_HI)
    let mtimecmpLoMatch := busAddr === (BitVec.ofNat 16 clintMTIMECMP_LO)
    let mtimecmpHiMatch := busAddr === (BitVec.ofNat 16 clintMTIMECMP_HI)

    -- MTIME auto-increment
    let mtimeLoInc := mtimeLoReg + 1#32
    let mtimeCarry := mtimeLoInc === 0#32
    let mtimeHiInc := Signal.mux mtimeCarry
      (mtimeHiReg + 1#32) mtimeHiReg

    -- Write logic: bus write takes priority over increment
    let msipNext := Signal.mux (busWE &&& msipMatch)
      busWdata msipReg
    let mtimeLoNext := Signal.mux (busWE &&& mtimeLoMatch)
      busWdata mtimeLoInc
    let mtimeHiNext := Signal.mux (busWE &&& mtimeHiMatch)
      busWdata mtimeHiInc
    let mtimecmpLoNext := Signal.mux (busWE &&& mtimecmpLoMatch)
      busWdata mtimecmpLoReg
    let mtimecmpHiNext := Signal.mux (busWE &&& mtimecmpHiMatch)
      busWdata mtimecmpHiReg

    bundleAll! [
      Signal.register 0#32 msipNext,
      Signal.register 0#32 mtimeLoNext,
      Signal.register 0#32 mtimeHiNext,
      Signal.register 0xFFFFFFFF#32 mtimecmpLoNext,
      Signal.register 0xFFFFFFFF#32 mtimecmpHiNext
    ]

  -- Extract registered state for outputs
  let msipReg       := projN! clint 5 0
  let mtimeLoReg    := projN! clint 5 1
  let mtimeHiReg    := projN! clint 5 2
  let mtimecmpLoReg := projN! clint 5 3
  let mtimecmpHiReg := projN! clint 5 4

  -- Bus read mux
  let msipMatch     := busAddr === (BitVec.ofNat 16 clintMSIP)
  let mtimeLoMatch  := busAddr === (BitVec.ofNat 16 clintMTIME_LO)
  let mtimeHiMatch  := busAddr === (BitVec.ofNat 16 clintMTIME_HI)
  let mtimecmpLoMatch := busAddr === (BitVec.ofNat 16 clintMTIMECMP_LO)
  let mtimecmpHiMatch := busAddr === (BitVec.ofNat 16 clintMTIMECMP_HI)
  let busRdata :=
    Signal.mux msipMatch msipReg
    (Signal.mux mtimecmpLoMatch mtimecmpLoReg
    (Signal.mux mtimecmpHiMatch mtimecmpHiReg
    (Signal.mux mtimeLoMatch mtimeLoReg
    (Signal.mux mtimeHiMatch mtimeHiReg
      (Signal.pure 0#32)))))

  -- Timer interrupt: mtime >= mtimecmp (unsigned 64-bit comparison)
  let hiGt := Signal.ult mtimecmpHiReg mtimeHiReg
  let hiEq := mtimeHiReg === mtimecmpHiReg
  let loGe := ~~~(Signal.ult mtimeLoReg mtimecmpLoReg)
  let timerIrq := hiGt ||| (hiEq &&& loGe)

  -- Software interrupt: msip[0]
  let swIrq := (msipReg.map (BitVec.extractLsb' 0 1 ·)) === 1#1

  bundleAll! [busRdata, timerIrq, swIrq]

#synthesizeVerilog clintSignal

end Sparkle.Examples.RV32.CLINT
