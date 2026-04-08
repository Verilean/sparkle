/-
  UART (TX-only Console) — Signal DSL

  Memory-mapped transmit-only UART for debug output.
  Uses Signal.loop with 2 registers: txDataReg (8-bit), busyCntReg (5-bit).

  Register Map:
    0x00  TXDATA   - Transmit data (write bits [7:0] to send a byte)
    0x04  TXSTATUS - TX status (read-only, bit 0 = ready / not busy)
-/

import Sparkle
import Sparkle.Compiler.Elab

set_option maxRecDepth 4096

namespace Sparkle.IP.RV32.UART

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Number of cycles the transmitter stays busy after a byte write. -/
def uartTxCycles : BitVec 5 := 16#5

/-- UART — Signal DSL.

    Inputs:
      addr[7:0]          - Bus address (offset within UART region)
      wdata[31:0]        - Bus write data
      we                 - Bus write enable

    Output:
      (rdata[31:0] × uart_tx_data[7:0] × uart_tx_valid × uart_tx_ready) -/
def uartSignal {dom : DomainConfig}
    (addr : Signal dom (BitVec 8))
    (wdata : Signal dom (BitVec 32))
    (we : Signal dom Bool)
    : Signal dom (BitVec 32 × (BitVec 8 × (Bool × Bool))) :=
  let uart := Signal.loop fun state =>
    let txDataReg := projN! state 2 0  -- BitVec 8
    let busyCntReg := projN! state 2 1 -- BitVec 5

    -- Address decode
    let isTxData := addr === 0x00#8
    let isTxStatus := addr === 0x04#8

    -- TX ready = busy counter is zero
    let isZero := busyCntReg === 0#5
    let isBusy := ~~~isZero
    let txReady := ~~~isBusy

    -- TX data write enable
    let txDataWE := we &&& isTxData

    -- TX valid pulse: write accepted when ready
    let txValid := txDataWE &&& txReady

    -- TX data register: latch write data on write
    let txDataNext := Signal.mux txDataWE
      (wdata.map (BitVec.extractLsb' 0 8 ·)) txDataReg

    -- Busy counter: load on tx_valid, decrement while busy, else 0
    let busyCntDec := busyCntReg - 1#5
    let busyCntNext := Signal.mux txValid (Signal.pure uartTxCycles)
      (Signal.mux isBusy busyCntDec (Signal.pure 0#5))

    -- Bus read data mux
    let statusWord := Signal.mux txReady (Signal.pure 1#32) (Signal.pure 0#32)
    let txDataWord := 0#24 ++ txDataReg
    let rdata := Signal.mux isTxData txDataWord
      (Signal.mux isTxStatus statusWord (Signal.pure 0#32))

    -- Output: (state_next, outputs)
    -- state_next = (txDataNext, busyCntNext)
    -- outputs packed with state for extraction
    -- We return: (rdata × txData × txValid × txReady × txDataReg_next × busyCntReg_next)
    -- But Signal.loop needs state → state, so we bundle state with outputs
    -- Actually: return the state tuple, extract outputs separately
    bundleAll! [
      Signal.register 0#8 txDataNext,
      Signal.register 0#5 busyCntNext
    ]

  -- Extract outputs (need to recompute from state since loop returns state)
  -- Re-derive outputs from the registered state
  let txDataOut := projN! uart 2 0
  let busyCntOut := projN! uart 2 1
  let isZero := busyCntOut === 0#5
  let isBusy := ~~~isZero
  let txReady := ~~~isBusy
  let isTxData := addr === 0x00#8
  let isTxStatus := addr === 0x04#8
  let txDataWE := we &&& isTxData
  let txValid := txDataWE &&& txReady
  let statusWord := Signal.mux txReady (Signal.pure 1#32) (Signal.pure 0#32)
  let txDataWord := 0#24 ++ txDataOut
  let rdata := Signal.mux isTxData txDataWord
    (Signal.mux isTxStatus statusWord (Signal.pure 0#32))
  bundleAll! [rdata, txDataOut, txValid, txReady]

#synthesizeVerilog uartSignal

end Sparkle.IP.RV32.UART
