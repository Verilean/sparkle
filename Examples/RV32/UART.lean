/-
  UART (TX-only Console)

  Memory-mapped transmit-only UART for debug output.
  Base address: 0x10000000

  Register Map:
    0x00  TXDATA   - Transmit data (write bits [7:0] to send a byte)
    0x04  TXSTATUS - TX status (read-only, bit 0 = ready / FIFO not full)
-/

import Sparkle.IR.Builder
import Sparkle.IR.AST
import Sparkle.IR.Type

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.UART

open Sparkle.IR.Builder
open Sparkle.IR.AST
open Sparkle.IR.Type
open CircuitM

/-- Number of cycles the transmitter stays busy after a byte write.
    Simulates baud-rate timing (e.g., 16 cycles per byte). -/
def uartTxCycles : Nat := 16

/-- Generate the UART module.

    Inputs:
      clk, rst           - Clock and reset
      addr[7:0]          - Bus address (offset within UART region)
      wdata[31:0]        - Bus write data
      we                 - Bus write enable
      re                 - Bus read enable

    Outputs:
      rdata[31:0]        - Bus read data
      uart_tx_data[7:0]  - Transmit data byte
      uart_tx_valid      - TX valid pulse (1 cycle on write)
      uart_tx_ready      - TX ready (not busy)
-/
def generateUART : CircuitM Unit := do
  addInput "clk" .bit
  addInput "rst" .bit
  addInput "addr" (.bitVector 8)
  addInput "wdata" (.bitVector 32)
  addInput "we" .bit
  addInput "re" .bit
  addOutput "rdata" (.bitVector 32)
  addOutput "uart_tx_data" (.bitVector 8)
  addOutput "uart_tx_valid" .bit
  addOutput "uart_tx_ready" .bit

  let addr := Expr.ref "addr"
  let wdata := Expr.ref "wdata"
  let we := Expr.ref "we"

  -- =========================================================================
  -- Address Decode
  -- =========================================================================
  let isTxData ← makeWire "is_txdata" .bit
  emitAssign isTxData (.op .eq [addr, .const 0x00 8])

  let isTxStatus ← makeWire "is_txstatus" .bit
  emitAssign isTxStatus (.op .eq [addr, .const 0x04 8])

  -- =========================================================================
  -- TX Data Register (8-bit, latched on write to offset 0x00)
  -- =========================================================================
  let txDataWE ← makeWire "txdata_we" .bit
  emitAssign txDataWE (.op .and [we, .ref isTxData])

  let txDataNext ← makeWire "txdata_next" (.bitVector 8)
  let txDataReg ← emitRegister "txdata" "clk" "rst" (.ref txDataNext) 0 (.bitVector 8)
  emitAssign txDataNext (Expr.mux (.ref txDataWE) (.slice wdata 7 0) (.ref txDataReg))

  -- Drive output port
  emitAssign "uart_tx_data" (.ref txDataReg)

  -- =========================================================================
  -- TX Valid Pulse (active for 1 cycle when a byte is written)
  -- =========================================================================
  -- tx_valid = we AND is_txdata AND tx_ready (only accept when not busy)
  let txReady ← makeWire "tx_ready" .bit   -- forward declaration, assigned below

  let txValid ← makeWire "tx_valid" .bit
  emitAssign txValid (.op .and [.ref txDataWE, .ref txReady])

  emitAssign "uart_tx_valid" (.ref txValid)

  -- =========================================================================
  -- Busy Counter (counts down from uartTxCycles to 0)
  -- =========================================================================
  -- Counter width: 5 bits is sufficient for values up to 31
  let counterWidth := 5

  let busyCntNext ← makeWire "busy_cnt_next" (.bitVector counterWidth)
  let busyCntReg ← emitRegister "busy_cnt" "clk" "rst" (.ref busyCntNext) 0 (.bitVector counterWidth)

  -- Decrement: busy_cnt - 1
  let busyCntDec ← makeWire "busy_cnt_dec" (.bitVector counterWidth)
  emitAssign busyCntDec (Expr.sub (.ref busyCntReg) (.const 1 counterWidth))

  -- Counter is non-zero (busy)
  let isBusy ← makeWire "is_busy" .bit
  emitAssign isBusy (.op .not [.op .eq [.ref busyCntReg, .const 0 counterWidth]])

  -- tx_ready = NOT busy
  emitAssign txReady (.op .not [.ref isBusy])
  emitAssign "uart_tx_ready" (.ref txReady)

  -- Next counter value:
  --   If tx_valid (new write accepted): load uartTxCycles
  --   Else if busy (counter > 0):      decrement
  --   Else:                             stay at 0
  emitAssign busyCntNext
    (Expr.mux (.ref txValid) (.const uartTxCycles counterWidth)
    (Expr.mux (.ref isBusy)  (.ref busyCntDec)
      (.const 0 counterWidth)))

  -- =========================================================================
  -- Bus Read Mux
  -- =========================================================================
  -- Status register: bit 0 = tx_ready, bits [31:1] = 0
  -- We zero-extend tx_ready to 32 bits by placing it in a const-0 field
  let statusWord ← makeWire "status_word" (.bitVector 32)
  emitAssign statusWord (.concat [.const 0 31, .ref txReady])

  -- TX data register: zero-extended to 32 bits
  let txDataWord ← makeWire "txdata_word" (.bitVector 32)
  emitAssign txDataWord (.concat [.const 0 24, .ref txDataReg])

  -- Read mux: select based on address offset
  emitAssign "rdata"
    (Expr.mux (.ref isTxData) (.ref txDataWord)
    (Expr.mux (.ref isTxStatus) (.ref statusWord)
      (.const 0 32)))

/-- Build the UART module -/
def buildUART : Module :=
  CircuitM.runModule "RV32I_UART" do
    generateUART

end Sparkle.Examples.RV32.UART
