/-
  AXI4-Lite Slave — Signal DSL Implementation

  Synthesizable AXI4-Lite slave interface that mirrors the proven
  FSM in IP.Bus.AXI4Lite.Props.

  Channels: AW (write address), W (write data), B (write response),
            AR (read address), R (read data/response)

  Design: AW+W accepted simultaneously, write priority over read.
  BRESP/RRESP = 2'b00 (OKAY) always.
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

namespace Sparkle.IP.Bus.AXI4Lite.Slave

-- FSM encoding
private abbrev stIdle      : BitVec 2 := 0#2
private abbrev stWriteResp : BitVec 2 := 1#2
private abbrev stReadResp  : BitVec 2 := 2#2

declare_signal_state AXI4LiteSlaveState
  | fsm      : BitVec 2  := 0#2    -- 0=Idle, 1=WriteResp, 2=ReadResp
  | addrReg  : BitVec 32 := 0#32   -- latched address
  | wdataReg : BitVec 32 := 0#32   -- latched write data
  | wstrbReg : BitVec 4  := 0#4    -- latched write strobe

/-- AXI4-Lite slave loop body. Extracted for reuse by simulation path. -/
def axi4LiteSlaveBody {dom : DomainConfig}
    (awaddr  : Signal dom (BitVec 32))
    (awvalid : Signal dom Bool)
    (wdata   : Signal dom (BitVec 32))
    (wstrb   : Signal dom (BitVec 4))
    (wvalid  : Signal dom Bool)
    (bready  : Signal dom Bool)
    (araddr  : Signal dom (BitVec 32))
    (arvalid : Signal dom Bool)
    (rready  : Signal dom Bool)
    (state   : Signal dom AXI4LiteSlaveState)
    : Signal dom AXI4LiteSlaveState :=
  let fsm := AXI4LiteSlaveState.fsm state
  let addrReg  := AXI4LiteSlaveState.addrReg state
  let wdataReg := AXI4LiteSlaveState.wdataReg state
  let wstrbReg := AXI4LiteSlaveState.wstrbReg state

  -- State decode
  let isIdle      := fsm === (stIdle : Signal dom _)
  let isWriteResp := fsm === (stWriteResp : Signal dom _)
  let isReadResp  := fsm === (stReadResp : Signal dom _)

  -- Transaction conditions
  let doWrite   := isIdle &&& awvalid &&& wvalid
  let doRead    := isIdle &&& arvalid &&& (~~~doWrite)  -- write priority
  let writeDone := isWriteResp &&& bready
  let readDone  := isReadResp &&& rready

  -- Next FSM state
  let nextFsm := hw_cond (stIdle : Signal dom _)
    | doWrite  => (stWriteResp : Signal dom _)
    | doRead   => (stReadResp : Signal dom _)
    | isWriteResp &&& (~~~bready) => (stWriteResp : Signal dom _)
    | isReadResp  &&& (~~~rready) => (stReadResp : Signal dom _)

  -- Latch address and data on acceptance
  let nextAddr  := Signal.mux (doWrite ||| doRead)
                    (Signal.mux doWrite awaddr araddr) addrReg
  let nextWdata := Signal.mux doWrite wdata wdataReg
  let nextWstrb := Signal.mux doWrite wstrb wstrbReg

  bundleAll! [
    Signal.register stIdle nextFsm,
    Signal.register 0#32 nextAddr,
    Signal.register 0#32 nextWdata,
    Signal.register 0#4 nextWstrb
  ]

/-- AXI4-Lite slave interface.

  Inputs: AXI4-Lite channel signals + memory read data.
  Outputs: (awready, wready, bvalid, arready, rvalid,
            memAddr, memWdata, memWstrb, memWe)

  BRESP/RRESP are always OKAY (2'b00).
  memRdata should be driven by the memory at memAddr. -/
def axi4LiteSlave {dom : DomainConfig}
    (awaddr  : Signal dom (BitVec 32))
    (awvalid : Signal dom Bool)
    (wdata   : Signal dom (BitVec 32))
    (wstrb   : Signal dom (BitVec 4))
    (wvalid  : Signal dom Bool)
    (bready  : Signal dom Bool)
    (araddr  : Signal dom (BitVec 32))
    (arvalid : Signal dom Bool)
    (rready  : Signal dom Bool)
    (memRdata : Signal dom (BitVec 32))
    : Signal dom (Bool × (Bool × (Bool × (Bool × (Bool ×
       (BitVec 32 × (BitVec 32 × (BitVec 4 × Bool)))))))) :=
  let state := Signal.loop (axi4LiteSlaveBody awaddr awvalid wdata wstrb wvalid bready araddr arvalid rready)

  let fsm := AXI4LiteSlaveState.fsm state
  let addrReg  := AXI4LiteSlaveState.addrReg state
  let wdataReg := AXI4LiteSlaveState.wdataReg state
  let wstrbReg := AXI4LiteSlaveState.wstrbReg state

  -- State decode
  let isIdle      := fsm === (stIdle : Signal dom _)
  let isWriteResp := fsm === (stWriteResp : Signal dom _)
  let isReadResp  := fsm === (stReadResp : Signal dom _)

  -- Channel outputs
  let awreadyOut := isIdle
  let wreadyOut  := isIdle
  let bvalidOut  := isWriteResp
  let arreadyOut := isIdle &&& (~~~(awvalid &&& wvalid))  -- write priority
  let rvalidOut  := isReadResp

  -- Memory interface: address, write data, write strobe, write enable
  let memAddr  := addrReg
  let memWdata := wdataReg
  let memWstrb := wstrbReg
  let memWe    := isWriteResp  -- write is committed when response is valid

  bundleAll! [awreadyOut, wreadyOut, bvalidOut, arreadyOut, rvalidOut,
              memAddr, memWdata, memWstrb, memWe]

-- Verify synthesis
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
#synthesizeVerilog axi4LiteSlave

end Sparkle.IP.Bus.AXI4Lite.Slave
