/-
  AXI4-Lite Master — Signal DSL Implementation

  Synthesizable AXI4-Lite master interface that drives transactions
  from a simple command interface (valid/write/addr/wdata/wstrb).

  FSM: Idle → WaitWriteResp / WaitReadResp → Idle
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.StateMacro

namespace Sparkle.IP.Bus.AXI4Lite.Master

-- FSM encoding
private abbrev stIdle          : BitVec 2 := 0#2
private abbrev stWaitWriteResp : BitVec 2 := 1#2
private abbrev stWaitReadResp  : BitVec 2 := 2#2

declare_signal_state AXI4LiteMasterState
  | fsm      : BitVec 2  := 0#2
  | addrReg  : BitVec 32 := 0#32
  | wdataReg : BitVec 32 := 0#32
  | wstrbReg : BitVec 4  := 0#4
  | rdataReg : BitVec 32 := 0#32   -- captured read response

/-- AXI4-Lite master loop body. -/
def axi4LiteMasterBody {dom : DomainConfig}
    (cmdValid : Signal dom Bool)
    (cmdWrite : Signal dom Bool)     -- true=write, false=read
    (cmdAddr  : Signal dom (BitVec 32))
    (cmdWdata : Signal dom (BitVec 32))
    (cmdWstrb : Signal dom (BitVec 4))
    -- AXI4-Lite response from slave
    (bvalid   : Signal dom Bool)
    (rvalid   : Signal dom Bool)
    (rdata    : Signal dom (BitVec 32))
    (state    : Signal dom AXI4LiteMasterState)
    : Signal dom AXI4LiteMasterState :=
  let fsm := AXI4LiteMasterState.fsm state
  let addrReg  := AXI4LiteMasterState.addrReg state
  let wdataReg := AXI4LiteMasterState.wdataReg state
  let wstrbReg := AXI4LiteMasterState.wstrbReg state
  let rdataReg := AXI4LiteMasterState.rdataReg state

  let isIdle := fsm === (stIdle : Signal dom _)
  let isWaitWrite := fsm === (stWaitWriteResp : Signal dom _)
  let isWaitRead  := fsm === (stWaitReadResp : Signal dom _)

  -- Accept command in Idle
  let doWrite := isIdle &&& cmdValid &&& cmdWrite
  let doRead  := isIdle &&& cmdValid &&& (~~~cmdWrite)
  let writeDone := isWaitWrite &&& bvalid
  let readDone  := isWaitRead &&& rvalid

  -- Next FSM
  let nextFsm := hw_cond (stIdle : Signal dom _)
    | doWrite => (stWaitWriteResp : Signal dom _)
    | doRead  => (stWaitReadResp : Signal dom _)
    | isWaitWrite &&& (~~~bvalid) => (stWaitWriteResp : Signal dom _)
    | isWaitRead  &&& (~~~rvalid) => (stWaitReadResp : Signal dom _)

  -- Latch command on acceptance
  let nextAddr  := Signal.mux (doWrite ||| doRead) cmdAddr addrReg
  let nextWdata := Signal.mux doWrite cmdWdata wdataReg
  let nextWstrb := Signal.mux doWrite cmdWstrb wstrbReg
  -- Capture read data on response
  let nextRdata := Signal.mux readDone rdata rdataReg

  bundleAll! [
    Signal.register stIdle nextFsm,
    Signal.register 0#32 nextAddr,
    Signal.register 0#32 nextWdata,
    Signal.register 0#4 nextWstrb,
    Signal.register 0#32 nextRdata
  ]

/-- AXI4-Lite master interface.

  Command inputs: cmdValid, cmdWrite, cmdAddr, cmdWdata, cmdWstrb
  AXI slave response inputs: bvalid, rvalid, rdata
  Outputs: (awaddr, awvalid, wdata, wstrb, wvalid, bready,
            araddr, arvalid, rready,
            cmdReady, respValid, respRdata) -/
def axi4LiteMaster {dom : DomainConfig}
    (cmdValid : Signal dom Bool)
    (cmdWrite : Signal dom Bool)
    (cmdAddr  : Signal dom (BitVec 32))
    (cmdWdata : Signal dom (BitVec 32))
    (cmdWstrb : Signal dom (BitVec 4))
    (bvalid   : Signal dom Bool)
    (rvalid   : Signal dom Bool)
    (rdata    : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (Bool × (BitVec 32 × (BitVec 4 × (Bool × (Bool ×
       (BitVec 32 × (Bool × (Bool × (Bool × (Bool × BitVec 32))))))))))) :=
  let state := Signal.loop (axi4LiteMasterBody cmdValid cmdWrite cmdAddr cmdWdata cmdWstrb bvalid rvalid rdata)

  let fsm := AXI4LiteMasterState.fsm state
  let addrReg  := AXI4LiteMasterState.addrReg state
  let wdataReg := AXI4LiteMasterState.wdataReg state
  let wstrbReg := AXI4LiteMasterState.wstrbReg state
  let rdataReg := AXI4LiteMasterState.rdataReg state

  let isIdle := fsm === (stIdle : Signal dom _)
  let isWaitWrite := fsm === (stWaitWriteResp : Signal dom _)
  let isWaitRead  := fsm === (stWaitReadResp : Signal dom _)

  -- AW channel: drive address when starting write
  let awaddrOut  := addrReg
  let awvalidOut := isWaitWrite
  -- W channel
  let wdataOut   := wdataReg
  let wstrbOut   := wstrbReg
  let wvalidOut  := isWaitWrite
  -- B channel: always ready to accept response
  let breadyOut  := isWaitWrite
  -- AR channel
  let araddrOut  := addrReg
  let arvalidOut := isWaitRead
  -- R channel: always ready to accept response
  let rreadyOut  := isWaitRead

  -- Command interface
  let cmdReady  := isIdle
  let respValid := (isWaitWrite &&& bvalid) ||| (isWaitRead &&& rvalid)
  let respRdata := rdataReg

  bundleAll! [awaddrOut, awvalidOut, wdataOut, wstrbOut, wvalidOut, breadyOut,
              araddrOut, arvalidOut, rreadyOut,
              cmdReady, respValid, respRdata]

-- Verify synthesis
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
#synthesizeVerilog axi4LiteMaster

end Sparkle.IP.Bus.AXI4Lite.Master
