/-
  RV32I Supervisor-mode CSR Register File — Signal DSL

  Adds S-mode CSRs alongside the M-mode CSR file.
  Uses Signal.loop with 8 registers: privMode, sie, stvec, sscratch, sepc, scause, stval, satp.
  SSTATUS is a combinational masked view of mstatus (no separate register).
  Privilege mode transitions via trap/MRET/SRET.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.RV32.CSR.Types

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.RV32.CSR.Supervisor

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32.CSR

/-- CSR write value computation helper. -/
def mkCsrNewVal {dom : DomainConfig}
    (csrIsRW csrIsRS csrIsRC : Signal dom Bool)
    (csrWdata oldVal : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let rsVal := oldVal ||| csrWdata
  let rcVal := oldVal &&& (~~~csrWdata)
  Signal.mux csrIsRW csrWdata
    (Signal.mux csrIsRS rsVal (Signal.mux csrIsRC rcVal oldVal))

/-- S-mode CSR registers and privilege mode tracking — Signal DSL.

    Inputs:
      csrAddr[11:0]      - CSR address to read/write
      csrFunct3[2:0]     - CSR operation type
      csrWdata[31:0]     - Write data
      csrWE              - Write enable
      trapToS            - Trap targets S-mode
      trapCause[31:0]    - Trap cause code
      trapPC[31:0]       - PC of trapping instruction
      trapVal[31:0]      - Trap value
      sretTaken          - SRET strobe
      trapToM            - Trap targets M-mode (for priv update)
      mretTaken          - MRET strobe (for priv update)
      mstatusIn[31:0]    - Current mstatus value

    Output:
      (csr_rdata[31:0] × csr_hit × stvec_out[31:0] × sepc_out[31:0] ×
       satp_out[31:0] × priv_mode[1:0] × sstatus_write × sstatus_wdata[31:0]) -/
def supervisorCsrSignal {dom : DomainConfig}
    (csrAddr : Signal dom (BitVec 12))
    (csrFunct3 : Signal dom (BitVec 3))
    (csrWdata : Signal dom (BitVec 32))
    (csrWE : Signal dom Bool)
    (trapToS : Signal dom Bool)
    (trapCause : Signal dom (BitVec 32))
    (trapPC : Signal dom (BitVec 32))
    (trapVal : Signal dom (BitVec 32))
    (sretTaken : Signal dom Bool)
    (trapToM : Signal dom Bool)
    (mretTaken : Signal dom Bool)
    (mstatusIn : Signal dom (BitVec 32))
    : Signal dom (BitVec 32 × (Bool × (BitVec 32 × (BitVec 32 ×
       (BitVec 32 × (BitVec 2 × (Bool × BitVec 32))))))) :=
  -- CSR write type decode
  let csrF3Low := csrFunct3.map (BitVec.extractLsb' 0 2 ·)
  let csrIsRW := csrF3Low === 0b01#2
  let csrIsRS := csrF3Low === 0b10#2
  let csrIsRC := csrF3Low === 0b11#2
  let csrDoWrite := csrWE &&& (csrIsRW ||| (csrIsRS ||| csrIsRC))

  -- CSR address matching
  let isSstatus  := csrAddr === (BitVec.ofNat 12 csrSSTATUS)
  let isSie      := csrAddr === (BitVec.ofNat 12 csrSIE)
  let isStvec    := csrAddr === (BitVec.ofNat 12 csrSTVEC)
  let isSscratch := csrAddr === (BitVec.ofNat 12 csrSSCRATCH)
  let isSepc     := csrAddr === (BitVec.ofNat 12 csrSEPC)
  let isScause   := csrAddr === (BitVec.ofNat 12 csrSCAUSE)
  let isStval    := csrAddr === (BitVec.ofNat 12 csrSTVAL)
  let isSip      := csrAddr === (BitVec.ofNat 12 csrSIP)
  let isSatp     := csrAddr === (BitVec.ofNat 12 csrSATP)

  -- Combined hit signal
  let csrHit := ((isSstatus ||| isSie) ||| (isStvec ||| isSscratch)) |||
    ((isSepc ||| isScause) ||| (isStval ||| (isSip ||| isSatp)))

  -- SSTATUS: restricted view of mstatus
  -- sstatus exposes: SIE(1), SPIE(5), SPP(8), MXR(19), SUM(18)
  let sstatusMask : Signal dom (BitVec 32) := Signal.pure 0x000C0122#32  -- bits 1,5,8,18,19
  let sstatusView := mstatusIn &&& sstatusMask

  -- MPP and SPP for privilege mode transitions
  let mpp := mstatusIn.map (BitVec.extractLsb' 11 2 ·)
  let sppBit := mstatusIn.map (BitVec.extractLsb' 8 1 ·)
  let spp := 0#1 ++ sppBit

  let regs := Signal.loop fun state =>
    let privReg    := projN! state 8 0  -- BitVec 2
    let sieReg     := projN! state 8 1  -- BitVec 32
    let stvecReg   := projN! state 8 2  -- BitVec 32
    let sscratchReg := projN! state 8 3 -- BitVec 32
    let sepcReg    := projN! state 8 4  -- BitVec 32
    let scauseReg  := projN! state 8 5  -- BitVec 32
    let stvalReg   := projN! state 8 6  -- BitVec 32
    let satpReg    := projN! state 8 7  -- BitVec 32

    -- Privilege mode transitions
    let privNext := Signal.mux trapToM (Signal.pure (BitVec.ofNat 2 privM))
      (Signal.mux trapToS (Signal.pure (BitVec.ofNat 2 privS))
      (Signal.mux mretTaken mpp
      (Signal.mux sretTaken spp
        privReg)))

    -- CSR write values
    let sieNewCSR     := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata sieReg
    let stvecNewCSR   := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata stvecReg
    let sscratchNewCSR := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata sscratchReg
    let sepcNewCSR    := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata sepcReg
    let scauseNewCSR  := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata scauseReg
    let stvalNewCSR   := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata stvalReg
    let satpNewCSR    := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata satpReg

    -- Register updates
    let sieNext := Signal.mux (csrDoWrite &&& isSie) sieNewCSR sieReg
    let stvecNext := Signal.mux (csrDoWrite &&& isStvec) stvecNewCSR stvecReg
    let sscratchNext := Signal.mux (csrDoWrite &&& isSscratch) sscratchNewCSR sscratchReg
    let sepcNext := Signal.mux trapToS trapPC
      (Signal.mux (csrDoWrite &&& isSepc) sepcNewCSR sepcReg)
    let scauseNext := Signal.mux trapToS trapCause
      (Signal.mux (csrDoWrite &&& isScause) scauseNewCSR scauseReg)
    let stvalNext := Signal.mux trapToS trapVal
      (Signal.mux (csrDoWrite &&& isStval) stvalNewCSR stvalReg)
    let satpNext := Signal.mux (csrDoWrite &&& isSatp) satpNewCSR satpReg

    bundleAll! [
      Signal.register (BitVec.ofNat 2 privM) privNext,
      Signal.register 0#32 sieNext,
      Signal.register 0#32 stvecNext,
      Signal.register 0#32 sscratchNext,
      Signal.register 0#32 sepcNext,
      Signal.register 0#32 scauseNext,
      Signal.register 0#32 stvalNext,
      Signal.register 0#32 satpNext
    ]

  -- Extract registered state for outputs
  let privReg    := projN! regs 8 0
  let sieReg     := projN! regs 8 1
  let stvecReg   := projN! regs 8 2
  let sscratchReg := projN! regs 8 3
  let sepcReg    := projN! regs 8 4
  let scauseReg  := projN! regs 8 5
  let stvalReg   := projN! regs 8 6
  let satpReg    := projN! regs 8 7

  -- CSR read mux
  let csrRdata :=
    Signal.mux isSstatus sstatusView
    (Signal.mux isSie sieReg
    (Signal.mux isStvec stvecReg
    (Signal.mux isSscratch sscratchReg
    (Signal.mux isSepc sepcReg
    (Signal.mux isScause scauseReg
    (Signal.mux isStval stvalReg
    (Signal.mux isSip (Signal.pure 0#32)
    (Signal.mux isSatp satpReg
      (Signal.pure 0#32)))))))))

  -- SSTATUS write-back: merge S-mode bits into mstatus
  let sstatusWr := csrDoWrite &&& isSstatus
  let sstatusNewVal := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata sstatusView
  let mstatusNonS := mstatusIn &&& (~~~sstatusMask)
  let sstatusMasked := sstatusNewVal &&& sstatusMask
  let sstatusWdataOut := mstatusNonS ||| sstatusMasked

  bundleAll! [csrRdata, csrHit, stvecReg, sepcReg, satpReg, privReg, sstatusWr, sstatusWdataOut]

#synthesizeVerilog supervisorCsrSignal

end Sparkle.Examples.RV32.CSR.Supervisor
