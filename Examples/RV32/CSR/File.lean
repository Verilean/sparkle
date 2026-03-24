/-
  RV32I CSR Register File — Signal DSL

  Implements M-mode CSR registers with read/write/trap logic.
  Uses Signal.loop with 7 registers: mstatus, mie, mtvec, mscratch, mepc, mcause, mtval.
  Supports CSRRW, CSRRS, CSRRC operations, trap entry, and MRET.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.RV32.CSR.Types

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace Sparkle.Examples.RV32.CSR.File

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32.CSR

/-- CSR write value computation helper.
    Given current value and write data, compute new value based on RW/RS/RC. -/
def mkCsrNewVal {dom : DomainConfig}
    (csrIsRW csrIsRS csrIsRC : Signal dom Bool)
    (csrWdata oldVal : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let rsVal := oldVal ||| csrWdata
  let rcVal := oldVal &&& ((fun x => ~~~ x) <$> csrWdata)
  Signal.mux csrIsRW csrWdata
    (Signal.mux csrIsRS rsVal (Signal.mux csrIsRC rcVal oldVal))

/-- M-mode CSR register file — Signal DSL.

    Inputs:
      csrAddr[11:0]      - CSR address to read/write
      csrFunct3[2:0]     - CSR operation type
      csrWdata[31:0]     - Write data (rs1 value or zimm)
      csrWE              - CSR write enable
      trapTaken          - Trap entry strobe
      trapCause[31:0]    - Cause code for trap
      trapPC[31:0]       - PC of trapping instruction
      trapVal[31:0]      - Trap value
      mretTaken          - MRET strobe
      extTimerIrq        - Timer interrupt from CLINT
      extSwIrq           - Software interrupt from CLINT

    Output:
      (csr_rdata[31:0] × mtvec_out[31:0] × mepc_out[31:0] ×
       mstatus_mie × mie_mtie × mie_msie × mip_mtip × mip_msip) -/
def csrFileSignal {dom : DomainConfig}
    (csrAddr : Signal dom (BitVec 12))
    (csrFunct3 : Signal dom (BitVec 3))
    (csrWdata : Signal dom (BitVec 32))
    (csrWE : Signal dom Bool)
    (trapTaken : Signal dom Bool)
    (trapCause : Signal dom (BitVec 32))
    (trapPC : Signal dom (BitVec 32))
    (trapVal : Signal dom (BitVec 32))
    (mretTaken : Signal dom Bool)
    (extTimerIrq : Signal dom Bool)
    (extSwIrq : Signal dom Bool)
    : Signal dom (BitVec 32 × (BitVec 32 × (BitVec 32 ×
       (Bool × (Bool × (Bool × (Bool × Bool))))))) :=
  -- CSR write type decode
  let csrF3Low := csrFunct3.map (BitVec.extractLsb' 0 2 ·)
  let csrIsRW := csrF3Low === 0b01#2
  let csrIsRS := csrF3Low === 0b10#2
  let csrIsRC := csrF3Low === 0b11#2
  let csrDoWrite := csrWE &&& (csrIsRW ||| (csrIsRS ||| csrIsRC))

  -- CSR address matching
  let isMstatus  := csrAddr === (BitVec.ofNat 12 csrMSTATUS)
  let isMie      := csrAddr === (BitVec.ofNat 12 csrMIE)
  let isMtvec    := csrAddr === (BitVec.ofNat 12 csrMTVEC)
  let isMscratch := csrAddr === (BitVec.ofNat 12 csrMSCRATCH)
  let isMepc     := csrAddr === (BitVec.ofNat 12 csrMEPC)
  let isMcause   := csrAddr === (BitVec.ofNat 12 csrMCAUSE)
  let isMtval    := csrAddr === (BitVec.ofNat 12 csrMTVAL)
  let isMip      := csrAddr === (BitVec.ofNat 12 csrMIP)
  let isMisa     := csrAddr === (BitVec.ofNat 12 csrMISA)
  let isMhartid  := csrAddr === (BitVec.ofNat 12 csrMHARTID)

  -- MIP value (read-only, driven by external interrupts)
  let mipTimerBit := Signal.mux extTimerIrq (Signal.pure 0x00000080#32) (Signal.pure 0#32)
  let mipSwBit := Signal.mux extSwIrq (Signal.pure 0x00000008#32) (Signal.pure 0#32)
  let mipValue := mipTimerBit ||| mipSwBit

  let csrFile := Signal.loop fun state =>
    let mstatusReg  := projN! state 7 0  -- BitVec 32
    let mieReg      := projN! state 7 1  -- BitVec 32
    let mtvecReg    := projN! state 7 2  -- BitVec 32
    let mscratchReg := projN! state 7 3  -- BitVec 32
    let mepcReg     := projN! state 7 4  -- BitVec 32
    let mcauseReg   := projN! state 7 5  -- BitVec 32
    let mtvalReg    := projN! state 7 6  -- BitVec 32

    -- CSR write values
    let mstatusNewCSR  := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata mstatusReg
    let mieNewCSR      := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata mieReg
    let mtvecNewCSR    := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata mtvecReg
    let mscratchNewCSR := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata mscratchReg
    let mepcNewCSR     := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata mepcReg
    let mcauseNewCSR   := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata mcauseReg
    let mtvalNewCSR    := mkCsrNewVal csrIsRW csrIsRS csrIsRC csrWdata mtvalReg

    -- Current MIE and MPIE bits for MSTATUS
    let mstatusMIE_flag := (· == ·) <$> (mstatusReg.map (BitVec.extractLsb' 3 1 ·)) <*> Signal.pure 1#1
    let mstatusMPIE_flag := (· == ·) <$> (mstatusReg.map (BitVec.extractLsb' 7 1 ·)) <*> Signal.pure 1#1

    -- MSTATUS on trap: MPIE←MIE, MIE←0, MPP←11 (M-mode)
    let msClearMIE := mstatusReg &&& 0xFFFFFFF7#32
    let msSetMPIE := Signal.mux mstatusMIE_flag
      (msClearMIE ||| 0x00000080#32)
      (msClearMIE &&& 0xFFFFFF7F#32)
    let mstatusTrapVal := msSetMPIE ||| 0x00001800#32

    -- MSTATUS on MRET: MIE←MPIE, MPIE←1, MPP←00
    let msClearMPP := mstatusReg &&& 0xFFFFE7FF#32
    let msRestoreMIE := Signal.mux mstatusMPIE_flag
      (msClearMPP ||| 0x00000008#32)
      (msClearMPP &&& 0xFFFFFFF7#32)
    let mstatusMretVal := msRestoreMIE ||| 0x00000080#32

    -- MSTATUS: trap > MRET > CSR write > hold
    let mstatusNext := Signal.mux trapTaken mstatusTrapVal
      (Signal.mux mretTaken mstatusMretVal
      (Signal.mux (csrDoWrite &&& isMstatus) mstatusNewCSR
        mstatusReg))
    let mieNext := Signal.mux (csrDoWrite &&& isMie) mieNewCSR mieReg
    let mtvecNext := Signal.mux (csrDoWrite &&& isMtvec) mtvecNewCSR mtvecReg
    let mscratchNext := Signal.mux (csrDoWrite &&& isMscratch) mscratchNewCSR mscratchReg
    let mepcNext := Signal.mux trapTaken trapPC
      (Signal.mux (csrDoWrite &&& isMepc) mepcNewCSR mepcReg)
    let mcauseNext := Signal.mux trapTaken trapCause
      (Signal.mux (csrDoWrite &&& isMcause) mcauseNewCSR mcauseReg)
    let mtvalNext := Signal.mux trapTaken trapVal
      (Signal.mux (csrDoWrite &&& isMtval) mtvalNewCSR mtvalReg)

    bundleAll! [
      Signal.register 0#32 mstatusNext,
      Signal.register 0#32 mieNext,
      Signal.register 0#32 mtvecNext,
      Signal.register 0#32 mscratchNext,
      Signal.register 0#32 mepcNext,
      Signal.register 0#32 mcauseNext,
      Signal.register 0#32 mtvalNext
    ]

  -- Extract registered state for outputs
  let mstatusReg := projN! csrFile 7 0
  let mieReg     := projN! csrFile 7 1
  let mtvecReg   := projN! csrFile 7 2
  let mepcReg    := projN! csrFile 7 4

  -- CSR read mux
  let csrRdata :=
    Signal.mux isMstatus mstatusReg
    (Signal.mux isMie mieReg
    (Signal.mux isMtvec mtvecReg
    (Signal.mux isMscratch (projN! csrFile 7 3)
    (Signal.mux isMepc mepcReg
    (Signal.mux isMcause (projN! csrFile 7 5)
    (Signal.mux isMtval (projN! csrFile 7 6)
    (Signal.mux isMip mipValue
    (Signal.mux isMisa (Signal.pure (BitVec.ofNat 32 misaValue))
    (Signal.mux isMhartid (Signal.pure 0#32)
      (Signal.pure 0#32))))))))))

  -- Output signals
  let mstatusMIE := (· == ·) <$> (mstatusReg.map (BitVec.extractLsb' 3 1 ·)) <*> Signal.pure 1#1
  let mieMTIE := (· == ·) <$> (mieReg.map (BitVec.extractLsb' 7 1 ·)) <*> Signal.pure 1#1
  let mieMSIE := (· == ·) <$> (mieReg.map (BitVec.extractLsb' 3 1 ·)) <*> Signal.pure 1#1
  let mipMTIP := (· == ·) <$> (mipValue.map (BitVec.extractLsb' 7 1 ·)) <*> Signal.pure 1#1
  let mipMSIP := (· == ·) <$> (mipValue.map (BitVec.extractLsb' 3 1 ·)) <*> Signal.pure 1#1

  bundleAll! [csrRdata, mtvecReg, mepcReg, mstatusMIE, mieMTIE, mieMSIE, mipMTIP, mipMSIP]

#synthesizeVerilog csrFileSignal

end Sparkle.Examples.RV32.CSR.File
