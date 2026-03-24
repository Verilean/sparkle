/-
  Trap Delegation Logic — Signal DSL

  Extends trap handling for M→S delegation using medeleg/mideleg registers.
  Uses Signal.loop with 2 registers: medeleg, mideleg.
  When a trap cause bit is set in medeleg/mideleg and the current privilege
  is ≤ S, the trap is routed to the S-mode handler instead of M-mode.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Examples.RV32.CSR.Types

set_option maxRecDepth 4096

namespace Sparkle.Examples.RV32.Trap

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Examples.RV32.CSR

/-- CSR write value computation helper.
    Given current value and write data, compute new value based on funct3.
    csrIsRW/csrIsRS/csrIsRC indicate the operation type. -/
def mkCsrNewVal {dom : DomainConfig}
    (csrIsRW csrIsRS csrIsRC : Signal dom Bool)
    (csrWdata oldVal : Signal dom (BitVec 32))
    : Signal dom (BitVec 32) :=
  let rsVal := oldVal ||| csrWdata
  let rcVal := oldVal &&& ((fun x => ~~~ x) <$> csrWdata)
  Signal.mux csrIsRW csrWdata
    (Signal.mux csrIsRS rsVal (Signal.mux csrIsRC rcVal oldVal))

/-- Trap delegation unit — Signal DSL.

    Inputs:
      csrAddr[11:0]      - CSR address for medeleg/mideleg writes
      csrWdata[31:0]     - CSR write data
      csrWE              - CSR write enable
      csrFunct3[2:0]     - CSR operation type
      trapValid          - A trap is being taken
      trapCause[31:0]    - Trap cause code (bit 31 = interrupt)
      privMode[1:0]      - Current privilege mode
      mtvec[31:0]        - M-mode trap vector
      stvec[31:0]        - S-mode trap vector

    Output:
      (trap_to_m × trap_to_s × trap_target[31:0] ×
       medeleg_out[31:0] × mideleg_out[31:0] ×
       deleg_rdata[31:0] × deleg_hit) -/
def trapDelegSignal {dom : DomainConfig}
    (csrAddr : Signal dom (BitVec 12))
    (csrWdata : Signal dom (BitVec 32))
    (csrWE : Signal dom Bool)
    (csrFunct3 : Signal dom (BitVec 3))
    (trapValid : Signal dom Bool)
    (trapCause : Signal dom (BitVec 32))
    (privMode : Signal dom (BitVec 2))
    (mtvec : Signal dom (BitVec 32))
    (stvec : Signal dom (BitVec 32))
    : Signal dom (Bool × (Bool × (BitVec 32 × (BitVec 32 × (BitVec 32 ×
       (BitVec 32 × Bool)))))) :=
  -- CSR write type decode
  let csrF3Low := csrFunct3.map (BitVec.extractLsb' 0 2 ·)
  let csrIsRW := csrF3Low === 0b01#2
  let csrIsRS := csrF3Low === 0b10#2
  let csrIsRC := csrF3Low === 0b11#2
  -- Also handle CSRRWI/CSRRSI/CSRRCI (funct3[2]=1, same low 2 bits)
  let csrF3Hi := csrFunct3.map (BitVec.extractLsb' 2 1 ·)
  let csrIsRW_i := csrF3Low === 0b01#2
  let csrIsRS_i := csrF3Low === 0b10#2
  let csrIsRC_i := csrF3Low === 0b11#2
  let isRW := csrIsRW ||| csrIsRW_i
  let isRS := csrIsRS ||| csrIsRS_i
  let isRC := csrIsRC ||| csrIsRC_i
  let doWrite := csrWE &&& (isRW ||| (isRS ||| isRC))

  -- Address matching
  let isMedeleg := csrAddr === (BitVec.ofNat 12 csrMEDELEG)
  let isMideleg := csrAddr === (BitVec.ofNat 12 csrMIDELEG)

  let deleg := Signal.loop fun state =>
    let medelegReg := projN! state 2 0  -- BitVec 32
    let midelegReg := projN! state 2 1  -- BitVec 32

    let medelegNewVal := mkCsrNewVal isRW isRS isRC csrWdata medelegReg
    let midelegNewVal := mkCsrNewVal isRW isRS isRC csrWdata midelegReg

    let medelegWr := doWrite &&& isMedeleg
    let midelegWr := doWrite &&& isMideleg

    let medelegNext := Signal.mux medelegWr medelegNewVal medelegReg
    let midelegNext := Signal.mux midelegWr midelegNewVal midelegReg

    bundleAll! [
      Signal.register 0#32 medelegNext,
      Signal.register 0#32 midelegNext
    ]

  let medelegReg := projN! deleg 2 0
  let midelegReg := projN! deleg 2 1

  -- Delegation decision
  let isInterrupt := (· == ·) <$> (trapCause.map (BitVec.extractLsb' 31 1 ·)) <*> Signal.pure 1#1
  let causeIdx := trapCause.map (BitVec.extractLsb' 0 5 ·)
  let causeIdxExt := (· ++ ·) <$> Signal.pure 0#27 <*> causeIdx

  -- Check delegation bit: (deleg_reg >>> cause_idx)[0]
  let medelegShifted := (· >>> ·) <$> medelegReg <*> causeIdxExt
  let medelegBit := (· == ·) <$> (medelegShifted.map (BitVec.extractLsb' 0 1 ·)) <*> Signal.pure 1#1
  let midelegShifted := (· >>> ·) <$> midelegReg <*> causeIdxExt
  let midelegBit := (· == ·) <$> (midelegShifted.map (BitVec.extractLsb' 0 1 ·)) <*> Signal.pure 1#1

  let delegated := Signal.mux isInterrupt midelegBit medelegBit

  -- Trap goes to S-mode if: delegated AND current_priv ≤ S
  let privGtS := (BitVec.ult · ·) <$> Signal.pure (BitVec.ofNat 2 privS) <*> privMode
  let privLeS := ~~~privGtS
  let toSmode := trapValid &&& (delegated &&& privLeS)
  let toMmode := trapValid &&& ((fun s => !s) <$> toSmode)

  -- Trap target: clear bottom 2 bits of tvec
  let mtvecBase := mtvec &&& 0xFFFFFFFC#32
  let stvecBase := stvec &&& 0xFFFFFFFC#32
  let trapTarget := Signal.mux toSmode stvecBase mtvecBase

  -- CSR read
  let delegHit := isMedeleg ||| isMideleg
  let delegRdata := Signal.mux isMedeleg medelegReg
    (Signal.mux isMideleg midelegReg (Signal.pure 0#32))

  bundleAll! [toMmode, toSmode, trapTarget, medelegReg, midelegReg, delegRdata, delegHit]

#synthesizeVerilog trapDelegSignal

end Sparkle.Examples.RV32.Trap
