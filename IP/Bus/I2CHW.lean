/-
  IP.Bus.I2CHW — I2C master HW building blocks.

  Implements the master-side FSM the way a small mem-mapped
  controller would drive an I2C bus:

      idle → start → addr (8 clock pulses) → ack → data
        → ack → stop → idle

  Simplifications vs a full production I2C master:
    * 7-bit addressing only (10-bit variant is a separate mode
      the FSM can be extended to later).
    * Fixed clock divider `bitDiv` passed in from outside (one
      divider period = bitDiv+1 cycles = one SCL half-period).
      Standard-mode (100 kHz) at 100 MHz sys clock ⇒ bitDiv = 500.
    * `addr`, `rw` and `dataByte` are latched on the cycle of the
      accepted `start` pulse (any idle cycle, not only a divider
      tick); later changes are ignored.  A `start` while busy is
      ignored.  The FSM does a single-byte write (SDA carries the
      data byte also when rw = 1; there is no read capture).
    * ACK from slave is captured but the FSM continues
      unconditionally.

  Wiring:
      start      : Bool — pulse to begin a transaction
      addr       : BitVec 7 — target slave address
      dataByte   : BitVec 8 — byte to transmit (write mode)
      rw         : Bool — 0 = write, 1 = read
      bitDiv     : BitVec 16 — cycles per SCL half-period − 1
      sdaFromBus : Bool — sampled SDA line (for ACK read)

      state      : BitVec 3 — current FSM state (visible for
                              downstream mux/probe)
      scl        : Bool — SCL line driven by master
      sda        : Bool — SDA line driven by master (open-drain
                          convention: this is the drive-low
                          enable; a real IO ring would OR with
                          a pull-up)
      busy       : Bool — high while transaction in progress

  Bus waveform (one slot = two half-periods, e = bitDiv+1 cycles each):
    idle      SCL=1 SDA=1
    startC    SCL=1 SDA=0            (START: SDA falls while SCL high)
    bit slot  SCL=0 SDA=bit | SCL=1 SDA=bit   (SDA changes only while
              SCL is low and is sampled at the SCL rise); 8 addr/rw
              bits, ack slot (SDA released), 8 data bits, ack slot
    stopC     SCL=0 SDA=0 | SCL=1 SDA=0, then idle: SDA rises while SCL
              high (STOP).  busy = state /= idle: 39 half-periods.
  SDA changes on the same cycle as the SCL fall (no extra hold phase).

  State encoding (3-bit):
    0 = idle
    1 = start-cond
    2 = addrPhase
    3 = ackAddr
    4 = dataPhase
    5 = ackData
    6 = stopCond
    7 = (reserved)

  Validation: instantiate the FSM, walk it for a few dozen
  cycles, and confirm the state trajectory + SCL toggle
  pattern make sense.  A real cycle-accurate against
  pure-data reference would require the pure-data reference
  to also emit per-half-cycle bus events, which
  `IP.Bus.I2C.buildTransaction` doesn't do; we exercise
  behaviour instead.
-/
import Sparkle

namespace Sparkle.IP.Bus.I2CHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

structure MasterOut (dom : DomainConfig) where
  state : Signal dom (BitVec 3)
  scl   : Signal dom Bool
  sda   : Signal dom Bool
  busy  : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MasterOut dom) dom := ⟨⟩

/-- I2C master single-byte transaction FSM.

    18 SCL pulses for 8 addr/rw + ack + 8 data + ack, each bit slot
    split in an SCL-low and an SCL-high half; START is one SCL-high
    half with SDA low, STOP is an SCL-low and an SCL-high half with
    SDA low, then SDA is released.  The divider ticks once per half;
    `phR` marks the SCL-high half and the state advances at its end. -/
def i2cMasterHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16))
    (addr : Signal dom (BitVec 7))
    (rw : Signal dom Bool)
    (dataByte : Signal dom (BitVec 8))
    (sdaFromBus : Signal dom Bool) :
    MasterOut dom :=
  circuit do
    let stR ← Signal.reg (0#3)
    -- Bit counter within a byte (0..7).
    let bitCntR ← Signal.reg (0#4)
    -- Clock divider countdown (one tick per half-slot).
    let divR ← Signal.reg (0#16)
    -- Half-slot phase: false = SCL low half, true = SCL high half.
    let phR ← Signal.reg false
    -- Shift register (address byte, then data byte), MSB drives SDA.
    let shiftR ← Signal.reg (0x1FF#9)
    -- Data byte latched at the start pulse.
    let dataR ← Signal.reg (0#8)
    -- Captured ACK.
    let ackR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 3))
    let bcSig := (bitCntR : Signal dom (BitVec 4))
    let dcSig := (divR : Signal dom (BitVec 16))
    let phSig := (phR : Signal dom Bool)
    let shSig := (shiftR : Signal dom (BitVec 9))
    let dataSig := (dataR : Signal dom (BitVec 8))
    let _ackSig := (ackR : Signal dom Bool)

    let stIdle    := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let stStartC  := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let stAddr    := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let stAckA    := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let stData    := (Signal.pure 4#3 : Signal dom (BitVec 3))
    let stAckD    := (Signal.pure 5#3 : Signal dom (BitVec 3))
    let stStopC   := (Signal.pure 6#3 : Signal dom (BitVec 3))
    let p0_4      := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let p1_4      := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let p7_4      := (Signal.pure 7#4 : Signal dom (BitVec 4))
    let p0_16     := (Signal.pure 0#16 : Signal dom (BitVec 16))
    let p1_16     := (Signal.pure 1#16 : Signal dom (BitVec 16))
    let p0_9      := (Signal.pure 0#9 : Signal dom (BitVec 9))
    let p1_9      := (Signal.pure 1#9 : Signal dom (BitVec 9))
    let pMSB_9    := (Signal.pure 0x100#9 : Signal dom (BitVec 9))
    let sigTrue   := (Signal.pure true : Signal dom Bool)

    let tick := (dcSig === p0_16 : Signal dom Bool)

    let rwBit := Signal.mux rw (Signal.pure 1#1) (Signal.pure 0#1)
    let addrRw := (addr ++ rwBit : Signal dom (BitVec 8))
    let addrShift := (addrRw ++ 1#1 : Signal dom (BitVec 9))
    let dataShift := (dataSig ++ 1#1 : Signal dom (BitVec 9))

    let isIdle := (stSig === stIdle : Signal dom Bool)
    let isStartC := (stSig === stStartC : Signal dom Bool)
    let isAddr := (stSig === stAddr : Signal dom Bool)
    let isAckA := (stSig === stAckA : Signal dom Bool)
    let isData := (stSig === stData : Signal dom Bool)
    let isAckD := (stSig === stAckD : Signal dom Bool)
    let isStopC := (stSig === stStopC : Signal dom Bool)
    let inCountingPhase := (isAddr ||| isData : Signal dom Bool)
    let inAck := (isAckA ||| isAckD : Signal dom Bool)
    let bcAtMax := (bcSig === p7_4 : Signal dom Bool)

    -- A start pulse is accepted on ANY idle cycle (not only on a divider tick).
    let startNow := (isIdle &&& start : Signal dom Bool)
    -- A half-slot ends on a divider tick while a transaction runs; the slot
    -- ends (state advances) at the end of the SCL-high half.
    let advance := (tick &&& phSig : Signal dom Bool)

    -- Next state.  startC → addr after one half-slot; each bit / ack / stop slot
    -- is two half-slots (low then high); stopC → idle ends the transaction.
    let s1next := stAddr
    let s2next := Signal.mux bcAtMax stAckA stAddr
    let s3next := stData
    let s4next := Signal.mux bcAtMax stAckD stData
    let s5next := stStopC
    let s6next := stIdle
    let slotNext :=
      Signal.mux isAddr s2next
        (Signal.mux isAckA s3next
          (Signal.mux isData s4next
            (Signal.mux isAckD s5next
              (Signal.mux isStopC s6next stSig))))
    let stRunning :=
      Signal.mux isStartC (Signal.mux tick s1next stSig)
        (Signal.mux advance slotNext stSig)
    let stNext := Signal.mux isIdle (Signal.mux start stStartC stIdle) stRunning
    stR <~ stNext

    -- Phase: toggles on each tick while a transaction runs, except the start
    -- half-slot (SCL high) which is followed by a low half.
    let phToggle := Signal.mux tick (~~~phSig : Signal dom Bool) phSig
    let phRunning := Signal.mux isStartC (Signal.pure false) phToggle
    phR <~ Signal.mux isIdle (Signal.pure false) phRunning

    -- Bit counter: counts at the end of each high half in addr / data.
    let bcInc := (bcSig + p1_4 : Signal dom (BitVec 4))
    let bcOnAdv := Signal.mux bcAtMax p0_4 bcInc
    let bcRun := Signal.mux (advance &&& inCountingPhase : Signal dom Bool) bcOnAdv bcSig
    bitCntR <~ Signal.mux isIdle p0_4 bcRun

    -- Divider: reload on the accepted start pulse and on every tick.
    let dcDec := (dcSig - p1_16 : Signal dom (BitVec 16))
    let dcNext := Signal.mux tick bitDiv dcDec
    divR <~ Signal.mux startNow bitDiv dcNext

    -- Latch data at the start pulse; load the address byte into the shifter at
    -- the same time; load data into the shifter at the end of the address ACK.
    dataR <~ Signal.mux startNow dataByte dataSig
    let loadData := (advance &&& isAckA : Signal dom Bool)
    let shiftLeft := (shSig <<< p1_9 : Signal dom (BitVec 9))
    let shiftRun :=
      Signal.mux loadData dataShift
        (Signal.mux (advance &&& inCountingPhase : Signal dom Bool) shiftLeft shSig)
    shiftR <~ Signal.mux startNow addrShift shiftRun

    -- SDA: idle / ack slots released (high); START and STOP slots low; bit slots
    -- carry the shift MSB (changes only in the SCL low half, see `phR`).
    let msbAnd := (shSig &&& pMSB_9 : Signal dom (BitVec 9))
    let msbIsZero := (msbAnd === p0_9 : Signal dom Bool)
    let msbBit := (~~~msbIsZero : Signal dom Bool)
    let pullLow := (isStartC ||| isStopC : Signal dom Bool)
    let sdaOut :=
      Signal.mux pullLow (Signal.pure false)
        (Signal.mux inCountingPhase msbBit sigTrue)

    -- SCL: high in idle and the start slot; otherwise high only in the high half.
    let sclOut := (isIdle ||| isStartC ||| phSig : Signal dom Bool)

    -- Latch ACK (active-low SDA) at the end of the SCL-high half of an ack slot.
    let ackLoad := (advance &&& inAck : Signal dom Bool)
    let ackReceived := (~~~sdaFromBus : Signal dom Bool)
    ackR <~ Signal.mux ackLoad ackReceived _ackSig

    let busy := (~~~isIdle : Signal dom Bool)

    return ({ state := stSig, scl := sclOut, sda := sdaOut, busy := busy } : MasterOut dom)

end Sparkle.IP.Bus.I2CHW
