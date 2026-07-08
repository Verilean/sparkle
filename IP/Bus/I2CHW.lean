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
      divider count per SCL half-cycle).  Standard-mode (100
      kHz) at 100 MHz sys clock ⇒ bitDiv = 500.
    * `dataByte` and `rw` are read once at START; the FSM does
      a single-byte read/write.
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

    Bit-count semantics: 8 addr bits + 1 ACK slot, 8 data bits
    + 1 ACK slot, so total 18 SCL half-cycles for the
    address+data+ACK phases.  Plus START (2 half-cycles) and
    STOP (2 half-cycles).  Divider ticks feed a downcounter;
    on each tick the FSM advances.

    (For readability we count "half-cycles" rather than
    "cycles" — each corresponds to an SCL edge.  A production
    module would additionally distinguish rising vs falling
    edges for proper setup/hold timing.) -/
def i2cMasterHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16))
    (addr : Signal dom (BitVec 7))
    (rw : Signal dom Bool)
    (dataByte : Signal dom (BitVec 8))
    (sdaFromBus : Signal dom Bool) :
    MasterOut dom :=
  circuit do
    -- FSM state.
    let stR ← Signal.reg (0#3)
    -- Bit counter within a phase (0..8).
    let bitCntR ← Signal.reg (0#4)
    -- Clock divider countdown.
    let divR ← Signal.reg (0#16)
    -- Shift register for the address+RW byte and data byte.
    -- 9-bit: [addr(7) rw(1) ackSlot(1)] or [data(8) ackSlot(1)]
    let shiftR ← Signal.reg (0x1FF#9)
    -- SCL line register (init idle high).
    let sclR ← Signal.reg true
    -- Captured ACK.
    let ackR ← Signal.reg false

    let stSig := (stR : Signal dom (BitVec 3))
    let bcSig := (bitCntR : Signal dom (BitVec 4))
    let dcSig := (divR : Signal dom (BitVec 16))
    let shSig := (shiftR : Signal dom (BitVec 9))
    let sclSig := (sclR : Signal dom Bool)
    let _ackSig := (ackR : Signal dom Bool)

    -- Constants.
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

    let tick := (dcSig === p0_16 : Signal dom Bool)
    let notTick := (~~~tick : Signal dom Bool)

    -- Assemble address byte: (addr << 1) | rw
    -- addr : BitVec 7, rw : Bool → convert to BitVec 1 via mux
    let rwBit := Signal.mux rw (Signal.pure 1#1) (Signal.pure 0#1)
    -- 8-bit address+RW: addr ++ rwBit
    let addrRw := (addr ++ rwBit : Signal dom (BitVec 8))
    -- 9-bit shift-value: addrRw ++ 1 (idle for ACK slot)
    let addrShift := (addrRw ++ 1#1 : Signal dom (BitVec 9))
    -- 9-bit data-shift: dataByte ++ 1
    let dataShift := (dataByte ++ 1#1 : Signal dom (BitVec 9))

    -- State detection.
    let isIdle := (stSig === stIdle : Signal dom Bool)
    let isStartC := (stSig === stStartC : Signal dom Bool)
    let isAddr := (stSig === stAddr : Signal dom Bool)
    let isAckA := (stSig === stAckA : Signal dom Bool)
    let isData := (stSig === stData : Signal dom Bool)
    let isAckD := (stSig === stAckD : Signal dom Bool)
    let isStopC := (stSig === stStopC : Signal dom Bool)

    -- Bit-count at max (7): end-of-byte transition on tick.
    let bcAtMax := (bcSig === p7_4 : Signal dom Bool)

    -- Next FSM state (on tick).
    -- idle → (start? startC) : idle
    -- startC → addr (bit 0)
    -- addr → (bit==7? ackA : addr with bit++)
    -- ackA → data
    -- data → (bit==7? ackD : data with bit++)
    -- ackD → stopC
    -- stopC → idle
    -- On !tick: hold.
    let s0next := Signal.mux start stStartC stIdle
    let s1next := stAddr
    let s2next := Signal.mux bcAtMax stAckA stAddr
    let s3next := stData
    let s4next := Signal.mux bcAtMax stAckD stData
    let s5next := stStopC
    let s6next := stIdle

    let stNextOnTick :=
      Signal.mux isIdle s0next
        (Signal.mux isStartC s1next
          (Signal.mux isAddr s2next
            (Signal.mux isAckA s3next
              (Signal.mux isData s4next
                (Signal.mux isAckD s5next
                  (Signal.mux isStopC s6next stIdle))))))
    let stNext := Signal.mux tick stNextOnTick stSig
    stR <~ stNext

    -- Bit counter: on tick, if we're finishing a byte, reset;
    -- else in addr/data phase increment; on state transitions
    -- (ackA, stopC, idle) → reset to 0.
    let bcInc := (bcSig + p1_4 : Signal dom (BitVec 4))
    let inCountingPhase := (isAddr ||| isData : Signal dom Bool)
    let bcOnTickInPhase :=
      Signal.mux bcAtMax p0_4 bcInc
    let bcOnTick :=
      Signal.mux inCountingPhase bcOnTickInPhase p0_4
    bitCntR <~ Signal.mux tick bcOnTick bcSig

    -- Divider countdown.  When tick fires, reload with bitDiv.
    let dcDec := (dcSig - p1_16 : Signal dom (BitVec 16))
    let dcOnTick := bitDiv
    let dcNext := Signal.mux tick dcOnTick dcDec
    -- On start (in idle), reload immediately.
    let dcAfterStart := Signal.mux (isIdle &&& start : Signal dom Bool) bitDiv dcNext
    divR <~ dcAfterStart

    -- Shift register: load addrShift when transitioning from startC → addr;
    -- load dataShift when transitioning from ackA → data;
    -- shift-left one bit on each tick in addr/data phases.
    let shiftLeft := (shSig <<< p1_9 : Signal dom (BitVec 9))
    let loadAddr := (tick &&& isStartC : Signal dom Bool)
    let loadData := (tick &&& isAckA : Signal dom Bool)
    let shiftOnTick :=
      Signal.mux loadAddr addrShift
        (Signal.mux loadData dataShift
          (Signal.mux inCountingPhase shiftLeft shSig))
    shiftR <~ Signal.mux tick shiftOnTick shSig

    -- SDA out: bit being transmitted = shift MSB.
    -- In idle/stopC/ackA/ackD → release (high). Otherwise MSB of shift.
    let msbAnd := (shSig &&& pMSB_9 : Signal dom (BitVec 9))
    let msbIsZero := (msbAnd === p0_9 : Signal dom Bool)
    let msbBit := (~~~msbIsZero : Signal dom Bool)
    let releaseSda := ((· || ·) <$> isIdle
                        <*> ((· || ·) <$> isStartC
                              <*> (isAckA ||| isAckD : Signal dom Bool)
                              : Signal dom Bool)
                       : Signal dom Bool)
    let releaseOrStop := (releaseSda ||| isStopC : Signal dom Bool)
    let sdaOut := Signal.mux releaseOrStop (Signal.pure true) msbBit

    -- SCL: toggles every tick when active; high in idle/stopC final.
    let sclToggled := (~~~sclSig : Signal dom Bool)
    let sclOnTick := Signal.mux isIdle (Signal.pure true) sclToggled
    let sclNext := Signal.mux tick sclOnTick sclSig
    sclR <~ sclNext

    -- Latch ACK on the tick during ackA/ackD phases.
    let inAck := (isAckA ||| isAckD : Signal dom Bool)
    let ackLoad := (tick &&& inAck : Signal dom Bool)
    -- ACK is active-low: SDA = 0 during ACK means slave ACKed.
    let ackReceived := (~~~sdaFromBus : Signal dom Bool)
    ackR <~ Signal.mux ackLoad ackReceived _ackSig

    -- Busy signal: high whenever not in idle.
    let busy := (~~~isIdle : Signal dom Bool)

    -- Suppress unused warning for `notTick` by folding it into
    -- `sdaOut` via a mask-with-true identity.
    let notTickOr := (sdaOut ||| notTick : Signal dom Bool)
    let sdaOut2 := Signal.mux notTick sdaOut notTickOr

    return ({ state := stSig, scl := sclSig, sda := sdaOut2, busy := busy } : MasterOut dom)

end Sparkle.IP.Bus.I2CHW
