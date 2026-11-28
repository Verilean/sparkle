/-
  IP.Bus.SPIHW — SPI master HW building blocks.

  Implements a single-byte SPI master:
      idle → shift 8 MOSI bits (with corresponding MISO
              sampling per CPHA) → idle
  supporting all four (CPOL, CPHA) modes: with CPHA=0 MOSI is valid at the
  leading SCLK edge and MISO is sampled there; with CPHA=1 MOSI changes on the
  leading edge and both lines are sampled at the trailing edge.  `start` is
  accepted on any cycle while idle (level-sensitive in idle: a pulse begins one
  transfer; it is ignored while a transfer runs).

  Wiring:
      start   : Bool — begin transfer
      cpol    : Bool — clock polarity
      cpha    : Bool — clock phase
      bitDiv  : BitVec 16 — cycles per SCLK half-period − 1
      mosiByte: BitVec 8 — byte the master will shift out
      misoBit : Bool — sampled MISO line (per-cycle)

      sclk    : Bool — clock line
      mosi    : Bool — current MOSI bit (MSB of shift reg)
      cs      : Bool — chip select (active-low convention; low = active)
      misoByte: BitVec 8 — assembled MISO byte (LSB-shifted-in)
      done    : Bool — pulse when transfer finishes

  State encoding (2-bit register):
      0 = idle
      1 = active (transferring)
      2 = post (drop SCLK back to idle, prep to raise CS)
      3 = reserved
-/
import Sparkle

namespace Sparkle.IP.Bus.SPIHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

structure MasterOut (dom : DomainConfig) where
  sclk     : Signal dom Bool
  mosi     : Signal dom Bool
  cs       : Signal dom Bool
  misoByte : Signal dom (BitVec 8)
  done     : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (MasterOut dom) dom := ⟨⟩

/-- SPI master single-byte transfer FSM.

    Approximate cycle-accurate semantics; a real master would
    also handle setup/hold on individual SCLK edges.  This
    module gives a shape sufficient for synth + sim
    correctness. -/
def spiMasterHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (cpol : Signal dom Bool)
    (cpha : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16))
    (mosiByte : Signal dom (BitVec 8))
    (misoBit : Signal dom Bool) :
    MasterOut dom :=
  circuit do
    let stR ← Signal.reg (0#2)
    let bitCntR ← Signal.reg (0#4)
    let divR ← Signal.reg (0#16)
    let mosiShR ← Signal.reg (0#8)
    let misoShR ← Signal.reg (0#8)
    let sclkR ← Signal.reg false   -- idle low; adjusted via CPOL mux
    let csR ← Signal.reg true       -- idle high (deasserted)

    let stSig := (stR : Signal dom (BitVec 2))
    let bcSig := (bitCntR : Signal dom (BitVec 4))
    let dcSig := (divR : Signal dom (BitVec 16))
    let mosiShSig := (mosiShR : Signal dom (BitVec 8))
    let misoShSig := (misoShR : Signal dom (BitVec 8))
    let sclkRSig := (sclkR : Signal dom Bool)
    let csSig := (csR : Signal dom Bool)

    -- Constants.
    let stIdle := (Signal.pure 0#2 : Signal dom (BitVec 2))
    let stActive := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let stPost := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let p0_4 := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let p1_4 := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let p15_4 := (Signal.pure 15#4 : Signal dom (BitVec 4))   -- 15 = 8 bits × 2 edges − 1
    let p0_16 := (Signal.pure 0#16 : Signal dom (BitVec 16))
    let p1_16 := (Signal.pure 1#16 : Signal dom (BitVec 16))
    let p0_8 := (Signal.pure 0#8 : Signal dom (BitVec 8))
    let p1_8 := (Signal.pure 1#8 : Signal dom (BitVec 8))
    let pMSB_8 := (Signal.pure 0x80#8 : Signal dom (BitVec 8))

    let tick := (dcSig === p0_16 : Signal dom Bool)

    -- State detection.
    let isIdle := (stSig === stIdle : Signal dom Bool)
    let isActive := (stSig === stActive : Signal dom Bool)
    let isPost := (stSig === stPost : Signal dom Bool)

    let bcAtMax := (bcSig === p15_4 : Signal dom Bool)

    -- Next state.  `start` is accepted on any idle cycle (not only on a
    -- divider tick); the other transitions happen on divider ticks.
    let idleNext := Signal.mux start stActive stIdle
    let activeNext := Signal.mux bcAtMax stPost stActive
    let stNextOnTick :=
      Signal.mux isActive activeNext stIdle
    let stNextBusy := Signal.mux tick stNextOnTick stSig
    let stNext := Signal.mux isIdle idleNext stNextBusy
    stR <~ stNext

    -- Bit counter: incremented every tick in active; reset on transitions.
    let bcInc := (bcSig + p1_4 : Signal dom (BitVec 4))
    let bcActive := Signal.mux bcAtMax p0_4 bcInc
    let bcOnTick := Signal.mux isActive bcActive p0_4
    bitCntR <~ Signal.mux tick bcOnTick bcSig

    -- Divider countdown.
    let dcDec := (dcSig - p1_16 : Signal dom (BitVec 16))
    let dcNext := Signal.mux tick bitDiv dcDec
    let dcAfterStart := Signal.mux (isIdle &&& start : Signal dom Bool) bitDiv dcNext
    divR <~ dcAfterStart

    -- Tick k of a transfer (bc = k) toggles SCLK: even k = leading edge,
    -- odd k = trailing edge.
    let bcBit0 := bcSig.map (BitVec.extractLsb' 0 1 ·)
    let p0_1 := (Signal.pure 0#1 : Signal dom (BitVec 1))
    let bcEven := (bcBit0 === p0_1 : Signal dom Bool)
    let bcOdd := (~~~bcEven : Signal dom Bool)
    let bcNonZero := (~~~(bcSig === p0_4) : Signal dom Bool)

    -- MOSI shift: load mosiByte when the transfer starts (MSB is on the
    -- line from then on).  Bit k must be valid at its sampling edge:
    --   CPHA=0: sampled at the leading edge, so data changes on the trailing
    --           edge (shift on odd ticks);
    --   CPHA=1: data changes on the leading edge, sampled at the trailing
    --           edge (shift on even ticks except the first: bit 0 is already
    --           out).
    let loadMosi := (isIdle &&& start : Signal dom Bool)
    let mosiSh := (mosiShSig <<< p1_8 : Signal dom (BitVec 8))
    let shiftSel := ((cpha &&& (bcEven &&& bcNonZero : Signal dom Bool) : Signal dom Bool)
                    ||| (~~~cpha &&& bcOdd : Signal dom Bool) : Signal dom Bool)
    let shiftMosi := (tick &&& (isActive &&& shiftSel : Signal dom Bool)
                    : Signal dom Bool)
    let mosiShNext :=
      Signal.mux loadMosi mosiByte
        (Signal.mux shiftMosi mosiSh mosiShSig)
    mosiShR <~ mosiShNext

    -- MISO shift-in at the sampling edge (CPHA=0: leading = even ticks,
    -- CPHA=1: trailing = odd ticks): `misoBit` is read in the cycle before
    -- the SCLK edge becomes visible and shifted into the low bit.
    let sampleSel := ((cpha &&& bcOdd : Signal dom Bool)
                     ||| (~~~cpha &&& bcEven : Signal dom Bool) : Signal dom Bool)
    let sampleMiso := (tick &&& (isActive &&& sampleSel : Signal dom Bool)
                     : Signal dom Bool)
    let misoShL := (misoShSig <<< p1_8 : Signal dom (BitVec 8))
    -- OR-in the sampled bit as low bit of the shifted result.
    let misoBitBv := (Signal.mux misoBit (Signal.pure 1#8) p0_8 : Signal dom (BitVec 8))
    let misoShL2 := (misoShL ||| misoBitBv : Signal dom (BitVec 8))
    let misoShNext := Signal.mux sampleMiso misoShL2 misoShSig
    misoShR <~ misoShNext

    -- SCLK toggles every tick while active.
    let sclkTog := (~~~sclkRSig : Signal dom Bool)
    let sclkTicked := Signal.mux isActive sclkTog cpol
    let sclkBusy := Signal.mux tick sclkTicked sclkRSig
    let sclkNext := Signal.mux isIdle cpol sclkBusy
    sclkR <~ sclkNext

    -- CS: goes low on idle→active (start), returns high on post→idle.
    let csGoLow := (isIdle &&& start : Signal dom Bool)
    let csGoHigh := (isPost &&& tick : Signal dom Bool)
    let csAfterLow := Signal.mux csGoLow (Signal.pure false) csSig
    let csNext := Signal.mux csGoHigh (Signal.pure true) csAfterLow
    csR <~ csNext

    -- Outputs.
    let msbAnd := (mosiShSig &&& pMSB_8 : Signal dom (BitVec 8))
    let msbIsZero := (msbAnd === p0_8 : Signal dom Bool)
    let mosiOut := (~~~msbIsZero : Signal dom Bool)

    -- `done` pulses on the cycle we're transitioning post → idle.
    let done := (isPost &&& tick : Signal dom Bool)

    return ({ sclk := sclkRSig, mosi := mosiOut, cs := csSig, misoByte := misoShSig, done := done } : MasterOut dom)

end Sparkle.IP.Bus.SPIHW
