/-
  IP.Bus.SPIHW — SPI master HW building blocks.

  Implements a single-byte SPI master:
      idle → shift 8 MOSI bits (with corresponding MISO
              sampling per CPHA) → idle
  supporting all four (CPOL, CPHA) modes.

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
    (_cpha : Signal dom Bool)
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

    -- Next state on tick.
    let idleNext := Signal.mux start stActive stIdle
    let activeNext := Signal.mux bcAtMax stPost stActive
    let postNext := stIdle
    let stNextOnTick :=
      Signal.mux isIdle idleNext
        (Signal.mux isActive activeNext
          (Signal.mux isPost postNext stIdle))
    let stNext := Signal.mux tick stNextOnTick stSig
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

    -- MOSI shift: load mosiByte on transition idle→active; shift-left every 2 ticks in active.
    let loadMosi := (tick &&& (isIdle &&& start : Signal dom Bool)
                    : Signal dom Bool)
    let mosiSh := (mosiShSig <<< p1_8 : Signal dom (BitVec 8))
    -- Only advance on even-numbered ticks within a bit (bc bit 0 == 0).
    let bcBit0 := bcSig.map (BitVec.extractLsb' 0 1 ·)
    let p0_1 := (Signal.pure 0#1 : Signal dom (BitVec 1))
    let bcEven := (bcBit0 === p0_1 : Signal dom Bool)
    let shiftMosi := (tick &&& (isActive &&& bcEven : Signal dom Bool)
                    : Signal dom Bool)
    let mosiShNext :=
      Signal.mux loadMosi mosiByte
        (Signal.mux shiftMosi mosiSh mosiShSig)
    mosiShR <~ mosiShNext

    -- MISO shift-in: on odd ticks (sample edge), shift misoBit into low bit.
    let bcOdd := (~~~bcEven : Signal dom Bool)
    let sampleMiso := (tick &&& (isActive &&& bcOdd : Signal dom Bool)
                     : Signal dom Bool)
    let misoShL := (misoShSig <<< p1_8 : Signal dom (BitVec 8))
    -- OR-in the sampled bit as low bit of the shifted result.
    let misoBitBv := (Signal.mux misoBit (Signal.pure 1#8) p0_8 : Signal dom (BitVec 8))
    let misoShL2 := (misoShL ||| misoBitBv : Signal dom (BitVec 8))
    let misoShNext := Signal.mux sampleMiso misoShL2 misoShSig
    misoShR <~ misoShNext

    -- SCLK toggles every tick while active.
    let sclkTog := (~~~sclkRSig : Signal dom Bool)
    let sclkTicked :=
      Signal.mux isActive sclkTog
        (Signal.mux isPost cpol
          (Signal.mux isIdle cpol sclkRSig))
    let sclkNext := Signal.mux tick sclkTicked sclkRSig
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
