/-
  IP.Net.UART — bit-level UART RX / TX for the SLIP-over-USB path.

  This is the *physical layer* under SLIP framing for the Tang
  Nano 50K Web-server demo:

      USB-C (host) ──BL616──UART──> FPGA pin ──┐
                                                ▼
                                           uartRxByte ──> SLIP deframer
                                                              │
                                                              ▼
                                                       ipv4RxParser → …

      … → ipv4HeaderByte → SLIP framer ──┐
                                          ▼
                                     uartTxByte ──> FPGA pin ──UART──BL616──> host

  8-N-1 framing, LSB first, clk-divider-based bit timing.

  The two engines (RX / TX) each take their bit-divider count as
  a config parameter so the same modules work at any baud / clock
  combination — for the demo we pre-compute it for
  100 MHz / 1 Mbps = 100 cycles/bit.
-/
import Sparkle

namespace Sparkle.IP.Net.UART

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### Pure-data reference (used for sim cross-checks).

    These don't run on hardware — they just produce the wire
    bit-stream a real UART line would carry, so the Signal-DSL
    HW versions can be validated cycle-by-cycle against the
    same expected sequence.
-/

/-- Wire bits a UART TX would emit for one byte, in the order
    they appear on the line (oldest first):
       start(0) + d0 + d1 + … + d7 + stop(1) = 10 bits. -/
def uartByteToBits (b : UInt8) : List Bool :=
  let bits := (List.range 8).map (fun i => (b.toNat >>> i) &&& 1 == 1)
  [false] ++ bits ++ [true]

/-- The wire image of a whole byte sequence: each byte expanded
    to its 10 bits, then concatenated.  Between back-to-back
    bytes there is no idle gap (the stop bit of one byte is
    immediately followed by the start bit of the next). -/
def uartBytesToBits (bs : List UInt8) : List Bool :=
  bs.flatMap uartByteToBits

/-- Decode a wire bit-stream back into bytes.  Lossy on garbage
    (no start bit, no stop bit at the expected slot) — those
    bytes are dropped. -/
partial def uartBitsToBytes (bits : List Bool) : List UInt8 :=
  let rec go (xs : List Bool) (acc : List UInt8) : List UInt8 :=
    match xs with
    | [] => acc.reverse
    | b :: rest =>
      if b then
        -- Idle / stop fill — skip until next start bit (= false).
        go rest acc
      else
        -- Start bit consumed; need 8 data bits + 1 stop.
        if rest.length ≥ 9 then
          let dataBits := rest.take 8
          let stop := rest[8]?.getD true
          if stop then
            let n := (List.range 8).foldl
              (fun acc i =>
                let bit := dataBits[i]?.getD false
                acc ||| (if bit then 1 <<< i else 0)) 0
            go (rest.drop 9) (n.toUInt8 :: acc)
          else
            go (rest.drop 9) acc
        else
          acc.reverse
  go bits []

/-! ### Bit-level UART TX HW engine (Signal.circuit do).

    State:
      shiftReg : BitVec 10       — current frame (start + 8 + stop), LSBfirst
      bitCount : BitVec 4        — bits remaining (0..10)
      divCount : BitVec 16       — cycles remaining in current bit slot
      busy     : Bool            — actively transmitting

    Inputs:
      tx_byte  : BitVec 8        — payload byte
      tx_valid : Bool            — pulse: latch byte and start transmit
      bitDiv   : BitVec 16       — cycles per bit minus 1 (e.g. 99 for
                                     100MHz / 1Mbps)

    Outputs:
      tx_line  : Bool            — serial wire (idle = 1)
      tx_ready : Bool            — high when idle, low while busy
-/

structure TxOut (dom : DomainConfig) where
  txLine  : Signal dom Bool
  txReady : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TxOut dom) dom := ⟨⟩

def uartTxHW {dom : DomainConfig}
    (txByte  : Signal dom (BitVec 8))
    (txValid : Signal dom Bool)
    (bitDiv  : Signal dom (BitVec 16)) :
    TxOut dom :=
  circuit do
    let shiftReg ← Signal.reg (0x3FF#10)  -- idle = all 1s (line high)
    let bitCount ← Signal.reg (0#4)
    let divCount ← Signal.reg (0#16)
    let busyReg  ← Signal.reg false

    let busySig := (busyReg : Signal dom Bool)
    let shiftSig := (shiftReg : Signal dom (BitVec 10))
    let bcSig := (bitCount : Signal dom (BitVec 4))
    let dcSig := (divCount : Signal dom (BitVec 16))

    -- Build the 10-bit frame: stop(1) || byte || start(0)
    -- so that bit 0 (LSB) shifts out first.
    let p1b1 := (Signal.pure 1#1 : Signal dom (BitVec 1))
    let p1b0 := (Signal.pure 0#1 : Signal dom (BitVec 1))
    -- frame = {stop=1, b7..b0, start=0}, LSB out first
    let byteAsBV9 := ((· ++ ·) <$> txByte <*> p1b0 : Signal dom (BitVec 9))
    let frame10 := ((· ++ ·) <$> p1b1 <*> byteAsBV9 : Signal dom (BitVec 10))

    -- Start condition: a tx_valid pulse while idle.
    let p0_4 := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let p10_4 := (Signal.pure 10#4 : Signal dom (BitVec 4))
    let p0_16 := (Signal.pure 0#16 : Signal dom (BitVec 16))
    let pIdle10 := (Signal.pure 0x3FF#10 : Signal dom (BitVec 10))
    let p1_4 := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let p1_10 := (Signal.pure 1#10 : Signal dom (BitVec 10))
    let notBusy := ((fun b => !b) <$> busySig : Signal dom Bool)
    let startReq := ((· && ·) <$> txValid <*> notBusy : Signal dom Bool)

    -- Divider-tick: divCount == 0 means we cross to next bit this cycle.
    let bitTick := ((· == ·) <$> dcSig <*> p0_16 : Signal dom Bool)

    let dcDec := ((· - ·) <$> dcSig <*> (Signal.pure 1#16 : Signal dom (BitVec 16))
                  : Signal dom (BitVec 16))

    let shiftDown := ((· >>> ·) <$> shiftSig <*> p1_10 : Signal dom (BitVec 10))
    let bcDec := ((· - ·) <$> bcSig <*> p1_4 : Signal dom (BitVec 4))

    -- Next-state logic.
    -- shiftReg : on start load frame10; on bitTick while busy shift right; else hold.
    -- bitCount : on start load 10; on bitTick decrement; else hold.
    -- divCount : on start or on bitTick reload bitDiv; else decrement (while busy).
    -- busy     : on start become true; on bitTick && bitCount==1 become false; else hold.

    let shiftNext :=
      Signal.mux startReq frame10
        (Signal.mux (((· && ·) <$> busySig <*> bitTick : Signal dom Bool))
           shiftDown shiftSig)
    let bcNext :=
      Signal.mux startReq p10_4
        (Signal.mux (((· && ·) <$> busySig <*> bitTick : Signal dom Bool))
           bcDec bcSig)
    let dcNext :=
      Signal.mux startReq bitDiv
        (Signal.mux busySig
           (Signal.mux bitTick bitDiv dcDec) p0_16)
    let busyNext :=
      Signal.mux startReq (Signal.pure true)
        (Signal.mux (((· && ·) <$> bitTick <*>
                      (((· == ·) <$> bcSig <*> p1_4 : Signal dom Bool))
                      : Signal dom Bool))
           (Signal.pure false) busySig)
    -- When not busy and not starting, keep shiftReg at the idle all-1s
    -- pattern so tx_line stays high.
    let shiftNext2 := Signal.mux (((· || ·) <$> busySig <*> startReq : Signal dom Bool))
                        shiftNext pIdle10

    shiftReg <~ shiftNext2
    bitCount <~ bcNext
    divCount <~ dcNext
    busyReg  <~ busyNext

    -- tx_line = LSB of shiftReg.  When idle (shiftReg = 0x3FF) → 1.
    let p1_10b := (Signal.pure 1#10 : Signal dom (BitVec 10))
    let lsbAnd := ((· &&& ·) <$> shiftSig <*> p1_10b : Signal dom (BitVec 10))
    let isOne := ((· == ·) <$> lsbAnd <*> p1_10b : Signal dom Bool)

    let readyOut := ((fun b => !b) <$> busySig : Signal dom Bool)
    return ({ txLine := isOne, txReady := readyOut } : TxOut dom)

/-! ### Bit-level UART RX HW engine.

    State machine: idle → start-glitch-sample → 8 data bits → stop → emit.

    Sampling cadence: on each bit slot we sample at the midpoint
    (= bitDiv/2 cycles after the previous tick), the standard
    UART RX trick that gives noise immunity at both edges.

    Inputs:
      rx_line : Bool          — serial line (idle high)
      bitDiv  : BitVec 16     — cycles per bit minus 1

    Outputs:
      rx_byte  : BitVec 8     — received byte (valid only when rx_valid)
      rx_valid : Bool         — pulse on completed byte
-/

structure RxOut (dom : DomainConfig) where
  rxByte  : Signal dom (BitVec 8)
  rxValid : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (RxOut dom) dom := ⟨⟩

def uartRxHW {dom : DomainConfig}
    (rxLine : Signal dom Bool)
    (bitDiv : Signal dom (BitVec 16)) :
    RxOut dom :=
  circuit do
    -- stateReg : 0 = idle waiting for start, 1..9 = receiving bits
    --                (1 = sample start bit midpoint; 2..9 = data bits)
    --            10 = stop bit
    let stateReg ← Signal.reg (0#4)
    let shiftReg ← Signal.reg (0#8)
    let divReg   ← Signal.reg (0#16)
    let validReg ← Signal.reg false

    let stSig := (stateReg : Signal dom (BitVec 4))
    let shSig := (shiftReg : Signal dom (BitVec 8))
    let dvSig := (divReg : Signal dom (BitVec 16))

    -- Half-bit divider (= bitDiv >>> 1).  We use it on entry to
    -- align sampling to the bit-slot midpoint.
    let p1_16 := (Signal.pure 1#16 : Signal dom (BitVec 16))
    let halfDiv := ((· >>> ·) <$> bitDiv <*> p1_16 : Signal dom (BitVec 16))

    let p0_16 := (Signal.pure 0#16 : Signal dom (BitVec 16))
    let p0_4 := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let p1_4 := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let p10_4 := (Signal.pure 10#4 : Signal dom (BitVec 4))

    let inIdle := ((· == ·) <$> stSig <*> p0_4 : Signal dom Bool)
    let dvIsZero := ((· == ·) <$> dvSig <*> p0_16 : Signal dom Bool)
    let startEdge := ((· && ·) <$> inIdle <*> ((fun b => !b) <$> rxLine : Signal dom Bool)
                      : Signal dom Bool)

    let stInc := ((· + ·) <$> stSig <*> p1_4 : Signal dom (BitVec 4))
    let dvDec := ((· - ·) <$> dvSig <*> p1_16 : Signal dom (BitVec 16))
    let stIsStop := ((· == ·) <$> stSig <*> p10_4 : Signal dom Bool)

    -- Sample-and-shift: when divider hits zero (and we're not idle),
    -- we cross into the next bit slot.  For data bits (state in 2..9),
    -- shift the sampled rxLine into shiftReg's MSB and shift right by 1.
    let bitTick := ((· && ·) <$> ((fun b => !b) <$> inIdle : Signal dom Bool)
                     <*> dvIsZero : Signal dom Bool)
    let stIsOne := ((· == ·) <$> stSig <*> p1_4 : Signal dom Bool)
    let inData2_9 :=
      ((· && ·) <$>
        ((fun b => !b) <$> stIsOne : Signal dom Bool) <*>
        ((fun b => !b) <$> stIsStop : Signal dom Bool) : Signal dom Bool)
    let inDataAndTick := ((· && ·) <$> inData2_9 <*> bitTick : Signal dom Bool)
    let shiftRight1 := ((· >>> ·) <$> shSig <*>
                        (Signal.pure 1#8 : Signal dom (BitVec 8)) : Signal dom (BitVec 8))
    let p0x80_8 := (Signal.pure 0x80#8 : Signal dom (BitVec 8))
    let p0_8 := (Signal.pure 0#8 : Signal dom (BitVec 8))
    let bitAsBV1 := Signal.mux rxLine p0x80_8 p0_8
    let shiftWithBit := ((· ||| ·) <$> shiftRight1 <*> bitAsBV1 : Signal dom (BitVec 8))
    let shiftNext := Signal.mux inDataAndTick shiftWithBit shSig

    -- State transitions:
    --   idle → 1 on start edge, reload halfDiv (sample midpoint)
    --   1..9 → +1 on tick, reload bitDiv
    --   10 (stop) → 0 on tick (back to idle); emit valid if stop=1
    --   else hold
    let stateNext :=
      Signal.mux startEdge p1_4
        (Signal.mux bitTick
           (Signal.mux stIsStop p0_4 stInc)
           stSig)
    let divNext :=
      Signal.mux startEdge halfDiv
        (Signal.mux bitTick bitDiv
           (Signal.mux inIdle p0_16 dvDec))

    -- emit valid pulse when leaving the stop slot AND stop bit was high
    let validPulse := ((· && ·) <$>
      (((· && ·) <$> bitTick <*> stIsStop) : Signal dom Bool) <*>
      rxLine : Signal dom Bool)

    stateReg <~ stateNext
    shiftReg <~ shiftNext
    divReg   <~ divNext
    validReg <~ validPulse

    return ({ rxByte := shSig, rxValid := (validReg : Signal dom Bool) } : RxOut dom)

end Sparkle.IP.Net.UART
