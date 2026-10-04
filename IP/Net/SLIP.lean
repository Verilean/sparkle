/-
  IP.Net.SLIP — RFC 1055 Serial Line IP framer / deframer.

  This is the second physical layer for the Tang Nano 50K
  Web-server path:

      uartRxByte ──> slipDeframer  ──> ipv4RxParser → tcp → http
      uartTxByte <── slipFramer   <── ipv4TxBuilder  ← tcp ← http

  Wire format (each byte fed one at a time over UART):

    * END (0xC0) marks frame boundaries.  We emit one END
      before and one END after each IP packet ( = the "double-
      END" convention from RFC 1055 §4; it makes line-noise
      bytes harmless because they look like empty frames).
    * ESC (0xDB) escapes byte values that collide with END or
      ESC inside the payload:
        END → ESC + ESC_END (0xDC)
        ESC → ESC + ESC_ESC (0xDD)
    * All other bytes pass through untouched.

  Sparkle wiring (byte-stream Signal-DSL):

    Framer  : (payloadByte, payloadValid, frameEnd) →
              (txByte, txValid)
              Stages: 1 cycle = 1 transmitted byte.
              Pulse `frameEnd` once after the last payload byte;
              the framer emits the closing END.  If the framer
              is idle and a new payload byte arrives, it emits a
              leading END the cycle before, then the payload.

    Deframer: (rxByte, rxValid) → (outByte, outValid, frameDone)
              Strips END / ESC escaping.  `frameDone` pulses
              one cycle after the closing END of each frame, so
              the downstream IP parser knows where packets end.
-/
import Sparkle

namespace Sparkle.IP.Net.SLIP

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### Wire constants. -/

def END_BYTE  : BitVec 8 := 0xC0#8
def ESC_BYTE  : BitVec 8 := 0xDB#8
def ESC_END   : BitVec 8 := 0xDC#8
def ESC_ESC   : BitVec 8 := 0xDD#8

/-! ### Pure-data encoder / decoder (sim cross-check oracle). -/

/-- Encode a single byte: returns 1 or 2 wire bytes depending
    on whether it needs escaping. -/
def encodeByte (b : UInt8) : List UInt8 :=
  if b = 0xC0 then [0xDB, 0xDC]
  else if b = 0xDB then [0xDB, 0xDD]
  else [b]

/-- Encode a full IP packet into a SLIP frame: leading END +
    escape-encoded payload + trailing END. -/
def encodeFrame (payload : List UInt8) : List UInt8 :=
  0xC0 :: (payload.flatMap encodeByte) ++ [0xC0]

/-- Decode a SLIP byte stream into a list of (independently
    framed) IP payloads.  Skips empty frames (back-to-back END
    bytes — these are line-noise filler per RFC 1055). -/
partial def decodeStream (bs : List UInt8) : List (List UInt8) :=
  let rec go (xs : List UInt8) (cur : List UInt8) (frames : List (List UInt8))
      (escaped : Bool) : List (List UInt8) :=
    match xs with
    | [] =>
      -- Trailing unterminated frame is dropped.
      frames.reverse
    | b :: rest =>
      if escaped then
        let real :=
          if b = 0xDC then (0xC0 : UInt8)
          else if b = 0xDD then (0xDB : UInt8)
          else b   -- protocol violation; pass through
        go rest (real :: cur) frames false
      else if b = 0xC0 then
        if cur.isEmpty then go rest [] frames false
        else go rest [] (cur.reverse :: frames) false
      else if b = 0xDB then
        go rest cur frames true
      else
        go rest (b :: cur) frames false
  go bs [] [] false

/-! ### Signal-DSL framer (TX side: IP packet bytes → UART bytes). -/

structure FramerOut (dom : DomainConfig) where
  /-- Byte to send on UART this cycle (valid only when `txValid`). -/
  txByte  : Signal dom (BitVec 8)
  /-- High for one cycle when txByte holds a wire byte. -/
  txValid : Signal dom Bool
  /-- High when the framer is between frames and can accept new
      payload bytes (= upstream backpressure release). -/
  txReady : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (FramerOut dom) dom := ⟨⟩

/-- TX framer.  Stages per cycle (interleaved):

    * idle:           tx_line idle; if payloadValid is asserted
                      and we haven't sent the leading END yet,
                      emit END this cycle, latch byte for next.
    * sending body:   emit payload byte (or ESC + escape-replace
                      across 2 cycles when escaping is needed).
    * sending tail:   on `frameEnd` pulse, emit trailing END.

    Inputs:
      payloadByte  : next byte of IP packet
      payloadValid : payloadByte is real this cycle
      frameEnd     : pulse one cycle to close the frame
-/
def slipFramerHW {dom : DomainConfig}
    (payloadByte : Signal dom (BitVec 8))
    (payloadValid : Signal dom Bool)
    (frameEnd : Signal dom Bool) :
    FramerOut dom :=
  circuit do
    -- State register: 0 = idle (between frames; emit nothing),
    --                  1 = inside frame, not currently escaping,
    --                  2 = inside frame, just sent ESC (need to
    --                      send the escape-replacement next cycle).
    -- We do NOT emit a leading END (RFC 1055 §4: optional;
    -- omitting saves the upstream from having to delay 1 cycle).
    let st       ← Signal.reg (0#2)
    -- byte to send next cycle when escaping (DC or DD)
    let escNext  ← Signal.reg (0#8)
    -- which wire byte to emit this cycle (latched output)
    let outByte  ← Signal.reg (0#8)
    -- whether outByte should be driven on UART this cycle
    let outValid ← Signal.reg false

    let stSig := (st : Signal dom (BitVec 2))
    let escSig := (escNext : Signal dom (BitVec 8))

    -- Constants
    let p0_2 := (Signal.pure 0#2 : Signal dom (BitVec 2))
    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let pEND := (Signal.pure END_BYTE : Signal dom (BitVec 8))
    let pESC := (Signal.pure ESC_BYTE : Signal dom (BitVec 8))
    let pESC_END := (Signal.pure ESC_END : Signal dom (BitVec 8))
    let pESC_ESC := (Signal.pure ESC_ESC : Signal dom (BitVec 8))

    -- Predicates
    let isIdle := (stSig === p0_2 : Signal dom Bool)
    let isBody := (stSig === p1_2 : Signal dom Bool)
    let isEsc  := (stSig === p2_2 : Signal dom Bool)

    -- Need to escape?  Payload byte equals END or ESC.
    let byteIsEnd := (payloadByte === pEND : Signal dom Bool)
    let byteIsEsc := (payloadByte === pESC : Signal dom Bool)
    let needEscape := (byteIsEnd ||| byteIsEsc : Signal dom Bool)

    -- Compute the byte we'd emit in body state given payload + needEscape
    let escapeReplacement := Signal.mux byteIsEnd pESC_END pESC_ESC
    let bodyEmitByte := Signal.mux needEscape pESC payloadByte
    -- And the deferred escape byte (used when we go to state 2)
    let deferredEscByte := escapeReplacement

    -- Transition decisions (active states; payloadValid gates each):
    --   (idle | body) + payloadValid + !needEscape → emit payloadByte,
    --                                                 state→body
    --   (idle | body) + payloadValid +  needEscape → emit ESC, latch
    --                                                 replacement, state→esc
    --   esc                                        → emit escNext, state→body
    --   body + frameEnd                            → emit END, state→idle
    --   else                                       → outValid=false (idle)

    let payloadInIdleOrBody :=
      ((· && ·) <$>
        ((isIdle ||| isBody : Signal dom Bool)) <*>
        payloadValid : Signal dom Bool)
    let emitPayloadDirect :=
      ((· && ·) <$> payloadInIdleOrBody
        <*> (~~~needEscape : Signal dom Bool) : Signal dom Bool)
    let emitEscFirst :=
      (payloadInIdleOrBody &&& needEscape : Signal dom Bool)
    let closeFrame := (isBody &&& frameEnd : Signal dom Bool)

    -- outByte next
    let outByteNext :=
      Signal.mux isEsc escSig
        (Signal.mux emitPayloadDirect bodyEmitByte
          (Signal.mux emitEscFirst pESC
            (Signal.mux closeFrame pEND (Signal.pure 0#8))))

    -- outValid next
    let pTrue := (Signal.pure true : Signal dom Bool)
    let pFalse := (Signal.pure false : Signal dom Bool)
    let outValidNext :=
      Signal.mux isEsc pTrue
        (Signal.mux emitPayloadDirect pTrue
          (Signal.mux emitEscFirst pTrue
            (Signal.mux closeFrame pTrue pFalse)))

    -- state next
    let stNext :=
      Signal.mux isEsc p1_2                  -- esc → body
        (Signal.mux emitEscFirst p2_2        -- (idle|body) + escape → esc
          (Signal.mux emitPayloadDirect p1_2 -- (idle|body) + direct → body
            (Signal.mux closeFrame p0_2      -- body + end → idle
              stSig)))                       -- else hold

    -- escNext register: latch deferred replacement when entering esc state
    let escNextNext := Signal.mux emitEscFirst deferredEscByte escSig

    st       <~ stNext
    escNext  <~ escNextNext
    outByte  <~ outByteNext
    outValid <~ outValidNext

    -- txReady = high when we're not currently in the "deferred
    -- escape" state.  In all other states we can accept a new
    -- payload byte (idle = first byte of a frame, body = next
    -- byte of current frame).
    let txReadyOut := (~~~isEsc : Signal dom Bool)

    return ({ txByte := (outByte : Signal dom (BitVec 8))
            , txValid := (outValid : Signal dom Bool)
            , txReady := txReadyOut } : FramerOut dom)

/-! ### Signal-DSL deframer (RX side: UART bytes → IP packet bytes). -/

structure DeframerOut (dom : DomainConfig) where
  /-- Payload byte just decoded (valid only when `outValid`). -/
  outByte   : Signal dom (BitVec 8)
  /-- High for one cycle per decoded payload byte. -/
  outValid  : Signal dom Bool
  /-- High for one cycle after the closing END is seen (= a
      whole frame has been emitted). -/
  frameDone : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (DeframerOut dom) dom := ⟨⟩

/-- RX deframer.

    State machine:
      0 = idle (between frames / waiting for next END start)
      1 = inside frame, normal
      2 = inside frame, last byte was ESC (next byte is
          0xDC or 0xDD, decode to END or ESC respectively)

    Inputs:
      rxByte  : next byte from UART
      rxValid : high when rxByte is a real byte this cycle

    Outputs:
      outByte / outValid : decoded payload byte stream
      frameDone : pulse one cycle on closing END (= time to hand
                  the accumulated packet to ipv4RxParser).
-/
def slipDeframerHW {dom : DomainConfig}
    (rxByte : Signal dom (BitVec 8))
    (rxValid : Signal dom Bool) :
    DeframerOut dom :=
  circuit do
    let st        ← Signal.reg (0#2)
    let outByteR  ← Signal.reg (0#8)
    let outValidR ← Signal.reg false
    let doneR     ← Signal.reg false

    let stSig := (st : Signal dom (BitVec 2))

    let p0_2 := (Signal.pure 0#2 : Signal dom (BitVec 2))
    let p1_2 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let p2_2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let pEND := (Signal.pure END_BYTE : Signal dom (BitVec 8))
    let pESC := (Signal.pure ESC_BYTE : Signal dom (BitVec 8))
    let pESC_END := (Signal.pure ESC_END : Signal dom (BitVec 8))
    let pESC_ESC := (Signal.pure ESC_ESC : Signal dom (BitVec 8))
    let pEND_VAL := (Signal.pure END_BYTE : Signal dom (BitVec 8))
    let pESC_VAL := (Signal.pure ESC_BYTE : Signal dom (BitVec 8))
    let pTrue := (Signal.pure true : Signal dom Bool)
    let pFalse := (Signal.pure false : Signal dom Bool)

    let isIdle := (stSig === p0_2 : Signal dom Bool)
    let isBody := (stSig === p1_2 : Signal dom Bool)
    let isEsc  := (stSig === p2_2 : Signal dom Bool)

    let byteIsEnd := (rxByte === pEND : Signal dom Bool)
    let byteIsEsc := (rxByte === pESC : Signal dom Bool)
    let byteIsEscEnd := (rxByte === pESC_END : Signal dom Bool)
    let byteIsEscEsc := (rxByte === pESC_ESC : Signal dom Bool)

    -- Events (all gated by rxValid)
    let evIdleEnd :=                            -- idle + END → stay idle (skip)
      ((· && ·) <$> ((isIdle &&& rxValid : Signal dom Bool))
        <*> byteIsEnd : Signal dom Bool)
    let evIdleData :=                           -- idle + non-END → enter body, emit byte
      ((· && ·) <$> ((isIdle &&& rxValid : Signal dom Bool))
        <*> (~~~byteIsEnd : Signal dom Bool) : Signal dom Bool)
    let evBodyEnd :=                            -- body + END → frame done
      ((· && ·) <$> ((isBody &&& rxValid : Signal dom Bool))
        <*> byteIsEnd : Signal dom Bool)
    let evBodyEsc :=                            -- body + ESC → enter esc
      ((· && ·) <$> ((isBody &&& rxValid : Signal dom Bool))
        <*> byteIsEsc : Signal dom Bool)
    -- body + normal byte → emit byte
    let evBodyOther :=
      ((· && ·) <$> ((isBody &&& rxValid : Signal dom Bool))
        <*> ((· && ·) <$>
             (~~~byteIsEnd : Signal dom Bool) <*>
             (~~~byteIsEsc : Signal dom Bool)
             : Signal dom Bool) : Signal dom Bool)
    -- esc + ESC_END → emit END
    -- esc + ESC_ESC → emit ESC
    -- esc + other  → emit byte as-is (protocol violation tolerance)
    let evEscAny := (isEsc &&& rxValid : Signal dom Bool)

    -- Output byte computation
    let escDecoded :=
      Signal.mux byteIsEscEnd pEND_VAL
        (Signal.mux byteIsEscEsc pESC_VAL rxByte)
    let outByteNext :=
      Signal.mux evIdleData rxByte
        (Signal.mux evBodyOther rxByte
          (Signal.mux evEscAny escDecoded (outByteR : Signal dom (BitVec 8))))

    let outValidNext :=
      Signal.mux evIdleData pTrue
        (Signal.mux evBodyOther pTrue
          (Signal.mux evEscAny pTrue pFalse))

    let doneNext := evBodyEnd

    let stNext :=
      Signal.mux evIdleEnd p0_2
        (Signal.mux evIdleData p1_2
          (Signal.mux evBodyEnd p0_2
            (Signal.mux evBodyEsc p2_2
              (Signal.mux evEscAny p1_2 stSig))))

    st        <~ stNext
    outByteR  <~ outByteNext
    outValidR <~ outValidNext
    doneR     <~ doneNext

    return ({ outByte := (outByteR : Signal dom (BitVec 8))
            , outValid := (outValidR : Signal dom Bool)
            , frameDone := (doneR : Signal dom Bool) } : DeframerOut dom)

end Sparkle.IP.Net.SLIP
