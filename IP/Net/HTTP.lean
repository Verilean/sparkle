/-
  IP.Net.HTTP — minimal HTTP/1.0 byte emitters + parsers.

  Wire format:
    Request:  GET / HTTP/1.0\r\n\r\n              (18 bytes fixed)
    Response: HTTP/1.0 200 OK\r\n\r\nHello, Sparkle!  (34 bytes fixed)

  Demo scope:
    * Server's response body is hard-coded to "Hello,
      Sparkle!" — sufficient for a Sparkle-self-loopback
      "I served a page over TCP" claim.
    * Client only emits `GET /` for path `/`.  Path / method
      parsing on the server side detects the leading `GET `
      and pulses `gotRequest`.
    * Status-code parser captures the 3 ASCII digits at
      offset 9..11 ("200" / "404" / etc.) and converts to a
      9-bit BitVec status code, so downstream logic can
      branch on 2xx / 4xx / 5xx without dragging the
      full reason-phrase parser in.

  This file provides:
    * `httpGetByte`   : `@[hardware_module]` 18-byte mux
                       emitting `GET / HTTP/1.0\r\n\r\n`.
    * `httpRespByte`  : `@[hardware_module]` 34-byte mux
                       emitting the response above.
    * `httpGetEmitter` : trigger-driven 18-cycle burst
                         wrapping `httpGetByte`.
    * `httpRespEmitter`: trigger-driven 34-cycle burst.
    * `httpRequestParser`: detects the 4-byte `"GET "`
                           prefix in the inbound byte stream
                           and pulses `gotRequest` once.
    * `httpStatusParser` : captures the 3-digit status code
                           from `HTTP/1.0 NNN ...`.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.HTTP

/-! ### ASCII byte constants. -/

abbrev cG    : BitVec 8 := 0x47#8   -- 'G'
abbrev cE    : BitVec 8 := 0x45#8   -- 'E'
abbrev cT    : BitVec 8 := 0x54#8   -- 'T'
abbrev cSP   : BitVec 8 := 0x20#8   -- ' '
abbrev cSlash : BitVec 8 := 0x2F#8  -- '/'
abbrev cH    : BitVec 8 := 0x48#8   -- 'H'
abbrev cTT   : BitVec 8 := 0x54#8   -- 'T'
abbrev cP    : BitVec 8 := 0x50#8   -- 'P'
abbrev cDot  : BitVec 8 := 0x2E#8   -- '.'
abbrev c1    : BitVec 8 := 0x31#8   -- '1'
abbrev c0    : BitVec 8 := 0x30#8   -- '0'
abbrev cCR   : BitVec 8 := 0x0D#8   -- \r
abbrev cLF   : BitVec 8 := 0x0A#8   -- \n
abbrev c2    : BitVec 8 := 0x32#8   -- '2'
abbrev cO    : BitVec 8 := 0x4F#8   -- 'O'
abbrev cK    : BitVec 8 := 0x4B#8   -- 'K'
abbrev cComma : BitVec 8 := 0x2C#8  -- ','
abbrev cS    : BitVec 8 := 0x53#8   -- 'S'
abbrev cp    : BitVec 8 := 0x70#8   -- 'p'
abbrev ca    : BitVec 8 := 0x61#8   -- 'a'
abbrev cr    : BitVec 8 := 0x72#8   -- 'r'
abbrev ck    : BitVec 8 := 0x6B#8   -- 'k'
abbrev cl    : BitVec 8 := 0x6C#8   -- 'l'
abbrev ce    : BitVec 8 := 0x65#8   -- 'e'
abbrev cBang : BitVec 8 := 0x21#8   -- '!'
abbrev co    : BitVec 8 := 0x6F#8   -- 'o'
abbrev cH_l  : BitVec 8 := 0x48#8   -- 'H' (capital)

/-! ### Per-byte selector helper.

    Builds an N-way mux from a list of (cntSig-eq selector,
    byte) pairs.  cnt = 1..N corresponds to offset 0..N-1;
    cnt = 0 is idle (don't-care output). -/
@[inline] private def eqK {dom : DomainConfig}
    (cntSig : Signal dom (BitVec 6)) (k : Nat) :
    Signal dom Bool :=
  cntSig === (Signal.pure (BitVec.ofNat 6 k) : Signal dom (BitVec 6))

/-! ### 18-byte GET request mux. -/

/-- "GET / HTTP/1.0\r\n\r\n" — 18 bytes. -/
@[hardware_module] def httpGetByte {dom : DomainConfig}
    (cntSig : Signal dom (BitVec 6)) : Signal dom (BitVec 8) :=
  let b0  := (Signal.pure cG    : Signal dom (BitVec 8))
  let b1  := (Signal.pure cE    : Signal dom (BitVec 8))
  let b2  := (Signal.pure cT    : Signal dom (BitVec 8))
  let b3  := (Signal.pure cSP   : Signal dom (BitVec 8))
  let b4  := (Signal.pure cSlash: Signal dom (BitVec 8))
  let b5  := (Signal.pure cSP   : Signal dom (BitVec 8))
  let b6  := (Signal.pure cH    : Signal dom (BitVec 8))
  let b7  := (Signal.pure cT    : Signal dom (BitVec 8))
  let b8  := (Signal.pure cT    : Signal dom (BitVec 8))
  let b9  := (Signal.pure cP    : Signal dom (BitVec 8))
  let b10 := (Signal.pure cSlash: Signal dom (BitVec 8))
  let b11 := (Signal.pure c1    : Signal dom (BitVec 8))
  let b12 := (Signal.pure cDot  : Signal dom (BitVec 8))
  let b13 := (Signal.pure c0    : Signal dom (BitVec 8))
  let b14 := (Signal.pure cCR   : Signal dom (BitVec 8))
  let b15 := (Signal.pure cLF   : Signal dom (BitVec 8))
  let b16 := (Signal.pure cCR   : Signal dom (BitVec 8))
  let b17 := (Signal.pure cLF   : Signal dom (BitVec 8))
  Signal.mux (eqK cntSig 1) b0
    (Signal.mux (eqK cntSig 2) b1
      (Signal.mux (eqK cntSig 3) b2
        (Signal.mux (eqK cntSig 4) b3
          (Signal.mux (eqK cntSig 5) b4
            (Signal.mux (eqK cntSig 6) b5
              (Signal.mux (eqK cntSig 7) b6
                (Signal.mux (eqK cntSig 8) b7
                  (Signal.mux (eqK cntSig 9) b8
                    (Signal.mux (eqK cntSig 10) b9
                      (Signal.mux (eqK cntSig 11) b10
                        (Signal.mux (eqK cntSig 12) b11
                          (Signal.mux (eqK cntSig 13) b12
                            (Signal.mux (eqK cntSig 14) b13
                              (Signal.mux (eqK cntSig 15) b14
                                (Signal.mux (eqK cntSig 16) b15
                                  (Signal.mux (eqK cntSig 17) b16 b17))))))))))))))))

/-! ### 34-byte response mux: "HTTP/1.0 200 OK\r\n\r\nHello, Sparkle!" -/

@[hardware_module] def httpRespByte {dom : DomainConfig}
    (cntSig : Signal dom (BitVec 6)) : Signal dom (BitVec 8) :=
  let b0  := (Signal.pure cH    : Signal dom (BitVec 8))
  let b1  := (Signal.pure cT    : Signal dom (BitVec 8))
  let b2  := (Signal.pure cT    : Signal dom (BitVec 8))
  let b3  := (Signal.pure cP    : Signal dom (BitVec 8))
  let b4  := (Signal.pure cSlash: Signal dom (BitVec 8))
  let b5  := (Signal.pure c1    : Signal dom (BitVec 8))
  let b6  := (Signal.pure cDot  : Signal dom (BitVec 8))
  let b7  := (Signal.pure c0    : Signal dom (BitVec 8))
  let b8  := (Signal.pure cSP   : Signal dom (BitVec 8))
  let b9  := (Signal.pure c2    : Signal dom (BitVec 8))   -- '2'
  let b10 := (Signal.pure c0    : Signal dom (BitVec 8))   -- '0'
  let b11 := (Signal.pure c0    : Signal dom (BitVec 8))   -- '0'
  let b12 := (Signal.pure cSP   : Signal dom (BitVec 8))
  let b13 := (Signal.pure cO    : Signal dom (BitVec 8))
  let b14 := (Signal.pure cK    : Signal dom (BitVec 8))
  let b15 := (Signal.pure cCR   : Signal dom (BitVec 8))
  let b16 := (Signal.pure cLF   : Signal dom (BitVec 8))
  let b17 := (Signal.pure cCR   : Signal dom (BitVec 8))
  let b18 := (Signal.pure cLF   : Signal dom (BitVec 8))
  -- Body: "Hello, Sparkle!" (15 bytes)
  let b19 := (Signal.pure cH    : Signal dom (BitVec 8))   -- 'H'
  let b20 := (Signal.pure ce    : Signal dom (BitVec 8))   -- 'e'
  let b21 := (Signal.pure cl    : Signal dom (BitVec 8))   -- 'l'
  let b22 := (Signal.pure cl    : Signal dom (BitVec 8))   -- 'l'
  let b23 := (Signal.pure co    : Signal dom (BitVec 8))   -- 'o'
  let b24 := (Signal.pure cComma: Signal dom (BitVec 8))   -- ','
  let b25 := (Signal.pure cSP   : Signal dom (BitVec 8))
  let b26 := (Signal.pure cS    : Signal dom (BitVec 8))   -- 'S'
  let b27 := (Signal.pure cp    : Signal dom (BitVec 8))   -- 'p'
  let b28 := (Signal.pure ca    : Signal dom (BitVec 8))   -- 'a'
  let b29 := (Signal.pure cr    : Signal dom (BitVec 8))   -- 'r'
  let b30 := (Signal.pure ck    : Signal dom (BitVec 8))   -- 'k'
  let b31 := (Signal.pure cl    : Signal dom (BitVec 8))   -- 'l'
  let b32 := (Signal.pure ce    : Signal dom (BitVec 8))   -- 'e'
  let b33 := (Signal.pure cBang : Signal dom (BitVec 8))   -- '!'
  Signal.mux (eqK cntSig 1) b0
    (Signal.mux (eqK cntSig 2) b1
      (Signal.mux (eqK cntSig 3) b2
        (Signal.mux (eqK cntSig 4) b3
          (Signal.mux (eqK cntSig 5) b4
            (Signal.mux (eqK cntSig 6) b5
              (Signal.mux (eqK cntSig 7) b6
                (Signal.mux (eqK cntSig 8) b7
                  (Signal.mux (eqK cntSig 9) b8
                    (Signal.mux (eqK cntSig 10) b9
                      (Signal.mux (eqK cntSig 11) b10
                        (Signal.mux (eqK cntSig 12) b11
                          (Signal.mux (eqK cntSig 13) b12
                            (Signal.mux (eqK cntSig 14) b13
                              (Signal.mux (eqK cntSig 15) b14
                                (Signal.mux (eqK cntSig 16) b15
                                  (Signal.mux (eqK cntSig 17) b16
                                    (Signal.mux (eqK cntSig 18) b17
                                      (Signal.mux (eqK cntSig 19) b18
                                        (Signal.mux (eqK cntSig 20) b19
                                          (Signal.mux (eqK cntSig 21) b20
                                            (Signal.mux (eqK cntSig 22) b21
                                              (Signal.mux (eqK cntSig 23) b22
                                                (Signal.mux (eqK cntSig 24) b23
                                                  (Signal.mux (eqK cntSig 25) b24
                                                    (Signal.mux (eqK cntSig 26) b25
                                                      (Signal.mux (eqK cntSig 27) b26
                                                        (Signal.mux (eqK cntSig 28) b27
                                                          (Signal.mux (eqK cntSig 29) b28
                                                            (Signal.mux (eqK cntSig 30) b29
                                                              (Signal.mux (eqK cntSig 31) b30
                                                                (Signal.mux (eqK cntSig 32) b31
                                                                  (Signal.mux (eqK cntSig 33) b32 b33))))))))))))))))))))))))))))))))

/-! ### Burst emitters wrapping the byte mux. -/

structure HttpEmitOut (dom : DomainConfig) where
  byte  : Signal dom (BitVec 8)
  valid : Signal dom Bool
  last  : Signal dom Bool
  start : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HttpEmitOut dom) dom := ⟨⟩

/-- Generic burst emitter shared by request / response.
    `nBytes` is the total burst length. -/
@[inline] private def burstEmit {dom : DomainConfig}
    (trigger : Signal dom Bool)
    (nBytes : Nat)
    (byteFn : Signal dom (BitVec 6) → Signal dom (BitVec 8)) :
    HttpEmitOut dom :=
  circuit do
    let cnt ← Signal.reg (0#6)
    let cntSig := (cnt : Signal dom (BitVec 6))
    let pZero := (Signal.pure 0#6 : Signal dom (BitVec 6))
    let p1    := (Signal.pure 1#6 : Signal dom (BitVec 6))
    let pLast := (Signal.pure (BitVec.ofNat 6 nBytes) : Signal dom (BitVec 6))
    let isIdle  := cntSig === pZero
    let isLast  := cntSig === pLast
    let isEmitting := ~~~isIdle
    let byteOut := byteFn cntSig
    let cntInc := cntSig + p1
    cnt <~ Signal.mux trigger p1
            (Signal.mux isLast pZero
              (Signal.mux isEmitting cntInc cntSig))
    return ({ byte  := byteOut
            , valid := isEmitting
            , last  := isLast
            , start := trigger
            } : HttpEmitOut dom)

def httpGetEmitter {dom : DomainConfig}
    (trigger : Signal dom Bool) : HttpEmitOut dom :=
  burstEmit trigger 18 httpGetByte

def httpRespEmitter {dom : DomainConfig}
    (trigger : Signal dom Bool) : HttpEmitOut dom :=
  burstEmit trigger 34 httpRespByte

/-! ### HTTP request parser — detect `GET ` at offset 0..3. -/

structure HttpRequestParserOut (dom : DomainConfig) where
  /-- Pulsed high for one cycle once the four-byte `"GET "`
      prefix has been seen at the start of a fresh request. -/
  gotRequest : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HttpRequestParserOut dom) dom := ⟨⟩

/-- Tiny state machine that walks the byte stream and pulses
    `gotRequest` after the 4th matching byte of `"GET "`
    arrives.  No timeout / no error recovery (yet) — a
    mismatched byte resets the counter to 0. -/
def httpRequestParser {dom : DomainConfig}
    (byte : Signal dom (BitVec 8))
    (valid : Signal dom Bool) :
    HttpRequestParserOut dom :=
  circuit do
    -- Match counter: 0 = looking for 'G', 1 = next 'E',
    -- 2 = 'T', 3 = ' ', 4 = matched.  Reset to 0 on
    -- mismatch.
    let cnt ← Signal.reg (0#3)
    let gotR ← Signal.reg false

    let cntSig := (cnt : Signal dom (BitVec 3))
    let gotSig := (gotR : Signal dom Bool)

    let pG := (Signal.pure cG  : Signal dom (BitVec 8))
    let pE := (Signal.pure cE  : Signal dom (BitVec 8))
    let pT := (Signal.pure cT  : Signal dom (BitVec 8))
    let pSP_ := (Signal.pure cSP : Signal dom (BitVec 8))

    let p0_3 := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let p1_3 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let p2_3 := (Signal.pure 2#3 : Signal dom (BitVec 3))
    let p3_3 := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let p4_3 := (Signal.pure 4#3 : Signal dom (BitVec 3))

    let isAt0 := cntSig === p0_3
    let isAt1 := cntSig === p1_3
    let isAt2 := cntSig === p2_3
    let isAt3 := cntSig === p3_3
    let isAt4 := cntSig === p4_3

    let isG := byte === pG
    let isE := byte === pE
    let isT := byte === pT
    let isSp := byte === pSP_

    -- Step on valid byte: increment if it matches the expected,
    -- otherwise reset to 0 (but if the mismatched byte itself
    -- is 'G', stay at 1 so we don't miss back-to-back 'G's).
    let matchHere :=
      (isAt0 &&& isG) ||| (isAt1 &&& isE) |||
      (isAt2 &&& isT) ||| (isAt3 &&& isSp)
    -- "go to state 1 because the current byte is 'G'" — used
    -- on mismatch in any state.
    let restartG := isG
    let cntInc := cntSig + p1_3
    let cntNext :=
      Signal.mux (valid &&& matchHere) cntInc
        (Signal.mux (valid &&& restartG) p1_3
          (Signal.mux valid p0_3 cntSig))
    cnt <~ Signal.mux isAt4 p0_3 cntNext

    -- gotRequest pulses for one cycle when we just matched the
    -- 4th byte (the space).  That's the cycle when cnt
    -- transitions to 4 — so the registered pulse goes high
    -- on the NEXT cycle.  Detect `matchHere` AND `isAt3` to
    -- signal "we just took the GET-prefix-complete transition".
    -- `isAt4` is computed but only used as a counter-reset
    -- guard above; not consumed here.
    gotR <~ valid &&& isAt3 &&& isSp
    return ({ gotRequest := gotSig } : HttpRequestParserOut dom)

/-! ### HTTP status-code parser — capture digits at offset 9..11. -/

structure HttpStatusParserOut (dom : DomainConfig) where
  /-- 9-bit status code (e.g. 200, 404, 500).  Valid once
      `done` pulses high. -/
  status : Signal dom (BitVec 16)
  /-- Pulses for one cycle after the 12th byte (final status
      digit) has been latched. -/
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HttpStatusParserOut dom) dom := ⟨⟩

/-- Parser that assumes the byte stream starts with
    `HTTP/1.0 NNN OK\r\n...` and extracts NNN as a decimal
    integer.  Byte offsets 9, 10, 11 are the three ASCII
    digits; we treat each as `byte - '0'` and combine as
    `d0*100 + d1*10 + d2`.

    `sop` pulses high on the first byte of the response
    (offset 0 = 'H'). -/
def httpStatusParser {dom : DomainConfig}
    (byte : Signal dom (BitVec 8))
    (valid : Signal dom Bool)
    (sop   : Signal dom Bool) :
    HttpStatusParserOut dom :=
  circuit do
    let cnt   ← Signal.reg (0#5)
    let d0R   ← Signal.reg (0#8)
    let d1R   ← Signal.reg (0#8)
    let d2R   ← Signal.reg (0#8)
    let doneR ← Signal.reg false

    let cntSig := (cnt : Signal dom (BitVec 5))
    let d0Sig  := (d0R : Signal dom (BitVec 8))
    let d1Sig  := (d1R : Signal dom (BitVec 8))
    let d2Sig  := (d2R : Signal dom (BitVec 8))
    let doneSig := (doneR : Signal dom Bool)

    -- Offset 9 = first digit.  cnt counts the byte offset of
    -- the wire byte (sop = offset 0 → cnt = 1 next cycle).
    -- We capture when cnt = 9, 10, 11 (the wire byte at those
    -- positions is the digit).
    let p1  := (Signal.pure 1#5  : Signal dom (BitVec 5))
    let p9  := (Signal.pure 9#5  : Signal dom (BitVec 5))
    let p10 := (Signal.pure 10#5 : Signal dom (BitVec 5))
    let p11 := (Signal.pure 11#5 : Signal dom (BitVec 5))
    let at9  := cntSig === p9
    let at10 := cntSig === p10
    let at11 := cntSig === p11

    let cntInc := cntSig + p1
    cnt   <~ Signal.mux sop p1
              (Signal.mux valid cntInc cntSig)
    d0R   <~ Signal.mux (valid &&& at9)  byte d0Sig
    d1R   <~ Signal.mux (valid &&& at10) byte d1Sig
    d2R   <~ Signal.mux (valid &&& at11) byte d2Sig
    doneR <~ valid &&& at11

    -- Combine digits: status = (d0-'0')*100 + (d1-'0')*10 +
    -- (d2-'0').  All on 16-bit signals.
    let p30 := (Signal.pure (c0 : BitVec 8) : Signal dom (BitVec 8))
    let p100_16 := (Signal.pure (100#16 : BitVec 16) : Signal dom (BitVec 16))
    let p10_16  := (Signal.pure (10#16  : BitVec 16) : Signal dom (BitVec 16))
    let d0Num   := d0Sig - p30
    let d1Num   := d1Sig - p30
    let d2Num   := d2Sig - p30
    -- Zero-extend each digit to 16 bits via concat.
    let p0_8 := (Signal.pure (0#8 : BitVec 8) : Signal dom (BitVec 8))
    let d0Wide := p0_8 ++ d0Num
    let d1Wide := p0_8 ++ d1Num
    let d2Wide := p0_8 ++ d2Num
    let d0_100 := d0Wide * p100_16
    let d1_10  := d1Wide * p10_16
    let part1  := d0_100 + d1_10
    let statusOut := part1 + d2Wide

    return ({ status := statusOut
            , done   := doneSig
            } : HttpStatusParserOut dom)

end Sparkle.IP.Net.HTTP
