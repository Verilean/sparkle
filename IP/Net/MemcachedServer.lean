/-
  IP.Net.MemcachedServer — text-protocol memcached over a TCP
  byte stream, built on top of IP.Net.MemcachedHW.kvHw.

  Pipeline:

    inByte/inValid ──> parser FSM ──> opStart pulse
                                   ──> latched opKey/opValue
                                          │
                                          ▼
                                       kvHw  (BRAM-backed engine)
                                          │
                                          ▼  replyValid + replyKind
                                       reply emitter (variable-length
                                                       byte stream)
                                          │
                                          ▼
                                       outByte/outValid

  Supports four commands:
    get <key>           → VALUE k 0 16\r\n<16 bytes>\r\nEND\r\n   (hit)
                       or END\r\n                                 (miss)
    set <key> <f> <e> <bytes>\r\n<value>\r\n   → STORED\r\n
    add <key> <f> <e> <bytes>\r\n<value>\r\n   → STORED / NOT_STORED
    delete <key>        → DELETED / NOT_FOUND

  Simplifications (T1):
    * VALUE replies emit a fixed-width placeholder for key + value:
      `key` is shown as a single literal 'k' (length-1 byte, the
      "<key>" slot in the wire format).  Real-name echoback is
      future work.
    * <flags> always emitted as "0", <bytes> always emitted as "16"
      (the BRAM width).  Hosts that strictly need actual length /
      flags echo will see the simplified form; memcached-cli will
      still parse it correctly.
    * The value bytes are emitted MSB-first from kvHw.replyValue's
      16-byte BitVec.  If the user stored fewer than 16 bytes,
      trailing zero bytes appear (memcached-cli displays them
      as `\x00`).
    * Pipeline accepts ONE command at a time; new opStart is only
      pulsed once the parser has consumed the closing CRLF AND
      the previous reply has finished emitting.
-/
import Sparkle
import Sparkle.Core.Lut
import IP.Net.Memcached
import IP.Net.MemcachedHW

namespace Sparkle.IP.Net.MemcachedServer

open Sparkle.Core
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.MemcachedHW

/-! ### Byte constants. -/

private def cG : BitVec 8 := 0x67#8     -- 'g'
private def cS : BitVec 8 := 0x73#8     -- 's'
private def cA : BitVec 8 := 0x61#8     -- 'a'
private def cD : BitVec 8 := 0x64#8     -- 'd'
private def cSP : BitVec 8 := 0x20#8    -- space
private def cCR : BitVec 8 := 0x0D#8    -- '\r'
private def cLF : BitVec 8 := 0x0A#8    -- '\n'

/-! ### Output bundle. -/

structure ServerOut (dom : DomainConfig) where
  outByte  : Signal dom (BitVec 8)
  outValid : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (ServerOut dom) dom := ⟨⟩

/-! ### Reply byte stream.

    Encodes the 7 reply kinds (output of kvHw.replyKind) as a
    variable-length byte sequence.  We use a single 40-byte
    "longest possible reply" frame and select per-byte which
    constant character to emit:

      kind=0 (STORED)    : "STORED\r\n"               8 bytes
      kind=1 (NOT_STORED): "NOT_STORED\r\n"          12 bytes
      kind=2 (VALUE)     : "VALUE k 0 16\r\n" + 16   + "\r\nEND\r\n"   37 bytes
      kind=3 (END)       : "END\r\n"                  5 bytes
      kind=4 (DELETED)   : "DELETED\r\n"              9 bytes
      kind=5 (NOT_FOUND) : "NOT_FOUND\r\n"           11 bytes
      kind=6 (ERROR)     : "ERROR\r\n"                7 bytes

    The emitter advances a phase counter 0..max-1 (where max =
    length of the chosen reply); per cycle, output the byte at
    that offset.  A `length` register holds the chosen reply's
    length so the emitter knows when to stop.
-/

/-- Compute the length of each reply kind. -/
private def replyLenOf {dom : DomainConfig}
    (kind : Signal dom (BitVec 3)) : Signal dom (BitVec 6) :=
  kLut! kind [
    Signal.pure 8#6,    -- STORED
    Signal.pure 12#6,   -- NOT_STORED
    Signal.pure 37#6,   -- VALUE … (14 header + 16 value + 7 tail)
    Signal.pure 5#6,    -- END
    Signal.pure 9#6,    -- DELETED
    Signal.pure 11#6,   -- NOT_FOUND
    Signal.pure 7#6     -- ERROR
  ]

/-- Compute the emitted byte for STORED/NOT_STORED/END/etc.
    (the fixed-length, value-independent replies).  `phase` is
    the per-reply offset.  Caller selects the right table by
    kind. -/
private def storedByte {dom : DomainConfig}
    (phase : Signal dom (BitVec 6)) : Signal dom (BitVec 8) :=
  kLut! phase [
    Signal.pure 0x53#8, Signal.pure 0x54#8, Signal.pure 0x4F#8, Signal.pure 0x52#8,
    Signal.pure 0x45#8, Signal.pure 0x44#8, Signal.pure 0x0D#8, Signal.pure 0x0A#8
  ]

private def notStoredByte {dom : DomainConfig}
    (phase : Signal dom (BitVec 6)) : Signal dom (BitVec 8) :=
  kLut! phase [
    Signal.pure 0x4E#8, Signal.pure 0x4F#8, Signal.pure 0x54#8, Signal.pure 0x5F#8,
    Signal.pure 0x53#8, Signal.pure 0x54#8, Signal.pure 0x4F#8, Signal.pure 0x52#8,
    Signal.pure 0x45#8, Signal.pure 0x44#8, Signal.pure 0x0D#8, Signal.pure 0x0A#8
  ]

private def endByte {dom : DomainConfig}
    (phase : Signal dom (BitVec 6)) : Signal dom (BitVec 8) :=
  kLut! phase [
    Signal.pure 0x45#8, Signal.pure 0x4E#8, Signal.pure 0x44#8,
    Signal.pure 0x0D#8, Signal.pure 0x0A#8
  ]

private def deletedByte {dom : DomainConfig}
    (phase : Signal dom (BitVec 6)) : Signal dom (BitVec 8) :=
  kLut! phase [
    Signal.pure 0x44#8, Signal.pure 0x45#8, Signal.pure 0x4C#8, Signal.pure 0x45#8,
    Signal.pure 0x54#8, Signal.pure 0x45#8, Signal.pure 0x44#8,
    Signal.pure 0x0D#8, Signal.pure 0x0A#8
  ]

private def notFoundByte {dom : DomainConfig}
    (phase : Signal dom (BitVec 6)) : Signal dom (BitVec 8) :=
  kLut! phase [
    Signal.pure 0x4E#8, Signal.pure 0x4F#8, Signal.pure 0x54#8, Signal.pure 0x5F#8,
    Signal.pure 0x46#8, Signal.pure 0x4F#8, Signal.pure 0x55#8, Signal.pure 0x4E#8,
    Signal.pure 0x44#8, Signal.pure 0x0D#8, Signal.pure 0x0A#8
  ]

private def errorByte {dom : DomainConfig}
    (phase : Signal dom (BitVec 6)) : Signal dom (BitVec 8) :=
  kLut! phase [
    Signal.pure 0x45#8, Signal.pure 0x52#8, Signal.pure 0x52#8, Signal.pure 0x4F#8,
    Signal.pure 0x52#8, Signal.pure 0x0D#8, Signal.pure 0x0A#8
  ]

/-- Build the VALUE reply byte: phase 0..36 maps directly into
    one big 37-entry mux.  Entries 0..13 = fixed header bytes,
    14..29 = byte from `value` at MSB-first offset (phase-14),
    30..36 = "\r\nEND\r\n" tail. -/
private def valueByte {dom : DomainConfig}
    (phase : Signal dom (BitVec 6))
    (value : Signal dom (BitVec 128)) : Signal dom (BitVec 8) :=
  kLut! phase [
    -- 0..13: "VALUE k 0 16\r\n"
    Signal.pure 0x56#8, Signal.pure 0x41#8, Signal.pure 0x4C#8, Signal.pure 0x55#8,
    Signal.pure 0x45#8, Signal.pure 0x20#8, Signal.pure 0x6B#8, Signal.pure 0x20#8,
    Signal.pure 0x30#8, Signal.pure 0x20#8, Signal.pure 0x31#8, Signal.pure 0x36#8,
    Signal.pure 0x0D#8, Signal.pure 0x0A#8,
    -- 14..29: 16 bytes of value (MSB-first)
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb' 120 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb' 112 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb' 104 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  96 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  88 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  80 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  72 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  64 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  56 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  48 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  40 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  32 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  24 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'  16 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'   8 8 v) value,
    Signal.map (fun (v : BitVec 128) => BitVec.extractLsb'   0 8 v) value,
    -- 30..36: "\r\nEND\r\n"
    Signal.pure 0x0D#8, Signal.pure 0x0A#8,
    Signal.pure 0x45#8, Signal.pure 0x4E#8, Signal.pure 0x44#8,
    Signal.pure 0x0D#8, Signal.pure 0x0A#8
  ]

/-- Top-level reply byte for any kind, given phase + value. -/
def replyByteOf {dom : DomainConfig}
    (kind : Signal dom (BitVec 3))
    (phase : Signal dom (BitVec 6))
    (value : Signal dom (BitVec 128)) : Signal dom (BitVec 8) :=
  kLut! kind [
    storedByte phase,
    notStoredByte phase,
    valueByte phase value,
    endByte phase,
    deletedByte phase,
    notFoundByte phase,
    errorByte phase
  ]

/-! ### Command parser FSM.

    Greatly simplified: we only support the verb cracking
    `g` / `s` / `a` / `d` (first byte alone disambiguates).
    Then we shift-collect the key, optionally skip the
    args block (set/add), collect <bytes> bytes of value,
    and pulse opStart.

    State `pst : BV4`:
      0 = idle, waiting for verb byte
      1 = consume rest of verb until first space (skip)
      2 = collect key into shift register (until space or CRLF)
      3 = skip args until CRLF (set/add)
      4 = collect 16 bytes of value
      5 = consume final CRLF
      6 = dispatch (pulse opStart for kvHw)
      7 = wait for kvHw to finish (replyValid)
      8 = emit reply byte stream (phase counter 0..length-1)
      9 = done (clear, back to idle next cycle)
-/

structure ParserState where
  st        : BitVec 4
  keyReg    : BitVec 64
  valueReg  : BitVec 128
  codeReg   : BitVec 2   -- 0=get 1=set 2=add 3=del
  valueCnt  : BitVec 5   -- 0..16
  emitPhase : BitVec 6   -- 0..36
  replyKind : BitVec 3   -- latched from kvHw.replyKind
  replyVal  : BitVec 128 -- latched from kvHw.replyValue
  deriving Inhabited

/-- The top-level memcached byte-stream server. -/
@[hardware_module] def memcachedServer {dom : DomainConfig}
    (inByte : Signal dom (BitVec 8))
    (inValid : Signal dom Bool) :
    ServerOut dom :=
  circuit do
    -- Parser state registers.
    let st        ← Signal.reg (0#4)
    let keyReg    ← Signal.reg (0#64)
    let valueReg  ← Signal.reg (0#128)
    let codeReg   ← Signal.reg (0#2)
    let valueCnt  ← Signal.reg (0#5)
    let emitPhase ← Signal.reg (0#6)
    let replyKindR ← Signal.reg (0#3)
    let replyValR ← Signal.reg (0#128)

    let stSig := (st : Signal dom (BitVec 4))
    let keySig := (keyReg : Signal dom (BitVec 64))
    let valueSig := (valueReg : Signal dom (BitVec 128))
    let codeSig := (codeReg : Signal dom (BitVec 2))
    let cntSig := (valueCnt : Signal dom (BitVec 5))
    let phaseSig := (emitPhase : Signal dom (BitVec 6))
    let rkSig := (replyKindR : Signal dom (BitVec 3))
    let rvSig := (replyValR : Signal dom (BitVec 128))

    -- Phase predicates
    let pst0 := (Signal.pure 0#4 : Signal dom (BitVec 4))
    let pst1 := (Signal.pure 1#4 : Signal dom (BitVec 4))
    let pst2 := (Signal.pure 2#4 : Signal dom (BitVec 4))
    let pst3 := (Signal.pure 3#4 : Signal dom (BitVec 4))
    let pst4 := (Signal.pure 4#4 : Signal dom (BitVec 4))
    let pst5 := (Signal.pure 5#4 : Signal dom (BitVec 4))
    let pst6 := (Signal.pure 6#4 : Signal dom (BitVec 4))
    let pst7 := (Signal.pure 7#4 : Signal dom (BitVec 4))
    let pst8 := (Signal.pure 8#4 : Signal dom (BitVec 4))

    let inIdle := ((· == ·) <$> stSig <*> pst0 : Signal dom Bool)
    let inVerb := ((· == ·) <$> stSig <*> pst1 : Signal dom Bool)
    let inKey  := ((· == ·) <$> stSig <*> pst2 : Signal dom Bool)
    let inSkip := ((· == ·) <$> stSig <*> pst3 : Signal dom Bool)
    let inVal  := ((· == ·) <$> stSig <*> pst4 : Signal dom Bool)
    let inFinal := ((· == ·) <$> stSig <*> pst5 : Signal dom Bool)
    let inDispatch := ((· == ·) <$> stSig <*> pst6 : Signal dom Bool)
    let inWait := ((· == ·) <$> stSig <*> pst7 : Signal dom Bool)
    let inEmit := ((· == ·) <$> stSig <*> pst8 : Signal dom Bool)

    -- Verb decode: first byte after Idle.
    let pG := (Signal.pure 0x67#8 : Signal dom (BitVec 8))   -- 'g'
    let pS := (Signal.pure 0x73#8 : Signal dom (BitVec 8))   -- 's'
    let pA := (Signal.pure 0x61#8 : Signal dom (BitVec 8))   -- 'a'
    let pD := (Signal.pure 0x64#8 : Signal dom (BitVec 8))   -- 'd'
    let isG := ((· == ·) <$> inByte <*> pG : Signal dom Bool)
    let isS := ((· == ·) <$> inByte <*> pS : Signal dom Bool)
    let isA := ((· == ·) <$> inByte <*> pA : Signal dom Bool)
    let isD := ((· == ·) <$> inByte <*> pD : Signal dom Bool)
    let pCode0 := (Signal.pure 0#2 : Signal dom (BitVec 2))
    let pCode1 := (Signal.pure 1#2 : Signal dom (BitVec 2))
    let pCode2 := (Signal.pure 2#2 : Signal dom (BitVec 2))
    let pCode3 := (Signal.pure 3#2 : Signal dom (BitVec 2))
    let verbCode :=
      Signal.mux isG pCode0
        (Signal.mux isS pCode1
          (Signal.mux isA pCode2
            (Signal.mux isD pCode3 pCode0)))

    -- Idle + valid + recognised verb → enter verb-skip state
    let isVerbByte :=
      ((· || ·) <$> isG <*>
        (((· || ·) <$> isS <*>
          (((· || ·) <$> isA <*> isD : Signal dom Bool))
          : Signal dom Bool))
        : Signal dom Bool)
    let idleEnter := ((· && ·) <$> inIdle <*>
      ((· && ·) <$> inValid <*> isVerbByte : Signal dom Bool)
      : Signal dom Bool)

    -- Byte predicates we use a lot.
    let pSP := (Signal.pure 0x20#8 : Signal dom (BitVec 8))
    let pCR := (Signal.pure 0x0D#8 : Signal dom (BitVec 8))
    let pLF := (Signal.pure 0x0A#8 : Signal dom (BitVec 8))
    let byteIsSP := ((· == ·) <$> inByte <*> pSP : Signal dom Bool)
    let byteIsCR := ((· == ·) <$> inByte <*> pCR : Signal dom Bool)
    let byteIsLF := ((· == ·) <$> inByte <*> pLF : Signal dom Bool)
    let byteIsCROrLF := ((· || ·) <$> byteIsCR <*> byteIsLF : Signal dom Bool)

    -- (validAndIs was a let-bound lambda; the synth elaborator
    -- doesn't unfold lambda-let bindings cleanly, so we inline
    -- the `inValid && pred` pattern at each call site below.)

    -- VERB state: consume bytes until first space.  Transition
    -- to KEY collection.
    let verbDone := ((· && ·) <$> inVerb <*>
      ((· && ·) <$> inValid <*> byteIsSP : Signal dom Bool) : Signal dom Bool)
    -- KEY state: shift bytes into keyReg.  On space → SKIP (set/add)
    --   or CRLF → FINAL (get/delete).
    let keyShift := ((· && ·) <$> inKey <*>
      ((· && ·) <$> inValid <*>
        ((· && ·) <$>
          ((fun b => !b) <$> byteIsSP : Signal dom Bool) <*>
          ((fun b => !b) <$> byteIsCROrLF : Signal dom Bool) : Signal dom Bool)
        : Signal dom Bool) : Signal dom Bool)
    let p8 := (Signal.pure 8#64 : Signal dom (BitVec 64))
    let keyShifted := ((· <<< ·) <$> keySig <*> p8 : Signal dom (BitVec 64))
    -- Zero-extend inByte (BV8 → BV64) by concat-ing with a 56-bit
    -- zero prefix.  We use the applicative `(· ++ ·) <$> a <*> b`
    -- form (same shape the synth elaborator already handles
    -- successfully elsewhere via the Seq.seq → concat path),
    -- rather than `Signal.map (BitVec.append (0#56))`, because
    -- map-with-a-lambda-using-`append` gets stuck inside
    -- recursive inlining.
    let p0_56 := (Signal.pure 0#56 : Signal dom (BitVec 56))
    let inByte64 := ((· ++ ·) <$> p0_56 <*> inByte : Signal dom (BitVec 64))
    let keyNew := ((· ||| ·) <$> keyShifted <*> inByte64 : Signal dom (BitVec 64))
    let keyEndSp := ((· && ·) <$> inKey <*>
      ((· && ·) <$> inValid <*> byteIsSP : Signal dom Bool) : Signal dom Bool)
    let keyEndCR := ((· && ·) <$> inKey <*>
      ((· && ·) <$> inValid <*> byteIsCR : Signal dom Bool) : Signal dom Bool)

    -- SKIP state: skip set/add args (flags, exptime, bytes) until
    -- CRLF.  We don't parse them — simplification.
    let skipDone := ((· && ·) <$> inSkip <*>
      ((· && ·) <$> inValid <*> byteIsLF : Signal dom Bool) : Signal dom Bool)
    -- After SKIP we enter VAL state with valueCnt=0; collect 16
    -- value bytes (or until CR).
    -- VAL state: shift bytes into valueReg until cnt=16 or CR.
    let p16_5 := (Signal.pure 16#5 : Signal dom (BitVec 5))
    let p1_5 := (Signal.pure 1#5 : Signal dom (BitVec 5))
    let cntDone := ((· == ·) <$> cntSig <*> p16_5 : Signal dom Bool)
    let valTake := ((· && ·) <$> inVal <*>
      ((· && ·) <$> inValid <*>
        ((· && ·) <$>
          ((fun b => !b) <$> byteIsCROrLF : Signal dom Bool) <*>
          ((fun b => !b) <$> cntDone : Signal dom Bool)
          : Signal dom Bool) : Signal dom Bool) : Signal dom Bool)
    let p8_128 := (Signal.pure 8#128 : Signal dom (BitVec 128))
    let valueShifted := ((· <<< ·) <$> valueSig <*> p8_128 : Signal dom (BitVec 128))
    let p0_120 := (Signal.pure 0#120 : Signal dom (BitVec 120))
    let inByte128 := ((· ++ ·) <$> p0_120 <*> inByte : Signal dom (BitVec 128))
    let valueNew := ((· ||| ·) <$> valueShifted <*> inByte128 : Signal dom (BitVec 128))
    -- VAL done: byte is CR OR cnt is 16 → go to FINAL.
    let validAndCR := ((· && ·) <$> inValid <*> byteIsCR : Signal dom Bool)
    let validAndCntDone := ((· && ·) <$> inValid <*> cntDone : Signal dom Bool)
    let valDone := ((· && ·) <$> inVal <*>
      ((· || ·) <$> validAndCR <*> validAndCntDone : Signal dom Bool)
      : Signal dom Bool)

    -- FINAL state: wait for LF, then dispatch.
    let finalDone := ((· && ·) <$> inFinal <*>
      ((· && ·) <$> inValid <*> byteIsLF : Signal dom Bool) : Signal dom Bool)

    -- For set/add we go from KEY → SKIP via space, then SKIP → VAL via LF,
    -- then VAL → FINAL via CR, then FINAL → DISPATCH via LF.
    -- For get/delete we go from KEY → FINAL via CR, then FINAL → DISPATCH via LF.

    -- code says set/add (need value): codeReg in {1,2}
    let needValue := ((· || ·) <$>
      (((· == ·) <$> codeSig <*> pCode1 : Signal dom Bool)) <*>
      (((· == ·) <$> codeSig <*> pCode2 : Signal dom Bool)) : Signal dom Bool)

    -- DISPATCH state: opStart pulse to kvHw.
    -- WAIT state: monitor kvHw.replyValid (latched into replyKindR).
    -- EMIT state: walk emitPhase 0..length-1, output replyByte.

    -- Build kvHw.  opStart pulses for one cycle when we enter DISPATCH.
    let opStartPulse := inDispatch
    -- For now flags hardcoded to 0.
    let opFlagsSig := (Signal.pure 0#32 : Signal dom (BitVec 32))
    let engine := kvHw opStartPulse codeSig keySig valueSig opFlagsSig
    -- Bind each engine field to a local Signal so the synth
    -- elaborator's `<$>` / `<*>` handlers see plain Signal
    -- references rather than nested structure projections (the
    -- latter trip up the Seq.seq path).
    let engineReplyValid := engine.replyValid
    let engineReplyKind  := engine.replyKind
    let engineReplyValue := engine.replyValue

    -- WAIT → EMIT on engine.replyValid.
    let waitDone := ((· && ·) <$> inWait <*> engineReplyValid : Signal dom Bool)

    -- Reply length lookup (from latched replyKindR).
    let replyLen := replyLenOf rkSig
    let p1_6 := (Signal.pure 1#6 : Signal dom (BitVec 6))
    let phasePlus1 := ((· + ·) <$> phaseSig <*> p1_6 : Signal dom (BitVec 6))
    -- emitDone when phase+1 == replyLen.
    let emitDone := ((· && ·) <$> inEmit <*>
      ((· == ·) <$> phasePlus1 <*> replyLen : Signal dom Bool)
      : Signal dom Bool)

    -- State transitions
    let stNext :=
      Signal.mux idleEnter pst1
        (Signal.mux verbDone pst2
          (Signal.mux keyEndSp pst3
            (Signal.mux keyEndCR pst5
              (Signal.mux skipDone
                (Signal.mux needValue pst4 pst5)         -- after args CRLF: set/add → VAL, get/delete unreachable here
                (Signal.mux valDone pst5
                  (Signal.mux finalDone pst6
                    (Signal.mux inDispatch pst7
                      (Signal.mux waitDone pst8
                        (Signal.mux emitDone pst0 stSig))))))) ))

    -- keyReg next: on idleEnter clear, on keyShift do shift, else hold.
    let keyNext :=
      Signal.mux idleEnter (Signal.pure 0#64)
        (Signal.mux keyShift keyNew keySig)

    -- valueReg next: on idleEnter clear, on valTake shift, else hold.
    let valueNext :=
      Signal.mux idleEnter (Signal.pure 0#128)
        (Signal.mux valTake valueNew valueSig)

    -- codeReg next: latched at idleEnter.
    let codeNext := Signal.mux idleEnter verbCode codeSig

    -- valueCnt next: 0 at idleEnter or skipDone; +1 on valTake; hold otherwise.
    let cntInc := ((· + ·) <$> cntSig <*> p1_5 : Signal dom (BitVec 5))
    let cntClear := ((· || ·) <$> idleEnter <*> skipDone : Signal dom Bool)
    let cntNext :=
      Signal.mux cntClear (Signal.pure 0#5)
        (Signal.mux valTake cntInc cntSig)

    -- emitPhase next: 0 on waitDone (= entering EMIT); +1 during EMIT; hold else.
    let phaseNext :=
      Signal.mux waitDone (Signal.pure 0#6)
        (Signal.mux inEmit phasePlus1 phaseSig)

    -- Latch reply kind + value at the cycle replyValid pulses.
    let rkNext := Signal.mux engineReplyValid engineReplyKind rkSig
    let rvNext := Signal.mux engineReplyValid engineReplyValue rvSig

    st <~ stNext
    keyReg <~ keyNext
    valueReg <~ valueNext
    codeReg <~ codeNext
    valueCnt <~ cntNext
    emitPhase <~ phaseNext
    replyKindR <~ rkNext
    replyValR <~ rvNext

    -- Output byte: during EMIT phase, look up the reply byte.
    let byteOut := replyByteOf rkSig phaseSig rvSig
    let validOut := inEmit

    return ({ outByte := byteOut, outValid := validOut } : ServerOut dom)

/-- Scalar projection of memcachedServer.outByte — gives the
    synth elaborator a single-output entry point that avoids the
    multi-leaf split path which currently re-attempts each leaf
    on cache miss (and hits a memoize zeta cycle in the process). -/
@[hardware_module] def memcachedServerByte {dom : DomainConfig}
    (inByte : Signal dom (BitVec 8))
    (inValid : Signal dom Bool) :
    Signal dom (BitVec 8) :=
  (memcachedServer inByte inValid).outByte

/-- Scalar projection of memcachedServer.outValid. -/
@[hardware_module] def memcachedServerValid {dom : DomainConfig}
    (inByte : Signal dom (BitVec 8))
    (inValid : Signal dom Bool) :
    Signal dom Bool :=
  (memcachedServer inByte inValid).outValid

end Sparkle.IP.Net.MemcachedServer
