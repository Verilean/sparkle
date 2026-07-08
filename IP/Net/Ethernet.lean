/-
  IP.Net.Ethernet — minimal Ethernet RX framer (byte/cycle MVP).

  Pipeline contract (one cycle per byte; preamble/SFD assumed already
  stripped by the PHY-side MAC):

    cycle 0 .. 5  : 6 bytes of destination MAC, MSB-first on the wire
    cycle 6 .. 11 : 6 bytes of source      MAC, MSB-first
    cycle 12, 13  : 2 bytes of EthType,        MSB-first
    cycle 14 ..   : payload bytes (passed through to `payloadByte`
                    with `payloadValid` high; the consumer is
                    expected to detect EOF from upstream `eop`)

  Inputs (Signal dom):
    rxByte    : the next byte from the MAC
    rxValid   : asserted when `rxByte` carries a real beat
    rxSop     : start-of-frame strobe (one-cycle pulse aligned with
                cycle-0 byte of the frame)
    rxEop     : end-of-frame strobe (one-cycle pulse aligned with
                the last byte; not used by the parser yet but
                tracked so future FCS / IPv4 logic can latch)

  Outputs (Signal dom):
    dmac           : full 48-bit destination MAC, valid once `state`
                     has passed the DMAC field
    smac           : full 48-bit source MAC
    ethType        : 16-bit EthType
    payloadByte    : current payload byte (zero when not in payload
                     state)
    payloadValid   : high in PAYLOAD state with `rxValid` high
    hdrDone        : single-cycle strobe one cycle after EthType byte
                     #1 is latched.  Consumers (IPv4 parser) start
                     their own counter from `hdrDone` + 1.

  Implementation notes:
    * State is a `BitVec 5` so the byte counter doubles as the
      transition index (0..13 for header, 14..30 for early payload —
      we don't actually need a precise count past the header).
    * `circuit do`'s `match` lowers to nested `Signal.mux` chains
      on each `state === pat` (see CLAUDE.md hardware style rules),
      which is exactly the case-statement shape Verilog wants.
    * No FCS check yet — the FCS engine (`IP.Net.CRC32.crc32Engine`)
      can be wired up at the top level once the frame iterator is
      wide-bus.

  Future work (tracked as task #341 sub-bullets):
    * Wide-bus (XGMII 64-bit/cycle) variant.
    * FCS check + `fcsOk` output.
    * Minimum-frame-size padding handling.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.Ethernet

/-! ### State encoding (BitVec 5)

    We pack the byte counter directly into the state register so the
    transition is just `state + 1` while valid bytes arrive.  Values
    0..13 walk through the header; 14 means "in payload".  Sticky
    at 14 until `rxSop` re-arms the parser. -/
private abbrev sIdle    : BitVec 5 := 0#5    -- waiting for SOP

-- Header byte indices.  Names mirror the cycle-0 ... cycle-13 walk:
--   0..5 : DMAC bytes 0..5 (MSB-first on the wire, so byte 0 is dmac[47:40])
--   6..11: SMAC bytes 0..5
--   12,13: EthType bytes 0..1

private abbrev sPayload : BitVec 5 := 14#5   -- in payload, sticky

/-- Reset the parser state.  Public so tests / TB drivers can pulse
    a parser-side reset without touching the Domain's global rst. -/
@[inline] private def isHeader (st : BitVec 5) : Bool :=
  st.ult 14#5

/-! ### Signal-level helpers — kept outside `circuit do` so we get
    the full Lean `let : T :=` syntax for type annotations.  Each
    one uses only Signal-native operators so the IR elaborator can
    inline them. -/

/-- Shift-left-by-8 and OR a zero-extended byte into a 48-bit
    accumulator.  Used for DMAC / SMAC byte-by-byte assembly. -/
@[inline] private def shiftIn48 {dom : DomainConfig}
    (acc : Signal dom (BitVec 48)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 48) :=
  (acc <<< (8#48 : BitVec 48)) ||| ((0#40 : BitVec 40) ++ b)

/-- Shift-left-by-8 and OR a zero-extended byte into a 16-bit
    accumulator.  Used for the 2-byte EthType field. -/
@[inline] private def shiftIn16 {dom : DomainConfig}
    (acc : Signal dom (BitVec 16)) (b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 16) :=
  (acc <<< (8#16 : BitVec 16)) ||| ((0#8 : BitVec 8) ++ b)

/-! ### The byte-feed framer. -/

structure RxIn (dom : DomainConfig) where
  byte  : Signal dom (BitVec 8)
  valid : Signal dom Bool
  sop   : Signal dom Bool
  eop   : Signal dom Bool

structure RxOut (dom : DomainConfig) where
  dmac          : Signal dom (BitVec 48)
  smac          : Signal dom (BitVec 48)
  ethType       : Signal dom (BitVec 16)
  payloadByte   : Signal dom (BitVec 8)
  payloadValid  : Signal dom Bool
  hdrDone       : Signal dom Bool

/-- `HasDomain` instance lets `circuit do { … return { dmac :=
    …, smac := …, … } }` recover the `dom` from `RxOut`.  One
    line per user record; see `Sparkle/Core/CircuitMonad.lean`
    for the `HasDomain` class. -/
instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (RxOut dom) dom := ⟨⟩

/-! ### Synthesis-friendly entry point.

    RX framer: walks the per-byte state machine described above
    and shift-registers each header byte into its destination
    48-bit / 16-bit field.

    Sticky behaviour on EOF: `dmac` / `smac` / `ethType` keep
    their last-frame values until the next SOP arrives, so the
    consumer has the full cycle window after `hdrDone` to
    inspect them.

    `rxFramer` takes each input Signal as an independent
    parameter (rather than bundling them in an `RxIn` record).
    This matches the convention every other Sparkle IP follows
    (see `IP/Arbiter/RoundRobin.lean:arbiterSignal`,
    `IP/RV32/SoCVerilog.lean:rv32iSoCSynth`, etc.) and lets
    `#synthesizeVerilog rxFramer` succeed without the IR
    elaborator needing to unpack record-typed inputs.

    The record-bundled convenience wrapper is `rxFramerOfRxIn`
    below — use that from simulation drivers, where the caller
    already has an `RxIn` record assembled.

    `_eop` is currently unused; it's threaded in so future
    FCS-check / minimum-length-padding logic can latch on the
    end-of-frame edge without a signature change. -/
def rxFramer {dom : DomainConfig}
    (byte : Signal dom (BitVec 8))
    (valid : Signal dom Bool)
    (sop : Signal dom Bool)
    (_eop : Signal dom Bool) :
    RxOut dom :=
  circuit do
    -- Byte counter / state.
    let st       ← Signal.reg sIdle
    -- 48-bit DMAC / SMAC accumulator: shift-left-by-8 each header byte.
    let dmacAcc  ← Signal.reg (0#48)
    let smacAcc  ← Signal.reg (0#48)
    -- 16-bit EthType accumulator.
    let etAcc    ← Signal.reg (0#16)
    -- 1-cycle pulse latched the cycle after the last header byte.
    let hdrDoneR ← Signal.reg false

    -- Per-cycle "next-value" for each accumulator.  The actual
    -- shift+OR logic lives in `shiftIn48` / `shiftIn16` above; we
    -- keep them outside `circuit do` because the macro doesn't
    -- accept `let x : T := …` with a type annotation, which the
    -- type-class search needs to disambiguate the Reg→Signal
    -- coercion + the HShiftLeft (Signal _, BitVec _) instance.
    let dmacNext := shiftIn48 dmacAcc byte
    let smacNext := shiftIn48 smacAcc byte
    let etNext   := shiftIn16 etAcc   byte

    -- Drive state.
    -- "Which field am I in?" derived from `st`.  Signal-Bool
    -- expressions; `circuit do`'s `match` doesn't accept
    -- `|`-separated patterns, so we collapse the 0..13 walk into
    -- predicates and gate the per-field accumulator updates with
    -- per-predicate `Signal.mux` chains rather than nested arms.
    -- Pull `st` out as an explicit Signal so the `===` instance
    -- search has no Reg-vs-Signal ambiguity to chew on.  `circuit
    -- do`'s `let` doesn't accept a type annotation on the binder,
    -- but the RHS is a normal Lean term so the ascription works
    -- there.
    let stSig := (st : Signal dom (BitVec 5))
    let isDmacByte :=
      (stSig === Signal.pure 1#5) ||| (stSig === Signal.pure 2#5) |||
      (stSig === Signal.pure 3#5) ||| (stSig === Signal.pure 4#5) |||
      (stSig === Signal.pure 5#5)
    let isSmacByte :=
      (stSig === Signal.pure 6#5)  ||| (stSig === Signal.pure 7#5)  |||
      (stSig === Signal.pure 8#5)  ||| (stSig === Signal.pure 9#5)  |||
      (stSig === Signal.pure 10#5) ||| (stSig === Signal.pure 11#5)
    let isEtByte0 := stSig === Signal.pure 12#5
    let isEtByte1 := stSig === Signal.pure 13#5
    let isHeaderByte :=
      isDmacByte ||| isSmacByte ||| isEtByte0 ||| isEtByte1

    if sop then
      -- SOP cycle: cycle-0 byte is DMAC[47:40].  Latch it, reset
      -- the other accumulators, and arm for byte 1.
      st       <~ 1#5
      dmacAcc  <~ dmacNext
      smacAcc  <~ 0#48
      etAcc    <~ 0#16
      hdrDoneR <~ false
    else
      if valid then
        -- Advance state: header bytes increment; on byte 13 jump
        -- to PAYLOAD; in PAYLOAD stay sticky.
        let dmacReadSig := (dmacAcc : Signal dom (BitVec 48))
        let smacReadSig := (smacAcc : Signal dom (BitVec 48))
        let etReadSig   := (etAcc   : Signal dom (BitVec 16))
        let stNext :=
          Signal.mux isEtByte1
            (Signal.pure (dom := dom) sPayload)
            (Signal.mux isHeaderByte
              (stSig + Signal.pure (dom := dom) (1#5 : BitVec 5))
              stSig)
        -- DMAC accumulator updates on the 5 DMAC bytes.
        let dmacNew := Signal.mux isDmacByte dmacNext dmacReadSig
        -- SMAC accumulator updates on the 6 SMAC bytes.
        let smacNew := Signal.mux isSmacByte smacNext smacReadSig
        -- EthType accumulator updates on either EthType byte.
        let etShift := isEtByte0 ||| isEtByte1
        let etNew   := Signal.mux etShift etNext etReadSig
        st       <~ stNext
        dmacAcc  <~ dmacNew
        smacAcc  <~ smacNew
        etAcc    <~ etNew
        hdrDoneR <~ isEtByte1
      else
        st       <~ stSig
        dmacAcc  <~ (dmacAcc : Signal dom (BitVec 48))
        smacAcc  <~ (smacAcc : Signal dom (BitVec 48))
        etAcc    <~ (etAcc   : Signal dom (BitVec 16))
        hdrDoneR <~ (false   : Bool)

    -- Payload pass-through: byte is whatever's on the wire when
    -- we're in the sticky payload state AND the upstream marks
    -- the beat valid.  Outside of payload we report 0/0.
    let inPayload := stSig === Signal.pure sPayload
    let payloadValid := inPayload &&& valid
    let payloadByte  :=
      Signal.mux inPayload byte (Signal.pure (0#8 : BitVec 8))

    -- Named-field return: each output is keyed by its semantic
    -- name, so downstream consumers read `out.dmac` / `out.smac`
    -- / `out.ethType` etc.  Field order in this literal is
    -- irrelevant; only the names matter.
    return ({ dmac         := (dmacAcc : Signal dom (BitVec 48))
            , smac         := (smacAcc : Signal dom (BitVec 48))
            , ethType      := (etAcc   : Signal dom (BitVec 16))
            , payloadByte  := payloadByte
            , payloadValid := payloadValid
            , hdrDone      := (hdrDoneR : Signal dom Bool)
            } : RxOut dom)

/-- Convenience wrapper for simulation drivers that already
    hold an `RxIn` record.  Delegates to `rxFramer` field by
    field.  Not for `#synthesizeVerilog` — use the per-Signal
    `rxFramer` form for synthesis. -/
def rxFramerOfRxIn {dom : DomainConfig} (i : RxIn dom) : RxOut dom :=
  rxFramer i.byte i.valid i.sop i.eop

/-! ### TX framer (byte-feed, one cycle per byte).

    Pipeline contract (mirrors the RX side):
      cycle 0  : `start` pulse arrives; framer latches DMAC/SMAC/
                 EthType from their input wires and begins emitting
                 byte 0 of DMAC on `txByte`.  `txSop` strobes this
                 cycle.
      cycle 1..5  : remaining DMAC bytes
      cycle 6..11 : SMAC bytes
      cycle 12,13 : EthType bytes
      cycle 14..  : payload pass-through.  The caller drives
                    `payloadByte` / `payloadValid` / `payloadLast`
                    per cycle.  `txEop` strobes the cycle that
                    carries the last payload byte (when
                    `payloadLast` is high).

    After `payloadLast`, the framer returns to IDLE and waits for
    the next `start` pulse.  No back-to-back frame support yet —
    the caller must hold `start` low for at least one cycle
    between frames.

    Header inputs (`dmacIn`, `smacIn`, `etIn`) are sampled on the
    `start` cycle and **latched into registers** so the caller is
    free to change them mid-frame without disturbing the in-flight
    transmission.

    Inputs:
      dmacIn       : 48-bit destination MAC (latched on `start`)
      smacIn       : 48-bit source MAC      (latched on `start`)
      etIn         : 16-bit EthType         (latched on `start`)
      payloadByte  : payload byte for the current cycle
      payloadValid : caller has a valid payload byte this cycle
      payloadLast  : this is the last payload byte of the frame
      start        : begin a new frame this cycle

    Outputs:
      txByte       : serialised byte (header or payload)
      txValid      : framer is emitting a real byte this cycle
      txSop        : start-of-frame strobe (one cycle, on byte 0)
      txEop        : end-of-frame strobe (one cycle, on the last
                     payload byte) -/

/-! ### TX state encoding.

    Same 0..13 = header byte index convention as the RX side, plus
    one extra state for "currently passing through payload". -/
private abbrev txIdle    : BitVec 5 := 0#5     -- waiting for start
private abbrev txPayload : BitVec 5 := 15#5    -- payload pass-through

/-- Extract byte `k` (0..5, MSB-first) from a 48-bit MAC.
    Uses the `signal.map (BitVec.extractLsb' lo 8 ·)` idiom that
    every other Sparkle IP uses for bit slices (see
    `IP/RV32/Trap.lean`, `IP/RV32/Bus.lean`). -/
@[inline] private def macByte {dom : DomainConfig}
    (mac : Signal dom (BitVec 48)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (5 - k) * 8
  mac.map (BitVec.extractLsb' lo 8 ·)

/-- Extract byte `k` (0..1, MSB-first) from a 16-bit EthType. -/
@[inline] private def etByte_ {dom : DomainConfig}
    (et : Signal dom (BitVec 16)) (k : Nat) :
    Signal dom (BitVec 8) :=
  let lo := (1 - k) * 8
  et.map (BitVec.extractLsb' lo 8 ·)

/-- Mux among 6 MAC bytes by the cycle-relative index (0..5).
    `eqK` is locally written out as the Applicative form because
    the IR elaborator needs `a === b` (not `===`,
    which desugars to non-`@[reducible]` `Signal.beq`) to lower
    cleanly to `.op .eq` via `handleApplicative`. -/
@[inline] private def macByteMux {dom : DomainConfig}
    (mac : Signal dom (BitVec 48))
    (idx : Signal dom (BitVec 3)) :
    Signal dom (BitVec 8) :=
  let b0 := macByte mac 0
  let b1 := macByte mac 1
  let b2 := macByte mac 2
  let b3 := macByte mac 3
  let b4 := macByte mac 4
  let b5 := macByte mac 5
  let pk0 : Signal dom (BitVec 3) := Signal.pure 0#3
  let pk1 : Signal dom (BitVec 3) := Signal.pure 1#3
  let pk2 : Signal dom (BitVec 3) := Signal.pure 2#3
  let pk3 : Signal dom (BitVec 3) := Signal.pure 3#3
  let pk4 : Signal dom (BitVec 3) := Signal.pure 4#3
  Signal.mux (idx === pk0) b0
    (Signal.mux (idx === pk1) b1
      (Signal.mux (idx === pk2) b2
        (Signal.mux (idx === pk3) b3
          (Signal.mux (idx === pk4) b4 b5))))

/-- Mux among 2 EthType bytes by index (0..1). -/
@[inline] private def etByteMux {dom : DomainConfig}
    (et : Signal dom (BitVec 16))
    (idx : Signal dom Bool) :
    Signal dom (BitVec 8) :=
  let b0 := etByte_ et 0
  let b1 := etByte_ et 1
  Signal.mux idx b1 b0

structure TxOut (dom : DomainConfig) where
  txByte  : Signal dom (BitVec 8)
  txValid : Signal dom Bool
  txSop   : Signal dom Bool
  txEop   : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TxOut dom) dom := ⟨⟩

def txFramer {dom : DomainConfig}
    (dmacIn : Signal dom (BitVec 48))
    (smacIn : Signal dom (BitVec 48))
    (etIn   : Signal dom (BitVec 16))
    (payloadByte  : Signal dom (BitVec 8))
    (payloadValid : Signal dom Bool)
    (payloadLast  : Signal dom Bool)
    (start        : Signal dom Bool) :
    TxOut dom :=
  circuit do
    let st       ← Signal.reg txIdle
    let dmacReg  ← Signal.reg (0#48)
    let smacReg  ← Signal.reg (0#48)
    let etReg    ← Signal.reg (0#16)

    -- Coerce Reg → Signal via explicit ascription.  Inside
    -- `circuit do` Lean's `let x : T := …` is rejected by the
    -- macro, so use the `(… : T)` form on the rhs instead.
    let stSig   := (st      : Signal dom (BitVec 5))
    let dmacSig := (dmacReg : Signal dom (BitVec 48))
    let smacSig := (smacReg : Signal dom (BitVec 48))
    let etSig   := (etReg   : Signal dom (BitVec 16))

    -- Region predicates.  Conceptually: when `start` pulses we're
    -- on stSig=0 emitting byte 0 of DMAC (live from dmacIn); on
    -- stSig=1..5 we're emitting DMAC bytes 1..5; etc.  When idle
    -- and `start` is low, no emission.
    -- Region predicates: use the explicit Applicative form
    -- `a === b` rather than the `===` infix, which
    -- desugars to `Signal.beq` and isn't `@[reducible]` enough
    -- for the IR elaborator to unfold reliably.  The Applicative
    -- form goes through `handleApplicative` and lowers cleanly
    -- to `.op .eq`.  See `Sparkle/Core/CircuitDo.lean:208`.
    let pIdle    := (Signal.pure txIdle    : Signal dom (BitVec 5))
    let pPayload := (Signal.pure txPayload : Signal dom (BitVec 5))
    let p1       := (Signal.pure 1#5  : Signal dom (BitVec 5))
    let p2       := (Signal.pure 2#5  : Signal dom (BitVec 5))
    let p3       := (Signal.pure 3#5  : Signal dom (BitVec 5))
    let p4       := (Signal.pure 4#5  : Signal dom (BitVec 5))
    let p5       := (Signal.pure 5#5  : Signal dom (BitVec 5))
    let p6       := (Signal.pure 6#5  : Signal dom (BitVec 5))
    let p7       := (Signal.pure 7#5  : Signal dom (BitVec 5))
    let p8       := (Signal.pure 8#5  : Signal dom (BitVec 5))
    let p9       := (Signal.pure 9#5  : Signal dom (BitVec 5))
    let p10      := (Signal.pure 10#5 : Signal dom (BitVec 5))
    let p11      := (Signal.pure 11#5 : Signal dom (BitVec 5))
    let p12      := (Signal.pure 12#5 : Signal dom (BitVec 5))
    let p13      := (Signal.pure 13#5 : Signal dom (BitVec 5))
    let isIdle    := stSig === pIdle
    let isPayload := stSig === pPayload
    let is1  := stSig === p1
    let is2  := stSig === p2
    let is3  := stSig === p3
    let is4  := stSig === p4
    let is5  := stSig === p5
    let is6  := stSig === p6
    let is7  := stSig === p7
    let is8  := stSig === p8
    let is9  := stSig === p9
    let is10 := stSig === p10
    let is11 := stSig === p11
    let is12 := stSig === p12
    let is13 := stSig === p13
    let inDmacRest := is1 ||| is2 ||| is3 ||| is4 ||| is5
    let inDmac     := (start &&& isIdle) ||| inDmacRest
    let inSmac     := is6 ||| is7 ||| is8 ||| is9 ||| is10 ||| is11
    let inEt       := is12 ||| is13
    let inHdr      := inDmac ||| inSmac ||| inEt

    -- Pre-compute the 6 DMAC / 6 SMAC bytes and the 2 EthType
    -- bytes, then pick via the existing per-state predicates
    -- (no Signal-arithmetic on indices needed — every selector
    -- is a `BitVec 5` equality that already lowers to `.op .eq`).
    --
    -- For byte 0 of DMAC we need to bypass the not-yet-latched
    -- dmacReg on the `start` cycle.  Express the bypass by
    -- pre-extracting byte 0 from BOTH sources and muxing the
    -- byte (not the wide MAC), because emitting
    -- `(mux start dmacIn dmacReg)[47:40]` produces iverilog-
    -- unfriendly Verilog (ternary-then-slice without paren).
    let dB0_live := macByte dmacIn 0
    let dB0_reg  := macByte dmacSig 0
    let dB0      := Signal.mux start dB0_live dB0_reg
    let dB1 := macByte dmacSig 1
    let dB2 := macByte dmacSig 2
    let dB3 := macByte dmacSig 3
    let dB4 := macByte dmacSig 4
    let dB5 := macByte dmacSig 5
    let sB0 := macByte smacSig 0
    let sB1 := macByte smacSig 1
    let sB2 := macByte smacSig 2
    let sB3 := macByte smacSig 3
    let sB4 := macByte smacSig 4
    let sB5 := macByte smacSig 5
    let eB0 := etByte_ etSig 0
    let eB1 := etByte_ etSig 1

    -- Header byte by `stSig` (or by `start` for the byte-0
    -- bypass).  Long mux chain; lowers to a clean case at synth.
    let dmacByte :=
      Signal.mux (start &&& isIdle) dB0
        (Signal.mux is1 dB1
          (Signal.mux is2 dB2
            (Signal.mux is3 dB3
              (Signal.mux is4 dB4 dB5))))
    let smacByte :=
      Signal.mux is6 sB0
        (Signal.mux is7 sB1
          (Signal.mux is8 sB2
            (Signal.mux is9 sB3
              (Signal.mux is10 sB4 sB5))))
    let etByte :=
      Signal.mux is12 eB0 eB1

    let hdrByte :=
      Signal.mux inDmac dmacByte
        (Signal.mux inSmac smacByte etByte)
    let outByte :=
      Signal.mux isPayload payloadByte hdrByte

    let outValid := inHdr ||| (isPayload &&& payloadValid)
    let outSop   := start
    let outEop   := isPayload &&& payloadValid &&& payloadLast

    -- Next-state: on start pulse, latch headers and advance to 1.
    -- During header walk (1..13), st += 1.  On stSig = 13 → 15
    -- (payload).  On payload + last → back to idle.
    let stNext :=
      Signal.mux start (Signal.pure 1#5)
        (Signal.mux is13
          (Signal.pure txPayload)
          (Signal.mux isPayload
            (Signal.mux (payloadValid &&& payloadLast)
              (Signal.pure txIdle)
              (Signal.pure txPayload))
            (Signal.mux isIdle
              (Signal.pure txIdle)
              -- Use the binary Applicative form so handleApplicative
              -- catches `BitVec.add` and lowers to `.op .add`.  A
              -- bare `<$>` (unary `Functor.map`) doesn't match
              -- handleApplicative and the elaborator falls back to
              -- treating `Functor.map` as a sub-module call.
              (stSig + (Signal.pure 1#5 : Signal dom (BitVec 5))))))
    st <~ stNext
    dmacReg <~ Signal.mux start dmacIn dmacSig
    smacReg <~ Signal.mux start smacIn smacSig
    etReg   <~ Signal.mux start etIn   etSig

    return ({ txByte  := outByte
            , txValid := outValid
            , txSop   := outSop
            , txEop   := outEop
            } : TxOut dom)

end Sparkle.IP.Net.Ethernet
