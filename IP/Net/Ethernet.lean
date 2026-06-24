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

end Sparkle.IP.Net.Ethernet
