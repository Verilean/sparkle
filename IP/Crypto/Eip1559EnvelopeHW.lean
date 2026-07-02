/-
  IP.Crypto.Eip1559EnvelopeHW — byte-serial EIP-1559 typed-
  transaction envelope header emitter (Signal DSL).

  An EIP-1559 broadcast envelope is

      0x02 ‖ rlp([ chainId, nonce, maxPriorityFee, maxFee, gas,
                   to, value, data, accessList,
                   yParity, r, s ])

  (see `IP.Crypto.Eip1559Tx.encodeSigned`: `#[0x02] ++ encode
  (.list body)`).  The *hardware-specific* piece a wallet writer
  can't avoid is: (1) the leading `0x02` TransactionType
  discriminator, and (2) the RLP list-length prefix header for
  the encoded body.  The body item bytes themselves are streamed
  by the caller after this header (a plain 8-bit pass, no state) —
  exactly the split `IP.Crypto.RLPHW` already established for the
  bare RLP header.

  This module wraps `RLPHW.rlpHeaderHW` (in list mode) and
  prepends the `0x02` type byte, so its output is the complete
  envelope *header* stream

      0x02, <rlp list header bytes…>

  followed by the caller's payload.

  Interface:
    inputs  start (Bool pulse), bodyLen (BitVec 11) — the length
            in bytes of the RLP-encoded body (the payload the
            caller will stream after the header).
    outputs headerByte (BitVec 8), headerValid (Bool),
            done (Bool pulse when the last header byte is emitted).

  Timing (start at cycle 0):
    cycle 0        — emit 0x02 (valid=1); latch bodyLen; kick the
                     inner RLP header emitter (started at cycle 1).
    cycle 1..K     — emit the K RLP list-header bytes (valid=1).
    cycle K+1      — done pulse, back to idle.
-/
import Sparkle
import IP.Crypto.RLPHW

namespace Sparkle.IP.Crypto.Eip1559EnvelopeHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.RLPHW (HeaderOut rlpHeaderHW)

/-- Output record for the envelope-header emitter. -/
structure EnvOut (dom : DomainConfig) where
  /-- Current header byte on this cycle (valid when `headerValid`). -/
  headerByte  : Signal dom (BitVec 8)
  /-- High while an envelope-header byte is being emitted. -/
  headerValid : Signal dom Bool
  /-- Pulses one cycle after the last header byte. -/
  done        : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (EnvOut dom) dom := ⟨⟩

/-- EIP-1559 envelope-header emitter: `0x02` then the RLP list
    header for `bodyLen` bytes.

    The `0x02` byte is emitted on the start cycle; the inner
    `rlpHeaderHW` is started one cycle later (via a registered
    delayed-start pulse) so its byte stream follows the type byte
    back-to-back.  The inner emitter runs in list mode
    (`isList = true`), matching `encode (.list body)`. -/
def eip1559EnvelopeHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (bodyLen : Signal dom (BitVec 11)) :
    EnvOut dom :=
  circuit do
    -- Delayed start for the inner RLP header emitter: high the
    -- cycle after our own `start`.
    let innerStartR ← Signal.reg false
    -- Latched body length, forwarded to the inner emitter.
    let lenR ← Signal.reg (0#11)

    let lenSig := (lenR : Signal dom (BitVec 11))
    lenR <~ Signal.mux start bodyLen lenSig
    innerStartR <~ start

    let innerStart := (innerStartR : Signal dom Bool)

    -- Inner RLP list-header emitter, kicked one cycle after start.
    let hdr :=
      (rlpHeaderHW innerStart lenSig (Signal.pure true : Signal dom Bool) : HeaderOut dom)

    -- Type byte 0x02 on the start cycle.
    let p0x02 := (Signal.pure 0x02#8 : Signal dom (BitVec 8))

    -- Output byte: on our start cycle emit 0x02; otherwise pass the
    -- inner emitter's byte through.
    let curByte :=
      (Signal.mux start p0x02 hdr.headerByte : Signal dom (BitVec 8))
    -- Valid whenever we emit the type byte or the inner emitter is
    -- emitting a header byte.
    let valid :=
      ((· || ·) <$> start <*> hdr.headerValid : Signal dom Bool)
    -- The whole envelope header is done when the inner RLP header
    -- finishes.
    let doneOut := hdr.done

    return ({ headerByte  := curByte
            , headerValid := valid
            , done        := doneOut
            } : EnvOut dom)

end Sparkle.IP.Crypto.Eip1559EnvelopeHW
