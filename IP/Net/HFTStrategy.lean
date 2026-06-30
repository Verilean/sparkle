/-
  IP.Net.HFTStrategy — minimal NIC-side strategy demo.

  Wires the HTTP request parser into the HTTP request
  emitter through a tiny "strategy core": when the parser
  detects an inbound `GET ` (= "market data event"), the
  emitter fires its 18-byte outbound GET (= "place order")
  one cycle later.

  This is the bare minimum to demonstrate the **HFT
  NIC-side strategy** value proposition: market data
  arrives over the wire, a hardware-side strategy block
  reacts and emits an outbound packet without ever
  involving the host CPU.

  Latency profile (cycle-accurate, see HFTStrategyTest):
    cycle 0 : inbound byte 0 'G' arrives at the parser
    cycle 1 : byte 1 'E'
    cycle 2 : byte 2 'T'
    cycle 3 : byte 3 ' '  → match complete; parser's
              gotRequest register latches to true on the
              NEXT cycle
    cycle 4 : gotRequest = 1; strategy fires its trigger
              into the emitter (also registered)
    cycle 5 : emitter starts emitting; first outbound byte
              'G' appears on the wire (txValid pulses high)
    cycle 22: last outbound byte (cycle 5 + 18 - 1 = 22)

  Total inbound-first-byte → outbound-first-byte: 5 cycles.
  At 10 GbE / 64-bit wire (156 MHz), that's ~32 ns — order
  of magnitude faster than any CPU-mediated path.

  The "strategy" is intentionally trivial (always-fire on
  parser match) so the demo focuses on the wire-level
  latency budget; a real HFT block would inspect the
  payload, do book lookups, etc., between parser and
  emitter.
-/

import Sparkle
import IP.Net.HTTP

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.HFTStrategy

/-! ### Output record. -/
structure HFTOut (dom : DomainConfig) where
  /-- Inbound side: pulsed when the parser saw `GET `. -/
  triggerSeen : Signal dom Bool
  /-- Outbound side: byte / valid / last for the emitter. -/
  outByte  : Signal dom (BitVec 8)
  outValid : Signal dom Bool
  outLast  : Signal dom Bool
  /-- Hard-counter of how many outbound segments have been
      fired since reset.  Useful for the "have we reacted?"
      assertion in tests. -/
  emitCount : Signal dom (BitVec 8)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HFTOut dom) dom := ⟨⟩

/-- The NIC-side strategy block.

    Takes the inbound byte stream + valid; produces the
    outbound byte stream + a "we fired" counter. -/
def hftStrategy {dom : DomainConfig}
    (inByte : Signal dom (BitVec 8))
    (inValid : Signal dom Bool) :
    HFTOut dom :=
  let parsed := HTTP.httpRequestParser inByte inValid
  let emitted := HTTP.httpGetEmitter parsed.gotRequest
  circuit do
    -- Cumulative count of how many requests we've fired.
    let cntR ← Signal.reg (0#8)
    let cntSig := (cntR : Signal dom (BitVec 8))
    let cntInc :=
      (· + ·) <$> cntSig <*> (Signal.pure 1#8 : Signal dom (BitVec 8))
    cntR <~ Signal.mux parsed.gotRequest cntInc cntSig
    return ({ triggerSeen := parsed.gotRequest
            , outByte    := emitted.byte
            , outValid   := emitted.valid
            , outLast    := emitted.last
            , emitCount  := cntSig
            } : HFTOut dom)

end Sparkle.IP.Net.HFTStrategy
