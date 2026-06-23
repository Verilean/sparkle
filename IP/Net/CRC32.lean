/-
  IP.Net.CRC32 — Ethernet FCS (CRC-32/IEEE-802.3) — Signal DSL

  Used by every layer of the HFT TCP/IP stack:
    * Ethernet frame check sequence (transmit + verify)
    * IPv4 / TCP / UDP one's-complement checksum reuses the same
      byte-feed shift-register idiom (separate module — this one
      is the polynomial-based CRC).

  Parameters (per IEEE 802.3):
    polynomial = 0x04C11DB7   (reflected: 0xEDB88320)
    init       = 0xFFFFFFFF
    refin      = true         (LSB-first byte ingress)
    refout     = true
    xorout     = 0xFFFFFFFF

  We implement the *reflected* variant directly so the byte input
  doesn't need an LSB↔MSB swap on every cycle.

  MVP: one byte per cycle.  Wide (32/64-bit/cycle) variants live in
  a follow-up module once the byte-feed reference + iverilog round-
  trip pin the golden vectors down.
-/

import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.CRC32

/-- Reflected Ethernet polynomial.  Constant; not a register. -/
private abbrev poly : BitVec 32 := 0xEDB88320#32

/--
  One reflected shift-register iteration, Signal-level.

  Implemented as a bitmask synth-friendly:
    mask = 0 - (crc & 1)   -- all-1s if LSB set, all-0s otherwise
    crc' = (crc >>> 1) ^ (poly & mask)

  Written at the Signal layer (every operator is the
  `Signal (BitVec 32)` overload registered in `Sparkle/Core/Signal.lean`)
  so the IR elaborator can inline it through `circuit do`.  The
  pure-`BitVec` formulation forces a `<$>/<*>` lift that the
  elaborator's `unfoldDefinition?` path can't peel.
-/
@[inline] private def crc32BitSig {dom : DomainConfig}
    (crc : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let mask := (0#32 : BitVec 32) - (crc &&& (1#32 : BitVec 32))
  (crc >>> (1#32 : BitVec 32)) ^^^ ((poly : BitVec 32) &&& mask)

/--
  One CRC-32 byte step at the Signal layer:
  XOR in the byte (zero-extended via `0#24 ++ byte`) then run 8
  bit iterations.  Every operator is Signal-native (`++`, `^^^`,
  `&&&`, `>>>`); no Applicative lift required.
-/
@[inline] private def crc32StepSig {dom : DomainConfig}
    (crc : Signal dom (BitVec 32))
    (byte : Signal dom (BitVec 8)) : Signal dom (BitVec 32) :=
  -- 0#24 ++ byte : Signal dom (BitVec 32) via the HAppend instance.
  let byteZX : Signal dom (BitVec 32) := (0#24 : BitVec 24) ++ byte
  let c0 := crc ^^^ byteZX
  crc32BitSig (crc32BitSig (crc32BitSig (crc32BitSig
    (crc32BitSig (crc32BitSig (crc32BitSig (crc32BitSig c0)))))))

/-- Pure-BitVec one-bit step, used by the reference oracle. -/
@[inline] private def crc32Bit (crc : BitVec 32) : BitVec 32 :=
  let mask := 0#32 - (crc &&& 1#32)
  (crc >>> 1) ^^^ (poly &&& mask)

/-- Pure-BitVec one-byte step, used by the reference oracle. -/
@[inline] private def crc32Step (crc : BitVec 32) (b : BitVec 8) : BitVec 32 :=
  let crc := crc ^^^ (BitVec.zeroExtend 32 b)
  crc32Bit (crc32Bit (crc32Bit (crc32Bit
    (crc32Bit (crc32Bit (crc32Bit (crc32Bit crc)))))))

/--
  Byte-feed CRC-32 engine.

  Inputs (per cycle):
    `byte`     — the next message byte
    `feed`     — assert to accept the byte and update the register
    `reset`    — assert to load `init` = 0xFFFFFFFF (start of frame)

  Output:
    the current CRC register state.  The transmit side reads the
    register after the last byte has been fed in and XORs with
    `xorout` to produce the FCS to append (this is done outside
    the engine so the register state stays semantically equal to
    the standard textbook definition).

  The register starts at 0 after async-reset; bring `reset` high
  on the first cycle of a frame to load `init` before feeding
  bytes.
-/
def crc32Engine {dom : DomainConfig}
    (byte : Signal dom (BitVec 8))
    (feed reset : Signal dom Bool) :
    Signal dom (BitVec 32) :=
  circuit do
    let crc ← Signal.reg 0#32
    -- Three cases:
    --   reset → load 0xFFFFFFFF (frame start)
    --   feed  → advance one byte
    --   else  → hold (no <~ → register keeps its value)
    if reset then
      crc <~ 0xFFFFFFFF#32
    else
      if feed then
        crc <~ crc32StepSig crc byte
      else
        crc <~ crc          -- explicit hold; else branch must assign
    return crc

/--
  Convenience: full CRC over a finite list of bytes computed
  combinationally.  Used by the Lean-side reference oracle in the
  sim test — NOT a circuit definition.  Mirrors the engine's
  per-step transition so the simulator can produce golden vectors
  without spinning up a `Signal.loop`.

  Returns the FCS already XOR'd with 0xFFFFFFFF.
-/
def crc32Ref (bytes : List (BitVec 8)) : BitVec 32 :=
  let final := bytes.foldl crc32Step 0xFFFFFFFF#32
  final ^^^ 0xFFFFFFFF#32

end Sparkle.IP.Net.CRC32
