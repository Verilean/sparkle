/-
  IP.Bus.DroneCANHW — DroneCAN HW building blocks.

  Implements the CRC-16-CCITT-FALSE LFSR (polynomial 0x1021,
  initial value 0xFFFF) that DroneCAN uses on the first two
  bytes of a multi-frame transfer.  Byte-serial: consumes one
  input byte per cycle (with `valid` high) and updates the
  16-bit CRC register through 8 combinationally-unrolled
  shift steps.

  Also provides a small "node-ID filter" combinational module
  — the frame is accepted iff the source node ID field on the
  wire matches the configured node ID.  This is the piece a
  real DroneCAN transceiver uses to skip messages destined
  for other nodes on the bus.

  Validation: cycle-by-cycle equivalence to
  `IP.Bus.DroneCAN.crc16Ccitt`.
-/
import Sparkle

namespace Sparkle.IP.Bus.DroneCANHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-- Output of the CRC-16-CCITT-FALSE HW unit. -/
structure CRC16Out (dom : DomainConfig) where
  crc : Signal dom (BitVec 16)

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (CRC16Out dom) dom := ⟨⟩

/-- One bit-serial step of the CRC-16-CCITT-FALSE unroll.
    Given current CRC candidate `c` (16 bits), produces the
    next:
      if (c & 0x8000) ≠ 0 then (c << 1) XOR 0x1021
      else                    (c << 1)
    (mask to 16 bits is implicit in BitVec 16 arithmetic). -/
def crc16Step {dom : DomainConfig} (c : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let p0    := (Signal.pure 0#16     : Signal dom (BitVec 16))
  let pPoly := (Signal.pure 0x1021#16 : Signal dom (BitVec 16))
  let p1    := (Signal.pure 1#16     : Signal dom (BitVec 16))
  let pMSB  := (Signal.pure 0x8000#16 : Signal dom (BitVec 16))
  let msbAnd := (c &&& pMSB : Signal dom (BitVec 16))
  let msbNZ := (~~~(msbAnd === p0 : Signal dom Bool)
                : Signal dom Bool)
  let shifted := (c <<< p1 : Signal dom (BitVec 16))
  let shiftedXor := (shifted ^^^ pPoly : Signal dom (BitVec 16))
  Signal.mux msbNZ shiftedXor shifted

/-- Byte-serial CRC-16-CCITT-FALSE (poly 0x1021, init 0xFFFF).

    Wiring:
      start : Bool — pulse resets crcR to 0xFFFF next cycle
      byteIn : BitVec 8 — one input byte per cycle
      valid : Bool — 1 when byteIn should be consumed
      crc  : BitVec 16 — running CRC register
-/
def crc16CcittHW {dom : DomainConfig}
    (start : Signal dom Bool)
    (byteIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool) :
    CRC16Out dom :=
  circuit do
    let crcR ← Signal.reg (0xFFFF#16)
    let crcSig := (crcR : Signal dom (BitVec 16))

    let pInit := (Signal.pure 0xFFFF#16 : Signal dom (BitVec 16))
    let p8    := (Signal.pure 8#16     : Signal dom (BitVec 16))

    -- Widen `byteIn` (BitVec 8) to BitVec 16 by concat with a
    -- top zero byte: (0#8 ++ byteIn) : BitVec 16 has byteIn in
    -- the LOW 8 bits and 0 in the HIGH 8 bits.
    let pZeroByte := (Signal.pure 0#8 : Signal dom (BitVec 8))
    let widened := (pZeroByte ++ byteIn : Signal dom (BitVec 16))

    -- Shift byte into upper octet: (byte << 8)
    let shBy8 := (widened <<< p8 : Signal dom (BitVec 16))

    let c0 := (crcSig ^^^ shBy8 : Signal dom (BitVec 16))
    let c1 := crc16Step c0
    let c2 := crc16Step c1
    let c3 := crc16Step c2
    let c4 := crc16Step c3
    let c5 := crc16Step c4
    let c6 := crc16Step c5
    let c7 := crc16Step c6
    let c8 := crc16Step c7

    crcR <~ Signal.mux start pInit (Signal.mux valid c8 crcSig)

    return ({ crc := crcSig } : CRC16Out dom)

/-! ### Node-ID filter.

    DroneCAN uses the low 7 bits of the 29-bit CAN ID as the
    source node ID.  A transceiver typically wants to reject
    frames it originated (src == self) or (for services)
    frames not directed at itself.  This tiny combinational
    module compares the incoming src-node-id field against the
    configured self-node-id and asserts `accept` iff it
    differs (broadcast reception, source-filtered). -/

structure NodeFilterOut (dom : DomainConfig) where
  accept : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (NodeFilterOut dom) dom := ⟨⟩

/-- Accept a frame iff its `srcNode` field differs from the
    configured `selfNode`.  Both are 7-bit values.  Purely
    combinational — no registers. -/
def nodeFilterHW {dom : DomainConfig}
    (srcNode : Signal dom (BitVec 7))
    (selfNode : Signal dom (BitVec 7)) :
    NodeFilterOut dom :=
  let eq := (srcNode === selfNode : Signal dom Bool)
  let notEq := (~~~eq : Signal dom Bool)
  { accept := notEq }

/-! ### Transfer-ID + toggle-bit tracker.

    DroneCAN transports payloads that span more than one CAN
    frame using a 5-bit transfer ID (constant across all
    frames of a transfer) plus a 1-bit toggle that alternates
    on every frame after the first.  A receiver tracks the
    (transfer-id, toggle) pair to detect frame loss.

    This module accepts a per-frame stimulus (`tid`, `tog`,
    `sot`, `eot`, `valid`) and outputs:
      * `expectedTog` — the toggle we expect on the next frame
      * `expectedTid` — the transfer ID we expect (locked from SOT)
      * `error`      — asserted when a mid-transfer frame's
                        toggle or transfer-ID doesn't match
                        the tracked expectation.  Cleared on
                        the next SOT.
-/

structure TidOut (dom : DomainConfig) where
  expectedTid : Signal dom (BitVec 5)
  expectedTog : Signal dom Bool
  error       : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TidOut dom) dom := ⟨⟩

def transferIdTrackerHW {dom : DomainConfig}
    (tid    : Signal dom (BitVec 5))
    (tog    : Signal dom Bool)
    (sot    : Signal dom Bool)
    (eot    : Signal dom Bool)
    (valid  : Signal dom Bool) :
    TidOut dom :=
  circuit do
    -- expected transfer ID (locked on SOT)
    let tidReg ← Signal.reg (0#5)
    -- expected toggle (starts at false on SOT, then alternates)
    let togReg ← Signal.reg false
    -- error latch (sticky within a transfer, cleared on SOT)
    let errReg ← Signal.reg false

    let tidSig := (tidReg : Signal dom (BitVec 5))
    let togSig := (togReg : Signal dom Bool)
    let errSig := (errReg : Signal dom Bool)

    let togEq := (tog === togSig : Signal dom Bool)
    let togMismatch := (~~~togEq : Signal dom Bool)
    let tidEq := (tid === tidSig : Signal dom Bool)
    let tidMismatch := (~~~tidEq : Signal dom Bool)
    let midMismatch := (togMismatch ||| tidMismatch : Signal dom Bool)

    -- validFrame = valid && !sot   (mid-transfer frame)
    let notSot := (~~~sot : Signal dom Bool)
    let midValid := (valid &&& notSot : Signal dom Bool)
    let midErr := (midValid &&& midMismatch : Signal dom Bool)

    -- validSot = valid && sot
    let sotValid := (valid &&& sot : Signal dom Bool)

    -- next expected toggle: after SOT it becomes true;
    --   after any mid-transfer valid frame it flips;
    --   after EOT (last valid frame) it doesn't matter but hold.
    let togFlipped := (~~~togSig : Signal dom Bool)
    let togNextMid := Signal.mux midValid togFlipped togSig
    let togNext := Signal.mux sotValid (Signal.pure true) togNextMid

    -- next expected TID: latch on SOT, hold otherwise.
    let tidNext := Signal.mux sotValid tid tidSig

    -- error latch: clear on SOT, set on midErr, else hold.
    let errClear := sotValid
    let errAfterClear := Signal.mux errClear (Signal.pure false) errSig
    let errNext := Signal.mux midErr (Signal.pure true) errAfterClear

    -- `eot` reserved for future extension (transfer boundary
    -- notification); prevent "unused" warning by folding it
    -- through error preservation (identity — mux by 0).
    let _eotHold := (eot &&& false : Signal dom Bool)
    let errNext2 := (errNext ||| _eotHold : Signal dom Bool)

    tidReg <~ tidNext
    togReg <~ togNext
    errReg <~ errNext2

    return ({ expectedTid := tidSig, expectedTog := togSig, error := errSig } : TidOut dom)

end Sparkle.IP.Bus.DroneCANHW
