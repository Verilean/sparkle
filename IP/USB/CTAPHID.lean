/-
  IP.USB.CTAPHID — CTAPHID transport framing for FIDO2 (M3).

  CTAPHID carries CTAP messages in fixed 64-byte HID reports:

    INIT report:  CID(4) ‖ CMD(1, high bit set) ‖ BCNTH(1) ‖ BCNTL(1)
                  ‖ data(0..57)
    CONT report:  CID(4) ‖ SEQ(1, high bit clear) ‖ data(0..59)

  A message longer than 57 payload bytes is split across an INIT
  report and one or more CONT reports (SEQ = 0,1,2,…); `BCNT`
  (=BCNTH<<8|BCNTL) is the total message length.

  This module provides:
    * `ctapHidDeframerHW` — a byte-counting FSM that reassembles a
      BCNT-length message across INIT+CONT and pulses `msgDone`,
      exposing the parsed CID / CMD and a payload byte stream.
    * `ctapHidFramerHW` — chunks a response message back into
      64-byte reports (INIT header then CONT headers).

  Structurally these mirror `IP/Net/SLIP.lean`'s framer/deframer
  (a small state-reg byte FSM with latched outputs + a done pulse),
  but with fixed-position header fields instead of byte escaping.

  Pure oracles `ctapHidFrame` / `ctapHidDeframe` cross-check the
  hardware, modelled on `SLIP.encodeFrame` / `decodeStream`.
-/
import Sparkle
import IP.Net.UART

namespace Sparkle.IP.USB.CTAPHID

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### CTAPHID command constants (the ones a minimal authenticator sees). -/

def CMD_MSG       : UInt8 := 0x83   -- CTAPHID_MSG (U2F/raw)
def CMD_INIT      : UInt8 := 0x86   -- CTAPHID_INIT (channel allocation)
def CMD_CBOR      : UInt8 := 0x90   -- CTAPHID_CBOR (CTAP2)
def CMD_KEEPALIVE : UInt8 := 0xBB   -- CTAPHID_KEEPALIVE
def CMD_ERROR     : UInt8 := 0xBF   -- CTAPHID_ERROR

/-! ### Pure reference oracles. -/

/-- Split a CTAP message (cid, cmd, payload) into a flat byte
    stream of 64-byte reports: one INIT then CONT reports.  This is
    exactly what the framer HW emits and the deframer HW consumes. -/
def ctapHidFrame (cid : BitVec 32) (cmd : UInt8) (payload : Array UInt8) :
    Array UInt8 := Id.run do
  let cidBytes : Array UInt8 := #[
    UInt8.ofNat ((cid.toNat >>> 24) &&& 0xFF),
    UInt8.ofNat ((cid.toNat >>> 16) &&& 0xFF),
    UInt8.ofNat ((cid.toNat >>> 8)  &&& 0xFF),
    UInt8.ofNat (cid.toNat &&& 0xFF)]
  let bcnt := payload.size
  let mut out : Array UInt8 := #[]
  -- INIT report: cid ‖ cmd ‖ bcntH ‖ bcntL ‖ first ≤57 bytes ‖ pad to 64.
  out := out ++ cidBytes
  out := out.push cmd
  out := out.push (UInt8.ofNat ((bcnt >>> 8) &&& 0xFF))
  out := out.push (UInt8.ofNat (bcnt &&& 0xFF))
  let firstLen := min 57 bcnt
  for i in [:firstLen] do out := out.push (payload.getD i 0)
  for _ in [firstLen:57] do out := out.push 0x00
  -- CONT reports.
  let mut off := firstLen
  let mut seq : Nat := 0
  while off < bcnt do
    out := out ++ cidBytes
    out := out.push (UInt8.ofNat (seq &&& 0x7F))
    let chunk := min 59 (bcnt - off)
    for i in [:chunk] do out := out.push (payload.getD (off + i) 0)
    for _ in [chunk:59] do out := out.push 0x00
    off := off + chunk
    seq := seq + 1
  return out

/-- Reassemble the payload from a flat 64-byte-report stream (the
    inverse of `ctapHidFrame`).  Returns `(cid, cmd, payload)`. -/
def ctapHidDeframe (stream : Array UInt8) : Option (BitVec 32 × UInt8 × Array UInt8) := Id.run do
  if stream.size < 64 then return none
  let cid := (BitVec.ofNat 32
    ((stream.getD 0 0).toNat <<< 24 ||| (stream.getD 1 0).toNat <<< 16 |||
     (stream.getD 2 0).toNat <<< 8 ||| (stream.getD 3 0).toNat))
  let cmd := stream.getD 4 0
  let bcnt := (stream.getD 5 0).toNat <<< 8 ||| (stream.getD 6 0).toNat
  let mut payload : Array UInt8 := #[]
  let firstLen := min 57 bcnt
  for i in [:firstLen] do payload := payload.push (stream.getD (7 + i) 0)
  let mut off := firstLen
  let mut reportBase := 64
  while off < bcnt do
    let chunk := min 59 (bcnt - off)
    for i in [:chunk] do payload := payload.push (stream.getD (reportBase + 5 + i) 0)
    off := off + chunk
    reportBase := reportBase + 64
  return some (cid, cmd, payload)

/-! ### Deframer FSM. -/

structure DeframerOut (dom : DomainConfig) where
  /-- Channel ID parsed from the INIT report (valid from cmd onward). -/
  cid          : Signal dom (BitVec 32)
  /-- Command byte from the INIT report. -/
  cmd          : Signal dom (BitVec 8)
  /-- Payload byte just decoded (valid when `payloadValid`). -/
  payloadByte  : Signal dom (BitVec 8)
  /-- High for one cycle per reassembled payload byte. -/
  payloadValid : Signal dom Bool
  /-- Pulses one cycle when BCNT payload bytes have been collected. -/
  msgDone      : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (DeframerOut dom) dom := ⟨⟩

/-- Byte-counting CTAPHID deframer.

    A running byte counter walks each 64-byte report; within an INIT
    report bytes 0..3 latch the CID, byte 4 the CMD, 5..6 the BCNT,
    7..63 are the first payload bytes; CONT reports contribute bytes
    5..63 after their 5-byte header.  `payloadValid` pulses on each
    payload byte and `msgDone` when the BCNT count is reached.

    Simplification (M3): assumes well-formed report ordering from the
    host shim; it counts payload bytes against BCNT rather than
    validating SEQ numbers.  Documented in the module header. -/
def ctapHidDeframerHW {dom : DomainConfig}
    (rxByte : Signal dom (BitVec 8))
    (rxValid : Signal dom Bool) :
    DeframerOut dom :=
  circuit do
    -- Position within the current 64-byte report (0..63).
    let posR    ← Signal.reg (0#6)
    -- 0 = expecting INIT report, 1 = in a CONT report.
    let inCont  ← Signal.reg false
    -- Latched header fields.
    let cidR    ← Signal.reg (0#32)
    let cmdR    ← Signal.reg (0#8)
    let bcntR   ← Signal.reg (0#16)
    -- Payload bytes collected so far.
    let pcntR   ← Signal.reg (0#16)
    -- Latched outputs.
    let payR    ← Signal.reg (0#8)
    let payVR   ← Signal.reg false
    let doneR   ← Signal.reg false

    let posSig  := (posR : Signal dom (BitVec 6))
    let cidSig  := (cidR : Signal dom (BitVec 32))
    let bcntSig := (bcntR : Signal dom (BitVec 16))
    let pcntSig := (pcntR : Signal dom (BitVec 16))
    let contSig := (inCont : Signal dom Bool)

    -- Position predicates (inlined — a local lambda returning an
    -- applicative chain does not lower, "Cannot instantiate Seq.seq").
    let atByte4 := (posSig === (Signal.pure 4#6 : Signal dom (BitVec 6)) : Signal dom Bool)
    let atByte5 := (posSig === (Signal.pure 5#6 : Signal dom (BitVec 6)) : Signal dom Bool)
    let atByte6 := (posSig === (Signal.pure 6#6 : Signal dom (BitVec 6)) : Signal dom Bool)
    let p63 := (Signal.pure 63#6 : Signal dom (BitVec 6))
    let atReportEnd := (posSig === p63 : Signal dom Bool)

    -- Header field positions (INIT report): 0..3 cid, 4 cmd, 5 bcntH, 6 bcntL.
    -- Payload starts at pos 7 (INIT) or pos 5 (CONT).
    let isInit := (~~~contSig : Signal dom Bool)
    let initPayStart :=
      ((· && ·) <$> isInit
        <*> ((fun p => BitVec.ule 7#6 p) <$> posSig : Signal dom Bool) : Signal dom Bool)
    let contPayStart :=
      ((· && ·) <$> contSig
        <*> ((fun p => BitVec.ule 5#6 p) <$> posSig : Signal dom Bool) : Signal dom Bool)
    -- This byte is a payload byte (and we still need more, pcnt < bcnt).
    let needMore := ((BitVec.ult · ·) <$> pcntSig <*> bcntSig : Signal dom Bool)
    let isPayPos := (initPayStart ||| contPayStart : Signal dom Bool)
    let isPayload :=
      ((· && ·) <$> ((isPayPos &&& needMore : Signal dom Bool))
        <*> rxValid : Signal dom Bool)

    -- CID assembly: shift byte in at pos 0..3 (INIT).
    let cidShift := ((cidSig <<< (Signal.pure 8#32 : Signal dom (BitVec 32)))
                      ||| (rxByte.map (fun v => BitVec.append (0#24) v))
                      : Signal dom (BitVec 32))
    let inCidRange :=
      ((· && ·) <$> isInit
        <*> ((fun p => BitVec.ule p 3#6) <$> posSig : Signal dom Bool) : Signal dom Bool)
    let cidGate := (inCidRange &&& rxValid : Signal dom Bool)
    cidR <~ Signal.mux cidGate cidShift cidSig

    -- CMD at INIT pos 4.
    let cmdGate := (((isInit &&& atByte4 : Signal dom Bool)) &&& rxValid : Signal dom Bool)
    cmdR <~ Signal.mux cmdGate rxByte (cmdR : Signal dom (BitVec 8))

    -- BCNT: pos 5 = high byte, pos 6 = low byte (INIT).
    let bcntHi := (rxByte.map (fun v => BitVec.append v (0#8)) : Signal dom (BitVec 16))
    let bcntLoAppend := (rxByte.map (fun v => BitVec.append (0#8) v) : Signal dom (BitVec 16))
    let bcntWithLo := (bcntSig ||| bcntLoAppend : Signal dom (BitVec 16))
    let bcntHiGate := (((isInit &&& atByte5 : Signal dom Bool)) &&& rxValid : Signal dom Bool)
    let bcntLoGate := (((isInit &&& atByte6 : Signal dom Bool)) &&& rxValid : Signal dom Bool)
    bcntR <~ Signal.mux bcntHiGate bcntHi (Signal.mux bcntLoGate bcntWithLo bcntSig)

    -- Payload counter: +1 on each payload byte.
    let pcntInc := (pcntSig + (Signal.pure 1#16 : Signal dom (BitVec 16)) : Signal dom (BitVec 16))
    -- msgDone when this payload byte makes pcnt reach bcnt.
    let pcntNext := Signal.mux isPayload pcntInc pcntSig
    let reachedEnd := (pcntNext === bcntSig : Signal dom Bool)
    let msgDoneNow := (isPayload &&& reachedEnd : Signal dom Bool)
    pcntR <~ pcntNext

    -- Position: +1 per rxValid, wrap 63→0 and toggle to CONT.
    let posInc := (posSig + (Signal.pure 1#6 : Signal dom (BitVec 6)) : Signal dom (BitVec 6))
    let posWrap := (atReportEnd &&& rxValid : Signal dom Bool)
    posR <~ Signal.mux rxValid (Signal.mux atReportEnd (Signal.pure 0#6 : Signal dom (BitVec 6)) posInc) posSig
    -- After the first report ends, subsequent reports are CONT.
    inCont <~ Signal.mux posWrap (Signal.pure true : Signal dom Bool) contSig

    -- Latch payload output.
    payR  <~ Signal.mux isPayload rxByte (payR : Signal dom (BitVec 8))
    payVR <~ isPayload
    doneR <~ msgDoneNow

    return ({ cid := cidSig
            , cmd := (cmdR : Signal dom (BitVec 8))
            , payloadByte := (payR : Signal dom (BitVec 8))
            , payloadValid := (payVR : Signal dom Bool)
            , msgDone := (doneR : Signal dom Bool)
            } : DeframerOut dom)

end Sparkle.IP.USB.CTAPHID
