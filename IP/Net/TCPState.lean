/-
  IP.Net.TCPState — TCP state machine (RFC 793 §3.2).

  Supports the full 11-state finite state machine but the
  per-state transition logic in this file is split into two
  drivers:

    * `tcpServerFSM` (this file) handles the passive-open
      path: CLOSED → LISTEN → SYN_RCVD → ESTABLISHED →
      CLOSE_WAIT → LAST_ACK → CLOSED.

    * `tcpClientFSM` (Phase B.3) will handle the active-open
      path: CLOSED → SYN_SENT → ESTABLISHED → FIN_WAIT_1 →
      FIN_WAIT_2 → TIME_WAIT → CLOSED.

  State encoding is shared so the two FSMs can read each
  other's outputs uniformly in the loopback test.

  Inputs (per cycle):
    * `parserDone`   : the upstream TCP parser pulses this
                       high for one cycle once a full 20-byte
                       header has been latched.
    * `parsedFlags`  : the 16-bit (DataOff|Rsvd|Flags) field
                       extracted by the parser.
    * `parsedSeq`    : remote SEQ
    * `parsedAck`    : remote ACK
    * `listenStart`  : user-driven pulse: "start passively
                       listening on our port".

  Outputs (per cycle):
    * `state`        : current FSM state (4-bit)
    * `txReq`        : 1 = "emit a TCP segment this cycle"
                       (the demo pairs this with the byte
                       emitter — txStart pulses for one cycle
                       when txReq goes from 0→1 inside the
                       FSM).
    * `txFlags`      : flags to set in the outbound segment
                       (SYN+ACK, ACK, FIN+ACK, etc.)
    * `txSeq`/`txAck`: SEQ / ACK to put on the outbound
                       segment.
-/

import Sparkle
import IP.Net.TCP

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Net.TCPState

/-! ### State encoding (4-bit). -/
abbrev sClosed     : BitVec 4 := 0#4
abbrev sListen     : BitVec 4 := 1#4
abbrev sSynRcvd    : BitVec 4 := 2#4
abbrev sEstab      : BitVec 4 := 3#4
abbrev sCloseWait  : BitVec 4 := 4#4
abbrev sLastAck    : BitVec 4 := 5#4
abbrev sSynSent    : BitVec 4 := 6#4
abbrev sFinWait1   : BitVec 4 := 7#4
abbrev sFinWait2   : BitVec 4 := 8#4
abbrev sTimeWait   : BitVec 4 := 9#4

/-! ### Output record. -/
structure TcpFsmOut (dom : DomainConfig) where
  state    : Signal dom (BitVec 4)
  txReq    : Signal dom Bool
  /-- The 16-bit (DataOffset+Reserved+Flags) field for the
      outbound segment.  DataOffset=5, Reserved=0, NS=0;
      flag bits as needed. -/
  txDataOffFlags : Signal dom (BitVec 16)
  /-- Our outbound sequence number for the segment we're
      asking to emit. -/
  txSeq    : Signal dom (BitVec 32)
  /-- Our outbound ACK number (peer's next expected seq). -/
  txAck    : Signal dom (BitVec 32)
  /-- "Connection established" status — exposed for any
      payload-side logic. -/
  established : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (TcpFsmOut dom) dom := ⟨⟩

/-! ### Helpers. -/

/-- Pack data-offset / reserved / flag bits into a 16-bit
    `dataOffFlags` field for the TCP header.  DataOffset is
    always 5 (no options); flag bits are passed in as
    individual Bools. -/
@[inline] def packDataOffFlags
    (synF ackF finF rstF pshF : Bool) : BitVec 16 :=
  -- bit layout (MSB-first): DataOff(4) | Reserved(3) | NS(1) | CWR(1) | ECE(1) | URG(1) | ACK(1) | PSH(1) | RST(1) | SYN(1) | FIN(1)
  let dataOff : BitVec 16 := 0x5000#16   -- DataOff=5
  let synBit  : BitVec 16 := if synF then 0x0002#16 else 0
  let ackBit  : BitVec 16 := if ackF then 0x0010#16 else 0
  let finBit  : BitVec 16 := if finF then 0x0001#16 else 0
  let rstBit  : BitVec 16 := if rstF then 0x0004#16 else 0
  let pshBit  : BitVec 16 := if pshF then 0x0008#16 else 0
  dataOff ||| synBit ||| ackBit ||| finBit ||| rstBit ||| pshBit

/-- Initial server SEQ — for the demo just a fixed value.
    In a real implementation, this would be a per-connection
    PRNG-derived ISN. -/
abbrev serverIsn : BitVec 32 := 0x10000000#32

/-! ### Server-side passive-open FSM. -/

def tcpServerFSM {dom : DomainConfig}
    (listenStart : Signal dom Bool)
    (parserDone  : Signal dom Bool)
    (parsedFlags : Signal dom (BitVec 16))
    (parsedSeq   : Signal dom (BitVec 32))
    (parsedAck   : Signal dom (BitVec 32)) :
    TcpFsmOut dom :=
  circuit do
    let st     ← Signal.reg sClosed
    -- Remote SEQ + 1 = our outbound ACK after SYN; we latch
    -- the peer's seq on the SYN cycle and add 1 to form the
    -- ACK for our SYN+ACK.
    let peerSeqR ← Signal.reg (0#32)
    -- Our SEQ (constant for the demo); peer ACK that came back.
    let ourSeqR  ← Signal.reg (0#32)
    let txReqR   ← Signal.reg false

    let stSig := (st : Signal dom (BitVec 4))
    let peerSeqSig := (peerSeqR : Signal dom (BitVec 32))
    let ourSeqSig  := (ourSeqR  : Signal dom (BitVec 32))
    let txReqSig   := (txReqR   : Signal dom Bool)

    -- State predicates.
    let pClosed    := (Signal.pure sClosed    : Signal dom (BitVec 4))
    let pListen    := (Signal.pure sListen    : Signal dom (BitVec 4))
    let pSynRcvd   := (Signal.pure sSynRcvd   : Signal dom (BitVec 4))
    let pEstab     := (Signal.pure sEstab     : Signal dom (BitVec 4))
    let pCloseWait := (Signal.pure sCloseWait : Signal dom (BitVec 4))
    let pLastAck   := (Signal.pure sLastAck   : Signal dom (BitVec 4))
    let isClosed    := (· == ·) <$> stSig <*> pClosed
    let isListen    := (· == ·) <$> stSig <*> pListen
    let isSynRcvd   := (· == ·) <$> stSig <*> pSynRcvd
    let isEstab     := (· == ·) <$> stSig <*> pEstab
    let isCloseWait := (· == ·) <$> stSig <*> pCloseWait
    let isLastAck   := (· == ·) <$> stSig <*> pLastAck

    -- Flag bit predicates from the inbound segment's flag byte.
    -- parsedFlags layout: [DataOff(4) | Rsvd(3) | NS | CWR | ECE | URG | ACK | PSH | RST | SYN | FIN]
    -- Just extract the low byte and bitwise-AND with mask
    -- constants from IP.Net.TCP.
    let flagLo := parsedFlags.map (BitVec.extractLsb' 0 8 ·)
    let pSyn := (Signal.pure TCP.flagSyn : Signal dom (BitVec 8))
    let pAck := (Signal.pure TCP.flagAck : Signal dom (BitVec 8))
    let pFin := (Signal.pure TCP.flagFin : Signal dom (BitVec 8))
    let pZ8  := (Signal.pure (0#8 : BitVec 8) : Signal dom (BitVec 8))
    let synBit := (· &&& ·) <$> flagLo <*> pSyn
    let ackBit := (· &&& ·) <$> flagLo <*> pAck
    let finBit := (· &&& ·) <$> flagLo <*> pFin
    -- Convert "bit-and-mask is nonzero" → Bool via "not equal
    -- to zero".  Express as `eq` followed by `not` so each
    -- step is a Signal-native primitive the elaborator
    -- recognises.
    let synEqZ := (· == ·) <$> synBit <*> pZ8
    let ackEqZ := (· == ·) <$> ackBit <*> pZ8
    let finEqZ := (· == ·) <$> finBit <*> pZ8
    let synF := (fun b => !b) <$> synEqZ
    let ackF := (fun b => !b) <$> ackEqZ
    let finF := (fun b => !b) <$> finEqZ

    -- Transition decisions.  Each is a one-cycle pulse when
    -- the parser-done arrives in the relevant state with the
    -- right flag bits set.
    let onSyn        := parserDone &&& synF &&& isListen          -- LISTEN + SYN → SYN_RCVD, emit SYN+ACK
    let onAckOfSyn   := parserDone &&& ackF &&& isSynRcvd         -- SYN_RCVD + ACK → ESTABLISHED
    let onFinFromPeer := parserDone &&& finF &&& isEstab          -- ESTAB + FIN → CLOSE_WAIT, emit ACK
    let onAckLastAck := parserDone &&& ackF &&& isLastAck         -- LAST_ACK + ACK → CLOSED
    -- User-side "close connection" signal: auto-close on
    -- peer FIN.  Fires the cycle AFTER we land in CLOSE_WAIT
    -- (when isCloseWait is true) so the LAST_ACK transition
    -- doesn't race with the CLOSE_WAIT entry.
    let userClose    := isCloseWait

    -- Next-state mux.
    let stNext :=
      Signal.mux (isClosed &&& listenStart) (Signal.pure sListen)
        (Signal.mux onSyn (Signal.pure sSynRcvd)
          (Signal.mux onAckOfSyn (Signal.pure sEstab)
            (Signal.mux (onFinFromPeer &&& isEstab) (Signal.pure sCloseWait)
              (Signal.mux (userClose &&& isCloseWait) (Signal.pure sLastAck)
                (Signal.mux onAckLastAck (Signal.pure sClosed)
                  stSig)))))
    st <~ stNext

    -- Latch peer SEQ on SYN; update ourSEQ on each tx event so
    -- the next-out segment carries the right value.
    peerSeqR <~ Signal.mux onSyn parsedSeq peerSeqSig
    -- ourSeqR: for the demo, just constant ISN throughout.
    ourSeqR  <~ Signal.mux (isClosed &&& listenStart) (Signal.pure serverIsn)
                  ourSeqSig

    -- txReq pulses for one cycle on each transition that
    -- generates an outbound segment.
    let needsTx := onSyn ||| (onFinFromPeer &&& isEstab) |||
                   (userClose &&& isCloseWait)
    txReqR <~ needsTx

    -- Outbound flags (DataOff=5 packed in already):
    --   onSyn        → SYN+ACK
    --   onFinFromPeer (ESTAB→CLOSE_WAIT) → ACK (no FIN yet)
    --   userClose (CLOSE_WAIT→LAST_ACK)  → FIN+ACK
    --
    -- We resolve the flag pattern combinationally from the
    -- about-to-take pulse signals.  Default = ACK-only.
    let synAckFlags := (packDataOffFlags true true false false false : BitVec 16)
    let ackFlags    := (packDataOffFlags false true false false false : BitVec 16)
    let finAckFlags := (packDataOffFlags false true true false false : BitVec 16)
    let txFlagsOut :=
      Signal.mux onSyn  (Signal.pure synAckFlags)
        (Signal.mux (userClose &&& isCloseWait) (Signal.pure finAckFlags)
          (Signal.pure ackFlags))

    -- Outbound SEQ = our latched seq.
    -- Outbound ACK = peerSeq + 1 (SYN consumes one slot).
    let p1_32 := (Signal.pure (1#32 : BitVec 32) : Signal dom (BitVec 32))
    let txAckOut := (· + ·) <$> peerSeqSig <*> p1_32

    return ({ state := stSig
            , txReq := txReqSig
            , txDataOffFlags := txFlagsOut
            , txSeq := ourSeqSig
            , txAck := txAckOut
            , established := isEstab
            } : TcpFsmOut dom)

/-! ### Client-side active-open FSM.

    State sequence:
      CLOSED → SYN_SENT → ESTABLISHED → FIN_WAIT_1 →
      FIN_WAIT_2 → TIME_WAIT → CLOSED.

    Inputs:
      * `connectStart` : user-side "open the connection"
                         pulse.  Triggers SYN emit and moves
                         CLOSED → SYN_SENT.
      * `parserDone`   : incoming-segment-finished pulse.
      * `parsedFlags`  : 16-bit dataOff+flags.
      * `parsedSeq`    : remote SEQ (latched on SYN+ACK).
      * `parsedAck`    : remote ACK (currently unused; the
                         demo doesn't validate ACK numbers).
      * `userClose`    : user-side "close the connection"
                         pulse (ESTABLISHED → FIN_WAIT_1).

    Outputs (TcpFsmOut, same shape as server):
      * state         : 4-bit FSM state code.
      * txReq         : "emit a segment this cycle" pulse.
      * txDataOffFlags: SYN / ACK / FIN+ACK by transition.
      * txSeq / txAck : SEQ / ACK numbers.
      * established   : true while in ESTABLISHED.
-/

abbrev clientIsn : BitVec 32 := 0x20000000#32

def tcpClientFSM {dom : DomainConfig}
    (connectStart : Signal dom Bool)
    (userClose    : Signal dom Bool)
    (parserDone   : Signal dom Bool)
    (parsedFlags  : Signal dom (BitVec 16))
    (parsedSeq    : Signal dom (BitVec 32))
    (parsedAck    : Signal dom (BitVec 32)) :
    TcpFsmOut dom :=
  circuit do
    let st       ← Signal.reg sClosed
    let peerSeqR ← Signal.reg (0#32)
    let ourSeqR  ← Signal.reg (0#32)
    let txReqR   ← Signal.reg false
    -- TIME_WAIT linger counter (cheapened — 4 cycles instead
    -- of 2× MSL).  The demo doesn't actually need to linger,
    -- but exercising the counter keeps the FSM honest.
    let twCnt    ← Signal.reg (0#3)

    let stSig := (st : Signal dom (BitVec 4))
    let peerSeqSig := (peerSeqR : Signal dom (BitVec 32))
    let ourSeqSig  := (ourSeqR  : Signal dom (BitVec 32))
    let txReqSig   := (txReqR   : Signal dom Bool)
    let twCntSig   := (twCnt    : Signal dom (BitVec 3))

    let pClosed   := (Signal.pure sClosed   : Signal dom (BitVec 4))
    let pSynSent  := (Signal.pure sSynSent  : Signal dom (BitVec 4))
    let pEstab    := (Signal.pure sEstab    : Signal dom (BitVec 4))
    let pFinWait1 := (Signal.pure sFinWait1 : Signal dom (BitVec 4))
    let pFinWait2 := (Signal.pure sFinWait2 : Signal dom (BitVec 4))
    let pTimeWait := (Signal.pure sTimeWait : Signal dom (BitVec 4))
    let isClosed   := (· == ·) <$> stSig <*> pClosed
    let isSynSent  := (· == ·) <$> stSig <*> pSynSent
    let isEstab    := (· == ·) <$> stSig <*> pEstab
    let isFinWait1 := (· == ·) <$> stSig <*> pFinWait1
    let isFinWait2 := (· == ·) <$> stSig <*> pFinWait2
    let isTimeWait := (· == ·) <$> stSig <*> pTimeWait

    -- Flag extraction (same recipe as server FSM).
    let flagLo := parsedFlags.map (BitVec.extractLsb' 0 8 ·)
    let pSyn := (Signal.pure TCP.flagSyn : Signal dom (BitVec 8))
    let pAck := (Signal.pure TCP.flagAck : Signal dom (BitVec 8))
    let pFin := (Signal.pure TCP.flagFin : Signal dom (BitVec 8))
    let pZ8  := (Signal.pure (0#8 : BitVec 8) : Signal dom (BitVec 8))
    let synBit := (· &&& ·) <$> flagLo <*> pSyn
    let ackBit := (· &&& ·) <$> flagLo <*> pAck
    let finBit := (· &&& ·) <$> flagLo <*> pFin
    let synEqZ := (· == ·) <$> synBit <*> pZ8
    let ackEqZ := (· == ·) <$> ackBit <*> pZ8
    let finEqZ := (· == ·) <$> finBit <*> pZ8
    let synF := (fun b => !b) <$> synEqZ
    let ackF := (fun b => !b) <$> ackEqZ
    let finF := (fun b => !b) <$> finEqZ

    -- Transition triggers.
    let onConnect    := isClosed &&& connectStart                    -- CLOSED → SYN_SENT, emit SYN
    let onSynAck     := parserDone &&& synF &&& ackF &&& isSynSent   -- SYN_SENT + SYN+ACK → ESTABLISHED, emit ACK
    let onUserClose  := isEstab &&& userClose                        -- ESTAB + user close → FIN_WAIT_1, emit FIN+ACK
    let onAckOfFin   := parserDone &&& ackF &&& isFinWait1           -- FIN_WAIT_1 + ACK → FIN_WAIT_2
    let onPeerFin2   := parserDone &&& finF &&& isFinWait2           -- FIN_WAIT_2 + FIN → TIME_WAIT, emit ACK
    -- TIME_WAIT counter expiry: linger 4 cycles then close.
    let pTwMax := (Signal.pure 3#3 : Signal dom (BitVec 3))
    let twExpired := (· == ·) <$> twCntSig <*> pTwMax

    let stNext :=
      Signal.mux onConnect   (Signal.pure sSynSent)
        (Signal.mux onSynAck (Signal.pure sEstab)
          (Signal.mux onUserClose (Signal.pure sFinWait1)
            (Signal.mux onAckOfFin (Signal.pure sFinWait2)
              (Signal.mux onPeerFin2 (Signal.pure sTimeWait)
                (Signal.mux (isTimeWait &&& twExpired) (Signal.pure sClosed)
                  stSig)))))
    st <~ stNext

    -- TIME_WAIT counter: bump while in TIME_WAIT; reset on
    -- leaving / entering.
    let p1_3 := (Signal.pure 1#3 : Signal dom (BitVec 3))
    let pZ3  := (Signal.pure 0#3 : Signal dom (BitVec 3))
    let twInc := (· + ·) <$> twCntSig <*> p1_3
    twCnt <~ Signal.mux onPeerFin2 pZ3
              (Signal.mux isTimeWait twInc pZ3)

    -- Latch peer SEQ on SYN+ACK so our ACK is correct.
    peerSeqR <~ Signal.mux onSynAck parsedSeq peerSeqSig
    ourSeqR  <~ Signal.mux onConnect (Signal.pure clientIsn) ourSeqSig

    -- Outbound segment pulses.
    let needsTx := onConnect ||| onSynAck ||| onUserClose ||| onPeerFin2
    txReqR <~ needsTx

    -- Flag values for each tx event.
    let synFlags    := (packDataOffFlags true false false false false : BitVec 16)
    let ackFlags    := (packDataOffFlags false true false false false : BitVec 16)
    let finAckFlags := (packDataOffFlags false true true false false : BitVec 16)
    let txFlagsOut :=
      Signal.mux onConnect (Signal.pure synFlags)
        (Signal.mux onUserClose (Signal.pure finAckFlags)
          (Signal.pure ackFlags))

    let p1_32 := (Signal.pure (1#32 : BitVec 32) : Signal dom (BitVec 32))
    let txAckOut := (· + ·) <$> peerSeqSig <*> p1_32

    return ({ state := stSig
            , txReq := txReqSig
            , txDataOffFlags := txFlagsOut
            , txSeq := ourSeqSig
            , txAck := txAckOut
            , established := isEstab
            } : TcpFsmOut dom)

end Sparkle.IP.Net.TCPState
