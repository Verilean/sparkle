/-
  IP.Bus.CANopen — CANopen (CiA 301) application layer on
  top of IP.Bus.CAN.

  COB-ID encoding (11-bit CAN ID):
      [10..7]  function code (FC)
      [ 6..0]  node-ID (1..127)

  Function codes (CiA 301 §7.3 default predefined connection set):
      FC=0   COB-ID 0x000           NMT     (master broadcast)
      FC=1   COB-ID 0x080           SYNC    (node-id always 0)
      FC=1   COB-ID 0x080+nid       EMCY    (nodes ≥ 1)
      FC=3   COB-ID 0x180+nid       TPDO1   (slave → master)
      FC=4   COB-ID 0x200+nid       RPDO1   (master → slave)
      FC=11  COB-ID 0x580+nid       SDO Tx  (response)
      FC=12  COB-ID 0x600+nid       SDO Rx  (request)
      FC=14  COB-ID 0x700+nid       Heartbeat

  Two layers:
    1. `cobIdOf` / `decodeCobId` — pack/unpack the
       (function code, node-id) pair.
    2. Message builders/parsers per service type (NMT, SDO,
       heartbeat, etc.) returning fully-formed CAN frames.
-/

import IP.Bus.CAN

namespace Sparkle.IP.Bus.CANopen

open Sparkle.IP.Bus.CAN (Frame FrameKind)

/-! ### COB-ID. -/

/-- Compose an 11-bit COB-ID from a function code (4 bits)
    and a node-ID (7 bits). -/
@[inline] def cobIdOf (fc nid : Nat) : Nat :=
  ((fc &&& 0xF) <<< 7) ||| (nid &&& 0x7F)

/-- Decompose an 11-bit COB-ID into (function code, node-id). -/
@[inline] def decodeCobId (cobId : Nat) : Nat × Nat :=
  ((cobId >>> 7) &&& 0xF, cobId &&& 0x7F)

/-- Function-code constants (CiA 301). -/
def fcNmt        : Nat := 0
def fcSync       : Nat := 1   -- SYNC + EMCY share fc=1 (distinguished by nid)
def fcTime       : Nat := 2
def fcTpdo1      : Nat := 3
def fcRpdo1      : Nat := 4
def fcTpdo2      : Nat := 5
def fcRpdo2      : Nat := 6
def fcTpdo3      : Nat := 7
def fcRpdo3      : Nat := 8
def fcTpdo4      : Nat := 9
def fcRpdo4      : Nat := 10
def fcSdoTx      : Nat := 11
def fcSdoRx      : Nat := 12
def fcHeartbeat  : Nat := 14

/-! ### NMT (Network Management). -/

inductive NmtCommand where
  | startRemoteNode     -- 0x01: pre-operational/stopped → operational
  | stopRemoteNode      -- 0x02
  | enterPreOperational -- 0x80
  | resetNode           -- 0x81
  | resetCommunication  -- 0x82
  deriving Repr, BEq, DecidableEq, Inhabited

def NmtCommand.toByte : NmtCommand → UInt8
  | .startRemoteNode     => 0x01
  | .stopRemoteNode      => 0x02
  | .enterPreOperational => 0x80
  | .resetNode           => 0x81
  | .resetCommunication  => 0x82

def NmtCommand.ofByte? : UInt8 → Option NmtCommand
  | 0x01 => some .startRemoteNode
  | 0x02 => some .stopRemoteNode
  | 0x80 => some .enterPreOperational
  | 0x81 => some .resetNode
  | 0x82 => some .resetCommunication
  | _    => none

/-- Build an NMT broadcast (COB-ID = 0).  `target` = 0 means
    all nodes, otherwise a single node ID 1..127. -/
def buildNmt (cmd : NmtCommand) (target : Nat) : Frame :=
  { kind := .standard
  , id := 0
  , rtr := false
  , dlc := 2
  , data := #[cmd.toByte, UInt8.ofNat (target &&& 0x7F)] }

/-- Parse an NMT frame.  Returns `(cmd, target)` or `none`. -/
def parseNmt (f : Frame) : Option (NmtCommand × Nat) := Id.run do
  if f.id ≠ 0 then return none
  if f.data.size < 2 then return none
  match NmtCommand.ofByte? f.data[0]! with
  | none => return none
  | some cmd => return some (cmd, f.data[1]!.toNat)

/-! ### Heartbeat / NMT error control (CiA 301 §7.2.4.3). -/

/-- NMT state field (one byte heartbeat payload). -/
inductive NmtState where
  | bootUp            -- 0x00
  | stopped           -- 0x04
  | operational       -- 0x05
  | preOperational    -- 0x7F
  deriving Repr, BEq, DecidableEq, Inhabited

def NmtState.toByte : NmtState → UInt8
  | .bootUp         => 0x00
  | .stopped        => 0x04
  | .operational    => 0x05
  | .preOperational => 0x7F

def NmtState.ofByte? : UInt8 → Option NmtState
  | 0x00 => some .bootUp
  | 0x04 => some .stopped
  | 0x05 => some .operational
  | 0x7F => some .preOperational
  | _    => none

/-- Build a heartbeat message from a node.  COB-ID =
    0x700 + nid; payload is one byte (NMT state). -/
def buildHeartbeat (nid : Nat) (state : NmtState) : Frame :=
  { kind := .standard
  , id := cobIdOf fcHeartbeat nid
  , rtr := false
  , dlc := 1
  , data := #[state.toByte] }

/-- Parse a heartbeat message.  Returns (node-id, state). -/
def parseHeartbeat (f : Frame) : Option (Nat × NmtState) := Id.run do
  let (fc, nid) := decodeCobId f.id
  if fc ≠ fcHeartbeat then return none
  if f.data.size < 1 then return none
  match NmtState.ofByte? f.data[0]! with
  | none => return none
  | some st => return some (nid, st)

/-! ### SDO (Service Data Object) — expedited transfer.

    Used to read/write entries in a node's Object Dictionary.
    Expedited transfer covers values up to 4 bytes (= scalars
    like UInt8/UInt16/UInt32/Int32/Float32, plus 0..4-byte
    strings).  Multi-segment transfers for larger data are
    out of scope.

    Request CCS values:
      0x23: download (write) expedited, size=4
      0x27: download (write) expedited, size=3
      0x2B: download (write) expedited, size=2
      0x2F: download (write) expedited, size=1
      0x40: upload (read) request
      0x60: download response (no data)
      0x4F: upload response (read), 1 byte
      0x4B: upload response, 2 bytes
      0x47: upload response, 3 bytes
      0x43: upload response, 4 bytes
-/

inductive SdoDirection where
  | clientToServer   -- master → slave (function code 12, COB-ID 0x600+nid)
  | serverToClient   -- slave → master (function code 11, COB-ID 0x580+nid)
  deriving Repr, BEq, Inhabited

/-- One SDO expedited transfer (request or response). -/
structure SdoExpedited where
  direction : SdoDirection
  /-- The CANopen node we're talking to. -/
  nodeId    : Nat
  /-- First byte of the SDO payload — encodes the
      command specifier + size flags. -/
  ccs       : UInt8
  /-- Object Dictionary index (16-bit). -/
  index     : Nat
  /-- Sub-index (8-bit). -/
  subindex  : Nat
  /-- 0..4 data bytes (size determined by `ccs`). -/
  data      : Array UInt8
  deriving Repr, Inhabited

/-- Compute the on-wire CCS byte for an expedited download
    (write) request with `n` bytes (0..4) of data. -/
def downloadCcsForSize (n : Nat) : UInt8 :=
  match n with
  | 1 => 0x2F
  | 2 => 0x2B
  | 3 => 0x27
  | 4 => 0x23
  | _ => 0x23   -- default to 4-byte for n = 0 or > 4

/-- Compute the on-wire CCS byte for an expedited upload
    (read) response. -/
def uploadResponseCcsForSize (n : Nat) : UInt8 :=
  match n with
  | 1 => 0x4F
  | 2 => 0x4B
  | 3 => 0x47
  | 4 => 0x43
  | _ => 0x43

/-- CCS for an upload request (read, no data). -/
def uploadRequestCcs : UInt8 := 0x40

/-- CCS for a download response (write acknowledged, no data). -/
def downloadResponseCcs : UInt8 := 0x60

/-- Header bytes (CCS + index LSB + index MSB + subindex)
    common to all SDO expedited frames. -/
private def sdoHeader (ccs : UInt8) (index subindex : Nat) : Array UInt8 :=
  #[ ccs
   , UInt8.ofNat (index &&& 0xFF)
   , UInt8.ofNat ((index >>> 8) &&& 0xFF)
   , UInt8.ofNat (subindex &&& 0xFF) ]

/-- Pad a payload data field to 4 bytes (the expedited
    transfer always carries 4 data bytes on the wire, even
    if fewer are semantically meaningful per the CCS). -/
private def padTo4 (data : Array UInt8) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.replicate 4 0
  for i in [:min data.size 4] do
    out := out.set! i data[i]!
  return out

/-- Build an SDO expedited download (write) request frame.
    Master → slave.  `data` is 1..4 bytes. -/
def buildSdoDownloadRequest
    (nodeId index subindex : Nat) (data : Array UInt8) : Frame :=
  let ccs := downloadCcsForSize (min data.size 4)
  { kind := .standard
  , id := cobIdOf fcSdoRx nodeId
  , rtr := false
  , dlc := 8
  , data := sdoHeader ccs index subindex ++ padTo4 data }

/-- Build an SDO expedited download response (write ack)
    frame.  Slave → master. -/
def buildSdoDownloadResponse
    (nodeId index subindex : Nat) : Frame :=
  { kind := .standard
  , id := cobIdOf fcSdoTx nodeId
  , rtr := false
  , dlc := 8
  , data := sdoHeader downloadResponseCcs index subindex ++ Array.replicate 4 0 }

/-- Build an SDO expedited upload (read) request frame.
    Master → slave; no data. -/
def buildSdoUploadRequest (nodeId index subindex : Nat) : Frame :=
  { kind := .standard
  , id := cobIdOf fcSdoRx nodeId
  , rtr := false
  , dlc := 8
  , data := sdoHeader uploadRequestCcs index subindex ++ Array.replicate 4 0 }

/-- Build an SDO expedited upload (read) response frame.
    Slave → master; carries `data` (1..4 bytes). -/
def buildSdoUploadResponse
    (nodeId index subindex : Nat) (data : Array UInt8) : Frame :=
  let ccs := uploadResponseCcsForSize (min data.size 4)
  { kind := .standard
  , id := cobIdOf fcSdoTx nodeId
  , rtr := false
  , dlc := 8
  , data := sdoHeader ccs index subindex ++ padTo4 data }

/-- Parse any SDO expedited frame.  Returns the
    `SdoExpedited` view, or `none` on non-SDO frames. -/
def parseSdo (f : Frame) : Option SdoExpedited := Id.run do
  let (fc, nid) := decodeCobId f.id
  let dir : SdoDirection :=
    if fc = fcSdoTx then SdoDirection.serverToClient
    else if fc = fcSdoRx then SdoDirection.clientToServer
    else SdoDirection.clientToServer  -- placeholder; we check below
  if fc ≠ fcSdoTx ∧ fc ≠ fcSdoRx then return none
  if f.data.size < 8 then return none
  let ccs := f.data[0]!
  let index :=
    f.data[1]!.toNat ||| (f.data[2]!.toNat <<< 8)
  let subindex := f.data[3]!.toNat
  -- Derive data length from CCS.
  let dataLen :=
    match ccs.toNat with
    | 0x2F | 0x4F => 1
    | 0x2B | 0x4B => 2
    | 0x27 | 0x47 => 3
    | 0x23 | 0x43 => 4
    | _ => 0  -- 0x40 upload request / 0x60 download response
  let mut data : Array UInt8 := Array.replicate dataLen 0
  for i in [:dataLen] do
    data := data.set! i f.data[4 + i]!
  return some { direction := dir, nodeId := nid, ccs := ccs
              , index := index, subindex := subindex, data := data }

/-! ### PDO (Process Data Object).

    PDOs carry application data with no transport overhead
    — the COB-ID identifies the "channel" and the receivers
    interpret the bytes per a static mapping.
    The mapping itself lives in each node's Object
    Dictionary (subindices of 0x1600/0x1A00 etc.) and is
    out of scope here; we just provide the frame
    construction. -/

/-- Build a TPDO (transmit PDO, slave→master).  `index`
    selects TPDO1..TPDO4 (0..3) via the function-code table. -/
def buildTpdo (nodeId index : Nat) (data : Array UInt8) : Frame :=
  let fc := match index with
    | 0 => fcTpdo1
    | 1 => fcTpdo2
    | 2 => fcTpdo3
    | _ => fcTpdo4
  { kind := .standard
  , id := cobIdOf fc nodeId
  , rtr := false
  , dlc := min data.size 8
  , data := data }

/-- Build an RPDO (receive PDO, master→slave). -/
def buildRpdo (nodeId index : Nat) (data : Array UInt8) : Frame :=
  let fc := match index with
    | 0 => fcRpdo1
    | 1 => fcRpdo2
    | 2 => fcRpdo3
    | _ => fcRpdo4
  { kind := .standard
  , id := cobIdOf fc nodeId
  , rtr := false
  , dlc := min data.size 8
  , data := data }

/-! ### SYNC. -/

/-- Build the SYNC broadcast frame (COB-ID = 0x080, no
    payload typically).  Optional counter byte may be added
    for "SYNC with counter" mode. -/
def buildSync (counter : Option UInt8 := none) : Frame :=
  match counter with
  | none =>
    { kind := .standard, id := 0x80, rtr := false, dlc := 0, data := #[] }
  | some c =>
    { kind := .standard, id := 0x80, rtr := false, dlc := 1, data := #[c] }

/-- Build an EMCY (emergency) frame from a slave.  Payload:
      bytes 0-1: error code (LSB first)
      byte 2:    error register (Object 0x1001)
      bytes 3-7: manufacturer-specific
-/
def buildEmcy (nodeId errorCode : Nat) (errReg : UInt8)
    (mfgSpecific : Array UInt8) : Frame :=
  let mfgPadded : Array UInt8 := Id.run do
    let mut out : Array UInt8 := Array.replicate 5 0
    for i in [:min mfgSpecific.size 5] do
      out := out.set! i mfgSpecific[i]!
    return out
  let payload : Array UInt8 :=
    #[ UInt8.ofNat (errorCode &&& 0xFF)
     , UInt8.ofNat ((errorCode >>> 8) &&& 0xFF)
     , errReg ] ++ mfgPadded
  { kind := .standard
  , id := cobIdOf fcSync nodeId
  , rtr := false
  , dlc := 8
  , data := payload }

end Sparkle.IP.Bus.CANopen
