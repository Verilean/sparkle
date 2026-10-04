/-
  IP.Bus.DroneCAN — DroneCAN (UAVCAN v0) message + service
  layer on top of IP.Bus.CAN.

  DroneCAN uses CAN 2.0B (29-bit ID extended frames) only.

  CAN ID layout (29 bits):

      Message frames (broadcast, FC = "message"):
        bits [28..24]  priority (0..31; 0 = highest)
        bits [23..8]   message type ID (uint16)
        bit  [7]       service_not_message = 0
        bits [6..0]    source node ID (1..127)

      Service frames (FC = "service"):
        bits [28..24]  priority
        bits [23..16]  service type ID (uint8)
        bit  [15]      request_not_response
        bits [14..8]   destination node ID
        bit  [7]       service_not_message = 1
        bits [6..0]    source node ID

  Tail byte (last byte of every CAN frame in a transfer):
        bit  [7]  start_of_transfer (SOT)
        bit  [6]  end_of_transfer   (EOT)
        bit  [5]  toggle
        bits [4..0]  transfer ID (mod 32)

  Single-frame transfer: SOT=1, EOT=1, toggle=0, content
  bytes in [0..6], tail byte at position 7 (or earlier if
  content is shorter).
-/

import IP.Bus.CAN

namespace Sparkle.IP.Bus.DroneCAN

open Sparkle.IP.Bus.CAN (Frame FrameKind)

/-! ### Tail byte. -/

structure TailByte where
  sot       : Bool
  eot       : Bool
  toggle    : Bool
  transferId : Nat   -- 0..31
  deriving Repr, Inhabited

def TailByte.toByte (t : TailByte) : UInt8 :=
  let sotBit := if t.sot then 1 else 0
  let eotBit := if t.eot then 1 else 0
  let togBit := if t.toggle then 1 else 0
  UInt8.ofNat
    ((sotBit <<< 7) ||| (eotBit <<< 6) ||| (togBit <<< 5)
      ||| (t.transferId &&& 0x1F))

def TailByte.ofByte (b : UInt8) : TailByte :=
  let n := b.toNat
  { sot := (n &&& 0x80) ≠ 0
  , eot := (n &&& 0x40) ≠ 0
  , toggle := (n &&& 0x20) ≠ 0
  , transferId := n &&& 0x1F }

/-! ### 29-bit CAN ID encoding. -/

/-- Build the CAN ID for a DroneCAN broadcast message. -/
def messageCanId (priority msgTypeId srcNodeId : Nat) : Nat :=
  ((priority &&& 0x1F) <<< 24)
    ||| ((msgTypeId &&& 0xFFFF) <<< 8)
    -- bit 7 (service_not_message) = 0
    ||| (srcNodeId &&& 0x7F)

/-- Build the CAN ID for a DroneCAN service request/response. -/
def serviceCanId (priority svcTypeId : Nat) (request : Bool)
    (dstNodeId srcNodeId : Nat) : Nat :=
  let reqBit := if request then 1 else 0
  ((priority &&& 0x1F) <<< 24)
    ||| ((svcTypeId &&& 0xFF) <<< 16)
    ||| (reqBit <<< 15)
    ||| ((dstNodeId &&& 0x7F) <<< 8)
    ||| (1 <<< 7)   -- service_not_message = 1
    ||| (srcNodeId &&& 0x7F)

/-- Decompose a DroneCAN CAN ID into its constituent fields.
    `isService` tells the caller whether to interpret the
    middle range as a 16-bit message type ID or an
    8-bit service type ID + req-bit + dst-node-id. -/
structure DecodedId where
  priority      : Nat
  isService     : Bool
  /-- For messages: 16-bit message type ID.
      For services: 8-bit service type ID. -/
  typeId        : Nat
  /-- For services only.  Meaningless for messages. -/
  isRequest     : Bool
  /-- For services only. -/
  dstNodeId     : Nat
  srcNodeId     : Nat
  deriving Repr, Inhabited

def decodeCanId (canId : Nat) : DecodedId :=
  let priority := (canId >>> 24) &&& 0x1F
  let srcNode := canId &&& 0x7F
  let isService := (canId &&& 0x80) ≠ 0
  if isService then
    let svcType := (canId >>> 16) &&& 0xFF
    let isReq := (canId &&& (1 <<< 15)) ≠ 0
    let dstNode := (canId >>> 8) &&& 0x7F
    { priority := priority
    , isService := true
    , typeId := svcType
    , isRequest := isReq
    , dstNodeId := dstNode
    , srcNodeId := srcNode }
  else
    let msgType := (canId >>> 8) &&& 0xFFFF
    { priority := priority
    , isService := false
    , typeId := msgType
    , isRequest := false
    , dstNodeId := 0
    , srcNodeId := srcNode }

/-! ### Single-frame transfers.

    Easy case: payload fits in the 7 bytes preceding the
    tail byte.  Multi-frame requires CRC-16-CCITT-FALSE +
    transfer reassembly, which is a follow-up. -/

/-- Build a single-frame broadcast message transfer.  `payload`
    must be ≤ 7 bytes. -/
def buildBroadcastSingle
    (priority msgTypeId srcNodeId : Nat)
    (transferId : Nat) (payload : Array UInt8) : Option Frame :=
  if payload.size > 7 then none
  else
    let tail := TailByte.toByte
      { sot := true, eot := true, toggle := false
      , transferId := transferId &&& 0x1F }
    let data := payload ++ #[tail]
    some
      { kind := .extended
      , id := messageCanId priority msgTypeId srcNodeId
      , rtr := false
      , dlc := data.size
      , data := data }

/-- Build a single-frame service request or response.  `payload`
    must be ≤ 7 bytes. -/
def buildServiceSingle
    (priority svcTypeId : Nat) (request : Bool)
    (dstNodeId srcNodeId transferId : Nat)
    (payload : Array UInt8) : Option Frame :=
  if payload.size > 7 then none
  else
    let tail := TailByte.toByte
      { sot := true, eot := true, toggle := false
      , transferId := transferId &&& 0x1F }
    let data := payload ++ #[tail]
    some
      { kind := .extended
      , id := serviceCanId priority svcTypeId request dstNodeId srcNodeId
      , rtr := false
      , dlc := data.size
      , data := data }

/-- Parse a single-frame transfer.  Returns the decoded CAN
    ID + tail byte + payload (= data minus the trailing tail
    byte).  Returns `none` if SOT/EOT aren't both set
    (= multi-frame transfer, not handled here). -/
def parseSingleFrame (f : Frame) :
    Option (DecodedId × TailByte × Array UInt8) := Id.run do
  if f.kind ≠ FrameKind.extended ∨ f.data.size = 0 then return none
  let tailIdx := f.data.size - 1
  let tail := TailByte.ofByte f.data[tailIdx]!
  if !tail.sot ∨ !tail.eot then return none
  let mut payload : Array UInt8 := Array.replicate tailIdx 0
  for i in [:tailIdx] do
    payload := payload.set! i f.data[i]!
  return some (decodeCanId f.id, tail, payload)

/-! ### CRC-16-CCITT-FALSE (poly 0x1021, init 0xFFFF).

    Used by DroneCAN for multi-frame transfers: the first 2
    bytes of the first frame's payload carry the
    CRC-16-CCITT-FALSE of (data type signature || actual
    transfer payload), byte-order LSB first. -/

@[inline] def crc16CcittStep (crc : Nat) (byte : UInt8) : Nat := Id.run do
  let mut c := crc ^^^ (byte.toNat <<< 8)
  for _ in [:8] do
    if (c &&& 0x8000) ≠ 0 then
      c := ((c <<< 1) ^^^ 0x1021) &&& 0xFFFF
    else
      c := (c <<< 1) &&& 0xFFFF
  return c

def crc16Ccitt (bs : Array UInt8) : Nat :=
  bs.foldl crc16CcittStep 0xFFFF

/-! ### Standard DroneCAN message types. -/

/-- uavcan.protocol.NodeStatus (data type ID 341):
      uint32 uptime_sec
      uint2  health      [OK=0, WARNING=1, ERROR=2, CRITICAL=3]
      uint3  mode        [OPERATIONAL=0, INITIALIZATION=1, MAINTENANCE=2,
                          SOFTWARE_UPDATE=3, OFFLINE=7]
      uint3  sub_mode
      uint16 vendor_specific_status_code

    Total: 7 bytes payload (uint2+uint3+uint3 = uint8). -/
def msgTypeIdNodeStatus : Nat := 341

inductive NodeHealth where | ok | warning | error | critical
  deriving Repr, BEq, DecidableEq, Inhabited

def NodeHealth.toNat : NodeHealth → Nat
  | .ok => 0 | .warning => 1 | .error => 2 | .critical => 3

inductive NodeMode where
  | operational | initialization | maintenance
  | softwareUpdate | offline
  deriving Repr, BEq, DecidableEq, Inhabited

def NodeMode.toNat : NodeMode → Nat
  | .operational => 0
  | .initialization => 1
  | .maintenance => 2
  | .softwareUpdate => 3
  | .offline => 7

/-- Serialize a NodeStatus into 7 payload bytes. -/
def encodeNodeStatus
    (uptimeSec : Nat) (health : NodeHealth) (mode : NodeMode)
    (subMode : Nat) (vendorCode : Nat) : Array UInt8 :=
  let modeHealthByte :=
    (health.toNat &&& 0x3)                 -- low 2 bits = health
    ||| ((mode.toNat &&& 0x7) <<< 2)        -- next 3 bits = mode
    ||| ((subMode &&& 0x7) <<< 5)           -- top 3 bits = sub-mode
  #[ UInt8.ofNat (uptimeSec &&& 0xFF)
   , UInt8.ofNat ((uptimeSec >>> 8) &&& 0xFF)
   , UInt8.ofNat ((uptimeSec >>> 16) &&& 0xFF)
   , UInt8.ofNat ((uptimeSec >>> 24) &&& 0xFF)
   , UInt8.ofNat modeHealthByte
   , UInt8.ofNat (vendorCode &&& 0xFF)
   , UInt8.ofNat ((vendorCode >>> 8) &&& 0xFF) ]

/-- Build a NodeStatus broadcast frame from a given source
    node.  Priority defaults to 7 (a common general-purpose
    priority for status messages). -/
def buildNodeStatus
    (srcNodeId : Nat) (transferId : Nat)
    (uptimeSec : Nat) (health : NodeHealth) (mode : NodeMode)
    (vendorCode : Nat := 0) (subMode : Nat := 0)
    (priority : Nat := 7) : Frame :=
  let payload := encodeNodeStatus uptimeSec health mode subMode vendorCode
  match buildBroadcastSingle priority msgTypeIdNodeStatus
            srcNodeId transferId payload with
  | some f => f
  | none =>
    -- 7-byte payload fits, should never hit `none`; fall back
    -- to an empty extended frame on the unlikely chance.
    { kind := .extended, id := 0, rtr := false, dlc := 0, data := #[] }

/-! ### uavcan.equipment.esc.RawCommand (data type ID 1030).

    Sends speed commands to multiple ESCs in a single
    broadcast.  Body is up to 20 channels of int14
    (-8191..+8191) packed bitwise.  For a single-frame
    transfer we limit to 3 channels (3 * 14 = 42 bits =
    5.25 bytes → fits in 6 bytes + tail = 7 bytes).
-/

def msgTypeIdEscRawCommand : Nat := 1030

/-- Encode up to 3 ESC RPM commands (signed -8191..+8191)
    into a 6-byte payload + tail byte (7 bytes total). -/
def encodeEscRawCommand3 (cmd0 cmd1 cmd2 : Int) : Array UInt8 := Id.run do
  -- Two's-complement 14-bit pack.  For negative v, return
  -- (2^14 + v) mod 2^14; for non-negative, v itself masked to 14 bits.
  let pack14 (v : Int) : Nat :=
    if v < 0 then ((1 <<< 14) + v).toNat &&& 0x3FFF
    else v.toNat &&& 0x3FFF
  let bits :=
    (pack14 cmd0)
    ||| ((pack14 cmd1) <<< 14)
    ||| ((pack14 cmd2) <<< 28)
  let mut out : Array UInt8 := Array.replicate 6 0
  for i in [:6] do
    out := out.set! i (UInt8.ofNat ((bits >>> (i * 8)) &&& 0xFF))
  return out

end Sparkle.IP.Bus.DroneCAN
