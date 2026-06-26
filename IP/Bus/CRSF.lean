/-
  IP.Bus.CRSF — TBS Crossfire protocol.

  CRSF is a UART-based protocol at 420 kbps used in FPV
  drones / RC: receiver ↔ flight controller, radio ↔ TX
  module.  Half-duplex; the FC and the radio share the same
  RX/TX wire and arbitrate by timeslot.

  Frame format:

      [sync  1B]  0xC8 (FC↔RX) or 0xEE (TX↔radio module)
      [len   1B]  count of bytes following = type + payload + crc
      [type  1B]  frame type ID
      [payload N]
      [crc8  1B]  CRC-8 (poly 0xD5) over (type || payload)

  Common frame types:
      0x02   GPS
      0x08   Battery sensor (voltage / current / capacity)
      0x14   Link Statistics (rssi / link quality / SNR)
      0x16   RC Channels Packed (16 × 11-bit)
      0x29   Device Info
      0x2B   Parameter Settings Entry
-/

import Sparkle

namespace Sparkle.IP.Bus.CRSF

/-- Sync byte conventions. -/
def syncFC : UInt8 := 0xC8     -- FC ↔ receiver
def syncTX : UInt8 := 0xEE     -- TX module ↔ radio module

/-- Frame type IDs. -/
def typeGps          : UInt8 := 0x02
def typeBatterySensor : UInt8 := 0x08
def typeLinkStats    : UInt8 := 0x14
def typeRcChannels   : UInt8 := 0x16
def typeDeviceInfo   : UInt8 := 0x29

/-! ### CRC-8 (poly 0xD5).

    Standard "Bosch CAN" CRC-8 with poly 0xD5; the same one
    used by CRSF, Dallas iButton, and several other
    embedded protocols. -/

@[inline] private def crc8Step (crc : UInt8) (b : UInt8) : UInt8 := Id.run do
  let mut c := crc ^^^ b
  for _ in [:8] do
    if (c.toNat &&& 0x80) ≠ 0 then
      c := (UInt8.ofNat ((c.toNat <<< 1) &&& 0xFF)) ^^^ 0xD5
    else
      c := UInt8.ofNat ((c.toNat <<< 1) &&& 0xFF)
  return c

def crc8 (bytes : Array UInt8) : UInt8 :=
  bytes.foldl crc8Step 0

/-! ### Frame envelope. -/

structure Frame where
  /-- Sync byte (0xC8 / 0xEE / custom). -/
  sync    : UInt8
  /-- Frame type. -/
  ftype   : UInt8
  /-- Payload bytes (without type or CRC). -/
  payload : Array UInt8
  deriving Repr, Inhabited

/-- Compute the CRC of a frame (over type + payload). -/
def frameCrc (f : Frame) : UInt8 :=
  crc8 (#[f.ftype] ++ f.payload)

/-- Serialize a CRSF frame.  Total wire size = 4 + payload.size. -/
def buildFrame (f : Frame) : Array UInt8 :=
  let len := f.payload.size + 2  -- type + crc
  #[f.sync, UInt8.ofNat len, f.ftype] ++ f.payload ++ #[frameCrc f]

/-- Parse a CRSF frame from a byte array.  Returns
    `(frame, crcOk)` plus the offset of the byte after the
    parsed frame (so streams of frames can be peeled
    one-by-one).  `none` on insufficient bytes or sync-byte
    mismatch. -/
def parseFrame (bytes : Array UInt8) (off : Nat := 0) :
    Option (Frame × Bool × Nat) := Id.run do
  if off + 2 > bytes.size then return none
  let sync := bytes[off]!
  let len := bytes[off + 1]!.toNat
  if len < 2 then return none
  if off + 2 + len > bytes.size then return none
  let ftype := bytes[off + 2]!
  let payloadLen := len - 2
  let mut payload : Array UInt8 := Array.replicate payloadLen 0
  for i in [:payloadLen] do
    payload := payload.set! i bytes[off + 3 + i]!
  let wireCrc := bytes[off + 2 + len - 1]!
  let f : Frame := { sync := sync, ftype := ftype, payload := payload }
  let crcOk := wireCrc = frameCrc f
  return some (f, crcOk, off + 2 + len)

/-! ### RC Channels Packed (frame type 0x16).

    Payload: 22 bytes = 16 × 11-bit channels, exact same
    bit-packing as S.BUS.  Each channel is 0..2047.
-/

/-- Pack 16 channels into a 22-byte RC Channels Packed payload. -/
def packChannels (channels : Array Nat) : Array UInt8 := Id.run do
  let mut bits : Nat := 0
  for i in [:16] do
    let v := if h : i < channels.size then channels[i]! &&& 0x7FF else 0
    bits := bits ||| (v <<< (i * 11))
  let mut out : Array UInt8 := Array.replicate 22 0
  for i in [:22] do
    out := out.set! i (UInt8.ofNat ((bits >>> (i * 8)) &&& 0xFF))
  return out

def unpackChannels (bytes : Array UInt8) : Array Nat := Id.run do
  let mut bits : Nat := 0
  for i in [:22] do
    let b := if h : i < bytes.size then bytes[i]!.toNat else 0
    bits := bits ||| (b <<< (i * 8))
  let mut out : Array Nat := Array.replicate 16 0
  for i in [:16] do
    out := out.set! i ((bits >>> (i * 11)) &&& 0x7FF)
  return out

/-- Convenience: build an RC Channels Packed frame from a
    16-channel array. -/
def buildRcChannelsFrame (channels : Array Nat) (sync : UInt8 := syncFC) : Array UInt8 :=
  buildFrame
    { sync := sync, ftype := typeRcChannels, payload := packChannels channels }

/-! ### Link Statistics (frame type 0x14).

    Payload: 10 bytes
      bytes 0     uplink RSSI antenna 1 (dBm, signed +127 offset)
      bytes 1     uplink RSSI antenna 2
      bytes 2     uplink link quality (0..100)
      bytes 3     uplink SNR (signed int8)
      bytes 4     active antenna (0 or 1)
      bytes 5     RF mode
      bytes 6     uplink TX power (lookup table index)
      bytes 7     downlink RSSI
      bytes 8     downlink link quality
      bytes 9     downlink SNR
-/

structure LinkStats where
  upRssiAnt1   : Int8
  upRssiAnt2   : Int8
  upLinkQuality : UInt8
  upSnr        : Int8
  activeAntenna : UInt8
  rfMode       : UInt8
  upTxPower    : UInt8
  dnRssi       : Int8
  dnLinkQuality : UInt8
  dnSnr        : Int8
  deriving Repr, Inhabited

private def i8ToUInt8 (x : Int8) : UInt8 :=
  let n := x.toInt
  if n < 0 then UInt8.ofNat ((256 + n).toNat) else UInt8.ofNat n.toNat

private def u8ToInt8 (x : UInt8) : Int8 :=
  let n := x.toNat
  if n ≥ 128 then Int8.ofInt ((n : Int) - 256) else Int8.ofInt n

def packLinkStats (s : LinkStats) : Array UInt8 :=
  #[ i8ToUInt8 s.upRssiAnt1
   , i8ToUInt8 s.upRssiAnt2
   , s.upLinkQuality
   , i8ToUInt8 s.upSnr
   , s.activeAntenna
   , s.rfMode
   , s.upTxPower
   , i8ToUInt8 s.dnRssi
   , s.dnLinkQuality
   , i8ToUInt8 s.dnSnr ]

def unpackLinkStats (bytes : Array UInt8) : Option LinkStats := Id.run do
  if bytes.size < 10 then return none
  return some
    { upRssiAnt1 := u8ToInt8 bytes[0]!
    , upRssiAnt2 := u8ToInt8 bytes[1]!
    , upLinkQuality := bytes[2]!
    , upSnr := u8ToInt8 bytes[3]!
    , activeAntenna := bytes[4]!
    , rfMode := bytes[5]!
    , upTxPower := bytes[6]!
    , dnRssi := u8ToInt8 bytes[7]!
    , dnLinkQuality := bytes[8]!
    , dnSnr := u8ToInt8 bytes[9]! }

end Sparkle.IP.Bus.CRSF
