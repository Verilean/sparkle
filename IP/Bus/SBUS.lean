/-
  IP.Bus.SBUS — Futaba S.BUS frame encoder/decoder.

  S.BUS is an inverted-UART 100 000 baud / 8E2 (1 start + 8
  data LSB-first + 1 even parity + 2 stop) serial bus used
  to drive servos and (more relevantly here) deliver RC
  channel data from a receiver to a flight controller.

  Frame format (25 bytes, ~3 ms on the wire at 100 kbps):

      byte 0    : 0x0F            (header)
      bytes 1..22 (22 bytes = 176 bits):
                  16 channels × 11 bits, channel 0 LSB-first
                  in bytes 1..2..3..  ↘ packed
      byte 23   : flags            (bits below)
      byte 24   : 0x00             (footer)

  Flag byte (byte 23):
      bit 0  digital channel 17 (ch17)
      bit 1  digital channel 18 (ch18)
      bit 2  frame lost          (radio lost telemetry to controller)
      bit 3  failsafe activated  (controller lost link to model)
      bits 4..7  reserved (0)

  Channel value range: 0..2047 (11-bit unsigned).  Typical
  mapping: 1000 = -100 %, 1500 = neutral, 2000 = +100 %.

  This module ships pure-data builder/parser.  The HW UART
  (4×11 = 44 bits per byte at 100 kbps with inversion) is a
  separate Sparkle circuit do module.
-/

import Sparkle

namespace Sparkle.IP.Bus.SBUS

/-- One S.BUS frame. -/
structure Frame where
  /-- 16 analog channels (each 11-bit, 0..2047). -/
  channels  : Array Nat       -- length must be 16
  /-- Digital channel 17. -/
  ch17      : Bool
  /-- Digital channel 18. -/
  ch18      : Bool
  /-- Frame lost (RX → FC link failure). -/
  frameLost : Bool
  /-- Failsafe active (TX → RX link failure). -/
  failsafe  : Bool
  deriving Repr, Inhabited

/-- Header byte. -/
def headerByte : UInt8 := 0x0F

/-- Footer byte. -/
def footerByte : UInt8 := 0x00

/-- Pack the flags into byte 23. -/
def encodeFlags (ch17 ch18 frameLost failsafe : Bool) : UInt8 :=
  let b0 := if ch17 then 1 else 0
  let b1 := if ch18 then 2 else 0
  let b2 := if frameLost then 4 else 0
  let b3 := if failsafe then 8 else 0
  UInt8.ofNat (b0 ||| b1 ||| b2 ||| b3)

/-- Decode the flag byte. -/
def decodeFlags (b : UInt8) : Bool × Bool × Bool × Bool :=
  let n := b.toNat
  ( (n &&& 1) ≠ 0
  , (n &&& 2) ≠ 0
  , (n &&& 4) ≠ 0
  , (n &&& 8) ≠ 0 )

/-- Pack 16 × 11-bit channels into 22 bytes LSB-first.

    The channels are concatenated bit-wise: channel 0 occupies
    bits 0..10, channel 1 bits 11..21, …, channel 15 bits
    165..175.  Each output byte i (0..21) takes bits
    [8·i .. 8·i + 7] of that bitstream. -/
def packChannels (channels : Array Nat) : Array UInt8 := Id.run do
  -- Concatenate all 16×11 bits into one 176-bit Nat (LSB first).
  let mut bits : Nat := 0
  for i in [:16] do
    let v := if h : i < channels.size then channels[i]! &&& 0x7FF else 0
    bits := bits ||| (v <<< (i * 11))
  -- Split into 22 bytes.
  let mut out : Array UInt8 := Array.replicate 22 0
  for i in [:22] do
    out := out.set! i (UInt8.ofNat ((bits >>> (i * 8)) &&& 0xFF))
  return out

/-- Reverse of `packChannels`: extract 16 × 11-bit channels
    from 22 bytes. -/
def unpackChannels (bytes : Array UInt8) : Array Nat := Id.run do
  let mut bits : Nat := 0
  for i in [:22] do
    let b := if h : i < bytes.size then bytes[i]!.toNat else 0
    bits := bits ||| (b <<< (i * 8))
  let mut out : Array Nat := Array.replicate 16 0
  for i in [:16] do
    out := out.set! i ((bits >>> (i * 11)) &&& 0x7FF)
  return out

/-- Build the 25-byte on-wire S.BUS frame. -/
def buildFrame (f : Frame) : Array UInt8 :=
  #[headerByte] ++ packChannels f.channels ++
    #[encodeFlags f.ch17 f.ch18 f.frameLost f.failsafe, footerByte]

/-- Parse a 25-byte S.BUS frame.  Returns `none` on wrong
    size, header, or footer. -/
def parseFrame (bytes : Array UInt8) : Option Frame := Id.run do
  if bytes.size ≠ 25 then return none
  if bytes[0]! ≠ headerByte then return none
  if bytes[24]! ≠ footerByte then return none
  let chBytes : Array UInt8 := Id.run do
    let mut out : Array UInt8 := Array.replicate 22 0
    for i in [:22] do
      out := out.set! i bytes[1 + i]!
    return out
  let channels := unpackChannels chBytes
  let (ch17, ch18, frameLost, failsafe) := decodeFlags bytes[23]!
  return some
    { channels := channels
    , ch17 := ch17, ch18 := ch18
    , frameLost := frameLost, failsafe := failsafe }

/-- Build then parse: round-trip. -/
def roundTrip (f : Frame) : Option Frame :=
  parseFrame (buildFrame f)

end Sparkle.IP.Bus.SBUS
