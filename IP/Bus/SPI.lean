/-
  IP.Bus.SPI — SPI transaction encoder/decoder.

  SPI is a 4-wire synchronous bus:
    * SCLK  — master-driven clock
    * MOSI  — master-out, slave-in (data the master sends)
    * MISO  — master-in,  slave-out (data the slave returns)
    * CS    — chip select (active-low by convention)

  Full-duplex: every clock pulse shifts one MOSI bit out
  AND one MISO bit in.  An N-byte transfer therefore
  consumes 8*N clock pulses and produces 8*N MISO bits.

  Four "modes" combine clock polarity and phase:
      MODE  CPOL  CPHA  notes
       0     0     0    idle-low, sample leading edge (rise)
       1     0     1    idle-low, sample trailing edge (fall)
       2     1     0    idle-high, sample leading edge (fall)
       3     1     1    idle-high, sample trailing edge (rise)

  Byte order: MSB-first by convention.  Word size: typically
  8 bits; we hard-code 8 for now (most devices).

  Since SPI has no protocol "framing" (just clock + data),
  the model is straightforward: caller provides `mosi` and
  `misoFromSlave` byte streams, we produce the bit-level
  pattern + chip-select envelope.
-/

import Sparkle

namespace Sparkle.IP.Bus.SPI

/-- SPI mode bundle. -/
structure Mode where
  cpol : Bool
  cpha : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

def Mode.mode0 : Mode := { cpol := false, cpha := false }
def Mode.mode1 : Mode := { cpol := false, cpha := true }
def Mode.mode2 : Mode := { cpol := true,  cpha := false }
def Mode.mode3 : Mode := { cpol := true,  cpha := true }

/-- Convert a (cpol, cpha) pair to the 0..3 numeric mode. -/
def Mode.toNumeric (m : Mode) : Nat :=
  (if m.cpol then 2 else 0) + (if m.cpha then 1 else 0)

/-! ### Bit-level transfer. -/

/-- Per-cycle observable lines for one half-cycle of SCLK. -/
structure Sample where
  sclk : Bool
  mosi : Bool
  miso : Bool
  cs   : Bool   -- low = active
  deriving Repr, BEq, Inhabited

/-- A complete SPI transaction.  `mosi` is the byte stream
    the master sends.  `miso` is the byte stream the slave
    returns (same length). -/
structure Transaction where
  mode : Mode
  mosi : Array UInt8
  miso : Array UInt8       -- same length as mosi
  deriving Repr, Inhabited

/-- Emit the 8 MOSI bits for one byte, MSB-first. -/
def byteToBitsMsb (b : UInt8) : List Bool := Id.run do
  let mut out : List Bool := []
  let n := b.toNat
  for i in [:8] do
    out := out ++ [decide (((n >>> (7 - i)) &&& 1) = 1)]
  return out

/-- Re-pack 8 bits (MSB-first) into a byte. -/
def bitsToByteMsb (bs : List Bool) : UInt8 := Id.run do
  let mut acc : Nat := 0
  for b in bs.take 8 do
    acc := (acc <<< 1) ||| (if b then 1 else 0)
  return UInt8.ofNat acc

/-! ### Sample-level expansion.

    For one bit of data we emit TWO samples (one per SCLK
    edge): the "drive" half and the "sample" half.  Which
    edge samples depends on CPHA:

      CPHA=0: master shifts MOSI before the leading edge
              of SCLK and samples MISO on the leading edge.
              We model as:
                * first sample:  sclk=idle, mosi=NEW data
                * second sample: sclk=active, mosi=same  (slave samples here)

      CPHA=1: master shifts MOSI on the leading edge and
              samples on the trailing edge.
                * first sample:  sclk=active, mosi=NEW data
                * second sample: sclk=idle, mosi=same    (slave samples here)
-/

/-- Expand a transaction into a stream of bus samples.
    CS goes low at the start and high after the last byte. -/
def buildSamples (t : Transaction) : List Sample := Id.run do
  let mut out : List Sample := []
  let idle := t.mode.cpol
  let active := !idle
  -- Initial idle period (CS high, SCLK idle, MOSI undefined).
  out := out ++ [{ sclk := idle, mosi := false, miso := false, cs := true }]
  -- Drop CS.
  out := out ++ [{ sclk := idle, mosi := false, miso := false, cs := false }]
  let n := t.mosi.size
  for i in [:n] do
    let mosiByte := if h : i < t.mosi.size then t.mosi[i]! else 0
    let misoByte := if h : i < t.miso.size then t.miso[i]! else 0
    let mosiBits := byteToBitsMsb mosiByte
    let misoBits := byteToBitsMsb misoByte
    for k in [:8] do
      let mb := mosiBits.toArray[k]!
      let sb := misoBits.toArray[k]!
      if t.mode.cpha then
        -- CPHA=1: edge1=active (master shifts), edge2=idle (slave samples)
        out := out ++
          [ { sclk := active, mosi := mb, miso := sb, cs := false }
          , { sclk := idle,   mosi := mb, miso := sb, cs := false } ]
      else
        -- CPHA=0: edge1=idle (master shifts), edge2=active (slave samples)
        out := out ++
          [ { sclk := idle,   mosi := mb, miso := sb, cs := false }
          , { sclk := active, mosi := mb, miso := sb, cs := false } ]
  -- Final idle then CS high.
  out := out ++ [{ sclk := idle, mosi := false, miso := false, cs := false }]
  out := out ++ [{ sclk := idle, mosi := false, miso := false, cs := true }]
  return out

/-! ### Parse the sample stream back.

    We look for CS-active sections, pick the samples at the
    correct edge per mode, and assemble bytes.  Designed for
    round-trip; not robust to noisy traces. -/

/-- Parse the bit (mosi, miso) pair sampled on the
    appropriate edge per `mode`, from a list of bus samples.
    Returns the byte sequence in (mosi, miso) form. -/
def parseSamples (samples : List Sample) (mode : Mode) :
    Array UInt8 × Array UInt8 := Id.run do
  -- Strip leading/trailing idle (cs high) samples.
  let active := samples.filter (fun s => !s.cs)
  -- For CPHA=0 the slave samples on the active edge (the
  -- second sample of each pair).  For CPHA=1 the slave
  -- samples on the idle edge (the second sample of each
  -- pair, when our generator put `idle` second).
  -- In both cases we want the second sample of each pair.
  -- The generator emits exactly 2 samples per data bit
  -- within the CS-low region, so we take every second one.
  let mut mosiBits : List Bool := []
  let mut misoBits : List Bool := []
  let activeArr := active.toArray
  let mut i := 1  -- start at second sample of first pair
  while i < activeArr.size do
    let s := activeArr[i]!
    mosiBits := mosiBits ++ [s.mosi]
    misoBits := misoBits ++ [s.miso]
    i := i + 2
  -- Drop any trailing partial byte (settling samples).
  let nBytes := mosiBits.length / 8
  let mut mosiOut : Array UInt8 := Array.replicate nBytes 0
  let mut misoOut : Array UInt8 := Array.replicate nBytes 0
  for j in [:nBytes] do
    let mbs := mosiBits.drop (j * 8) |>.take 8
    let sbs := misoBits.drop (j * 8) |>.take 8
    mosiOut := mosiOut.set! j (bitsToByteMsb mbs)
    misoOut := misoOut.set! j (bitsToByteMsb sbs)
  let _ := mode  -- mode currently affects only the encoded edge ordering
  return (mosiOut, misoOut)

/-- Round-trip: build samples then parse back, in the same mode. -/
def roundTrip (t : Transaction) : Array UInt8 × Array UInt8 :=
  parseSamples (buildSamples t) t.mode

end Sparkle.IP.Bus.SPI
