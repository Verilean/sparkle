/-
  IP.Bus.LIN — LIN 2.2A bus encoder/decoder.

  LIN (Local Interconnect Network) is a single-wire UART-based
  serial bus widely used in automotive body electronics
  (window switches, mirrors, seat sensors, etc.).  Master /
  slave architecture; up to 16 slaves per master.

  Frame structure (master header + slave/master response):

      [BREAK ≥13 bits dominant + break-delimiter (recessive)]
      [SYNC 0x55  ─── UART-framed (1 start + 8 data LSB-first + 1 stop)]
      [PID  6-bit ID + 2 parity ─── UART-framed]
      [DATA 1..8 bytes  ─── each UART-framed]
      [CHECKSUM 1 byte  ─── UART-framed]

  PID protection bits (LIN 2.2A §2.3.1.3):
      P0 = ID0 XOR ID1 XOR ID2 XOR ID4
      P1 = NOT (ID1 XOR ID3 XOR ID4 XOR ID5)

  Checksum:
      classic  (LIN 1.3): inv(sum(data))
      enhanced (LIN 2.x): inv(sum(PID, data))
    where `sum` adds with carry mod 0xFF (each carry-out is
    added back in), and `inv` is bitwise NOT.
-/

import Sparkle

namespace Sparkle.IP.Bus.LIN

inductive ChecksumKind where
  | classic       -- LIN 1.3: sum of data bytes only
  | enhanced      -- LIN 2.x: sum of PID + data bytes
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One LIN frame. -/
structure Frame where
  /-- 6-bit message ID (0..63).  ID 0x3C/0x3D are reserved
      for diagnostic master/slave frames in LIN 2.x. -/
  id        : Nat
  /-- 1..8 data bytes. -/
  data      : Array UInt8
  /-- Which checksum algorithm to use.  In LIN 2.x the
      classic checksum is mandated for diagnostic IDs
      0x3C/0x3D, enhanced for the rest. -/
  checksum  : ChecksumKind := .enhanced
  deriving Repr, Inhabited

/-! ### Protected ID. -/

/-- Compute the PID parity nibble for a 6-bit ID.  Returns
    `(P1 P0)` as a 2-bit value. -/
def pidParity (id : Nat) : Nat :=
  let bit (n : Nat) : Nat := (id >>> n) &&& 1
  let p0 := bit 0 ^^^ bit 1 ^^^ bit 2 ^^^ bit 4
  let p1 := 1 ^^^ (bit 1 ^^^ bit 3 ^^^ bit 4 ^^^ bit 5)
  (p1 <<< 1) ||| p0

/-- Pack a 6-bit ID + 2-bit parity into the 8-bit PID byte. -/
def encodePid (id : Nat) : UInt8 :=
  UInt8.ofNat ((pidParity id <<< 6) ||| (id &&& 0x3F))

/-- Recover the 6-bit ID from a PID byte, or `none` if
    parity check fails. -/
def decodePid (pid : UInt8) : Option Nat := Id.run do
  let n := pid.toNat
  let id := n &&& 0x3F
  let observed := (n >>> 6) &&& 0x3
  let expected := pidParity id
  if observed = expected then some id else none

/-! ### Checksum. -/

/-- One-step "sum with carry into next" arithmetic used by
    LIN's checksum.  After each addition, if there's a
    carry out of byte width, fold it back in. -/
private def addCarry (a b : UInt8) : UInt8 :=
  let s := a.toNat + b.toNat
  if s ≥ 0x100 then UInt8.ofNat ((s + 1) &&& 0xFF)
  else UInt8.ofNat s

/-- Compute the LIN frame checksum.  `inputs` is the list of
    bytes to sum (PID first if enhanced, else just data). -/
def computeChecksum (inputs : Array UInt8) : UInt8 := Id.run do
  let mut acc : UInt8 := 0
  for b in inputs do
    acc := addCarry acc b
  -- One's-complement inversion.
  return UInt8.ofNat ((255 - acc.toNat) &&& 0xFF)

/-- Compute the checksum for a frame, taking PID into account
    only for enhanced mode. -/
def frameChecksum (f : Frame) : UInt8 :=
  match f.checksum with
  | .classic =>
    computeChecksum f.data
  | .enhanced =>
    computeChecksum (#[encodePid f.id] ++ f.data)

/-! ### UART-framed bits per byte.

    LIN uses standard 8-N-1 UART: each byte is preceded by 1
    dominant start bit and followed by 1 recessive stop bit.
    Data bits are LSB-first. -/

/-- Emit the on-wire bits for one UART byte: start (0) +
    8 data bits LSB-first + stop (1). -/
def uartByte (b : UInt8) : List Bool := Id.run do
  let mut out : List Bool := [false]  -- start
  let n := b.toNat
  for i in [:8] do
    out := out ++ [decide (((n >>> i) &&& 1) = 1)]
  out := out ++ [true]  -- stop
  return out

/-! ### Frame builder + parser. -/

/-- Number of dominant break bits to emit (LIN spec ≥13). -/
def breakBits : Nat := 13

/-- Build the complete on-wire bitstream for a LIN frame:
    BREAK + break-delimiter + SYNC + PID + data + checksum. -/
def buildFrame (f : Frame) : List Bool := Id.run do
  let mut bits : List Bool := []
  -- Break: 13 dominant bits.
  bits := bits ++ List.replicate breakBits false
  -- Break delimiter: 1 recessive bit.
  bits := bits ++ [true]
  -- Sync byte 0x55.
  bits := bits ++ uartByte 0x55
  -- PID.
  bits := bits ++ uartByte (encodePid f.id)
  -- Data.
  for b in f.data do
    bits := bits ++ uartByte b
  -- Checksum.
  bits := bits ++ uartByte (frameChecksum f)
  return bits

/-- Strip the start bit, 8 data bits (LSB-first), and stop
    bit out of a 10-bit slice.  Returns `(byte, stopOk)`. -/
private def parseUartByte (bits : Array Bool) (off : Nat) : Option UInt8 := Id.run do
  if off + 10 > bits.size then return none
  -- Start bit must be dominant (false).
  if bits[off]! then return none
  let mut acc : Nat := 0
  for i in [:8] do
    if bits[off + 1 + i]! then
      acc := acc ||| (1 <<< i)
  -- Stop bit must be recessive (true).
  if !bits[off + 9]! then return none
  return some (UInt8.ofNat acc)

/-- Find the start of the first ≥13-dominant-bit break in
    the bit array, or `none` if absent. -/
private def findBreakStart (arr : Array Bool) : Option Nat := Id.run do
  let mut p : Nat := 0
  let mut run := 0
  while p < arr.size do
    if !arr[p]! then
      run := run + 1
      if run ≥ breakBits then
        return some ((p + 1) - run)
    else
      run := 0
    p := p + 1
  return none

/-- Advance past dominant break bits and the recessive
    break-delimiter, returning the offset of the next byte's
    start bit. -/
private def skipBreak (arr : Array Bool) (start : Nat) : Nat := Id.run do
  let mut q := start
  while q < arr.size ∧ !arr[q]! do
    q := q + 1
  return q + 1

/-- Pull `dataLen` data bytes from the bit array starting at
    `start`.  Returns `(data array, q offset after the last byte)`
    or `none` on UART failure. -/
private def readDataBytes (arr : Array Bool) (start dataLen : Nat) :
    Option (Array UInt8 × Nat) := Id.run do
  let mut data : Array UInt8 := Array.replicate dataLen 0
  let mut q := start
  for i in [:dataLen] do
    match parseUartByte arr q with
    | none => return none
    | some b =>
      data := data.set! i b
      q := q + 10
  return some (data, q)

def parseFrame (bits : List Bool) (dataLen : Nat)
    (kind : ChecksumKind := .enhanced) : Option (Frame × Bool) := do
  let arr := bits.toArray
  let bs ← findBreakStart arr
  let qSync := skipBreak arr (bs + breakBits)
  let sync ← parseUartByte arr qSync
  guard (sync = 0x55)
  let pid ← parseUartByte arr (qSync + 10)
  let id ← decodePid pid
  let (data, qChk) ← readDataBytes arr (qSync + 20) dataLen
  let chk ← parseUartByte arr qChk
  let frame : Frame := { id := id, data := data, checksum := kind }
  let expected := frameChecksum frame
  pure (frame, chk = expected)

/-- Build then parse: returns the round-tripped frame. -/
def roundTrip (f : Frame) : Option (Frame × Bool) :=
  parseFrame (buildFrame f) f.data.size f.checksum

end Sparkle.IP.Bus.LIN
