/-
  IP.Bus.CAN — CAN 2.0B MAC encoder/decoder (pure-data).

  Targets ISO 11898-1 (CAN 2.0B): both 11-bit standard (CBFF)
  and 29-bit extended (CEFF) frames.  Builds the on-wire
  bitstream INCLUDING bit-stuffing and CRC15.  The decoder
  reverses it.

  Frame layout (CBFF):
    SOF(1) | ID(11) | RTR(1) | IDE(1=0) | r0(1) | DLC(4)
      | data(8*DLC) | CRC15(15) | CRC_DEL(1=1) | ACK(1=1)
      | ACK_DEL(1=1) | EOF(7=1) | IFS(3=1)

  Frame layout (CEFF):
    SOF(1) | ID_A(11) | SRR(1=1) | IDE(1=1) | ID_B(18)
      | RTR(1) | r1(1=0) | r0(1=0) | DLC(4) | data
      | CRC15 | CRC_DEL | ACK | ACK_DEL | EOF | IFS

  Bit stuffing: in the dynamic-bit region (SOF .. end of CRC,
  inclusive), after 5 consecutive same-value bits insert one
  opposite-value bit.  CRC_DEL, ACK, ACK_DEL, EOF, IFS are
  in the fixed-bit region (no stuffing).

  CRC15 polynomial: x^15 + x^14 + x^10 + x^8 + x^7 + x^4
                  + x^3 + 1  (= 0x4599)
  Computed over the dynamic-bit region.

  Bit transmission order: each multi-bit field is sent MSB
  first.  CAN logic level: dominant = 0, recessive = 1.

  This file ships:
    * `buildFrame`  — frame fields → on-wire bit list (after
                      bit stuffing).
    * `parseFrame`  — on-wire bit list → (frame fields,
                      crc-ok-flag) or `none` on stuffing
                      violations / under-run.

  HW (`circuit do`) version lands in T.7.HW.
-/

import Sparkle

namespace Sparkle.IP.Bus.CAN

/-- CAN frame variant. -/
inductive FrameKind where
  | standard       -- 11-bit ID, CBFF (classic CAN 2.0A)
  | extended       -- 29-bit ID, CEFF (classic CAN 2.0B)
  | standardFD     -- 11-bit ID, CAN-FD (FDF=1, no RTR)
  | extendedFD     -- 29-bit ID, CAN-FD (FDF=1, no RTR)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- True for CAN-FD variants. -/
@[inline] def FrameKind.isFD : FrameKind → Bool
  | .standardFD | .extendedFD => true
  | _ => false

/-- True for extended-ID variants (CEFF, FD-CEFF). -/
@[inline] def FrameKind.isExtended : FrameKind → Bool
  | .extended | .extendedFD => true
  | _ => false

/-- A parsed CAN frame.  Covers both classic CAN 2.0A/B and
    ISO CAN-FD (FDF=1). -/
structure Frame where
  kind    : FrameKind
  /-- Identifier.  11 bits used for `.standard*`, 29 bits for
      `.extended*`. -/
  id      : Nat
  /-- Remote Transmission Request (classic CAN only; always
      false for CAN-FD where the bit is reused as RRS). -/
  rtr     : Bool
  /-- DLC: 0..8 maps to byte count for classic CAN; for
      CAN-FD the mapping extends to 12/16/20/24/32/48/64. -/
  dlc     : Nat
  /-- Payload bytes.  Length must equal `payloadSize dlc`
      (for the corresponding frame kind). -/
  data    : Array UInt8
  /-- Bit-Rate Switch flag (CAN-FD only).  When true, the
      data + CRC fields are transmitted at the higher data
      bitrate (typ. 2-5 Mbps).  Ignored for classic CAN. -/
  brs     : Bool := false
  /-- Error State Indicator (CAN-FD only).  Driven by the
      transmitter to signal error-passive state. -/
  esi     : Bool := false
  deriving Repr, Inhabited

/-- Map a CAN-FD DLC (0..15) to its byte payload size.
    Classic CAN caps at 8 (DLC 9..15 are valid only in FD). -/
def payloadSizeFromDlc (kind : FrameKind) (dlc : Nat) : Nat :=
  if kind.isFD then
    match dlc with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => dlc
    | 9 => 12
    | 10 => 16
    | 11 => 20
    | 12 => 24
    | 13 => 32
    | 14 => 48
    | _  => 64       -- DLC 15
  else
    min dlc 8

/-! ### CRC15 (Bosch CAN, poly 0x4599). -/

/-- Update one bit through the CRC15 LFSR. -/
@[inline] def crc15Step (crc : Nat) (bit : Bool) : Nat :=
  let crcBit15 := (crc >>> 14) &&& 1
  let inBit := if bit then 1 else 0
  let xorBit := crcBit15 ^^^ inBit
  let shifted := (crc <<< 1) &&& 0x7FFF
  if xorBit = 1 then shifted ^^^ 0x4599 else shifted

/-- Compute CRC15 over a list of bits (MSB first). -/
def crc15 (bits : List Bool) : Nat :=
  bits.foldl crc15Step 0

/-! ### CRC-17 (ISO CAN-FD for ≤ 16-byte payloads).

    Polynomial: x^17 + x^16 + x^14 + x^13 + x^11 + x^6 + x^4
              + x^3 + x + 1
    Full constant including the leading bit: 0x3685B.
    LFSR constant (without the leading 1, since that's
    implicit in the shift-and-test logic): 0x1685B.
    Initial value: 1 << 16 (= 0x10000) per ISO 11898-1:2015. -/

@[inline] def crc17Step (crc : Nat) (bit : Bool) : Nat :=
  let crcBit17 := (crc >>> 16) &&& 1
  let inBit := if bit then 1 else 0
  let xorBit := crcBit17 ^^^ inBit
  let shifted := (crc <<< 1) &&& 0x1FFFF
  if xorBit = 1 then shifted ^^^ 0x1685B else shifted

def crc17 (bits : List Bool) : Nat :=
  bits.foldl crc17Step (1 <<< 16)

/-! ### CRC-21 (ISO CAN-FD for > 16-byte payloads).

    Polynomial: x^21 + x^20 + x^13 + x^11 + x^7 + x^4 + x^3 + 1
    Full constant: 0x302899; LFSR constant (without leading
    bit 21): 0x102899.
    Initial value: 1 << 20 (= 0x100000). -/

@[inline] def crc21Step (crc : Nat) (bit : Bool) : Nat :=
  let crcBit21 := (crc >>> 20) &&& 1
  let inBit := if bit then 1 else 0
  let xorBit := crcBit21 ^^^ inBit
  let shifted := (crc <<< 1) &&& 0x1FFFFF
  if xorBit = 1 then shifted ^^^ 0x102899 else shifted

def crc21 (bits : List Bool) : Nat :=
  bits.foldl crc21Step (1 <<< 20)

/-! ### Bit-level field encoders. -/

/-- Emit `n` bits of `value`, MSB first.  Bits beyond the
    natural width are taken as 0. -/
def natToBitsMsb (value n : Nat) : List Bool := Id.run do
  let mut out : List Bool := []
  for i in [:n] do
    let shift := n - 1 - i
    let b : Bool := decide (((value >>> shift) &&& 1) = 1)
    out := out ++ [b]
  return out

/-- One byte → 8 bits MSB first. -/
def byteToBits (b : UInt8) : List Bool :=
  natToBitsMsb b.toNat 8

/-! ### Bit-stuffing. -/

/-- Insert stuffing bits: after every 5 consecutive
    same-value bits in the input, emit one opposite bit.
    Used for the dynamic-bit region of the CAN frame. -/
def applyBitStuffing (bits : List Bool) : List Bool := Id.run do
  let mut out : List Bool := []
  let mut runVal : Bool := false
  let mut runLen : Nat := 0
  for b in bits do
    out := out ++ [b]
    if b = runVal then
      runLen := runLen + 1
    else
      runVal := b
      runLen := 1
    if runLen = 5 then
      let stuff := !b
      out := out ++ [stuff]
      runVal := stuff
      runLen := 1
  return out

/-- Reverse bit-stuffing.  Removes every 6th bit that follows
    5 consecutive same-value bits.  Fails (returns `none`)
    on a stuffing violation (6 same bits in a row in the
    dynamic region). -/
def removeBitStuffing (bits : List Bool) : Option (List Bool) := Id.run do
  let mut out : List Bool := []
  let mut runVal : Bool := false
  let mut runLen : Nat := 0
  let mut skip := false
  for b in bits do
    if skip then
      -- This bit is the stuffing bit — must equal !runVal.
      if b = runVal then return none
      skip := false
      runVal := b
      runLen := 1
    else
      out := out ++ [b]
      if b = runVal then
        runLen := runLen + 1
        if runLen ≥ 6 then return none  -- 6 same → stuffing violation
        if runLen = 5 then
          skip := true
      else
        runVal := b
        runLen := 1
  return some out

/-! ### Frame builder. -/

/-- Build the dynamic-bit region of the frame BEFORE
    bit-stuffing (= SOF || arbitration || control || data || CRC).

    Layouts:
      * `.standard`   (classic):
          SOF | ID(11) | RTR | IDE=0 | r0 | DLC(4) | data | CRC15
      * `.extended`   (classic):
          SOF | IDA(11) | SRR=1 | IDE=1 | IDB(18) | RTR | r1 | r0
          | DLC(4) | data | CRC15
      * `.standardFD`:
          SOF | ID(11) | RRS=0 | IDE=0 | FDF=1 | res=0 | BRS | ESI
          | DLC(4) | data | CRC{17,21}
      * `.extendedFD`:
          SOF | IDA(11) | SRR=1 | IDE=1 | IDB(18) | RRS=0 | FDF=1
          | res=0 | BRS | ESI | DLC(4) | data | CRC{17,21}

    For FD frames the CRC width depends on payload size:
      ≤ 16 bytes → CRC-17; > 16 bytes → CRC-21. -/
def buildDynamicBits (f : Frame) : List Bool := Id.run do
  let mut bits : List Bool := []
  -- SOF dominant = 0.
  bits := bits ++ [false]
  match f.kind with
  | .standard =>
    bits := bits ++ natToBitsMsb f.id 11
    bits := bits ++ [f.rtr]
    bits := bits ++ [false]              -- IDE = 0
    bits := bits ++ [false]              -- r0
    bits := bits ++ natToBitsMsb f.dlc 4
  | .extended =>
    let idA := (f.id >>> 18) &&& ((1 <<< 11) - 1)
    let idB := f.id &&& ((1 <<< 18) - 1)
    bits := bits ++ natToBitsMsb idA 11
    bits := bits ++ [true]               -- SRR
    bits := bits ++ [true]               -- IDE = 1
    bits := bits ++ natToBitsMsb idB 18
    bits := bits ++ [f.rtr]
    bits := bits ++ [false]              -- r1
    bits := bits ++ [false]              -- r0
    bits := bits ++ natToBitsMsb f.dlc 4
  | .standardFD =>
    bits := bits ++ natToBitsMsb f.id 11
    bits := bits ++ [false]              -- RRS (was RTR; dominant in FD)
    bits := bits ++ [false]              -- IDE = 0
    bits := bits ++ [true]               -- FDF = 1
    bits := bits ++ [false]              -- res
    bits := bits ++ [f.brs]
    bits := bits ++ [f.esi]
    bits := bits ++ natToBitsMsb f.dlc 4
  | .extendedFD =>
    let idA := (f.id >>> 18) &&& ((1 <<< 11) - 1)
    let idB := f.id &&& ((1 <<< 18) - 1)
    bits := bits ++ natToBitsMsb idA 11
    bits := bits ++ [true]               -- SRR
    bits := bits ++ [true]               -- IDE = 1
    bits := bits ++ natToBitsMsb idB 18
    bits := bits ++ [false]              -- RRS
    bits := bits ++ [true]               -- FDF = 1
    bits := bits ++ [false]              -- res
    bits := bits ++ [f.brs]
    bits := bits ++ [f.esi]
    bits := bits ++ natToBitsMsb f.dlc 4
  -- Data field.  Classic: omit when RTR.  FD: always present
  -- (FD has no RTR).
  let nBytes :=
    if f.kind.isFD then payloadSizeFromDlc f.kind f.dlc
    else if f.rtr then 0
    else min f.dlc 8
  for i in [:nBytes] do
    let b := if h : i < f.data.size then f.data[i]! else 0
    bits := bits ++ byteToBits b
  -- CRC.  Classic uses CRC15.  FD uses CRC17 (≤16B) or CRC21.
  if f.kind.isFD then
    if nBytes ≤ 16 then
      let crc := crc17 bits
      bits := bits ++ natToBitsMsb crc 17
    else
      let crc := crc21 bits
      bits := bits ++ natToBitsMsb crc 21
  else
    let crc := crc15 bits
    bits := bits ++ natToBitsMsb crc 15
  return bits

/-- Build the full on-wire bitstream: dynamic region with
    bit-stuffing applied || fixed region (CRC_DEL, ACK_SLOT,
    ACK_DEL, EOF×7, IFS×3 — all recessive = 1 by convention
    when assembling the TX side; the actual ACK bit is
    driven dominant by the receiver, but here we just emit
    the bits as the TX would put them out).  -/
def buildFrame (f : Frame) : List Bool :=
  let dyn := buildDynamicBits f
  let stuffed := applyBitStuffing dyn
  -- Fixed region: 1 CRC_DEL + 1 ACK + 1 ACK_DEL + 7 EOF + 3 IFS.
  -- TX-side view: ACK is recessive (the receiver overlays a
  -- dominant ACK).  For a pure-bus capture, this is what
  -- both sides see except during the receiver's ACK pulse.
  stuffed ++ List.replicate 13 true

/-! ### Frame parser. -/

/-- Parse the dynamic-bit region (after bit-destuffing) into
    a `Frame` + the CRC field as carried on the wire.
    Returns `(frame, wireCrc, computedCrc)` so the caller can
    cross-check.  `none` on truncation or unsupported shape.

    Disambiguation: after SOF + ID(11), the next 2 bits tell
    us the frame format:
      bit12=RTR/RRS, bit13=IDE
        IDE=0: standard or standardFD (distinguished by FDF at bit14)
        IDE=1: extended or extendedFD (distinguished by FDF at bit32)
-/
def parseDynamicBits (bits : List Bool) : Option (Frame × Nat × Nat) := Id.run do
  let arr := bits.toArray
  if arr.size < 1 + 11 + 1 + 1 + 1 + 4 + 15 then return none
  let readBits (off n : Nat) : Nat := Id.run do
    let mut acc := 0
    for i in [:n] do
      let b := if h : off + i < arr.size then arr[off + i]! else false
      acc := (acc <<< 1) ||| (if b then 1 else 0)
    return acc
  let sof := arr[0]!
  if sof then return none
  let idA := readBits 1 11
  let bit12 := arr[12]!
  let bit13 := arr[13]!
  let isExtended := bit12 ∧ bit13
  if isExtended then
    -- Extended: bit14..31 = ID_B (18), bit32 onwards depends on FDF.
    if arr.size < 39 then return none
    let idB := readBits 14 18
    let id := (idA <<< 18) ||| idB
    -- Bit32 in extended: RTR (classic) or RRS=0 (FD).
    -- Bit33: r1 (classic) or FDF=1 (FD).
    -- We discriminate on bit33: if true, FD.
    let bit33 := arr[33]!
    if bit33 then
      -- extendedFD: bit32=RRS, bit33=FDF=1, bit34=res, bit35=BRS,
      -- bit36=ESI, bit37..40=DLC
      if arr.size < 41 then return none
      let brs := arr[35]!
      let esi := arr[36]!
      let dlc := readBits 37 4
      let kind : FrameKind := .extendedFD
      let nBytes := payloadSizeFromDlc kind dlc
      let dataStart := 41
      let dataBits := nBytes * 8
      let crcBits := if nBytes ≤ 16 then 17 else 21
      if arr.size < dataStart + dataBits + crcBits then return none
      let mut data : Array UInt8 := Array.replicate nBytes 0
      for i in [:nBytes] do
        data := data.set! i (UInt8.ofNat (readBits (dataStart + i * 8) 8))
      let wireCrc := readBits (dataStart + dataBits) crcBits
      let preBits := bits.take (dataStart + dataBits)
      let computed := if nBytes ≤ 16 then crc17 preBits else crc21 preBits
      return some
        ({ kind := kind, id := id, rtr := false, dlc := dlc, data := data
         , brs := brs, esi := esi },
         wireCrc, computed)
    else
      -- classic extended: bit32=RTR, bit33=r1, bit34=r0, bit35..38=DLC
      if arr.size < 39 + 15 then return none
      let rtr := bit12  -- placeholder unused; bit32 is the real RTR
      let _ := rtr
      let realRtr := arr[32]!
      let dlc := readBits 35 4
      let dataStart := 39
      let nBytes := min dlc 8
      let dataBits := if realRtr then 0 else nBytes * 8
      if arr.size < dataStart + dataBits + 15 then return none
      let mut data : Array UInt8 := Array.replicate nBytes 0
      if !realRtr then
        for i in [:nBytes] do
          data := data.set! i (UInt8.ofNat (readBits (dataStart + i * 8) 8))
      let wireCrc := readBits (dataStart + dataBits) 15
      let preBits := bits.take (dataStart + dataBits)
      let computed := crc15 preBits
      return some
        ({ kind := .extended, id := id, rtr := realRtr, dlc := dlc, data := data },
         wireCrc, computed)
  else
    -- Standard: bit12=RTR or RRS, bit13=IDE=0.
    if bit13 then return none
    -- Discriminate FD by bit14 = FDF.
    let bit14 := arr[14]!
    if bit14 then
      -- standardFD: bit12=RRS, bit13=IDE=0, bit14=FDF=1, bit15=res,
      -- bit16=BRS, bit17=ESI, bit18..21=DLC
      if arr.size < 22 then return none
      let brs := arr[16]!
      let esi := arr[17]!
      let dlc := readBits 18 4
      let kind : FrameKind := .standardFD
      let nBytes := payloadSizeFromDlc kind dlc
      let dataStart := 22
      let dataBits := nBytes * 8
      let crcBits := if nBytes ≤ 16 then 17 else 21
      if arr.size < dataStart + dataBits + crcBits then return none
      let mut data : Array UInt8 := Array.replicate nBytes 0
      for i in [:nBytes] do
        data := data.set! i (UInt8.ofNat (readBits (dataStart + i * 8) 8))
      let wireCrc := readBits (dataStart + dataBits) crcBits
      let preBits := bits.take (dataStart + dataBits)
      let computed := if nBytes ≤ 16 then crc17 preBits else crc21 preBits
      return some
        ({ kind := kind, id := idA, rtr := false, dlc := dlc, data := data
         , brs := brs, esi := esi },
         wireCrc, computed)
    else
      -- classic standard: bit12=RTR, bit13=IDE=0, bit14=r0, bit15..18=DLC
      let rtr := bit12
      let dlc := readBits 15 4
      let dataStart := 19
      let nBytes := min dlc 8
      let dataBits := if rtr then 0 else nBytes * 8
      if arr.size < dataStart + dataBits + 15 then return none
      let mut data : Array UInt8 := Array.replicate nBytes 0
      if !rtr then
        for i in [:nBytes] do
          data := data.set! i (UInt8.ofNat (readBits (dataStart + i * 8) 8))
      let wireCrc := readBits (dataStart + dataBits) 15
      let preBits := bits.take (dataStart + dataBits)
      let computed := crc15 preBits
      return some
        ({ kind := .standard, id := idA, rtr := rtr, dlc := dlc, data := data },
         wireCrc, computed)

/-- Parse a full on-wire frame.  Strips the fixed trailing
    region (CRC_DEL + ACK + ACK_DEL + EOF + IFS = 13 bits),
    de-stuffs, then parses the dynamic region.  Returns
    `(frame, crcOk)` or `none` on framing failure. -/
def parseFrame (wire : List Bool) : Option (Frame × Bool) := Id.run do
  if wire.length < 14 then return none
  -- Strip trailing 13 bits (fixed region).
  let dynStuffed := wire.take (wire.length - 13)
  match removeBitStuffing dynStuffed with
  | none => return none
  | some dyn =>
    match parseDynamicBits dyn with
    | none => return none
    | some (frame, wireCrc, computed) =>
      return some (frame, wireCrc = computed)

/-! ### Round-trip sanity. -/

/-- Build then parse: returns the round-tripped frame +
    crc-ok flag.  Used by sim tests. -/
def roundTrip (f : Frame) : Option (Frame × Bool) :=
  parseFrame (buildFrame f)

end Sparkle.IP.Bus.CAN
