/-
  IP.Bus.MIL1553 — MIL-STD-1553B (avionics + spacecraft
  command/data bus) word encoder/decoder.

  Physical layer: 1 Mbps, dual redundant differential bus,
  Manchester II encoded.  This module deals with the
  logical word level (20-bit per word).

  Word layout (20 bits):
      [3-bit SYNC]  [16-bit CONTENT]  [1-bit PARITY (odd)]

  SYNC discriminates word type:
      Command/Status sync: bus high for 1.5 bit times, then
                            low for 1.5 bit times.  Modeled
                            here as bits [1,1,0] over 3
                            Manchester slots.
      Data sync:           bus low for 1.5 bit times then
                            high.  Modeled as bits [0,0,1].

  Word types:
    Command (BC → RT):
        15..11  RT address (5 bits)
        10      T/R bit (1 = receive from RT, 0 = transmit)
        9..5    sub-address / mode (5 bits)
        4..0    word count (5 bits) OR mode code

    Status (RT → BC):
        15..11  RT address (5 bits)
        10      message error
        9       instrumentation (=0 in 1553B)
        8       service request
        7..5    reserved (=0)
        4       broadcast command received
        3       busy
        2       subsystem flag
        1       dynamic bus control acceptance
        0       terminal flag

    Data:
        15..0   payload data
-/

import Sparkle

namespace Sparkle.IP.Bus.MIL1553

/-! ### Sync patterns. -/

/-- The 3 bits that represent a command/status sync slot.
    In Manchester encoding, the actual bus pattern is
    1.5 high + 1.5 low bit times. -/
def syncCommand : List Bool := [true, true, false]

/-- The 3 bits that represent a data sync slot. -/
def syncData    : List Bool := [false, false, true]

/-- Whether the sync pattern is the command/status form. -/
def isCommandSync : List Bool → Bool
  | [true, true, false]   => true
  | [false, false, true]  => false
  | _                     => false

/-! ### Odd parity. -/

/-- Compute odd parity over a 16-bit value: returns the
    parity bit such that total number of 1-bits in
    (content || parity) is odd. -/
def oddParity (content : Nat) : Bool := Id.run do
  let mut ones : Nat := 0
  for i in [:16] do
    if ((content >>> i) &&& 1) = 1 then
      ones := ones + 1
  return ones % 2 = 0   -- ones==even ⇒ parity=1 makes it odd

/-! ### Word types. -/

inductive WordKind
  | command
  | status
  | data
  deriving Repr, BEq, DecidableEq, Inhabited

structure Word where
  kind    : WordKind
  /-- 16-bit content. -/
  content : Nat
  deriving Repr, Inhabited

/-! ### Bit-level encode/decode. -/

/-- Encode `n` bits of `value`, MSB-first, into a list. -/
private def msbBits (value n : Nat) : List Bool := Id.run do
  let mut out : List Bool := []
  for i in [:n] do
    let shift := n - 1 - i
    out := out ++ [decide (((value >>> shift) &&& 1) = 1)]
  return out

/-- Encode one 1553 word as a 20-bit list (3 sync + 16
    content MSB-first + 1 parity). -/
def encodeWord (w : Word) : List Bool :=
  let sync := match w.kind with
    | .command | .status => syncCommand
    | .data              => syncData
  let body := msbBits (w.content &&& 0xFFFF) 16
  sync ++ body ++ [oddParity (w.content &&& 0xFFFF)]

/-- Decode one 1553 word from a 20-bit list.  Returns the
    parsed word + a parity-OK flag.  Sync bits choose
    `command` vs `data`; status words are syntactically
    indistinguishable from commands (same sync), so callers
    that need the distinction must use protocol context. -/
def decodeWord (bits : List Bool) : Option (Word × Bool) := Id.run do
  if bits.length ≠ 20 then return none
  let sync := bits.take 3
  let body := bits.drop 3 |>.take 16
  let parityBit := (bits.drop 19).head!
  let kind :=
    if isCommandSync sync then WordKind.command
    else if sync = syncData then WordKind.data
    else WordKind.command  -- fallback; will fail parity below if wrong
  let mut content : Nat := 0
  for b in body do
    content := (content <<< 1) ||| (if b then 1 else 0)
  let parityOk := parityBit = oddParity content
  return some ({ kind := kind, content := content }, parityOk)

/-! ### Convenience constructors for the standard word
    shapes (Command, Status, Data). -/

/-- Build a Command word.
      rtAddr     : 5-bit Remote Terminal address (1..30; 31 = broadcast)
      transmit   : true if BC is asking RT to TX
      subAddr    : 5-bit sub-address / mode-code selector
      wordCount  : 5-bit word count (1..32; 0 = 32) OR mode code
-/
def commandWord (rtAddr : Nat) (transmit : Bool) (subAddr wordCount : Nat) : Word :=
  let tr := if transmit then 1 else 0
  let c :=
    ((rtAddr &&& 0x1F) <<< 11)
    ||| (tr <<< 10)
    ||| ((subAddr &&& 0x1F) <<< 5)
    ||| (wordCount &&& 0x1F)
  { kind := .command, content := c }

/-- Build a Status word.  `flags` packs the lower 11 bits
    per the spec; common settings are 0 (= "all good"). -/
def statusWord (rtAddr : Nat) (flags : Nat := 0) : Word :=
  let c := ((rtAddr &&& 0x1F) <<< 11) ||| (flags &&& 0x7FF)
  { kind := .status, content := c }

/-- Build a Data word. -/
def dataWord (value : Nat) : Word :=
  { kind := .data, content := value &&& 0xFFFF }

/-! ### High-level message framing.

    A 1553 *message* is a sequence of words.  Common shapes:
      BC → RT receive transfer:
        [Command (T/R=0, N words)] [Data×N]  → [Status]
      RT → BC transmit transfer:
        [Command (T/R=1, N words)] → [Status] [Data×N]
    We model only the BC's bus-side TX (a Command followed
    by N Data words for the BC→RT case). -/

/-- Build the wire-bit list for a BC→RT receive transfer:
    one Command word with T/R=0 + N data words.  `data`
    must have `≤ 32` words; word count of 0 encodes 32. -/
def buildBcToRtTransfer (rtAddr subAddr : Nat) (data : Array Nat) : List Bool := Id.run do
  let count := if data.size = 32 then 0 else data.size &&& 0x1F
  let cmd := commandWord rtAddr false subAddr count
  let mut bits := encodeWord cmd
  for v in data do
    bits := bits ++ encodeWord (dataWord v)
  return bits

/-- Build the wire-bit list for a "BC → RT receive" sequence
    PLUS the RT's status word.  Conceptually the BC sees this
    full sequence on the bus.  `rtStatusFlags` lets the
    caller stub a status — production would derive it from
    the RT side. -/
def buildBcToRtMessage
    (rtAddr subAddr : Nat) (data : Array Nat) (rtStatusFlags : Nat := 0) :
    List Bool :=
  buildBcToRtTransfer rtAddr subAddr data ++ encodeWord (statusWord rtAddr rtStatusFlags)

/-! ### Parser. -/

/-- Split a bit list into chunks of 20.  Last chunk may be
    short — dropped in that case. -/
def chunks20 (bits : List Bool) : List (List Bool) := Id.run do
  let mut out : List (List Bool) := []
  let mut remaining := bits
  while remaining.length ≥ 20 do
    out := out ++ [remaining.take 20]
    remaining := remaining.drop 20
  return out

/-- Parse a full bit stream as a sequence of 1553 words. -/
def parseMessage (bits : List Bool) : List (Word × Bool) := Id.run do
  let mut out : List (Word × Bool) := []
  for chunk in chunks20 bits do
    match decodeWord chunk with
    | some wp => out := out ++ [wp]
    | none => pure ()
  return out

end Sparkle.IP.Bus.MIL1553
