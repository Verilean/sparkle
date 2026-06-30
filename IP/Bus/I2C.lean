/-
  IP.Bus.I2C — I2C transaction encoder/decoder.

  I2C is a two-wire synchronous serial bus (SCL clock,
  SDA data, both open-drain).  Special edges:
    * START:  SDA falls while SCL high
    * STOP:   SDA rises while SCL high
    * Rep. START: another START without an intervening STOP

  Standard transaction:
      START | (addr<<1 | R/W) | ACK | data0 | ACK | … | dataN | A/NACK | STOP

  ACK / NACK is one bit on the SDA line driven by the
  receiver during a clock pulse owned by the transmitter.
  We model the on-wire form as a list of events rather than
  a raw bit stream — this keeps the START/STOP markers
  visible to the parser.

  10-bit addressing (NXP UM10204 §3.1.13):
      first  byte = 11110AA0 R   (AA = top 2 bits of addr, R = R/W)
      second byte = low 8 bits of addr
  Only the first byte has the special 11110 prefix; once
  recognized, the slave treats the next byte as the
  remaining address bits.
-/

import Sparkle

namespace Sparkle.IP.Bus.I2C

/-- One observable event on the I2C bus. -/
inductive Event where
  | start
  | restart    -- "repeated START" (no preceding STOP)
  | stop
  /-- A data byte transferred during 8 clock pulses.  ACK
      bit indicates whether the receiver pulled SDA low
      (`true` = ACK, `false` = NACK). -/
  | byte (b : UInt8) (ack : Bool)
  deriving Repr, BEq, Inhabited

/-- High-level transaction descriptor. -/
inductive RW where
  | write
  | read
  deriving Repr, BEq, DecidableEq, Inhabited

structure Transaction where
  /-- 7-bit address (0..127).  For 10-bit addressing put the
      full 10 bits here and set `tenBit := true`. -/
  address  : Nat
  rw       : RW
  /-- For writes: bytes to transmit.  For reads: bytes the
      master would expect (used to time the ACK bits — the
      caller normally fills with arbitrary zeros). -/
  data     : Array UInt8
  /-- Use 10-bit addressing? -/
  tenBit   : Bool := false
  deriving Repr, Inhabited

/-! ### Build the event stream. -/

/-- Encode a 7-bit address and R/W bit into the first
    transmitted byte. -/
def addrByte7 (addr : Nat) (rw : RW) : UInt8 :=
  let rwBit := match rw with | .read => 1 | .write => 0
  UInt8.ofNat (((addr &&& 0x7F) <<< 1) ||| rwBit)

/-- Encode the first byte of a 10-bit address transaction
    (11110 AA RW). -/
def addrByte10First (addr : Nat) (rw : RW) : UInt8 :=
  let rwBit := match rw with | .read => 1 | .write => 0
  -- 11110 AA RW where AA = bits [9:8] of addr.
  UInt8.ofNat (0xF0 ||| (((addr >>> 8) &&& 0x3) <<< 1) ||| rwBit)

/-- Build the event stream for one transaction (a single
    START..STOP block).  Read transactions assume the master
    NACKs the final byte (standard read termination); other
    bytes get ACK. -/
def buildTransaction (t : Transaction) : List Event := Id.run do
  let mut out : List Event := [.start]
  -- Address phase.
  if t.tenBit then
    out := out ++ [.byte (addrByte10First t.address t.rw) true]
    out := out ++ [.byte (UInt8.ofNat (t.address &&& 0xFF)) true]
  else
    out := out ++ [.byte (addrByte7 t.address t.rw) true]
  -- Data phase.
  let n := t.data.size
  for i in [:n] do
    let isLast := i + 1 = n
    -- For reads: NACK the LAST byte (standard).  For writes:
    -- the slave acks every data byte — model that as ACK on all.
    let ack := match t.rw with
      | .write => true
      | .read  => !isLast
    out := out ++ [.byte t.data[i]! ack]
  out := out ++ [.stop]
  return out

/-! ### Parse the event stream back into a Transaction. -/

structure ParsedTxn where
  address  : Nat
  rw       : RW
  tenBit   : Bool
  data     : Array UInt8
  /-- True iff the address byte received ACK from the slave. -/
  addrAcked : Bool
  deriving Repr

/-- Parse a single START..STOP block from an event stream.
    Returns the parsed transaction + any trailing events
    after STOP.  `none` on framing errors. -/
def parseTransaction : List Event → Option (ParsedTxn × List Event)
  | [] => none
  | e :: rest =>
    match e with
    | .start | .restart =>
      match rest with
      | [] => none
      | (.byte first ack0) :: tail =>
        -- Detect 10-bit address (high 5 bits = 11110).
        let firstN := first.toNat
        let tenBit := (firstN &&& 0xF8) = 0xF0
        let rw : RW :=
          if (firstN &&& 1) = 1 then .read else .write
        if tenBit then
          match tail with
          | (.byte second _) :: rest' =>
            let addr := (((firstN >>> 1) &&& 0x3) <<< 8) ||| second.toNat
            collectData rest' [] addr rw true ack0
          | _ => none
        else
          let addr := (firstN >>> 1) &&& 0x7F
          collectData tail [] addr rw false ack0
      | _ => none
    | _ => none
where
  collectData : List Event → List UInt8 → Nat → RW → Bool → Bool →
                Option (ParsedTxn × List Event)
    | [], _, _, _, _, _ => none
    | (.stop :: rest), acc, addr, rw, tenBit, addrAcked =>
      some ({ address := addr, rw := rw, tenBit := tenBit
            , data := acc.reverse.toArray
            , addrAcked := addrAcked }, rest)
    | ((.byte b _) :: rest), acc, addr, rw, tenBit, addrAcked =>
      collectData rest (b :: acc) addr rw tenBit addrAcked
    | (.restart :: rest), acc, addr, rw, tenBit, addrAcked =>
      -- Repeated START: end of this txn, the caller can
      -- re-parse from `restart` onward.
      some ({ address := addr, rw := rw, tenBit := tenBit
            , data := acc.reverse.toArray
            , addrAcked := addrAcked }, .restart :: rest)
    | (_ :: _), _, _, _, _, _ => none

/-- Round-trip: build then parse a transaction. -/
def roundTrip (t : Transaction) : Option ParsedTxn :=
  (parseTransaction (buildTransaction t)).map Prod.fst

end Sparkle.IP.Bus.I2C
