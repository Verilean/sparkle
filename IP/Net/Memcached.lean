/-
  IP.Net.Memcached — text-protocol memcached subset.

  Layered as:

    1. Pure-data ASCII parser + KV oracle (this file, no Signal).
       The reference semantics: bytes-in → (Command, KvStore) →
       bytes-out.
    2. Signal-DSL KV-store HW (IP/Net/MemcachedHW.lean — separate
       file because BRAM wiring is non-trivial).
    3. Top-level memcached server wrapping (2) on the existing
       UART/SLIP/IPv4/TCP byte stream (IP/Net/UsbMemcachedServer.lean).

  ASCII protocol subset (memcached 1.6 spec, simplified):

      set <key> <flags> <exptime> <bytes>\r\n
      <value bytes>\r\n
      → STORED\r\n  on success

      add <key> <flags> <exptime> <bytes>\r\n
      <value bytes>\r\n
      → STORED\r\n  if key absent,  NOT_STORED\r\n  if present

      get <key>\r\n
      → VALUE <key> <flags> <bytes>\r\n
        <value bytes>\r\n
        END\r\n
      OR
      → END\r\n     (key absent)

      delete <key>\r\n
      → DELETED\r\n    on success
      OR
      → NOT_FOUND\r\n  if absent

  Limits:  key ≤ 16 bytes, value ≤ 64 bytes, 16 slots total.
  No flags / exptime semantics — they're parsed but ignored
  (echoed back on get).  No CAS / incr / decr / stats / flush.

  This file is sim-only / spec / oracle: nothing here goes
  through `#synthesizeVerilog`.  The HW version (next file)
  re-implements the same semantics with `Signal.memory`.
-/

namespace Sparkle.IP.Net.Memcached

/-! ### Compile-time limits. -/

/-- Maximum key length in bytes. -/
def MAX_KEY : Nat := 16

/-- Maximum value length in bytes. -/
def MAX_VALUE : Nat := 64

/-- Number of slots in the KV store. -/
def NUM_SLOTS : Nat := 16

/-! ### Command AST. -/

/-- A parsed memcached request. -/
inductive Command where
  /-- `get <key>` — lookup. -/
  | get (key : Array UInt8) : Command
  /-- `set <key> <flags> <exptime> <bytes>\r\n<value>\r\n` —
      unconditional store. -/
  | set (key : Array UInt8) (flags : Nat) (exptime : Nat) (value : Array UInt8) : Command
  /-- `add <key> <flags> <exptime> <bytes>\r\n<value>\r\n` —
      store only if absent. -/
  | add (key : Array UInt8) (flags : Nat) (exptime : Nat) (value : Array UInt8) : Command
  /-- `delete <key>` — remove. -/
  | del (key : Array UInt8) : Command
  /-- Malformed input — host gets `ERROR\r\n` (kept simple). -/
  | err : Command
  deriving Inhabited, Repr

/-! ### Pure-data ASCII parser.

    The HW path is byte-stream-driven (`circuit do` FSM), but
    for the oracle we just consume a `List UInt8` containing
    a single request and try to extract one Command.  The
    parser is line-oriented: split on `\r\n`, take the first
    line as the command, and if it's `set`/`add`, take the
    next `<bytes>` bytes from the buffer as the value.
-/

/-- Strict whitespace split on ASCII space (0x20). -/
private partial def splitOnSpace (xs : List UInt8) : List (List UInt8) :=
  let rec go (cur : List UInt8) (acc : List (List UInt8)) (xs : List UInt8) : List (List UInt8) :=
    match xs with
    | [] => (cur.reverse :: acc).reverse.filter (fun w => !w.isEmpty)
    | 0x20 :: rest => go [] (cur.reverse :: acc) rest
    | b :: rest => go (b :: cur) acc rest
  go [] [] xs

/-- Decimal parse for the byte/flags/exptime fields. -/
private partial def parseDecimal (xs : List UInt8) : Option Nat :=
  let rec go (acc : Nat) (xs : List UInt8) : Option Nat :=
    match xs with
    | [] => some acc
    | b :: rest =>
      if 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 then
        go (acc * 10 + (b.toNat - 0x30)) rest
      else
        none
  if xs.isEmpty then none else go 0 xs

/-- Find the first `\r\n` in a byte list; return (before, after-without-CRLF). -/
private partial def splitCRLF (xs : List UInt8) : Option (List UInt8 × List UInt8) :=
  let rec go (acc : List UInt8) (xs : List UInt8) : Option (List UInt8 × List UInt8) :=
    match xs with
    | [] => none
    | 0x0D :: 0x0A :: rest => some (acc.reverse, rest)
    | b :: rest => go (b :: acc) rest
  go [] xs

/-- Parse a single command + (for set/add) its value out of a
    raw byte buffer.  Returns the Command and the unconsumed
    suffix (so the caller can stream more requests after). -/
partial def parseOne (input : List UInt8) : Option (Command × List UInt8) := do
  let (line, rest1) ← splitCRLF input
  let words := splitOnSpace line
  match words with
  | (verbBytes :: rest) =>
    let verb := String.ofList (verbBytes.map (fun b => Char.ofNat b.toNat))
    match verb, rest with
    | "get", [keyBytes] =>
      if keyBytes.length ≤ MAX_KEY then
        some (.get keyBytes.toArray, rest1)
      else
        some (.err, rest1)
    | "delete", [keyBytes] =>
      if keyBytes.length ≤ MAX_KEY then
        some (.del keyBytes.toArray, rest1)
      else
        some (.err, rest1)
    | "set", [keyBytes, flagsBytes, exptBytes, lenBytes] =>
      match parseDecimal flagsBytes, parseDecimal exptBytes, parseDecimal lenBytes with
      | some flags, some expt, some bytes =>
        if keyBytes.length ≤ MAX_KEY ∧ bytes ≤ MAX_VALUE ∧ rest1.length ≥ bytes + 2 then
          let value := rest1.take bytes
          let after := rest1.drop bytes
          match after with
          | 0x0D :: 0x0A :: tail =>
            some (.set keyBytes.toArray flags expt value.toArray, tail)
          | _ => some (.err, rest1)
        else
          some (.err, rest1)
      | _, _, _ => some (.err, rest1)
    | "add", [keyBytes, flagsBytes, exptBytes, lenBytes] =>
      match parseDecimal flagsBytes, parseDecimal exptBytes, parseDecimal lenBytes with
      | some flags, some expt, some bytes =>
        if keyBytes.length ≤ MAX_KEY ∧ bytes ≤ MAX_VALUE ∧ rest1.length ≥ bytes + 2 then
          let value := rest1.take bytes
          let after := rest1.drop bytes
          match after with
          | 0x0D :: 0x0A :: tail =>
            some (.add keyBytes.toArray flags expt value.toArray, tail)
          | _ => some (.err, rest1)
        else
          some (.err, rest1)
      | _, _, _ => some (.err, rest1)
    | _, _ => some (.err, rest1)
  | _ => some (.err, rest1)

/-! ### Pure-data KV oracle. -/

/-- A single slot: (present?, key, flags, value). -/
structure Slot where
  present : Bool := false
  key   : Array UInt8 := #[]
  flags : Nat := 0
  value : Array UInt8 := #[]
  deriving Inhabited

/-- An array-backed KV store with `NUM_SLOTS` slots and an
    age counter for slot replacement (FIFO; LRU is Tier-2). -/
structure KvStore where
  slots : Array Slot := Array.replicate NUM_SLOTS {}
  nextSlot : Nat := 0
  deriving Inhabited

private partial def keyEq (a b : Array UInt8) : Bool :=
  if a.size ≠ b.size then false
  else
    let rec go (i : Nat) : Bool :=
      if i < a.size then
        if a[i]! = b[i]! then go (i+1) else false
      else true
    go 0

/-- Look up `key`.  Returns the slot index if present. -/
partial def lookup (store : KvStore) (key : Array UInt8) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if i = NUM_SLOTS then none
    else
      let s := store.slots[i]!
      if s.present ∧ keyEq s.key key then some i
      else go (i+1)
  go 0

/-- Reply produced by applying a single command. -/
inductive Reply where
  | stored
  | notStored
  | value (key : Array UInt8) (flags : Nat) (value : Array UInt8)
  | end_       -- after VALUE or for empty get
  | deleted
  | notFound
  | error
  deriving Inhabited, Repr

/-- Apply a command and return (newStore, replies).  `get`
    returns a 2-reply list: [.value …, .end_] when hit, or
    [.end_] when miss.  Other commands return a single reply. -/
def applyCommand (store : KvStore) (c : Command) : KvStore × List Reply :=
  match c with
  | .get key =>
    match lookup store key with
    | some i =>
      let s := store.slots[i]!
      (store, [.value s.key s.flags s.value, .end_])
    | none => (store, [.end_])
  | .set key flags _exp value =>
    match lookup store key with
    | some i =>
      let s' : Slot := { present := true, key, flags, value }
      ({ store with slots := store.slots.set! i s' }, [.stored])
    | none =>
      let slot := store.nextSlot % NUM_SLOTS
      let s' : Slot := { present := true, key, flags, value }
      ({ store with slots := store.slots.set! slot s', nextSlot := store.nextSlot + 1 }, [.stored])
  | .add key flags _exp value =>
    match lookup store key with
    | some _ => (store, [.notStored])
    | none =>
      let slot := store.nextSlot % NUM_SLOTS
      let s' : Slot := { present := true, key, flags, value }
      ({ store with slots := store.slots.set! slot s', nextSlot := store.nextSlot + 1 }, [.stored])
  | .del key =>
    match lookup store key with
    | some i =>
      let s' : Slot := { (store.slots[i]!) with present := false }
      ({ store with slots := store.slots.set! i s' }, [.deleted])
    | none => (store, [.notFound])
  | .err => (store, [.error])

/-! ### Reply serializer.

    Convert a Reply into the wire bytes the host expects.  Used
    by sim oracles AND by the HW Signal-DSL emitter — the latter
    will compute the same byte stream via a kLut! mux. -/

private def strBytes (s : String) : List UInt8 :=
  s.toUTF8.toList.toArray.toList.map (fun c => c.toNat.toUInt8)

private def natToDecBytes (n : Nat) : List UInt8 :=
  let s := toString n
  strBytes s

def replyToBytes (r : Reply) : List UInt8 :=
  match r with
  | .stored => strBytes "STORED\r\n"
  | .notStored => strBytes "NOT_STORED\r\n"
  | .deleted => strBytes "DELETED\r\n"
  | .notFound => strBytes "NOT_FOUND\r\n"
  | .end_ => strBytes "END\r\n"
  | .error => strBytes "ERROR\r\n"
  | .value key flags value =>
    let header := strBytes "VALUE " ++ key.toList ++ [0x20]
                  ++ natToDecBytes flags ++ [0x20]
                  ++ natToDecBytes value.size ++ [0x0D, 0x0A]
    let body := value.toList ++ [0x0D, 0x0A]
    header ++ body

def repliesToBytes (rs : List Reply) : List UInt8 :=
  rs.flatMap replyToBytes

/-- Convenience: string literal → `Array UInt8` for tests
    that want to spell key/value as plain Lean strings. -/
def strToBytes (s : String) : Array UInt8 :=
  s.toUTF8.toList.toArray

/-! ### Convenience: drive a series of commands at once. -/

/-- Run multiple commands sequentially over an initial store,
    returning the final store and the concatenated reply bytes. -/
def runScript (initial : KvStore) (commands : List Command) :
    KvStore × List UInt8 :=
  commands.foldl (init := (initial, ([] : List UInt8))) fun (st, acc) c =>
    let (st', replies) := applyCommand st c
    (st', acc ++ repliesToBytes replies)

/-- Parse a raw byte buffer into as many Commands as possible. -/
partial def parseAll (input : List UInt8) : List Command :=
  match parseOne input with
  | some (c, rest) =>
    if rest.isEmpty then [c]
    else c :: parseAll rest
  | none => []

end Sparkle.IP.Net.Memcached
