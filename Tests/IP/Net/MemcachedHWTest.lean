/-
  Sim test for IP.Net.MemcachedHW.kvHw.

  Drives a sequence of commands cycle-by-cycle and asserts the
  reply stream matches the pure-data oracle's expectations.

  Per command we:
    1. Wait until busy is low (engine is idle).
    2. Pulse opStart for one cycle with the right opCode / key /
       value / flags.
    3. Sample replyValid / replyKind / replyKey / replyValue
       until replyValid pulses (= command done).
    4. Compare against the oracle's expected reply.
-/

import IP.Net.Memcached
import IP.Net.MemcachedHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.Memcached
open Sparkle.IP.Net.MemcachedHW

namespace Sparkle.Tests.IP.Net.MemcachedHWTest

abbrev D := defaultDomain

/-- Pack a byte list MSB-first into a Nat (byte 0 = highest). -/
private def packMsb (bytes : List UInt8) (width : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  let n := bytes.length
  for i in [:width] do
    let b : Nat := if i < n then (bytes[i]!).toNat else 0
    acc := acc * 256 + b
  return acc

/-- Pack a key string (≤ 8 chars) into a BitVec 64, MSB-aligned. -/
private def keyToBV (s : String) : BitVec 64 :=
  BitVec.ofNat 64 (packMsb (strToBytes s).toList 8)

/-- Pack a value string (≤ 16 chars) into a BitVec 128, MSB-aligned. -/
private def valueToBV (s : String) : BitVec 128 :=
  BitVec.ofNat 128 (packMsb (strToBytes s).toList 16)

/-- One command's stimulus across a long-enough cycle window.

    The lookup phase takes 16 cycles, plus 1 entry, 1 decide,
    1 emit = ~20 cycles per command.  We allot 32 to be safe.

    `startCycle` = absolute cycle at which we pulse opStart. -/
structure CmdStim where
  startCycle : Nat
  opCode     : BitVec 2
  key        : BitVec 64
  value      : BitVec 128
  flags      : BitVec 32

/-- Build the four control signals from a list of CmdStim, each
    pulsing opStart at its assigned cycle. -/
private def cmdSignals (cmds : List CmdStim) :
    Signal D Bool × Signal D (BitVec 2) × Signal D (BitVec 64) ×
    Signal D (BitVec 128) × Signal D (BitVec 32) :=
  let opStart : Signal D Bool :=
    ⟨fun t => cmds.any (fun c => c.startCycle = t)⟩
  -- "active command at cycle t" = the most recent cmd whose
  -- startCycle ≤ t (or default values).
  let mostRecent (t : Nat) : Option CmdStim :=
    cmds.foldl (fun acc c => if c.startCycle ≤ t then some c else acc) none
  let opCode : Signal D (BitVec 2) :=
    ⟨fun t => match mostRecent t with | some c => c.opCode | none => 0#2⟩
  let opKey : Signal D (BitVec 64) :=
    ⟨fun t => match mostRecent t with | some c => c.key | none => 0#64⟩
  let opValue : Signal D (BitVec 128) :=
    ⟨fun t => match mostRecent t with | some c => c.value | none => 0#128⟩
  let opFlags : Signal D (BitVec 32) :=
    ⟨fun t => match mostRecent t with | some c => c.flags | none => 0#32⟩
  (opStart, opCode, opKey, opValue, opFlags)

inductive ReplyKind where
  | stored | notStored | value | end_ | deleted | notFound | error
  deriving Repr, BEq, DecidableEq

def kindOfBV (b : BitVec 3) : ReplyKind :=
  match b.toNat with
  | 0 => .stored
  | 1 => .notStored
  | 2 => .value
  | 3 => .end_
  | 4 => .deleted
  | 5 => .notFound
  | _ => .error

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════════╗"
  IO.println "║  IP.Net.MemcachedHW — BRAM-backed KV store ║"
  IO.println "╚════════════════════════════════════════════╝"

  -- 4 commands: set foo=hello, get foo, delete foo, get foo
  let setFoo : CmdStim := {
    startCycle := 2
    opCode := 1#2   -- set
    key := keyToBV "foo"
    value := valueToBV "hello"
    flags := 0#32
  }
  let getFoo1 : CmdStim := {
    startCycle := 30
    opCode := 0#2   -- get
    key := keyToBV "foo"
    value := 0#128
    flags := 0#32
  }
  let delFoo : CmdStim := {
    startCycle := 60
    opCode := 3#2   -- del
    key := keyToBV "foo"
    value := 0#128
    flags := 0#32
  }
  let getFoo2 : CmdStim := {
    startCycle := 90
    opCode := 0#2
    key := keyToBV "foo"
    value := 0#128
    flags := 0#32
  }

  let cmds := [setFoo, getFoo1, delFoo, getFoo2]
  let (opStart, opCode, opKey, opValue, opFlags) := cmdSignals cmds

  let engine := kvHw opStart opCode opKey opValue opFlags

  -- Sample replyValid at each cycle and record the reply kind +
  -- (for VALUE) the value bits.
  let horizon := 120
  let mut replyEvents : List (Nat × ReplyKind × Nat) := []
  for t in [0:horizon] do
    if engine.replyValid.val t then
      let k := kindOfBV (engine.replyKind.val t)
      let v := (engine.replyValue.val t).toNat
      replyEvents := replyEvents ++ [(t, k, v)]

  IO.println s!"  observed {replyEvents.length} replyValid pulses over {horizon} cycles:"
  for (t, k, v) in replyEvents do
    IO.println s!"    cycle {t}: kind={repr k}  value=0x{Nat.toDigits 16 v |> String.ofList}"

  let mut ok := true

  -- Expected: [.stored, .value, .deleted, .end_]
  let expectedKinds : List ReplyKind := [.stored, .value, .deleted, .end_]
  let gotKinds := replyEvents.map (fun (_, k, _) => k)
  if gotKinds = expectedKinds then
    IO.println "  ✓ reply kinds match: [STORED, VALUE, DELETED, END]"
  else
    IO.println s!"  ✗ kinds got {repr gotKinds}, expected {repr expectedKinds}"
    ok := false

  -- Check the VALUE event's value bits = "hello" packed MSB-first
  let expectedValue := (valueToBV "hello").toNat
  let valueEvents := replyEvents.filter (fun (_, k, _) => k == ReplyKind.value)
  match valueEvents with
  | [(_, _, v)] =>
    if v = expectedValue then
      IO.println s!"  ✓ VALUE reply carries the correct \"hello\" payload"
    else
      IO.println s!"  ✗ VALUE bits = 0x{Nat.toDigits 16 v |> String.ofList} expected 0x{Nat.toDigits 16 expectedValue |> String.ofList}"
      ok := false
  | _ => IO.println s!"  ✗ expected exactly 1 VALUE event"; ok := false

  if ok then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.MemcachedHWTest
