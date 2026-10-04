/-
  End-to-end sim for IP.Net.MemcachedServer.

  Feeds a real memcached ASCII byte stream into the server,
  collects the outByte stream, and asserts the recovered text
  contains the expected reply tokens.

  The HW server is single-threaded: it processes one command,
  emits its reply, then accepts the next.  Our stim threads
  multiple commands with enough cycle slack between them for
  the lookup + dispatch + emit pipeline (~30-50 cycles).
-/

import IP.Net.Memcached
import IP.Net.MemcachedServer

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.Memcached (strToBytes)
open Sparkle.IP.Net.MemcachedServer

namespace Sparkle.Tests.IP.Net.MemcachedServerTest

abbrev D := defaultDomain

private def hasSubstr (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  let rec go (xs : List Char) : Bool :=
    if n.isPrefixOf xs then true
    else
      match xs with
      | [] => false
      | _ :: rest => go rest
  go h

/-- A scheduled command: starts feeding `bytes` at `startCycle`,
    one byte per cycle.  After the bytes are exhausted, valid
    goes low until the next scheduled command. -/
structure ByteSched where
  startCycle : Nat
  bytes      : List UInt8

/-- Build (byte, valid) signals from a list of scheduled bursts. -/
private def stim (bursts : List ByteSched) :
    Signal D (BitVec 8) × Signal D Bool :=
  -- For cycle t, find the first burst b such that
  -- b.startCycle ≤ t < b.startCycle + b.bytes.length;
  -- emit b.bytes[t - b.startCycle].
  let active (t : Nat) : Option (UInt8) :=
    bursts.foldl (fun acc b =>
      match acc with
      | some _ => acc
      | none =>
        if b.startCycle ≤ t ∧ t < b.startCycle + b.bytes.length then
          some (b.bytes[t - b.startCycle]!)
        else none) none
  let byteS : Signal D (BitVec 8) :=
    ⟨fun t => match active t with
              | some b => BitVec.ofNat 8 b.toNat
              | none => 0#8⟩
  let validS : Signal D Bool :=
    ⟨fun t => (active t).isSome⟩
  (byteS, validS)

def main : IO Unit := do
  IO.println "╔════════════════════════════════════════════════╗"
  IO.println "║  IP.Net.MemcachedServer — byte stream FSM e2e ║"
  IO.println "╚════════════════════════════════════════════════╝"

  -- Two commands: set then get, tight spacing to keep cycle
  -- count low (BitVec 128 sim is ~360ms/cycle).
  let cmd1 := strToBytes "set foo 0 0 5\r\nhello\r\n"   -- 22 bytes
  let cmd2 := strToBytes "get foo\r\n"                   -- 9 bytes

  let burst1 : ByteSched := { startCycle := 2, bytes := cmd1.toList }
  -- After cmd1's last byte (cycle 23) we need ~30 cycles for
  -- lookup + STORED reply (8 bytes) to complete.
  let burst2 : ByteSched := { startCycle := 60, bytes := cmd2.toList }

  let (byteS, validS) := stim [burst1, burst2]
  let server := memcachedServer byteS validS

  let horizon := 160
  IO.println s!"  horizon = {horizon}"
  let mut outBytes : List UInt8 := []
  for t in [0:horizon] do
    if server.outValid.val t then
      outBytes := outBytes ++ [(server.outByte.val t).toNat.toUInt8]

  let outStr := String.ofList (outBytes.map (fun b => Char.ofNat b.toNat))
  IO.println s!"  observed {outBytes.length} output bytes over {horizon} cycles"
  IO.println s!"  output: {repr outStr}"

  let mut ok := true

  -- We expect (in order): "STORED\r\n" from set, then a VALUE…END
  -- block from get.
  if outStr.startsWith "STORED\r\n" then
    IO.println "  ✓ first reply = STORED"
  else
    IO.println "  ✗ first reply not STORED"
    ok := false

  if hasSubstr outStr "VALUE k 0 16\r\n" then
    IO.println "  ✓ second reply contains VALUE header"
  else
    IO.println "  ✗ no VALUE header in output"
    ok := false

  if hasSubstr outStr "hello" then
    IO.println "  ✓ VALUE reply payload contains \"hello\""
  else
    IO.println "  ✗ no \"hello\" in output"
    ok := false

  if hasSubstr outStr "END\r\n" then
    IO.println "  ✓ second reply contains END"
  else
    IO.println "  ✗ no END after VALUE"
    ok := false

  if ok then
    IO.println "\nALL PASS — memcached over the FSM datapath is functional"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.MemcachedServerTest
