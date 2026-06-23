/-
  Sim parity test for IP.Net.CRC32.

  Asserts the byte-feed Signal-DSL engine matches:
    1. A pure Lean reference (`crc32Ref`, same byte-by-byte
       recurrence in plain code).
    2. Known IEEE 802.3 golden vectors:
         "" (empty)                              → 0x00000000 (init ^ xorout)
         "123456789"                             → 0xCBF43926
         "The quick brown fox jumps over the lazy dog"
                                                 → 0x414FA339
-/

import IP.Net.CRC32
import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.CRC32

/-! ## Synthesis check: the byte-feed CRC engine must lower to Verilog
    at `lake build` time.  This is the (2) of CLAUDE.md's
    "new circuit construct" rule. -/
namespace SynthesisChecks

def crc32EngineTop
    (byte : Signal defaultDomain (BitVec 8))
    (feed reset : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 32) :=
  crc32Engine byte feed reset

#synthesizeVerilog crc32EngineTop

end SynthesisChecks

namespace Sparkle.Tests.IP.Net.CRC32Test

/-- Pretty-print a 32-bit CRC as 8 hex digits. -/
private def hex32 (x : BitVec 32) : String :=
  let hex := String.ofList (Nat.toDigits 16 x.toNat)
  let pad := 8 - hex.length
  let zeros := String.ofList (List.replicate (max 0 pad) '0')
  "0x" ++ zeros ++ hex

/-- Convert a `String` to a list of bytes (each char is taken as
    a UTF-8 code unit; ASCII inputs only here). -/
private def strBytes (s : String) : List (BitVec 8) :=
  s.toList.map (fun c => BitVec.ofNat 8 c.toNat)

/--
  Drive the Signal-DSL engine for `n+2` cycles:
    cycle 0:   reset=1, feed=0   → load 0xFFFFFFFF
    cycle k+1 (k = 0..n-1): reset=0, feed=1, byte = bytes[k]
    cycle n+1: read-out (register has settled to post-last-byte
               value because the engine's <~ updates take effect
               at the *next* cycle boundary).
  Returns the cycle-(n+1) register value XOR'd with 0xFFFFFFFF.
-/
private def runEngine (bytes : List (BitVec 8)) : BitVec 32 :=
  let n := bytes.length
  let byteStream  : Signal defaultDomain (BitVec 8) :=
    ⟨fun t => if t = 0 then 0#8 else (bytes[t - 1]?).getD 0#8⟩
  let feedStream  : Signal defaultDomain Bool :=
    ⟨fun t => decide (t ≠ 0 ∧ t ≤ n)⟩
  let resetStream : Signal defaultDomain Bool :=
    ⟨fun t => decide (t = 0)⟩
  let crc := crc32Engine byteStream feedStream resetStream
  -- After n+1 cycles the register reflects all n bytes.
  ((crc.sample (n + 2))[n + 1]?).getD 0#32 ^^^ 0xFFFFFFFF#32

/-- Golden cases.  Each is `(name, input bytes, expected CRC)`. -/
private def cases : List (String × List (BitVec 8) × BitVec 32) :=
  [ ("empty",            [],                          0x00000000#32)
  , ("123456789",        strBytes "123456789",        0xCBF43926#32)
  , ("quick brown fox",
       strBytes "The quick brown fox jumps over the lazy dog",
                                                       0x414FA339#32)
  ]

def main : IO Unit := do
  let mut failed : Nat := 0
  for (name, bytes, expected) in cases do
    let refOut := crc32Ref bytes
    let engOut := runEngine bytes
    let refOk  := decide (refOut = expected)
    let engOk  := decide (engOut = expected)
    let parity := decide (refOut = engOut)
    IO.println s!"--- {name} ({bytes.length} bytes) ---"
    IO.println s!"  ref      = {hex32 refOut}    {if refOk  then "PASS" else "FAIL"} vs expected {hex32 expected}"
    IO.println s!"  engine   = {hex32 engOut}    {if engOk  then "PASS" else "FAIL"} vs expected {hex32 expected}"
    IO.println s!"  parity   = {if parity then "PASS" else "FAIL"} (ref vs engine)"
    if !(refOk && engOk && parity) then
      failed := failed + 1
  if failed = 0 then
    IO.println "\nALL PASS"
  else
    IO.println s!"\n{failed} case(s) FAILED"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.CRC32Test
