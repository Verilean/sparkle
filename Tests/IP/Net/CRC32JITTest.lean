/-
  JIT-backed sim test for `IP.Net.CRC32.crc32Engine`.

  Pilot for the JIT path on a SINGLE-output, sub-module-free
  design.  Same golden vectors as `crc32-test` but routes the
  cycle loop through `#sim` → C++ → dlopen → JIT step instead
  of evaluating `Signal.val` per cycle.

  Goals:
    * Show the infrastructure works end-to-end on a clean
      design (no multi-output `@[hardware_module]` sub-module
      duplication — that's Issue #71).
    * Establish a CONTRIBUTING.md pattern for fast IP sim
      tests.

  Expected timing: a few seconds for 3 golden vectors + a
  long-string fuzz, vs ~minutes for the pure-Lean form on
  longer inputs.
-/

import IP.Net.CRC32
import Sparkle.Core.JIT
import Sparkle.Core.SimTyped

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.JIT
open Sparkle.IP.Net.CRC32

namespace Sparkle.Tests.IP.Net.CRC32JITTest

abbrev D := defaultDomain

/-- Monomorphic top-level for `#sim`.  Matches the original
    `crc32Engine` signature exactly so the same inputs reach
    the engine. -/
def crc32Top
    (byte  : Signal D (BitVec 8))
    (feed  : Signal D Bool)
    (reset : Signal D Bool) :
    Signal D (BitVec 32) :=
  crc32Engine byte feed reset

#sim crc32Top

private def strBytes (s : String) : List (BitVec 8) :=
  s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

private def hex32 (v : BitVec 32) : String := Id.run do
  let mut out := ""
  for i in [:8] do
    let nib := (v.toNat >>> ((7 - i) * 4)) &&& 0xF
    let c := if nib < 10 then Char.ofNat (nib + 0x30) else Char.ofNat (nib - 10 + 0x61)
    out := out.push c
  return out

/-- Run the JIT engine for n+2 cycles, matching the
    pure-Lean test's cycle pattern. -/
def runJit (sim : crc32Top.Sim.Simulator) (bytes : List (BitVec 8)) :
    IO (BitVec 32) := do
  let n := bytes.length
  Sparkle.Core.Sim.Sim.reset sim
  let mut lastOut : BitVec 32 := 0
  for t in [:n + 2] do
    let byteVal : BitVec 8 :=
      if t = 0 then 0#8 else (bytes[t - 1]?).getD 0#8
    let feedVal : Bool := t ≠ 0 ∧ t ≤ n
    let resetVal : Bool := t = 0
    let inp : crc32Top.Sim.SimInput :=
      { _gen_byte := byteVal
      , _gen_feed := BitVec.ofNat 1 (if feedVal then 1 else 0)
      , _gen_reset := BitVec.ofNat 1 (if resetVal then 1 else 0) }
    Sparkle.Core.Sim.Sim.step sim inp
    let out ← Sparkle.Core.Sim.Sim.read sim
    if t = n + 1 then
      lastOut := out.out
  return lastOut ^^^ 0xFFFFFFFF#32

def main : IO Unit := do
  IO.println "=== CRC32 JIT-backed engine sim ==="
  let sim ← crc32Top.Sim.load

  let cases : List (String × List (BitVec 8) × BitVec 32) :=
    [ ("empty",        [],                          0x00000000#32)
    , ("123456789",    strBytes "123456789",        0xCBF43926#32)
    , ("quick brown fox",
         strBytes "The quick brown fox jumps over the lazy dog",
                                                     0x414FA339#32)
    , ("1 KiB of 'a'", List.replicate 1024 0x61#8,  0x7C5597B9#32)
    ]

  let mut failed : Nat := 0
  let t0 ← IO.monoMsNow
  for (name, bytes, expected) in cases do
    let got ← runJit sim bytes
    let ok := got = expected
    let mark := if ok then "✓" else "✗"
    IO.println s!"  {mark} {name} ({bytes.length} bytes) = 0x{hex32 got} (expected 0x{hex32 expected})"
    if !ok then failed := failed + 1
  let t1 ← IO.monoMsNow

  Sparkle.Core.Sim.Sim.destroy sim

  IO.println s!"\nTotal time: {t1 - t0} ms"
  if failed = 0 then
    IO.println "\nALL PASS — JIT path matches reference"
  else
    IO.println s!"\nFAIL ({failed} cases)"
    IO.Process.exit 1

end Sparkle.Tests.IP.Net.CRC32JITTest
