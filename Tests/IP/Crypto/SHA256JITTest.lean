/-
  JIT co-sim test for IP.Crypto.SHA256 (`sha256Block`) — real-cycle validation.

  `SHA256Test` only checks the pure-data reference (`Signal.val` cannot reach
  `sha256Block`: the 512-bit W buffer makes it exponential).  This test lowers
  the core through `#sim` (→ `CSim.toCJIT` → native), drives the actual
  hardware cycle by cycle and compares the digest with `sha256OfBytes`.

  Ports are addressed by NAME through the typed `#sim` API, never by index.
  Protocol: pulse `start` for one cycle with `blockIn` held and `first` set on
  the first block of a message, tick until `done`, repeat for the next block
  with `first = false` (the core carries H0..H7 across blocks).
-/
import Sparkle
import IP.Crypto.SHA256
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA256

namespace Sparkle.Tests.IP.Crypto.SHA256JITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def shaBlockTop
    (start : Signal defaultDomain Bool)
    (blockIn : Signal defaultDomain (BitVec 512))
    (first : Signal defaultDomain Bool) : SHA256Out defaultDomain :=
  sha256Block start blockIn first

#sim shaBlockTop

open shaBlockTop.Sim

/-- FIPS 180-4 padding to whole 512-bit blocks (word 0 = MSB). -/
private def padBlocks (msg : Array UInt8) : List (BitVec 512) := Id.run do
  let mut p := msg.push 0x80
  while p.size % 64 != 56 do p := p.push 0
  let bits := msg.size * 8
  for i in [:8] do p := p.push (UInt8.ofNat ((bits >>> ((7 - i) * 8)) &&& 0xFF))
  let mut out : List (BitVec 512) := []
  for b in [:p.size / 64] do
    let mut v : Nat := 0
    for i in [:64] do v := (v <<< 8) ||| (p.getD (b * 64 + i) 0).toNat
    out := out ++ [BitVec.ofNat 512 v]
  return out

private def refDigest (msg : Array UInt8) : BitVec 256 := Id.run do
  let mut v : Nat := 0
  for w in sha256OfBytes msg do v := (v <<< 32) ||| w.toNat
  return BitVec.ofNat 256 v

private def mkIn (start : Bool) (blk : BitVec 512) (first : Bool) : SimInput :=
  { _gen_start := if start then 1#1 else 0#1
  , _gen_blockIn := blk
  , _gen_first := if first then 1#1 else 0#1 }

private def runBlock (sim : Simulator) (blk : BitVec 512) (first : Bool) : IO SimOutput := do
  sim.step (mkIn true blk first)
  let mut out ← sim.read
  let mut cyc := 0
  while out.done == 0#1 && cyc < 200 do
    sim.step (mkIn false blk first)
    out ← sim.read
    cyc := cyc + 1
  if out.done == 0#1 then
    throw <| IO.userError "sha256Block did not assert done within 200 cycles"
  return out

private def hex (v : BitVec 256) : String :=
  let s := (Nat.toDigits 16 v.toNat).asString
  "".pushn '0' (64 - s.length) ++ s

def main : IO Unit := do
  IO.println "=== SHA-256 sha256Block — JIT real-cycle co-sim vs sha256OfBytes ==="
  (← IO.getStdout).flush
  let sim ← load
  let mut ok := true
  let a n := Array.replicate n (0x61 : UInt8)
  let fixtures : List (String × Array UInt8) :=
    [ ("empty", #[])
    , ("abc", "abc".toUTF8.toList.toArray)
    , ("56B (2 blocks)", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.toList.toArray)
    , ("100B (2 blocks)", a 100)
    , ("150B (3 blocks)", a 150)
    , ("abc again (re-init)", "abc".toUTF8.toList.toArray) ]
  for (label, msg) in fixtures do
    sim.reset
    let mut got : BitVec 256 := 0
    let mut first := true
    for blk in padBlocks msg do
      let o ← runBlock sim blk first
      got := o.hash
      first := false
    let ref := refDigest msg
    if got == ref then IO.println s!"  ✓ {label}: {hex got}"
    else
      IO.println s!"  ✗ {label}: HW {hex got} ≠ ref {hex ref}"
      ok := false
  sim.destroy
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.SHA256JITTest
