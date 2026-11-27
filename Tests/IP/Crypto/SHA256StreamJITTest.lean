/-
  JIT co-sim test for IP.Crypto.SHA256Stream (`sha256StreamHW`) — real-cycle
  validation of the multi-block streaming FSM.

  The top below wraps `sha256StreamHW`, `#sim` lowers it (→ `CSim.toCJIT` →
  native) and the test drives it cycle by cycle:  pulse `start` for one cycle
  with `nBlocks`, `blk0`, `blk1` held, tick until `done`, read `hash`.

  Digests are checked against the published FIPS 180-4 values AND the
  pure-data reference `sha256OfBytes`.  The design hashes at most two padded
  blocks (`nBlocks ∈ {1, 2}`, up to 119 bytes), so the longest message is
  119 bytes; longer messages cannot be expressed through this interface.
-/
import Sparkle
import IP.Crypto.SHA256
import IP.Crypto.SHA256Stream
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA256
open Sparkle.IP.Crypto.SHA256Stream

namespace Sparkle.Tests.IP.Crypto.SHA256StreamJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def shaStreamTop
    (start : Signal defaultDomain Bool)
    (nBlocks : Signal defaultDomain (BitVec 2))
    (blk0 blk1 : Signal defaultDomain (BitVec 512)) : StreamOut defaultDomain :=
  sha256StreamHW start nBlocks blk0 blk1

#sim shaStreamTop

open shaStreamTop.Sim

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

private def mkIn (start : Bool) (n : Nat) (b0 b1 : BitVec 512) : SimInput :=
  { _gen_start := if start then 1#1 else 0#1
  , _gen_nBlocks := BitVec.ofNat 2 n
  , _gen_blk0 := b0
  , _gen_blk1 := b1 }

/-- One message: returns (digest, cycles from the start pulse to `done`). -/
private def runMsg (sim : Simulator) (msg : Array UInt8) : IO (BitVec 256 × Nat) := do
  let blks := padBlocks msg
  let n := blks.length
  let b0 := blks.getD 0 0
  let b1 := blks.getD 1 0
  sim.step (mkIn true n b0 b1)
  let mut out ← sim.read
  let mut cyc := 1
  while out.done == 0#1 && cyc < 400 do
    sim.step (mkIn false n b0 b1)
    out ← sim.read
    cyc := cyc + 1
  if out.done == 0#1 then
    throw <| IO.userError "sha256StreamHW did not assert done within 400 cycles"
  return (out.hash, cyc)

private def hex (v : BitVec 256) : String :=
  let s := (Nat.toDigits 16 v.toNat).asString
  "".pushn '0' (64 - s.length) ++ s

private def bytes (s : String) : Array UInt8 := s.toUTF8.toList.toArray

private def h (s : String) : BitVec 256 :=
  BitVec.ofNat 256 (s.foldl (fun acc c =>
    acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0)

def main : IO Unit := do
  IO.println "=== SHA-256 sha256StreamHW — JIT real-cycle co-sim (FIPS 180-4) ==="
  (← IO.getStdout).flush
  let sim ← load
  let mut ok := true
  let a n := Array.replicate n (0x61 : UInt8)
  -- (label, message, published digest if any)
  let fixtures : List (String × Array UInt8 × Option (BitVec 256)) :=
    [ ("abc (1 block)", bytes "abc",
        some (h "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"))
    , ("empty (1 block)", #[],
        some (h "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"))
    , ("448-bit (2 blocks)",
        bytes "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        some (h "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"))
    , ("896-bit (2 blocks)",
        bytes "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
        some (h "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"))
    , ("55 B (1 block, max)", a 55, none)
    , ("56 B (2 blocks, length spills)", a 56, none)
    , ("119 B (2 blocks, max)", a 119, none) ]
  -- Every message is hashed with NO reset in between: `first` (= start) must
  -- re-initialise H0..H7 to the IV, and the FSM must clear its block index.
  sim.reset
  for pass in [0, 1] do
    for (label, msg, pub) in fixtures do
      let (got, cyc) ← runMsg sim msg
      let ref := refDigest msg
      let pubOk := match pub with | some p => got == p | none => true
      if got == ref && pubOk then
        IO.println s!"  ✓ [{pass}] {label}: {hex got}  ({cyc} cycles)"
      else
        IO.println s!"  ✗ [{pass}] {label}: HW {hex got} ≠ ref {hex ref} ({cyc} cycles)"
        ok := false
    -- idle cycles (done must drop) before the second pass
    for _ in [:3] do sim.step (mkIn false 1 0 0)
  sim.destroy
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.SHA256StreamJITTest
