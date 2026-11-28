/-
  JIT co-sim test for IP.Crypto.HMACSHA256HW (`hmacSha256`) — real-cycle
  validation of the HMAC-SHA256 FSM against RFC 4231.

  The hardware takes a 32-byte key and the message as one or two
  already-padded inner blocks (the pad length counts the 64-byte ipad block).
  So the harness
    * zero-pads keys of up to 32 bytes to 256 bits (HMAC zero-pads the key to
      the block size anyway),
    * replaces a key longer than the 64-byte block by its SHA-256 (RFC 2104;
      the hardware does no key hashing), computed with the pure-data
      `sha256Bytes`,
    * pads the message as a SHA-256 message of length `64 + len`.
  The digest is compared with the published RFC 4231 value and with the
  pure-data `Rfc6979.hmacSha256`.

  RFC 4231 test case 7 (152-byte message → 3 inner blocks) is out of the
  design's range (≤ 2 message blocks, ≤ 119 bytes) and is not exercised.
-/
import Sparkle
import IP.Crypto.SHA256
import IP.Crypto.HMACSHA256HW
import IP.Crypto.Rfc6979
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.HMACSHA256HW

namespace Sparkle.Tests.IP.Crypto.HMACSHA256JITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def hmacTop
    (start : Signal defaultDomain Bool)
    (key : Signal defaultDomain (BitVec 256))
    (blk1 blk2 : Signal defaultDomain (BitVec 512))
    (threeBlk : Signal defaultDomain Bool) : HmacOut defaultDomain :=
  hmacSha256 start key blk1 blk2 threeBlk

#sim hmacTop

open hmacTop.Sim

/-- SHA-256 padding of `msg` as if `extra` bytes preceded it, in 512-bit blocks. -/
private def padBlocks (msg : Array UInt8) (extra : Nat) : List (BitVec 512) := Id.run do
  let mut p := msg.push 0x80
  while (p.size + extra) % 64 != 56 do p := p.push 0
  let bits := (msg.size + extra) * 8
  for i in [:8] do p := p.push (UInt8.ofNat ((bits >>> ((7 - i) * 8)) &&& 0xFF))
  let mut out : List (BitVec 512) := []
  for b in [:p.size / 64] do
    let mut v : Nat := 0
    for i in [:64] do v := (v <<< 8) ||| (p.getD (b * 64 + i) 0).toNat
    out := out ++ [BitVec.ofNat 512 v]
  return out

private def bytesToNat (a : Array UInt8) : Nat := Id.run do
  let mut v : Nat := 0
  for b in a do v := (v <<< 8) ||| b.toNat
  return v

/-- 256-bit key operand: ≤ 32 bytes left-aligned; > 64 bytes → SHA-256(key). -/
private def keyOperand (key : Array UInt8) : Option (BitVec 256) :=
  let k := if key.size > 64 then Sparkle.IP.Crypto.Rfc6979.sha256Bytes key else key
  if k.size > 32 then none
  else some (BitVec.ofNat 256 (bytesToNat k <<< (8 * (32 - k.size))))

private def mkIn (start : Bool) (key : BitVec 256) (b1 b2 : BitVec 512) (three : Bool) : SimInput :=
  { _gen_start := if start then 1#1 else 0#1
  , _gen_key := key
  , _gen_blk1 := b1
  , _gen_blk2 := b2
  , _gen_threeBlk := if three then 1#1 else 0#1 }

/-- One HMAC: (digest, cycles from the start pulse to `done`). -/
private def runHmac (sim : Simulator) (key : BitVec 256) (msg : Array UInt8) :
    IO (BitVec 256 × Nat) := do
  let blks := padBlocks msg 64
  let three := blks.length == 2
  let b1 := blks.getD 0 0
  let b2 := blks.getD 1 0
  sim.step (mkIn true key b1 b2 three)
  let mut out ← sim.read
  let mut cyc := 1
  while out.done == 0#1 && cyc < 2000 do
    sim.step (mkIn false key b1 b2 three)
    out ← sim.read
    cyc := cyc + 1
  if out.done == 0#1 then
    throw <| IO.userError "hmacSha256 did not assert done within 2000 cycles"
  return (out.hmac, cyc)

private def hex (v : BitVec 256) : String :=
  let s := (Nat.toDigits 16 v.toNat).asString
  "".pushn '0' (64 - s.length) ++ s

private def hexNat (s : String) : Nat :=
  s.foldl (fun acc c =>
    acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0

private def bytes (s : String) : Array UInt8 := s.toUTF8.toList.toArray

structure Vec where
  label : String
  key : Array UInt8
  msg : Array UInt8
  /-- published digest (hex), and how many leading hex digits it covers -/
  pub : Option String

def main : IO Unit := do
  IO.println "=== HMAC-SHA256 hmacSha256 — JIT real-cycle co-sim (RFC 4231) ==="
  (← IO.getStdout).flush
  let sim ← load
  let mut ok := true
  let rep n (b : UInt8) := Array.replicate n b
  let vecs : List Vec :=
    [ { label := "RFC4231 case 1 (key 20B, 'Hi There')"
      , key := rep 20 0x0b, msg := bytes "Hi There"
      , pub := some "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7" }
    , { label := "RFC4231 case 2 (key 'Jefe')"
      , key := bytes "Jefe", msg := bytes "what do ya want for nothing?"
      , pub := some "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843" }
    , { label := "RFC4231 case 3 (key aa×20, data dd×50)"
      , key := rep 20 0xaa, msg := rep 50 0xdd
      , pub := some "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe" }
    , { label := "RFC4231 case 4 (key 0x01..0x19, data cd×50)"
      , key := (List.range 25).toArray.map (fun i => UInt8.ofNat (i + 1)) , msg := rep 50 0xcd
      , pub := some "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b" }
    , { label := "RFC4231 case 5 (key 0c×20, 'Test With Truncation', 128-bit prefix)"
      , key := rep 20 0x0c, msg := bytes "Test With Truncation"
      , pub := some "a3b6167473100ee06e0c796c2955552b" }
    , { label := "RFC4231 case 6 (key aa×131, long key hashed by the harness)"
      , key := rep 131 0xaa
      , msg := bytes "Test Using Larger Than Block-Size Key - Hash Key First"
      , pub := some "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54" }
    , { label := "32B key, 119B message (2 message blocks)"
      , key := rep 32 0x5a, msg := rep 119 0x61, pub := none }
    , { label := "32B key, 56B message (length spills to block 2)"
      , key := rep 32 0xc3, msg := rep 56 0x62, pub := none } ]
  -- All HMACs run back-to-back without a reset (the FSM must return to idle
  -- and `first` must re-initialise the SHA state for every pass).
  sim.reset
  for pass in [0, 1] do
    for v in vecs do
      match keyOperand v.key with
      | none =>
        IO.println s!"  ✗ [{pass}] {v.label}: key does not fit the 32-byte operand"
        ok := false
      | some k =>
        let (got, cyc) ← runHmac sim k v.msg
        let ref := bytesToNat (Sparkle.IP.Crypto.Rfc6979.hmacSha256 v.key v.msg)
        let pubOk := match v.pub with
          | some p => (hex got).take p.length == p
          | none => true
        if got.toNat == ref && pubOk then
          IO.println s!"  ✓ [{pass}] {v.label}: {hex got}  ({cyc} cycles)"
        else
          IO.println s!"  ✗ [{pass}] {v.label}: HW {hex got} ≠ ref {hex (BitVec.ofNat 256 ref)} ({cyc} cycles)"
          ok := false
    for _ in [:3] do sim.step (mkIn false 0 0 0 false)
  sim.destroy
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.HMACSHA256JITTest
