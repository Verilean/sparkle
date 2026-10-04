import Sparkle.Core.JIT
import IP.Crypto.SHA256
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.SHA256 (sha256OfBytes)
-- shaStreamTop ports: start=0 nBlocks=1 blk0=2..17 blk1=18..33 ; out hash=0..7 done=8
-- Verifies the re-initializable SHA-256 core by hashing several independent
-- messages back-to-back (each relies on `first` re-init of the H-state).

-- pure SHA-256 of bytes → hex-ish Nat digest (H0 in high bits).
def pureDigest (msg : Array UInt8) : Nat := Id.run do
  let h := sha256OfBytes msg
  let mut acc := 0
  for w in h do acc := (acc <<< 32) ||| w.toNat
  return acc

-- big-endian pad a ≤55-byte message to one 512-bit block (as a Nat).
def pad1 (msg : Array UInt8) : Nat := Id.run do
  let mut bytes := msg.push 0x80
  while bytes.size < 56 do bytes := bytes.push 0
  let bits := msg.size * 8
  for j in [0:8] do bytes := bytes.push (UInt8.ofNat ((bits >>> (8*(7-j))) &&& 0xFF))
  -- pack 64 bytes big-endian into a Nat (byte 0 in MSB)
  let mut v := 0
  for b in bytes do v := (v <<< 8) ||| b.toNat
  return v

def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/shaStreamTop_jit.c"
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWide (base w v : Nat) : IO Unit := do
    for j in [0:w] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let getHash : IO Nat := do
    let mut acc := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    -- output is 256-bit with H0 in MSB slot 7? getOutput packs low-word first,
    -- so reconstruct then the driver compares against the same packing.
    pure acc
  let hashOne (msg : Array UInt8) : IO Nat := do
    -- feed 1 padded block
    si 1 1                       -- nBlocks = 1
    setWide 2 16 (pad1 msg)      -- blk0
    setWide 18 16 0              -- blk1 unused
    si 0 1; JIT.eval h; JIT.tick h; si 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 2000 do
      JIT.eval h
      if (← JIT.getOutput h 8) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    getHash
  JIT.reset h
  let msgs : List (String × Array UInt8) :=
    [ ("abc", "abc".toUTF8.toList.toArray),
      ("hello", "hello".toUTF8.toList.toArray),
      ("", #[]),
      ("abc", "abc".toUTF8.toList.toArray) ]   -- repeat to test re-init determinism
  for (name, m) in msgs do
    let got ← hashOne m
    let exp := pureDigest m
    IO.println s!"sha256(\"{name}\"): {if got == exp then "PASS" else s!"FAIL\n got={got}\n exp={exp}"}"
  JIT.destroy h
