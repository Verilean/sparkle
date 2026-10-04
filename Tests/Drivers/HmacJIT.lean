import Sparkle.Core.JIT
import IP.Crypto.Rfc6979
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Rfc6979 (hmacSha256 i2octets32 octets2i)
-- hmacTop ports: start=0 key=1..8 blk1=9..24 blk2=25..40 threeBlk=41 ; out hmac=0..7 done=8
-- Build the padded inner message blocks (after the ipad block) for a message.

-- SHA-256 padding of the inner message (ipad already accounts for +64 bytes):
-- returns (blk1, blk2, threeBlk) as big-endian 512-bit Nats.
def innerBlocks (msg : Array UInt8) : Nat × Nat × Bool := Id.run do
  let total := 64 + msg.size                          -- ipad(64) + msg
  let mut bytes := msg.push 0x80
  -- pad with zeros until (ipad + bytes + 8) is a multiple of 64
  while (64 + bytes.size + 8) % 64 != 0 do bytes := bytes.push 0
  let bits := total * 8
  for j in [0:8] do bytes := bytes.push (UInt8.ofNat ((bits >>> (8*(7-j))) &&& 0xFF))
  -- bytes is now 64 (2-block) or 128 (3-block) long
  let three := bytes.size > 64
  let packBlk (off : Nat) : Nat := Id.run do
    let mut v := 0
    for i in [0:64] do
      let b := if off+i < bytes.size then bytes[off+i]!.toNat else 0
      v := (v <<< 8) ||| b
    return v
  return (packBlk 0, (if three then packBlk 64 else 0), three)

def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/hmacTop_jit.c"
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setW (base cnt v : Nat) : IO Unit := do for j in [0:cnt] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let run (key : Nat) (msg : Array UInt8) : IO Nat := do
    JIT.reset h
    let (b1, b2, three) := innerBlocks msg
    setW 1 8 key; setW 9 16 b1; setW 25 16 b2; si 41 (if three then 1 else 0)
    si 0 1; JIT.eval h; JIT.tick h; si 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 6000 do
      JIT.eval h
      if (← JIT.getOutput h 8) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    let mut acc := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    IO.println s!"  ({msg.size}B msg, done after {cyc} cyc)"
    pure acc
  -- test messages: 32B, 33B, 97B (the RFC-6979 shapes)
  let m32 : Array UInt8 := i2octets32 0x1234                          -- V (32 bytes)
  let m33 : Array UInt8 := m32.push 0x00
  let m97 : Array UInt8 := m32 ++ #[(0x01 : UInt8)] ++ i2octets32 0xd ++ i2octets32 0xC0FFEE  -- V‖tag‖dz(64)
  for key in [12345, 0] do
    for (name, msg) in [("32B", m32), ("33B", m33), ("97B", m97)] do
      let got ← run key msg
      let exp := octets2i (hmacSha256 (i2octets32 key) msg)
      IO.println s!"hmac key={key} {name}: {if got == exp then "PASS" else s!"FAIL got={got} exp={exp}"}"
  JIT.destroy h
