import Sparkle.Core.JIT
import IP.Crypto.Proof.Keccak256
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Keccak256 (keccak256OfBytes padEthereum rateBytes)
-- keccakSpongeTop ports (64-bit values are single slots in this JIT ABI):
--   in  start=0, nBlocks=1, m0..m33 = slots 2..35 (one slot per 64-bit lane).
--   out d0..d3 = slots 0..3 (one slot each), done = slot 4.
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/keccakSpongeTop_jit.c"
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  -- pack a padded block's 136 bytes (little-endian lanes) into 17 x 64-bit.
  let laneOf (bytes : Array UInt8) (blk lane : Nat) : Nat := Id.run do
    let mut v := 0
    for j in [0:8] do
      let idx := blk*136 + lane*8 + j
      let b := if idx < bytes.size then bytes[idx]!.toNat else 0
      v := v ||| (b <<< (8*j))       -- little-endian
    return v
  let run (msg : Array UInt8) : IO Nat := do
    JIT.reset h
    let padded := padEthereum msg
    let nBlocks := padded.size / rateBytes
    si 1 nBlocks
    for lane in [0:34] do
      let blk := lane / 17; let l := lane % 17
      let v := if blk < nBlocks then laneOf padded blk l else 0
      -- one slot per 64-bit lane: m{lane} = slot 2+lane
      si (2 + lane) v
    si 0 1; JIT.eval h; JIT.tick h; si 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 2000 do
      JIT.eval h
      if (← JIT.getOutput h 4) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    -- z = d0..d3, each a single 64-bit little-endian lane; keccak256OfBytes
    -- returns bytes (little-endian lanes) → assemble the digest bytes.
    let mut zbytes : Array UInt8 := #[]
    for lane in [0:4] do
      let laneVal := (← JIT.getOutput h lane.toUInt32).toNat
      for j in [0:8] do zbytes := zbytes.push (UInt8.ofNat ((laneVal >>> (8*j)) &&& 0xFF))
    -- compare byte arrays
    let exp := keccak256OfBytes msg
    let ok := zbytes == exp
    IO.println s!"  ({msg.size}B msg, done={done} cyc={cyc}) {if ok then "PASS" else "FAIL"}"
    pure (if ok then 1 else 0)
  let mkMsg (s : String) : Array UInt8 := s.toUTF8.toList.toArray
  let mut pass := 0; let mut total := 0
  -- 1-block fixtures + 2-block fixtures (135B → 1 block, 136B/200B → 2 blocks).
  for msg in [mkMsg "", mkMsg "abc", mkMsg "hello world",
              Array.replicate 135 (0x61 : UInt8), Array.replicate 136 (0x61 : UInt8),
              Array.replicate 200 (0x61 : UInt8)] do
    pass := pass + (← run msg); total := total + 1
  IO.println s!"{pass}/{total} PASS"
  JIT.destroy h
  if pass != total then IO.Process.exit 1
