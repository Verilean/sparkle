import Sparkle.Core.JIT
import IP.Crypto.Keccak256
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Keccak256 (keccak256OfBytes padEthereum rateBytes)
-- keccakSpongeTop ports: start=0 nBlocks=1 m0..m33 = slots 2.. (each lane 2 slots)
--   out d0..d3 = slots 0..7 (each 2 slots), done=8.
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
      -- lane input base = 2 + lane*2 ; feed 64-bit as 2 slots
      si (2 + lane*2) (v &&& 0xFFFFFFFF)
      si (2 + lane*2 + 1) ((v >>> 32) &&& 0xFFFFFFFF)
    si 0 1; JIT.eval h; JIT.tick h; si 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 2000 do
      JIT.eval h
      if (← JIT.getOutput h 8) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    -- z = d0..d3, but keccak256OfBytes returns bytes (little-endian lanes).
    -- read d0..d3 as 4 x 64-bit little-endian, assemble big digest bytes.
    let mut zbytes : Array UInt8 := #[]
    for lane in [0:4] do
      let lo := (← JIT.getOutput h (lane*2).toUInt32).toNat
      let hi := (← JIT.getOutput h (lane*2+1).toUInt32).toNat
      let laneVal := lo ||| (hi <<< 32)
      for j in [0:8] do zbytes := zbytes.push (UInt8.ofNat ((laneVal >>> (8*j)) &&& 0xFF))
    -- compare byte arrays
    let exp := keccak256OfBytes msg
    let ok := zbytes == exp
    IO.println s!"  ({msg.size}B msg, done={done} cyc={cyc}) {if ok then "PASS" else "FAIL"}"
    pure (if ok then 1 else 0)
  let mkMsg (s : String) : Array UInt8 := s.toUTF8.toList.toArray
  for name in ["", "abc", "hello world"] do
    let _ ← run (mkMsg name)
  JIT.destroy h
