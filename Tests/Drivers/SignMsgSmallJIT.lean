import Sparkle.Core.JIT
import IP.Crypto.Keccak256
import IP.Crypto.Rfc6979
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Keccak256 (keccak256OfBytes padEthereum rateBytes)
open Sparkle.IP.Crypto.Rfc6979 (signDeterministic)

-- signMsgTop ports: in start=0, nBlocks=1, m0..m33 = slots 2..35 (one 64-bit slot
--   per lane).  out rOut = 0..7, sOut = 8..15 (256-bit LE words), done = 16.
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/signMsgTop_jit.c"
  let dKey : Nat := 12345
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let laneOf (bytes : Array UInt8) (blk lane : Nat) : Nat := Id.run do
    let mut v := 0
    for j in [0:8] do
      let idx := blk*136 + lane*8 + j
      let b := if idx < bytes.size then bytes[idx]!.toNat else 0
      v := v ||| (b <<< (8*j))
    return v
  let read256 (base : Nat) : IO Nat := do
    let mut v := 0
    for w in [0:8] do
      let word := (← JIT.getOutput h (base + w).toUInt32).toNat &&& 0xFFFFFFFF
      v := v ||| (word <<< (32*w))
    pure v
  -- z = int.from_bytes(keccak256(msg), 'big')
  let hashInt (msg : Array UInt8) : Nat := Id.run do
    let d := keccak256OfBytes msg
    let mut v := 0
    for b in d do v := (v <<< 8) ||| b.toNat
    return v
  let check (msg : Array UInt8) : IO Bool := do
    JIT.reset h
    let padded := padEthereum msg
    let nBlocks := padded.size / rateBytes
    si 1 nBlocks
    for lane in [0:34] do
      let blk := lane / 17; let l := lane % 17
      let v := if blk < nBlocks then laneOf padded blk l else 0
      si (2 + lane) v
    si 0 1; JIT.eval h; JIT.tick h; si 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 5000000 do
      JIT.eval h
      if (← JIT.getOutput h 16) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    let r ← read256 0
    let s ← read256 8
    let z := hashInt msg
    match signDeterministic dKey z with
    | some (er, es) =>
      let ok := done && r == er && s == es
      IO.println s!"  ({msg.size}B msg) done={done} cyc={cyc} {if ok then "PASS" else s!"FAIL (r={r}/{er} s={s}/{es})"}"
      pure ok
    | none => IO.println "  golden=none"; pure false
  let mkMsg (s : String) : Array UInt8 := s.toUTF8.toList.toArray
  let mut pass := 0; let mut total := 0
  for msg in [mkMsg "abc", mkMsg "hello world"] do
    if (← check msg) then pass := pass + 1
    total := total + 1
  IO.println s!"{pass}/{total} PASS"
  JIT.destroy h
  if pass != total then IO.Process.exit 1
