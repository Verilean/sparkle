import Sparkle.Core.JIT
open Sparkle.Core.JIT
-- inputs: a=slots0..7, b=slots8..15 ; output 256-bit
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/addTop_jit.c"
  JIT.reset h
  let setW (base v : Nat) : IO Unit := do
    for j in [0:8] do JIT.setInput h (base+j).toUInt32 (UInt64.ofNat ((v >>> (32*j)) &&& 0xFFFFFFFF))
  let get256 : IO Nat := do
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  setW 0 5; setW 8 7
  JIT.eval h
  let o ← get256
  IO.println s!"add 5+7 = {o}  (expect 12)  {if o==12 then "PASS" else "FAIL"}"
  -- big values to exercise the reduce: (p-1) + 3 = 2 mod p
  setW 0 (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2E); setW 8 3
  JIT.eval h
  let o2 ← get256
  IO.println s!"add (p-1)+3 = {o2}  (expect 2)  {if o2==2 then "PASS" else "FAIL"}"
  JIT.destroy h
