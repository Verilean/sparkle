import Sparkle.Core.JIT
open Sparkle.Core.JIT
-- inputs: start=0, a=1..8, b=9..16 ; output 256-bit
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/mulPTop_jit.c"
  JIT.reset h
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setW (base v : Nat) : IO Unit := do
    for j in [0:8] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let get256 : IO Nat := do
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  setW 1 5; setW 9 7; si 0 1
  JIT.eval h; JIT.tick h; si 0 0
  for _ in [0:262] do JIT.eval h; JIT.tick h
  JIT.eval h
  let o ← get256
  IO.println s!"mulP 5*7 = {o}  (expect 35)  {if o==35 then "PASS" else "FAIL"}"
  JIT.destroy h
