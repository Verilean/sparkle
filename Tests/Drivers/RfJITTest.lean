import Sparkle.Core.JIT
open Sparkle.Core.JIT

def main : IO Unit := do
  IO.println "--- regFileTop (256-bit BRAM in a @[hardware_module] submodule) ---"
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/regFileTop_jit.c"
  JIT.reset h
  -- inputs: wa=0, wd=slots1..8, we=9, ra=10
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWd (v : Nat) : IO Unit := do
    for j in [0:8] do si (1+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let get256 : IO Nat := do
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  let v : Nat := 0xCAFEBABE00000000000000000000000000000000000000000000000DEADBEEF
  -- write mem[5] = v
  si 0 5; setWd v; si 9 1; si 10 0
  JIT.eval h; JIT.tick h
  -- read mem[5] — regFile has 2-cycle latency (BRAM read + internal rdReg)
  si 9 0; si 10 5
  for _ in [0:4] do JIT.eval h; JIT.tick h
  JIT.eval h
  let o ← get256
  IO.println s!"  read mem[5] = {o}"
  IO.println s!"  expect      = {v}   {if o==v then "PASS" else "FAIL"}"
  JIT.destroy h
