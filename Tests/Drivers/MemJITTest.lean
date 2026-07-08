import Sparkle.Core.JIT
open Sparkle.Core.JIT

def get256 (h : JITHandle) : IO Nat := do
  let mut acc : Nat := 0
  for j in [0:8] do
    acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
  pure acc

def testMem8 : IO Unit := do
  IO.println "--- mem8Top (8-bit top-level memory) ---"
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/mem8Top_jit.c"
  JIT.reset h
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  -- write mem[3] = 42
  si 0 3; si 1 42; si 2 1; si 3 0
  JIT.eval h; JIT.tick h
  -- read mem[3]
  si 2 0; si 3 3
  JIT.eval h; JIT.tick h
  JIT.eval h
  let o ← JIT.getOutput h 0
  IO.println s!"  read mem[3] = {o}  (expect 42)  {if o.toNat==42 then "PASS" else "FAIL"}"
  JIT.destroy h

def testMem256 : IO Unit := do
  IO.println "--- mem256Top (256-bit top-level memory) ---"
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/mem256Top_jit.c"
  JIT.reset h
  -- inputs: wa=0, wd=slots1..8, we=9, ra=10
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWd (v : Nat) : IO Unit := do
    for j in [0:8] do si (1+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  -- write mem[5] = 0xABCD...(use a value with high words)
  let v : Nat := 0xDEADBEEF00000000000000000000000000000000000000000000000CAFEBABE
  si 0 5; setWd v; si 9 1; si 10 0
  JIT.eval h; JIT.tick h
  -- read mem[5]
  si 9 0; si 10 5
  JIT.eval h; JIT.tick h
  JIT.eval h
  let o ← get256 h
  IO.println s!"  read mem[5] = {o}"
  IO.println s!"  expect      = {v}   {if o==v then "PASS" else "FAIL"}"
  JIT.destroy h

def main : IO Unit := do
  testMem8
  testMem256
