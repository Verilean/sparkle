import Sparkle.Core.JIT
open Sparkle.Core.JIT

-- inputs: start=0 srcA=1 srcB=2 dst=3 loadEn=4 loadAddr=5 loadData=6..13
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/aluLiteTop_jit.c"
  JIT.reset h
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let get256 : IO Nat := do
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  let loadReg (addr v : Nat) : IO Unit := do
    si 0 0; si 4 1; si 5 addr
    for j in [0:8] do si (6+j) (if j==0 then v else 0)
    JIT.eval h; JIT.tick h
    si 4 0; JIT.eval h; JIT.tick h
  loadReg 0 5
  loadReg 1 7
  -- ADDP reg2 = reg0 + reg1
  si 1 0; si 2 1; si 3 2; si 4 0; si 0 1
  JIT.eval h; JIT.tick h; si 0 0
  for _ in [0:14] do JIT.eval h; JIT.tick h
  JIT.eval h
  let o ← get256
  IO.println s!"aluLite ADDP 5+7 = {o}  (expect 12)  {if o==12 then "PASS" else "FAIL"}"
  JIT.destroy h
