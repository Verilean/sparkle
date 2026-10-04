import Sparkle.Core.JIT
open Sparkle.Core.JIT

def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/aluTop_jit.c"
  JIT.reset h
  let si (idx v : Nat) : IO Unit := JIT.setInput h idx.toUInt32 (UInt64.ofNat v)
  let out0 : IO Nat := do pure (← JIT.getOutput h 0).toNat

  -- load reg0 = 5 (three variants of the write cycle, to probe timing)
  let loadReg (addr v : Nat) : IO Unit := do
    si 0 0; si 1 0; si 5 1; si 6 addr
    for j in [0:8] do si (7+j) (if j==0 then v else 0)
    JIT.eval h; JIT.tick h
    si 5 0; JIT.eval h; JIT.tick h
  loadReg 0 5
  -- ADDP reg2 = reg0 + reg0  (should be 10 iff the load worked)
  si 1 2; si 2 0; si 3 0; si 4 2; si 5 0; si 0 1
  JIT.eval h; JIT.tick h; si 0 0
  for c in [0:14] do
    JIT.eval h
    IO.println s!"cyc {c}: out={← out0}"
    JIT.tick h
  JIT.destroy h
