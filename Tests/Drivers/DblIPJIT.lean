import Sparkle.Core.JIT
import IP.Crypto.Secp256k1PointJac
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Secp256k1PointJac
-- ladderEngine ports: runStart=0 loadEn=1 loadAddr=2 loadData=3..10 probeAddr=11 progStart=12
-- out probeVal=0..7 halted=8
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/dblEngTop_jit.c"
  JIT.reset h
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWide (base v : Nat) : IO Unit := do for j in [0:8] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let load (addr v : Nat) : IO Unit := do
    si 0 0; si 1 1; si 2 addr; setWide 3 v; JIT.eval h; JIT.tick h; si 1 0; JIT.eval h; JIT.tick h
  let probe (addr : Nat) : IO Nat := do
    si 11 addr
    for _ in [0:4] do JIT.eval h; JIT.tick h
    JIT.eval h
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  let g : Point := ⟨baseX, baseY, 1, false⟩
  let e := double g
  -- load acc = G into r0,r1,r2
  load 0 g.x; load 1 g.y; load 2 g.z
  -- progStart = 0 (DBL), run
  si 12 0; si 0 1; JIT.eval h; JIT.tick h; si 0 0
  let mut cyc := 0; let mut halted := false
  while (!halted) && cyc < 20000 do
    JIT.eval h
    if (← JIT.getOutput h 8) != 0 then halted := true
    JIT.tick h; cyc := cyc + 1
  IO.println s!"halted after {cyc} cycles"
  let x ← probe 0; let y ← probe 1; let z ← probe 2
  IO.println s!"acc X {if x==e.x then "PASS" else s!"FAIL got={x} exp={e.x}"}"
  IO.println s!"acc Y {if y==e.y then "PASS" else s!"FAIL got={y} exp={e.y}"}"
  IO.println s!"acc Z {if z==e.z then "PASS" else s!"FAIL got={z} exp={e.z}"}"
  JIT.destroy h
