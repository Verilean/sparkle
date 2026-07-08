import Sparkle.Core.JIT
import IP.Crypto.Secp256k1PointJac
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Secp256k1PointJac
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/addTop_jit.c"
  JIT.reset h
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setLd (v : Nat) : IO Unit := do for j in [0:8] do si (3+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let load (addr v : Nat) : IO Unit := do
    si 0 0; si 1 1; si 2 addr; setLd v; JIT.eval h; JIT.tick h; si 1 0; JIT.eval h; JIT.tick h
  let probe (addr : Nat) : IO Nat := do
    si 11 addr
    for _ in [0:4] do JIT.eval h; JIT.tick h
    JIT.eval h
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  -- P = G (Z=1), Q = 2G (from double), then P+Q = 3G
  let g : Point := ⟨baseX, baseY, 1, false⟩
  let q := double g
  let e := add g q
  load 0 g.x; load 1 g.y; load 2 g.z
  load 3 q.x; load 4 q.y; load 5 q.z
  si 0 1; JIT.eval h; JIT.tick h; si 0 0
  let mut cyc := 0; let mut halted := false
  while (!halted) && cyc < 8000 do
    JIT.eval h
    if (← JIT.getOutput h 8) != 0 then halted := true
    JIT.tick h; cyc := cyc + 1
  IO.println s!"halted after {cyc} cycles"
  let x3 ← probe 18; let y3 ← probe 23; let z3 ← probe 26
  IO.println s!"X3 {if x3==e.x then "PASS" else s!"FAIL got={x3} exp={e.x}"}"
  IO.println s!"Y3 {if y3==e.y then "PASS" else s!"FAIL got={y3} exp={e.y}"}"
  IO.println s!"Z3 {if z3==e.z then "PASS" else s!"FAIL got={z3} exp={e.z}"}"
  IO.println (if x3==e.x && y3==e.y && z3==e.z then "POINT-ADD PASS (JIT vs pure spec)" else "FAIL")
  JIT.destroy h
