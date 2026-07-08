import Sparkle.Core.JIT
import IP.Crypto.Proof.Secp256k1PointJac
open Sparkle.Core.JIT

-- inputs: runStart=0 loadEn=1 loadAddr=2 loadData=3..10 probeAddr=11
-- outputs: probeVal=0..7, halted=8
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/pdTop_jit.c"
  JIT.reset h
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setLd (v : Nat) : IO Unit := do
    for j in [0:8] do si (3+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let load (addr v : Nat) : IO Unit := do
    si 0 0; si 1 1; si 2 addr; setLd v
    JIT.eval h; JIT.tick h
    si 1 0; JIT.eval h; JIT.tick h
  let probe (addr : Nat) : IO Nat := do
    si 11 addr
    for _ in [0:4] do JIT.eval h; JIT.tick h
    JIT.eval h
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  let gx := Sparkle.IP.Crypto.Secp256k1PointJac.baseX
  let gy := Sparkle.IP.Crypto.Secp256k1PointJac.baseY
  -- expected via the pure spec
  let e := Sparkle.IP.Crypto.Secp256k1PointJac.double ⟨gx, gy, 1, false⟩
  -- load r0=X, r1=Y, r2=Z=1
  load 0 gx; load 1 gy; load 2 1
  -- run
  si 0 1; JIT.eval h; JIT.tick h; si 0 0
  -- wait for halted (double ≈ 7 muls × ~260 cyc)
  let mut cyc := 0
  let mut halted := false
  while (!halted) && cyc < 5000 do
    JIT.eval h
    if (← JIT.getOutput h 8) != 0 then halted := true
    JIT.tick h; cyc := cyc + 1
  IO.println s!"halted after {cyc} cycles"
  let x3 ← probe 11
  let y3 ← probe 14
  let z3 ← probe 16
  let ok := (x3 == e.x) && (y3 == e.y) && (z3 == e.z)
  IO.println s!"X3 {if x3==e.x then "PASS" else s!"FAIL got={x3} exp={e.x}"}"
  IO.println s!"Y3 {if y3==e.y then "PASS" else s!"FAIL got={y3} exp={e.y}"}"
  IO.println s!"Z3 {if z3==e.z then "PASS" else s!"FAIL got={z3} exp={e.z}"}"
  IO.println (if ok then "POINT-DOUBLE PASS (JIT vs pure spec)" else "FAIL")
  JIT.destroy h
