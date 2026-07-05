import Sparkle.Core.JIT
import IP.Crypto.Secp256k1PointJac
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Secp256k1PointJac
-- inputs: ladderStart=0 extLoadEn=1 extLoadAddr=2 extLoadData=3..10
--         scalarLoadEn=11 scalarIn=12..19 probeAddr=20 ; out probeVal=0..7 halted=8
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/ladderTop_jit.c"
  JIT.reset h
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWide (base v : Nat) : IO Unit := do for j in [0:8] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let load (addr v : Nat) : IO Unit := do
    si 0 0; si 1 1; si 2 addr; setWide 3 v; JIT.eval h; JIT.tick h; si 1 0; JIT.eval h; JIT.tick h
  let probe (addr : Nat) : IO Nat := do
    si 20 addr
    for _ in [0:4] do JIT.eval h; JIT.tick h
    JIT.eval h
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  let g : Point := ⟨baseX, baseY, 1, false⟩
  for k in [5, 7, 12345, 65537, 987654321] do
    JIT.reset h
    let expected := toAffine (mulScalar k g)
    -- preload base G into r3,r4,r5
    load 3 g.x; load 4 g.y; load 5 g.z
    -- load scalar
    si 11 1; setWide 12 k; JIT.eval h; JIT.tick h; si 11 0
    -- run ladder
    si 0 1; JIT.eval h; JIT.tick h; si 0 0
    let mut cyc := 0; let mut halted := false
    while (!halted) && cyc < 2000000 do
      JIT.eval h
      if (← JIT.getOutput h 8) != 0 then halted := true
      JIT.tick h; cyc := cyc + 1
    let x ← probe 0; let y ← probe 1; let z ← probe 2
    let got := toAffine ⟨x, y, z, false⟩
    IO.println s!"k={k}: {cyc} cyc  {if got == expected then "PASS" else s!"FAIL got={got} exp={expected}"}"
  JIT.destroy h
