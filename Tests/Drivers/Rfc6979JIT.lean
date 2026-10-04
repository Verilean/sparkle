import Sparkle.Core.JIT
import IP.Crypto.Rfc6979
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Rfc6979 (rfc6979)
-- rfcTop ports: start=0 z=1..8 ; out k=0..7 done=8.  Baked d = 12345.
def dKey : Nat := 12345
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/rfcTop_jit.c"
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWide (base v : Nat) : IO Unit := do for j in [0:8] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let run (z : Nat) : IO Nat := do
    JIT.reset h
    setWide 1 z
    si 0 1; JIT.eval h; JIT.tick h; si 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 100000 do
      JIT.eval h
      if (← JIT.getOutput h 8) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    let mut acc := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    IO.println s!"  (z={z}, done after {cyc} cyc)"
    pure acc
  for z in [9, 42, 0xDEADBEEF, 123456789] do
    let got ← run z
    let exp := rfc6979 dKey z
    IO.println s!"rfc6979 d={dKey} z={z}: {if got == exp then "PASS" else s!"FAIL\n got={got}\n exp={exp}"}"
  JIT.destroy h
