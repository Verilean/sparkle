import Sparkle.Core.JIT
import IP.Crypto.Proof.Secp256k1ECDSA
open Sparkle.Core.JIT
-- signCoreTop ports: start=0 d=1..8 k=9..16 z=17..24 ; out rOut=0..7 sOut=8..15 done=16
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/signCoreTop_jit.c"
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWide (base v : Nat) : IO Unit := do for j in [0:8] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let getWide (base : Nat) : IO Nat := do
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h (base+j).toUInt32).toNat <<< (32*j))
    pure acc
  let doSign (d k z : Nat) : IO (Nat × Nat) := do
    JIT.reset h
    setWide 1 d; setWide 9 k; setWide 17 z
    si 0 1; JIT.eval h; JIT.tick h; si 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 4000000 do
      JIT.eval h
      if (← JIT.getOutput h 16) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    let r ← getWide 0; let s ← getWide 8
    IO.println s!"  ({d},{k},{z}) done={done} after {cyc} cyc"
    pure (r, s)
  for (d,k,z) in [(2,5,9), (1234,7,42), (999,12345,88)] do
    let (r,s) ← doSign d k z
    match Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z with
    | some (er, es) => IO.println s!"core d={d} k={k} z={z}: {if (r,s)==(er,es) then "PASS" else s!"FAIL got=({r},{s}) exp=({er},{es})"}"
    | none => IO.println s!"core d={d}: reference none"
  JIT.destroy h
