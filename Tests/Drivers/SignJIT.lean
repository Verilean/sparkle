import Sparkle.Core.JIT
import IP.Crypto.Proof.Secp256k1PointJac
import IP.Crypto.Proof.Secp256k1ECDSA
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Secp256k1PointJac
-- signTop ports: signStart=0 extLoadEn=1 extLoadAddr=2 extLoadData=3..10
--   kIn=11..18 probeAddr=19 ; out probeVal=0..7 halted=8
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/signTop_jit.c"
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWide (base v : Nat) : IO Unit := do for j in [0:8] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let load (addr v : Nat) : IO Unit := do
    si 0 0; si 1 1; si 2 addr; setWide 3 v; JIT.eval h; JIT.tick h; si 1 0; JIT.eval h; JIT.tick h
  let probe (addr : Nat) : IO Nat := do
    si 19 addr
    for _ in [0:4] do JIT.eval h; JIT.tick h
    JIT.eval h
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  let doSign (d k z : Nat) : IO (Nat × Nat) := do
    JIT.reset h
    setWide 11 k                       -- kIn held stable = nonce
    load 3 baseX; load 4 baseY; load 5 1     -- G → r3,r4,r5
    load 40 d; load 41 z; load 42 k          -- d,z,k
    si 0 1; JIT.eval h; JIT.tick h; si 0 0    -- signStart
    let mut cyc := 0; let mut halted := false
    while (!halted) && cyc < 15000000 do
      JIT.eval h
      if (← JIT.getOutput h 8) != 0 then halted := true
      JIT.tick h; cyc := cyc + 1
    let r ← probe 35; let s ← probe 37
    pure (r, s)
  for (d,k,z) in [(2,5,9), (1234,7,42), (999,12345,88),
                  (0xC0FFEE, 0xBEEF, 0xDEADBEEF), (7, 65537, 123456789)] do
    let (r,s) ← doSign d k z
    match Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z with
    | some (er, es) =>
        IO.println s!"sign d={d} k={k} z={z}: {if (r,s)==(er,es) then "PASS" else s!"FAIL got=({r},{s}) exp=({er},{es})"}"
    | none => IO.println s!"sign d={d} k={k} z={z}: reference returned none"
  JIT.destroy h
