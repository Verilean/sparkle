import Sparkle.Core.JIT
import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1ECDSA
open Sparkle.Core.JIT
-- expTop ports: modN=0 expStart=1 extLoadEn=2 extLoadAddr=3 extLoadData=4..11
--   scalarLoadEn=12 scalarIn=13..20 probeAddr=21 ; out probeVal=0..7 halted=8
-- Computes acc = base^exp mod m (base in r3).  For a⁻¹, exp = m-2.
def pMod : Nat := Sparkle.IP.Crypto.Secp256k1Field.p
def nMod : Nat := Sparkle.IP.Crypto.Secp256k1ECDSA.n
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/expTop_jit.c"
  let si (i v : Nat) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v)
  let setWide (base v : Nat) : IO Unit := do for j in [0:8] do si (base+j) ((v >>> (32*j)) &&& 0xFFFFFFFF)
  let load (addr v : Nat) : IO Unit := do
    si 1 0; si 2 1; si 3 addr; setWide 4 v; JIT.eval h; JIT.tick h; si 2 0; JIT.eval h; JIT.tick h
  let probe (addr : Nat) : IO Nat := do
    si 21 addr
    for _ in [0:4] do JIT.eval h; JIT.tick h
    JIT.eval h
    let mut acc : Nat := 0
    for j in [0:8] do acc := acc ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure acc
  let run (modN : Nat) (base exp : Nat) : IO Nat := do
    JIT.reset h
    si 0 modN
    load 3 base                       -- base → r3
    si 12 1; setWide 13 exp; JIT.eval h; JIT.tick h; si 12 0   -- exponent
    si 1 1; JIT.eval h; JIT.tick h; si 1 0                     -- expStart
    let mut cyc := 0; let mut halted := false
    while (!halted) && cyc < 3000000 do
      JIT.eval h
      if (← JIT.getOutput h 8) != 0 then halted := true
      JIT.tick h; cyc := cyc + 1
    let r ← probe 0
    pure r
  -- inv mod p
  for a in [7, 12345] do
    let got ← run 0 a (pMod - 2)
    let exp := Sparkle.IP.Crypto.Secp256k1Field.inv a
    IO.println s!"inv_p({a}) {if got==exp then "PASS" else s!"FAIL got={got} exp={exp}"}"
  -- inv mod n
  for a in [7, 12345] do
    let got ← run 1 a (nMod - 2)
    let exp := Sparkle.IP.Crypto.Secp256k1ECDSA.invModN a
    IO.println s!"inv_n({a}) {if got==exp then "PASS" else s!"FAIL got={got} exp={exp}"}"
  JIT.destroy h
