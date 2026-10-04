import Sparkle.Core.JIT
open Sparkle.Core.JIT
-- mulSerTop: in start=0, a=1..8, b=9..16, m=17..25 (258b) ; out result=0..7, done=8.
def P : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
def N : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/mulSerTop_jit.c"
  let setW (base cnt v : Nat) : IO Unit := do
    for j in [0:cnt] do JIT.setInput h (base+j).toUInt32 (UInt64.ofNat ((v >>> (32*j)) &&& 0xFFFFFFFF))
  let run (a b m : Nat) : IO Nat := do
    JIT.reset h
    setW 1 8 a; setW 9 8 b; setW 17 9 m
    JIT.setInput h 0 1; JIT.eval h; JIT.tick h; JIT.setInput h 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 40000 do
      JIT.eval h
      if (← JIT.getOutput h 8) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    let mut r := 0
    for j in [0:8] do r := r ||| ((← JIT.getOutput h j.toUInt32).toNat <<< (32*j))
    pure r
  let mut pass := 0; let mut total := 0
  let vecs := [(5,7,P), (123456789, 987654321, P), (P-1, P-1, P), (5,7,N), (P-1, 2, N), (0xdeadbeef, 0xcafe, N)]
  for (a,b,m) in vecs do
    let r ← run a b m
    let exp := (a * b) % m
    let ok := r == exp
    IO.println s!"  {a%1000000}*{b%1000000} mod {if m==P then "p" else "n"} = {if ok then "PASS" else s!"FAIL got {r} exp {exp}"}"
    if ok then pass := pass + 1
    total := total + 1
  IO.println s!"{pass}/{total} PASS"
  JIT.destroy h
  if pass != total then IO.Process.exit 1
