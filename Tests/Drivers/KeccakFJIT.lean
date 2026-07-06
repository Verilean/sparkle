import Sparkle.Core.JIT
import IP.Crypto.Keccak256
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Keccak256 (keccakF State)

-- keccakFTop ports: in  start=0, i0..i24 = 1..25 ; out l0..l24 = 0..24, round=25, done=26.
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/keccakFTop_jit.c"
  let si (i : Nat) (v : BitVec 64) : IO Unit := JIT.setInput h i.toUInt32 (UInt64.ofNat v.toNat)
  let run (input : Array (BitVec 64)) : IO (Bool × Nat × Array (BitVec 64)) := do
    JIT.reset h
    -- cycle 0: start=1 with input lanes
    si 0 1
    for i in [0:25] do si (1+i) (input.getD i 0#64)
    JIT.eval h; JIT.tick h
    si 0 0
    -- run until done
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 60 do
      JIT.eval h
      if (← JIT.getOutput h 26) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    let mut outLanes : Array (BitVec 64) := #[]
    for i in [0:25] do
      outLanes := outLanes.push (BitVec.ofNat 64 (← JIT.getOutput h i.toUInt32).toNat)
    pure (done, cyc, outLanes)
  -- test 1: keccakF(all-zero state)
  let (done, cyc, got) ← run (Array.replicate 25 0#64)
  let exp := keccakF State.empty
  let ok := got == exp
  IO.println s!"F1600(0): done={done} cyc={cyc} match={ok}"
  if !ok then
    IO.println s!"  got[0]={got.getD 0 0} exp[0]={exp.getD 0 0}"
    IO.println s!"  got[1]={got.getD 1 0} exp[1]={exp.getD 1 0}"
  -- test 2: a nonzero state
  let st2 := (Array.range 25).map (fun i => BitVec.ofNat 64 (i * 0x0101010101010101))
  let (d2, c2, g2) ← run st2
  let e2 := keccakF st2
  let ok2 := g2 == e2
  IO.println s!"F1600(seq): done={d2} cyc={c2} match={ok2}"
  JIT.destroy h
  if ok && ok2 then IO.println "ALL PASS" else IO.Process.exit 1
