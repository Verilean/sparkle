import Sparkle.Core.JIT
import IP.Crypto.Rfc6979
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Rfc6979 (signDeterministic)

-- signZTop ports (256-bit values split into 8 LE 32-bit words):
--   in  start=0, z = slots 1..8.   out rOut = 0..7, sOut = 8..15, done = 16.
def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/signZTop_jit.c"
  let dKey : Nat := 12345
  let read256 (base : Nat) : IO Nat := do
    let mut v := 0
    for w in [0:8] do
      let word := (← JIT.getOutput h (base + w).toUInt32).toNat &&& 0xFFFFFFFF
      v := v ||| (word <<< (32*w))
    pure v
  let check (z : Nat) : IO Bool := do
    JIT.reset h
    for w in [0:8] do
      JIT.setInput h (1+w).toUInt32 (UInt64.ofNat ((z >>> (32*w)) &&& 0xFFFFFFFF))
    JIT.setInput h 0 1; JIT.eval h; JIT.tick h; JIT.setInput h 0 0
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 5000000 do
      JIT.eval h
      if (← JIT.getOutput h 16) != 0 then done := true
      JIT.tick h; cyc := cyc + 1
    JIT.eval h
    let r ← read256 0
    let s ← read256 8
    match signDeterministic dKey z with
    | some (er, es) =>
      let ok := done && r == er && s == es
      IO.println s!"  z={z}: done={done} cyc={cyc} {if ok then "PASS" else s!"FAIL (r={r} exp {er} / s={s} exp {es})"}"
      pure ok
    | none => IO.println s!"  z={z}: golden=none"; pure false
  let mut pass := 0; let mut total := 0
  for z in [9, 123456789] do
    if (← check z) then pass := pass + 1
    total := total + 1
  IO.println s!"{pass}/{total} PASS"
  JIT.destroy h
  if pass != total then IO.Process.exit 1
