import Sparkle.Core.JIT
import IP.Crypto.Rfc6979
open Sparkle.Core.JIT
open Sparkle.IP.Crypto.Rfc6979 (signDeterministic)

-- signZDemoJit ports: in uartRx=0, bitDiv=1 ; out uartTx=0, signDone=1.
-- 8-N-1 UART; host sends 32-byte z (MSB first); device replies 64 bytes r‖s.
def BITDIV : Nat := 15
def CPB : Nat := BITDIV + 1
def dKey : Nat := 12345

def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/signZDemoJit_jit.c"
  JIT.setInput h 1 (UInt64.ofNat BITDIV)
  let stepRx (rxBit : Bool) : IO Bool := do
    JIT.setInput h 0 (if rxBit then 1 else 0)
    JIT.eval h
    let t := (← JIT.getOutput h 0) != 0
    JIT.tick h
    pure t
  let doneNow : IO Bool := do pure ((← JIT.getOutput h 1) != 0)
  let sendByte (b : Nat) : IO Unit := do
    for _ in [0:CPB] do let _ ← stepRx false
    for i in [0:8] do
      let bit := (b >>> i) &&& 1 == 1
      for _ in [0:CPB] do let _ ← stepRx bit
    for _ in [0:CPB] do let _ ← stepRx true
  let check (z : Nat) : IO Bool := do
    JIT.reset h
    for _ in [0:20] do let _ ← stepRx true
    for i in [0:32] do sendByte ((z >>> (8*(31-i))) &&& 0xFF)   -- 32 bytes MSB-first
    let mut cyc := 0; let mut done := false
    while (!done) && cyc < 2000000 do
      let _ ← stepRx true
      if (← doneNow) then done := true
      cyc := cyc + 1
    let mut samples : Array Bool := Array.mkEmpty 90000
    for _ in [0:90000] do samples := samples.push (← stepRx true)
    let mut bytes : Array Nat := #[]
    let mut pos := 0
    while bytes.size < 64 && pos + CPB*10 < samples.size do
      if samples[pos]! && !samples[pos+1]! then
        let start := pos + 1
        let mut byte := 0
        for b in [0:8] do
          let idx := start + CPB*(b+1) + CPB/2
          if samples[idx]! then byte := byte ||| (1 <<< b)
        bytes := bytes.push byte
        pos := start + CPB*9
      else pos := pos + 1
    match signDeterministic dKey z with
    | some (er, es) =>
      if bytes.size == 64 then
        let mut r := 0; let mut s := 0
        for i in [0:32] do r := (r <<< 8) ||| bytes[i]!
        for i in [0:32] do s := (s <<< 8) ||| bytes[32+i]!
        let ok := done && r == er && s == es
        IO.println s!"  z={z}: done={done} rxCyc={cyc} {if ok then "PASS" else s!"FAIL r={r}/{er} s={s}/{es}"}"
        pure ok
      else IO.println s!"  z={z}: got {bytes.size} TX bytes — FAIL"; pure false
    | none => IO.println "  golden=none"; pure false
  let ok ← check 123456789
  JIT.destroy h
  if !ok then IO.Process.exit 1 else IO.println "1/1 PASS"
