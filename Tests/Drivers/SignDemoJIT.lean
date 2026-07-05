import Sparkle.Core.JIT
import IP.Crypto.Secp256k1ECDSA
open Sparkle.Core.JIT
-- demoTop ports: uartRx=0 bitDiv=1 ; out uartTx=0 signDone=1
-- UART 8-N-1, bitDiv=3 → 4 cycles/bit.  Host sends 64 bytes k‖z (MSB-first),
-- device replies 64 bytes r‖s.  Baked key d = 12345.
def BITDIV : Nat := 15
def CPB : Nat := BITDIV + 1        -- cycles per bit
def dKey : Nat := 12345

def main : IO Unit := do
  let h ← JIT.compileAndLoad ".lake/build/gen/sim/demoTop_jit.c"
  JIT.reset h
  JIT.setInput h 1 (UInt64.ofNat BITDIV)     -- bitDiv
  let mutTx : IO Bool := do pure ((← JIT.getOutput h 0) != 0)
  -- drive uartRx for one cycle, return the sampled tx bit
  let stepRx (rxBit : Bool) : IO Bool := do
    JIT.setInput h 0 (if rxBit then 1 else 0)
    JIT.eval h
    let t ← mutTx
    JIT.tick h
    pure t
  -- idle a while
  for _ in [0:20] do let _ ← stepRx true
  -- send one 8-N-1 byte (LSB first)
  let sendByte (b : Nat) : IO Unit := do
    for _ in [0:CPB] do let _ ← stepRx false          -- start bit
    for i in [0:8] do
      let bit := (b >>> i) &&& 1 == 1
      for _ in [0:CPB] do let _ ← stepRx bit
    for _ in [0:CPB] do let _ ← stepRx true           -- stop bit
  let sendWideMSB (v : Nat) : IO Unit := do
    for i in [0:32] do sendByte ((v >>> (8*(31-i))) &&& 0xFF)
  let k := 7; let z := 42
  -- send k then z (each 32 bytes MSB-first)
  sendWideMSB k
  sendWideMSB z
  IO.println "sent 64 bytes; sampling TX line..."
  -- Sample the TX line every cycle through signing + reply, decode offline.
  let mut samples : Array Bool := Array.mkEmpty 400000
  for _ in [0:320000] do samples := samples.push (← stepRx true)
  -- offline 8-N-1 decode (bit mid-point sampling).
  let mut bytes : Array Nat := #[]
  let mut pos := 0
  while bytes.size < 64 && pos + CPB*10 < samples.size do
    if samples[pos]! && !samples[pos+1]! then          -- falling edge → start bit at i+1
      let start := pos + 1
      let mut byte := 0
      for b in [0:8] do
        let idx := start + CPB*(b+1) + CPB/2       -- mid of data bit b
        if samples[idx]! then byte := byte ||| (1 <<< b)
      bytes := bytes.push byte
      pos := start + CPB*9                             -- into the stop bit (high); resync on next falling edge
    else pos := pos + 1
  IO.println s!"received {bytes.size} bytes"
  if bytes.size == 64 then
    let mut r := 0; let mut s := 0
    for i in [0:32] do r := (r <<< 8) ||| bytes[i]!
    for i in [0:32] do s := (s <<< 8) ||| bytes[32+i]!
    match Sparkle.IP.Crypto.Secp256k1ECDSA.sign dKey k z with
    | some (er, es) => IO.println s!"UART demo d={dKey} k={k} z={z}: {if (r,s)==(er,es) then "PASS" else s!"FAIL\n got r={r}\n s={s}\n exp r={er}\n s={es}"}"
    | none => IO.println "reference none"
  JIT.destroy h
