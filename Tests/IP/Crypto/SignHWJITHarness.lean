/-
  Shared driver for the signer-core JIT co-sims (secp256k1 `signCore`,
  P-256 `p256SignCore`).

  Both tops have the same port layout once `#sim` lowers them to C
  (inputs/outputs wider than 64 bits are split into 32-bit words, low
  word first):

      inputs : start = 0 · d = 1..8 · k = 9..16 · z = 17..24
      outputs: rOut = 0..7 · sOut = 8..15 · done = 16

  Protocol: reset, hold d/k/z, pulse `start` for one cycle, tick until
  `done`, read r/s at the `done` cycle and again a few cycles later (the
  result must stay put), and report the cycle count.
-/
import Sparkle.Core.JIT

namespace Sparkle.Tests.IP.Crypto.SignHWJIT

open Sparkle.Core.JIT

def startIdx : UInt32 := 0
def dBase : Nat := 1
def kBase : Nat := 9
def zBase : Nat := 17
def rBase : Nat := 0
def sBase : Nat := 8
def doneIdx : UInt32 := 16

structure Result where
  r : Nat
  s : Nat
  /-- cycles from the start pulse to the first `done` -/
  cycles : Nat
  done : Bool
  /-- r/s read again 8 cycles after `done` -/
  rLate : Nat
  sLate : Nat

private def setWide (h : JITHandle) (base v : Nat) : IO Unit := do
  for j in [0:8] do
    JIT.setInput h (base + j).toUInt32 (UInt64.ofNat ((v >>> (32 * j)) &&& 0xFFFFFFFF))

private def getWide (h : JITHandle) (base : Nat) : IO Nat := do
  let mut acc : Nat := 0
  for j in [0:8] do
    acc := acc ||| ((← JIT.getOutput h (base + j).toUInt32).toNat <<< (32 * j))
  pure acc

/-- Drive one signature; `cap` bounds the cycles waited for `done`. -/
def runSign (h : JITHandle) (d k z cap : Nat) : IO Result := do
  JIT.reset h
  setWide h dBase d; setWide h kBase k; setWide h zBase z
  JIT.setInput h startIdx 1
  JIT.eval h
  JIT.tick h
  JIT.setInput h startIdx 0
  let mut cyc := 0
  let mut done := false
  while (!done) && cyc < cap do
    JIT.eval h
    if (← JIT.getOutput h doneIdx) != 0 then
      done := true
    else
      JIT.tick h
      cyc := cyc + 1
  let r ← getWide h rBase
  let s ← getWide h sBase
  for _ in [0:8] do JIT.tick h
  JIT.eval h
  let rLate ← getWide h rBase
  let sLate ← getWide h sBase
  pure { r, s, cycles := cyc, done, rLate, sLate }

/-- Compare one run to the reference; print a line; return success. -/
def check (label : String) (res : Result) (ref : Option (Nat × Nat)) (cap : Nat) : IO Bool := do
  match ref with
  | none => IO.println s!"  ✗ {label}: reference returned none"; pure false
  | some (er, es) =>
    if !res.done then
      IO.println s!"  ✗ {label}: no done within {cap} cycles"; pure false
    else if res.r == er && res.s == es && res.rLate == er && res.sLate == es then
      IO.println s!"  ✓ {label}: HW (r,s) = reference after {res.cycles} cycles"; pure true
    else
      IO.println s!"  ✗ {label}: cycles={res.cycles}\n      got r={res.r}\n          s={res.s}\n      exp r={er}\n          s={es}\n      late r={res.rLate} s={res.sLate}"
      pure false

end Sparkle.Tests.IP.Crypto.SignHWJIT

/-! ### UART helpers (8-N-1, LSB first) shared by the UART-top co-sims. -/

namespace Uart

/-- Decode 8-N-1 bytes (mid-bit sampling) from a per-cycle TX line trace. -/
def decode (samples : Array Bool) (cpb : Nat) (want : Nat) : Array Nat := Id.run do
  let mut bytes : Array Nat := #[]
  let mut pos := 0
  while bytes.size < want && pos + cpb * 10 < samples.size do
    if samples[pos]! && !samples[pos+1]! then
      let start := pos + 1
      let mut byte := 0
      for b in [0:8] do
        if samples[start + cpb * (b + 1) + cpb / 2]! then byte := byte ||| (1 <<< b)
      bytes := bytes.push byte
      pos := start + cpb * 9
    else pos := pos + 1
  return bytes

/-- Big-endian bytes → Nat. -/
def beNat (bs : Array Nat) (off len : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:len] do v := (v <<< 8) ||| bs[off + i]!
  return v

end Uart
