/-
  JIT co-sim test for IP.Crypto.Rfc6979HW (`rfc6979HW`) — real-cycle
  validation of the RFC 6979 nonce FSM.

  The design targets secp256k1 (group order `Secp256k1ECDSA.n`) with
  HMAC-SHA256, NOT P-256, so the RFC 6979 A.2.5 (P-256) vectors do not apply.
  The private key `d` is an elaboration-time constant, hence one `#sim` top
  per key.  The nonce is checked against the pure-data `Rfc6979.rfc6979` and,
  where a published value is known, against it too (the widely used
  secp256k1 / SHA-256 RFC 6979 vectors, z = SHA-256(message)).  An extra pass
  feeds a hash `z ≥ n` (the `z mod n` step) and compares with the reference.
-/
import Sparkle
import IP.Crypto.SHA256
import IP.Crypto.Rfc6979
import IP.Crypto.Rfc6979HW
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Rfc6979HW

namespace Sparkle.Tests.IP.Crypto.Rfc6979JITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- d = 1 -/
def nonceD1
    (start : Signal defaultDomain Bool)
    (z : Signal defaultDomain (BitVec 256)) : NonceOut defaultDomain :=
  rfc6979HW (BitVec.ofNat 256 1) start z

/-- d = n - 1 -/
def nonceDn1
    (start : Signal defaultDomain Bool)
    (z : Signal defaultDomain (BitVec 256)) : NonceOut defaultDomain :=
  rfc6979HW (BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140) start z

#sim nonceD1
#sim nonceDn1

private def hexNat (s : String) : Nat :=
  s.foldl (fun acc c =>
    acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0

private def hex (v : Nat) : String :=
  let s := (Nat.toDigits 16 v).asString
  "".pushn '0' (64 - s.length) ++ s

private def zOf (msg : String) : Nat := Id.run do
  let mut v : Nat := 0
  for w in Sparkle.IP.Crypto.SHA256.sha256OfBytes msg.toUTF8.toList.toArray do
    v := (v <<< 32) ||| w.toNat
  return v

structure Case where
  label : String
  d : Nat
  z : Nat
  pub : Option Nat

private def checkCase (c : Case) (got : Nat) (cyc : Nat) : IO Bool := do
  let ref := Sparkle.IP.Crypto.Rfc6979.rfc6979 c.d c.z
  let pubOk := match c.pub with | some p => got == p && ref == p | none => true
  if got == ref && pubOk then
    IO.println s!"  ✓ {c.label}: k = {hex got}  ({cyc} cycles)"
    return true
  IO.println s!"  ✗ {c.label}: HW {hex got} ≠ ref {hex ref}"
  if let some p := c.pub then IO.println s!"      published {hex p}"
  return false

def cases1 : List Case :=
  [ { label := "d=1, 'Satoshi Nakamoto'", d := 1, z := zOf "Satoshi Nakamoto"
    , pub := some (hexNat "8f8a276c19f4149656b280621e358cce24f5f52542772691ee69063b74f15d15") }
  , { label := "d=1, 'All those moments…'", d := 1
    , z := zOf "All those moments will be lost in time, like tears in rain. Time to die..."
    , pub := some (hexNat "38aa22d72376b4dbc472e06c3ba403ee0a394da63fc58d88686c611aba98d6b3") }
  , { label := "d=1, z = 2^256-1 (z ≥ n, reduced mod n)", d := 1
    , z := 2 ^ 256 - 1, pub := none }
  , { label := "d=1, z = 0", d := 1, z := 0, pub := none } ]

def cases2 : List Case :=
  [ { label := "d=n-1, 'Satoshi Nakamoto'", d := hexNat "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140"
    , z := zOf "Satoshi Nakamoto"
    , pub := some (hexNat "33a19b60e25fb6f4435af53a3d42d493644827367e6453928554f43e49aa6f90") }
  , { label := "d=n-1, z = n + 5 (reduced mod n)"
    , d := hexNat "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140"
    , z := hexNat "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364146"
    , pub := none } ]

def main : IO Unit := do
  IO.println "=== RFC 6979 rfc6979HW (secp256k1, SHA-256) — JIT real-cycle co-sim ==="
  (← IO.getStdout).flush
  let mut ok := true
  -- d = 1
  do
    let sim ← nonceD1.Sim.load
    sim.reset
    for c in cases1 do
      let mk (s : Bool) : nonceD1.Sim.SimInput :=
        { _gen_start := if s then 1#1 else 0#1, _gen_z := BitVec.ofNat 256 c.z }
      sim.step (mk true)
      let mut out ← sim.read
      let mut cyc := 1
      while out.done == 0#1 && cyc < 6000 do
        sim.step (mk false)
        out ← sim.read
        cyc := cyc + 1
      if out.done == 0#1 then
        IO.println s!"  ✗ {c.label}: no done within 6000 cycles"
        ok := false
      else
        ok := (← checkCase c out.k.toNat cyc) && ok
    sim.destroy
  -- d = n - 1
  do
    let sim ← nonceDn1.Sim.load
    sim.reset
    for c in cases2 do
      let mk (s : Bool) : nonceDn1.Sim.SimInput :=
        { _gen_start := if s then 1#1 else 0#1, _gen_z := BitVec.ofNat 256 c.z }
      sim.step (mk true)
      let mut out ← sim.read
      let mut cyc := 1
      while out.done == 0#1 && cyc < 6000 do
        sim.step (mk false)
        out ← sim.read
        cyc := cyc + 1
      if out.done == 0#1 then
        IO.println s!"  ✗ {c.label}: no done within 6000 cycles"
        ok := false
      else
        ok := (← checkCase c out.k.toNat cyc) && ok
    sim.destroy
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Rfc6979JITTest
