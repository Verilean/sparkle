/-
  Sim + synth test for IP.Crypto.ModInvHW.modInvHW — the Fermat
  modular-inverse FSM (a^(m-2) mod m by square-and-multiply,
  driving an external field multiplier).

  Behavioural: the FSM realises LSB-first square-and-multiply.
  This test re-executes that EXACT logic as a pure-data model
  (`invSpec` — a faithful transcription of the register-update
  muxes in `modInvHW`, parameterised on the modulus of the wired
  multiplier) and cross-validates against the independent
  references:
    * mod p:  a^(p-2) mod p  ==  Secp256k1Field.inv a
    * mod n:  a^(n-2) mod n  ==  Secp256k1ECDSA.invModN a

  (The cycle-accurate Signal circuit is validated to *synthesize*
  by the `#synthesizeVerilog` checks below.  Full closed-loop cycle
  co-sim is left to the JIT-backed harness, as for the point-op /
  scalar-mul tests.)

  Synth: `#synthesizeVerilog` on result and done.
-/
import Sparkle
import IP.Crypto.Proof.Secp256k1Field
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.ModInvHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.ModInvHW

namespace Sparkle.Tests.IP.Crypto.ModInvHWTest

abbrev D := defaultDomain

/-- Pure-data model of the inverse FSM: LSB-first square-and-multiply
    of `e` over exactly 256 bits, all multiplies reduced mod `m`
    (matching the wired multiplier).  This mirrors `modInvHW`:
    `result` starts at 1, `b` starts at `a`; per bit, if set then
    `result := (result*b) mod m`, then always `b := (b*b) mod m`. -/
private def invSpec (m a e : Nat) : Nat := Id.run do
  let mut result := 1 % m
  let mut b := a % m
  let mut i : Nat := 0
  while i < 256 do
    if (e / (2 ^ i)) % 2 == 1 then
      result := (result * b) % m
    b := (b * b) % m
    i := i + 1
  return result

def main : IO Unit := do
  IO.println "=== secp256k1/order Fermat modular-inverse FSM check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let p := Sparkle.IP.Crypto.Secp256k1Field.p
  let n := Sparkle.IP.Crypto.Secp256k1ECDSA.n

  -- mod p: invSpec must match Secp256k1Field.inv.
  let casesP : List Nat := [2, 3, 7, 123456789, p - 1,
    0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798]
  for a in casesP do
    let hw := invSpec p a (p - 2)
    let ref := Sparkle.IP.Crypto.Secp256k1Field.inv a
    if hw = ref then
      IO.println s!"  ✓ mod p: a^(p-2) matches inv (a={a % p})"
    else
      IO.println s!"  ✗ mod p mismatch: hw={hw} ref={ref} (a={a})"
      ok := false

  -- mod n: invSpec must match Secp256k1ECDSA.invModN.
  let casesN : List Nat := [2, 3, 7, 123456789, n - 1,
    0xDEADBEEF0011223344556677889900AABBCCDDEEFF]
  for a in casesN do
    let hw := invSpec n a (n - 2)
    let ref := Sparkle.IP.Crypto.Secp256k1ECDSA.invModN a
    if hw = ref then
      IO.println s!"  ✓ mod n: a^(n-2) matches invModN (a={a % n})"
    else
      IO.println s!"  ✗ mod n mismatch: hw={hw} ref={ref} (a={a})"
      ok := false

  -- Spot-check the inverse property directly: a * a^(-1) ≡ 1.
  let a := 0x1234567890ABCDEF
  let ainv := invSpec p a (p - 2)
  if (a * ainv) % p = 1 then
    IO.println "  ✓ mod p: a · a⁻¹ ≡ 1"
  else
    IO.println "  ✗ mod p: a · a⁻¹ ≢ 1"
    ok := false

  IO.println s!"  · cycle cost per inverse (bit-serial mulHW):"
  IO.println s!"      256 bits · 2 muls/bit · ~258 cyc/mul ≈ {256 * 2 * 258} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.ModInvHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.ModInvHW

private def synth_modInvResult
    (start : Signal defaultDomain Bool)
    (aIn expBits : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (modInvHW start aIn expBits mulResult mulDone).result

#synthesizeVerilog synth_modInvResult

private def synth_modInvDone
    (start : Signal defaultDomain Bool)
    (aIn expBits : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (modInvHW start aIn expBits mulResult mulDone).done

#synthesizeVerilog synth_modInvDone

private def synth_modInvMulStart
    (start : Signal defaultDomain Bool)
    (aIn expBits : Signal defaultDomain (BitVec 256))
    (mulResult : Signal defaultDomain (BitVec 256))
    (mulDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (modInvHW start aIn expBits mulResult mulDone).mulStart

#synthesizeVerilog synth_modInvMulStart

end SynthesisChecks
