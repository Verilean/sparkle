/-
  Dataflow + synth test for IP.Crypto.P256SignDemo.p256SignCore —
  the P-256 ECDSA signer core.

  Behavioural: `coreSpec` reproduces the EXACT computation the wired
  engines perform (k·G in Jacobian coords via the a=-3 point-op /
  ladder, Zinv/Zinv²/x1 mod p, r = x1 mod n, kInv mod n, r·d, zrd,
  s), each engine replaced by its pure-data reference, and
  cross-checks the resulting (r,s) against the independent
  `P256ECDSA.sign d k z`.  (Full closed-loop `Signal.val` co-sim of
  the ~1.8M-cycle stack hangs the interpreter, issue #95 — so the
  dataflow is checked at the pure-data level and the Signal circuit
  is proven to lower by `#synthesizeVerilog`.)

  Synth: `#synthesizeVerilog` on the core's `rOut`.
-/
import Sparkle
import IP.Crypto.Proof.P256Field
import IP.Crypto.Proof.P256ECDSA
import IP.Crypto.Proof.P256PointJac
import IP.Crypto.P256SignDemo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.P256SignDemo

namespace Sparkle.Tests.IP.Crypto.P256SignDemoTest

abbrev D := defaultDomain

open Sparkle.IP.Crypto.P256PointJac (Point mulScalar generator)

/-- Pure-data model of the sign core's dataflow — mirrors
    `P256ECDSAHW.signHW`'s register updates over the P-256 engines. -/
private def coreSpec (d k z : Nat) : Nat × Nat :=
  let p := Sparkle.IP.Crypto.P256Field.p
  let n := Sparkle.IP.Crypto.P256ECDSA.n
  let P : Point := mulScalar k generator      -- k·G (Jacobian, a=-3)
  let X := P.x
  let Z := P.z
  let zinv := Sparkle.IP.Crypto.P256Field.inv Z
  let zinv2 := (zinv * zinv) % p
  let x1 := (X * zinv2) % p
  let r := x1 % n
  let kinv := Sparkle.IP.Crypto.P256ECDSA.invModN k
  let rd := (r * d) % n
  let zrd := (z + rd) % n
  let s := (kinv * zrd) % n
  (r, s)

def main : IO Unit := do
  IO.println "=== P-256 ECDSA signer core — dataflow check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let cases : List (Nat × Nat × Nat) :=
    [ (0x1, 0x2, 0x3)
    , (0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721,
       0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE,
       0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF)
    , (0xDEADBEEF, 0xCAFEBABE, 0x1234567890ABCDEF) ]

  for (d, k, z) in cases do
    let (r, s) := coreSpec d k z
    match Sparkle.IP.Crypto.P256ECDSA.sign d k z with
    | some (rRef, sRef) =>
      if r == rRef && s == sRef then
        IO.println s!"  ✓ P-256 core dataflow matches sign (r={rRef})"
      else
        IO.println s!"  ✗ MISMATCH: core (r={r}, s={s}) vs sign (r={rRef}, s={sRef})"
        ok := false
    | none =>
      IO.println s!"  ✗ reference sign returned none for d={d}"
      ok := false

  IO.println "  · one signature ≈ 1.8 M cycles ≈ 67 ms @ 27 MHz"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.P256SignDemoTest

section SynthesisChecks
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.P256SignDemo

set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

/-- Synth the full closed-loop P-256 signer core. -/
private def synth_p256SignCore
    (start : Signal defaultDomain Bool)
    (d k z : Signal defaultDomain (BitVec 256)) :
    Signal defaultDomain (BitVec 256) :=
  (p256SignCore start d k z).rOut

#synthesizeVerilog synth_p256SignCore

end SynthesisChecks
