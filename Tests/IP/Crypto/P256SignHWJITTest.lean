/-
  JIT co-sim of the generated hardware for `P256SignDemo.p256SignCore`
  (P-256 ECDSA signer core): drive (d, k, z), wait for `done`, and
  compare (r, s) with the pure-data `P256ECDSA.sign d k z`.

  `P256SignDemoTest` only checks the pure-data dataflow and that the
  core synthesizes; this checks what the lowered hardware computes.
-/
import IP.Crypto.Proof.P256ECDSA
import IP.Crypto.P256SignDemo
import Sparkle.Compiler.Elab
import Tests.IP.Crypto.SignHWJITHarness

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.P256SignDemo
open Sparkle.Tests.IP.Crypto.SignHWJIT

namespace Sparkle.Tests.IP.Crypto.P256SignHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- `#sim`-able top: the real signer core, outputs rOut / sOut / done. -/
def p256SignCoreTop
    (start : Signal defaultDomain Bool)
    (d k z : Signal defaultDomain (BitVec 256)) : SignCoreOut defaultDomain :=
  p256SignCore start d k z

#sim p256SignCoreTop

open p256SignCoreTop.Sim

/-- Cycle cap per signature (a full 256-bit signature is ≈ 1.8 M cycles). -/
def cap : Nat := 4000000

def main : IO Unit := do
  IO.println "=== P-256 p256SignCore — JIT co-sim vs P256ECDSA.sign ==="
  (← IO.getStdout).flush
  let sim ← load
  let mut ok := true
  -- (label, d, k, z): the first and last come from P256SignDemoTest; the
  -- middle one is RFC 6979 A.2.5 (P-256, SHA-256, "sample") — d, the
  -- RFC's k, and z = SHA-256("sample") — whose published (r, s) is also
  -- checked against the pure-data reference below.
  let cases : List (String × Nat × Nat × Nat) :=
    [ ("small d=1 k=2 z=3", 0x1, 0x2, 0x3)
    , ("RFC 6979 A.2.5 sample",
       0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721,
       0xA6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60,
       0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF)
    , ("full-width vector",
       0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721,
       0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE,
       0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF) ]
  -- RFC 6979 A.2.5 published signature (guards the reference itself).
  match Sparkle.IP.Crypto.P256ECDSA.sign
      0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
      0xA6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60
      0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF with
  | some (r, s) =>
    if r == 0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716
        && s == 0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8 then
      IO.println "  ✓ reference matches RFC 6979 A.2.5 published (r, s)"
    else
      IO.println "  ✗ reference disagrees with RFC 6979 A.2.5 published (r, s)"
      ok := false
  | none => IO.println "  ✗ reference none on RFC vector"; ok := false
  for (label, d, k, z) in cases do
    let res ← runSign sim.handle d k z cap
    let good ← check label res (Sparkle.IP.Crypto.P256ECDSA.sign d k z) cap
    if !good then ok := false
  sim.destroy
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.P256SignHWJITTest
