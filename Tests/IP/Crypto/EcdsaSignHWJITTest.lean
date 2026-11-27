/-
  JIT co-sim of the generated hardware for `EcdsaSignDemo.signCore`
  (secp256k1 ECDSA signer core): drive (d, k, z), wait for `done`, and
  compare (r, s) with the pure-data `Secp256k1ECDSA.sign d k z`.

  `EcdsaSignDemoTest` only checks the pure-data dataflow and that the
  core synthesizes; this checks what the lowered hardware computes.
-/
import IP.Crypto.Proof.Secp256k1ECDSA
import IP.Crypto.EcdsaSignDemo
import Sparkle.Compiler.Elab
import Tests.IP.Crypto.SignHWJITHarness

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignDemo
open Sparkle.Tests.IP.Crypto.SignHWJIT

namespace Sparkle.Tests.IP.Crypto.EcdsaSignHWJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- `#sim`-able top: the real signer core, outputs rOut / sOut / done. -/
def ecdsaSignCoreTop
    (start : Signal defaultDomain Bool)
    (d k z : Signal defaultDomain (BitVec 256)) : SignCoreOut defaultDomain :=
  signCore start d k z

#sim ecdsaSignCoreTop

open ecdsaSignCoreTop.Sim

/-- Cycle cap per signature (a full 256-bit signature is ≈ 1.8 M cycles). -/
def cap : Nat := 4000000

def main : IO Unit := do
  IO.println "=== secp256k1 signCore — JIT co-sim vs Secp256k1ECDSA.sign ==="
  (← IO.getStdout).flush
  let sim ← load
  let mut ok := true
  -- (label, d, k, z): the first two come from EcdsaSignDemoTest; the
  -- second is the SEC1 / RFC 6979 style vector with full-width scalars.
  let cases : List (String × Nat × Nat × Nat) :=
    [ ("small d=1 k=2 z=3", 0x1, 0x2, 0x3)
    , ("full-width vector",
       0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721,
       0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE,
       0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF) ]
  for (label, d, k, z) in cases do
    let res ← runSign sim.handle d k z cap
    let good ← check label res (Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z) cap
    if !good then ok := false
  sim.destroy
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.EcdsaSignHWJITTest
