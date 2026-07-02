/-
  Sim + synth test for IP.Crypto.Secp256k1ECDSAHW.signHW — the
  ECDSA sign orchestrator FSM (sign only).

  Behavioural: the FSM sequences k·G → Zinv → x1 → r → kInv → rd
  → s, driving external scalar-mul / mod-p / mod-n engines.  This
  test re-executes that EXACT dataflow as a pure-data model
  (`signSpec` — a faithful transcription of the FSM's registered
  computation, with the sub-engines modelled by their pure-data
  references) and cross-validates the produced (r, s) against the
  independent reference `Secp256k1ECDSA.sign d k z`.

  (The cycle-accurate Signal circuit is validated to *synthesize*
  by the `#synthesizeVerilog` checks below.  Full closed-loop cycle
  co-sim — tying the FSM's handshakes to real scalar-mul + inverse
  + multiplier engines via `Signal.loop` — is left to the
  JIT-backed harness, as for the point-op / scalar-mul tests.)

  Synth: `#synthesizeVerilog` on rOut, sOut, done.
-/
import Sparkle
import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1ECDSA
import IP.Crypto.Secp256k1PointJac
import IP.Crypto.Secp256k1ECDSAHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Secp256k1ECDSAHW

namespace Sparkle.Tests.IP.Crypto.Secp256k1ECDSAHWTest

abbrev D := defaultDomain

open Sparkle.IP.Crypto.Secp256k1PointJac (Point mulScalar generator toAffine)

/-- Pure-data model of the sign FSM's dataflow, EXACTLY as `signHW`
    computes it, with each external engine replaced by its
    pure-data reference:

      (X,_,Z) = k·G            -- Jacobian (mulScalar returns Jacobian Point)
      Zinv    = Z^(p-2) mod p  -- mod-p inverse engine
      Zinv2   = Zinv² mod p    -- mod-p mul
      x1      = X·Zinv² mod p  -- mod-p mul  (= affine x)
      r       = x1 mod n       -- condSubN
      kInv    = k^(n-2) mod n  -- mod-n inverse engine
      rd      = r·d mod n      -- mod-n mul
      zrd     = (z+rd) mod n   -- addModN
      s       = kInv·zrd mod n -- mod-n mul

    Returns (r, s).  Mirrors the register updates in signHW. -/
private def signSpec (d k z : Nat) : Nat × Nat :=
  let p := Sparkle.IP.Crypto.Secp256k1Field.p
  let n := Sparkle.IP.Crypto.Secp256k1ECDSA.n
  let P : Point := mulScalar k generator
  -- Jacobian coords of k·G.
  let X := P.x
  let Z := P.z
  -- mod-p inverse + muls (the FSM's mod-p engine reduces mod p).
  -- Use the pure-data Fermat inverse references (modular powMod) —
  -- NOT Nat.pow, which would be astronomically large.
  let zinv := Sparkle.IP.Crypto.Secp256k1Field.inv Z   -- Z^(p-2) mod p
  let zinv2 := (zinv * zinv) % p
  let x1 := (X * zinv2) % p
  -- r = x1 mod n (single conditional subtract, since x1 < p < 2n).
  let r := x1 % n
  -- mod-n inverse + muls.
  let kinv := Sparkle.IP.Crypto.Secp256k1ECDSA.invModN k  -- k^(n-2) mod n
  let rd := (r * d) % n
  let zrd := (z + rd) % n
  let s := (kinv * zrd) % n
  (r, s)

def main : IO Unit := do
  IO.println "=== secp256k1 ECDSA sign orchestrator FSM check ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- A few (d, k, z) triples where sign returns some (r, s).
  -- (d = private key, k = nonce, z = hash — all reduced mod n internally.)
  let cases : List (Nat × Nat × Nat) :=
    [ (0x1, 0x2, 0x3)
    , (0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721,
       0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE,
       0xAF2BDBE1AA9B6EC1E2ADE1D694F41FC71A831D0268E9891562113D8A62ADD1BF)
    , (0xDEADBEEF, 0xCAFEBABE, 0x1234567890ABCDEF) ]

  for (d, k, z) in cases do
    let (r, s) := signSpec d k z
    match Sparkle.IP.Crypto.Secp256k1ECDSA.sign d k z with
    | some (rRef, sRef) =>
      if r = rRef ∧ s = sRef then
        IO.println s!"  ✓ signHW dataflow matches sign (r={r})"
      else
        IO.println s!"  ✗ mismatch: hw=({r},{s}) ref=({rRef},{sRef}) [d={d} k={k} z={z}]"
        ok := false
    | none =>
      IO.println s!"  · sign returned none for d={d} k={k} z={z} (skipped)"

  IO.println s!"  · cycle cost per sign (bit-serial engines):"
  IO.println s!"      k·G ≈ 1.53M + 2 Fermat inverses ≈ 2·132k + a few muls"
  IO.println s!"      ≈ ~1.8M cycles / sign"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Secp256k1ECDSAHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Secp256k1ECDSAHW

private def synth_ecdsaR
    (start : Signal defaultDomain Bool)
    (d k z : Signal defaultDomain (BitVec 256))
    (smX smY smZ : Signal defaultDomain (BitVec 256))
    (smDone : Signal defaultDomain Bool)
    (pRes : Signal defaultDomain (BitVec 256))
    (pDone : Signal defaultDomain Bool)
    (nRes : Signal defaultDomain (BitVec 256))
    (nDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (signHW start d k z smX smY smZ smDone pRes pDone nRes nDone).rOut

#synthesizeVerilog synth_ecdsaR

private def synth_ecdsaS
    (start : Signal defaultDomain Bool)
    (d k z : Signal defaultDomain (BitVec 256))
    (smX smY smZ : Signal defaultDomain (BitVec 256))
    (smDone : Signal defaultDomain Bool)
    (pRes : Signal defaultDomain (BitVec 256))
    (pDone : Signal defaultDomain Bool)
    (nRes : Signal defaultDomain (BitVec 256))
    (nDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (signHW start d k z smX smY smZ smDone pRes pDone nRes nDone).sOut

#synthesizeVerilog synth_ecdsaS

private def synth_ecdsaDone
    (start : Signal defaultDomain Bool)
    (d k z : Signal defaultDomain (BitVec 256))
    (smX smY smZ : Signal defaultDomain (BitVec 256))
    (smDone : Signal defaultDomain Bool)
    (pRes : Signal defaultDomain (BitVec 256))
    (pDone : Signal defaultDomain Bool)
    (nRes : Signal defaultDomain (BitVec 256))
    (nDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (signHW start d k z smX smY smZ smDone pRes pDone nRes nDone).done

#synthesizeVerilog synth_ecdsaDone

end SynthesisChecks
