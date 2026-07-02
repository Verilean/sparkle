/-
  Sim + synth test for IP.Crypto.Secp256k1ScalarMulHW.scalarMulHW —
  the Montgomery-ladder scalar-mul FSM that drives the Jacobian
  point-op engine (which drives the field multiplier).

  Behavioural: the FSM realises a Montgomery ladder with an
  ∞-flag correction at the ladder level.  This test re-executes
  that EXACT ladder logic as a pure-data model (`ladderSpec`
  below — a faithful transcription of the register-update muxes
  in `scalarMulHW`) and cross-validates k·P against the
  independent reference `Secp256k1PointJac.mulScalar` for several
  scalars.  This de-risks the part that is easy to get wrong: the
  R0/R1 write routing, the bit-dependent swap, and the ∞
  handling.

  (The cycle-accurate Signal circuit is validated to *synthesize*
  by the `#synthesizeVerilog` checks below.  Full closed-loop
  cycle co-sim — tying `scalarMulHW`'s handshake to a real
  point-op + `mulHW` via `Signal.loop` — is left to the JIT-backed
  harness, as for the point-op test.)

  Known edge: the ladder uses the *generic* add branch, so the
  measure-zero near-order scalar k = n−1 (and n itself) are not
  handled; a real signer's nonce k ∈ [1, n−1] never hits these
  (probability ~2⁻²⁵⁶).  The test avoids them.

  Synth: `#synthesizeVerilog` on xOut and done.
-/
import Sparkle
import IP.Crypto.Secp256k1Field
import IP.Crypto.Secp256k1FieldHW
import IP.Crypto.Secp256k1PointJac
import IP.Crypto.Secp256k1ScalarMulHW

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Secp256k1ScalarMulHW

namespace Sparkle.Tests.IP.Crypto.Secp256k1ScalarMulHWTest

abbrev D := defaultDomain

open Sparkle.IP.Crypto.Secp256k1PointJac (Point double add mulScalar generator toAffine)

/-- Pure-data model of the ladder's per-bit state transition,
    EXACTLY as `scalarMulHW` routes it.  Carries (R0, R1, r0Inf).

    Per bit i:
      addSum = if r0Inf then R1 else add R0 R1        -- ∞ correction
      bit=1: R0 := addSum ; R1 := double R1 ; clear r0Inf
      bit=0: R1 := addSum ; R0 := double R0

    Matches the HW: the add always targets the "R0+R1" sum (with the
    ∞ mux), written into R0 (bit=1) or R1 (bit=0); the double targets
    (bit ? R1 : R0), written into R1 (bit=1) or R0 (bit=0). -/
private def ladderStep (bit : Bool) (r0 r1 : Point) (r0Inf : Bool) :
    Point × Point × Bool :=
  let addSum := if r0Inf then r1 else add r0 r1
  if bit then
    -- R0 := addSum ; R1 := double R1 ; r0Inf cleared
    (addSum, double r1, false)
  else
    -- R1 := addSum ; R0 := double R0 ; r0Inf unchanged
    (double r0, addSum, r0Inf)

/-- Run the ladder spec over 256 MSB-first bits of `k` on base `P`.
    Returns R0 = k·P (Jacobian). -/
private def ladderSpec (k : Nat) (P : Point) : Point := Id.run do
  let mut r0 : Point := ⟨0, 0, 0, true⟩   -- ∞ sentinel (matches HW start)
  let mut r1 : Point := P
  let mut inf := true
  let mut i : Nat := 256
  while i > 0 do
    i := i - 1
    let bit := (k / (2 ^ i)) % 2 == 1
    let (nr0, nr1, ninf) := ladderStep bit r0 r1 inf
    r0 := nr0; r1 := nr1; inf := ninf
  return r0

/-- Affine-normalise for comparison (Jacobian reps are not unique). -/
private def affOf (P : Point) : Nat × Nat := toAffine P

def main : IO Unit := do
  IO.println "=== secp256k1 Montgomery-ladder scalar-mul FSM check ==="
  (← IO.getStdout).flush
  let mut ok := true

  let G := generator

  -- Cross-check ladderSpec vs the double-and-add reference mulScalar.
  let scalars : List Nat := [1, 2, 3, 7, 8, 12345, 0xDEADBEEF,
    0x1111111111111111111111111111111111111111111111111111111111111111]
  for kk in scalars do
    let viaLadder := affOf (ladderSpec kk G)
    let viaRef    := affOf (mulScalar kk G)
    if viaLadder = viaRef then
      IO.println s!"  ✓ ladder k={kk} matches mulScalar"
    else
      IO.println s!"  ✗ ladder k={kk}: ladder={viaLadder} ref={viaRef}"
      ok := false

  -- A representative "random-ish" 256-bit scalar (not near the order).
  let kbig := 0x7C0FEEDF00DBABE5C0FFEE1234567890ABCDEF0011223344556677889900AABB
  if affOf (ladderSpec kbig G) = affOf (mulScalar kbig G) then
    IO.println "  ✓ ladder large-scalar matches mulScalar"
  else
    IO.println "  ✗ ladder large-scalar mismatch"
    ok := false

  IO.println s!"  · cycle cost per scalar-mul (bit-serial mulHW):"
  IO.println s!"      256 bits · (add 16 + double 7) muls · ~260 cyc/mul"
  IO.println s!"      ≈ {256 * (16 + 7) * 260} cycles"

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.Secp256k1ScalarMulHWTest

section SynthesisChecks
open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.Secp256k1ScalarMulHW

private def synth_secp256k1ScalarMulX
    (start : Signal defaultDomain Bool)
    (k : Signal defaultDomain (BitVec 256))
    (px py pz : Signal defaultDomain (BitVec 256))
    (poResX poResY poResZ : Signal defaultDomain (BitVec 256))
    (poResDone : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 256) :=
  (scalarMulHW start k px py pz poResX poResY poResZ poResDone).xOut

#synthesizeVerilog synth_secp256k1ScalarMulX

private def synth_secp256k1ScalarMulDone
    (start : Signal defaultDomain Bool)
    (k : Signal defaultDomain (BitVec 256))
    (px py pz : Signal defaultDomain (BitVec 256))
    (poResX poResY poResZ : Signal defaultDomain (BitVec 256))
    (poResDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (scalarMulHW start k px py pz poResX poResY poResZ poResDone).done

#synthesizeVerilog synth_secp256k1ScalarMulDone

private def synth_secp256k1ScalarMulPoStart
    (start : Signal defaultDomain Bool)
    (k : Signal defaultDomain (BitVec 256))
    (px py pz : Signal defaultDomain (BitVec 256))
    (poResX poResY poResZ : Signal defaultDomain (BitVec 256))
    (poResDone : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  (scalarMulHW start k px py pz poResX poResY poResZ poResDone).poStart

#synthesizeVerilog synth_secp256k1ScalarMulPoStart

end SynthesisChecks
