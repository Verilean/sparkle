/-
  Sim + synth test for IP.Crypto.TxPolicy.txPolicyHW.

  The policy engine is combinational and shallow, so unlike the
  deep crypto stacks we CAN co-sim it directly: feed constant
  `recipient` / `value` Signals, sample `policyOk.val` at cycle 0,
  and cross-check against the pure `policyRef` predicate.

  Cases exercise every decision boundary:
    * allowlisted recipient, value under cap        → ok
    * allowlisted recipient, value exactly at cap   → ok  (≤)
    * allowlisted recipient, value one over cap     → reject
    * non-allowlisted recipient, value under cap    → reject
    * each of the four allowlist entries            → ok

  Synth via `#synthesizeVerilog` at the bottom proves the gate
  tree lowers to hardware.
-/
import IP.Crypto.TxPolicy

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.TxPolicy

namespace Sparkle.Tests.IP.Crypto.TxPolicyTest

abbrev D := defaultDomain

/-- Constant Signal. -/
private def constSig {α : Type} (v : α) : Signal D α := ⟨fun _ => v⟩

/-- Sample `policyOk` at cycle 0 for a given (recipient, value). -/
private def evalPolicy (recipient : BitVec 160) (value : BitVec 256) : Bool :=
  (txPolicyHW (constSig recipient) (constSig value)).policyOk.val 0

/-- A non-allowlisted address (all ones). -/
private def badAddr : BitVec 160 := BitVec.allOnes 160

def main : IO Unit := do
  IO.println "=== TxPolicy engine — policy decision check ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- (label, recipient, value, expected)
  let cases : List (String × BitVec 160 × BitVec 256 × Bool) :=
    [ ("allow0 under cap",   allow0, (500000000000000000 : BitVec 256), true)
    , ("allow0 at cap",      allow0, maxValue,                          true)
    , ("allow0 over cap",    allow0, maxValue + 1,                      false)
    , ("allow0 zero value",  allow0, (0 : BitVec 256),                  true)
    , ("allow1 under cap",   allow1, (1 : BitVec 256),                  true)
    , ("allow2 under cap",   allow2, (1 : BitVec 256),                  true)
    , ("allow3 at cap",      allow3, maxValue,                          true)
    , ("bad addr under cap", badAddr, (1 : BitVec 256),                 false)
    , ("bad addr zero",      badAddr, (0 : BitVec 256),                 false) ]

  for (label, recipient, value, expected) in cases do
    let hw  := evalPolicy recipient value
    let ref := policyRef recipient value
    -- HW must match both the pure reference AND the hand-expected value.
    if hw == expected && ref == expected then
      IO.println s!"  ✓ {label}: policyOk = {hw}"
    else
      IO.println s!"  ✗ {label}: hw={hw} ref={ref} expected={expected}"
      ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.TxPolicyTest

section SynthesisChecks
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IP.Crypto.TxPolicy

/-- Synth the combinational policy engine's `policyOk` output. -/
private def synth_txPolicy
    (recipient : Signal defaultDomain (BitVec 160))
    (value : Signal defaultDomain (BitVec 256)) :
    Signal defaultDomain Bool :=
  (txPolicyHW recipient value).policyOk

#synthesizeVerilog synth_txPolicy

end SynthesisChecks
