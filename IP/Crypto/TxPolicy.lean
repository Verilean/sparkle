/-
  IP.Crypto.TxPolicy — on-chip transaction-policy engine.

  This is the piece that turns a *blind* signer (which will put
  its key on anything the host hands it) into a *security device*
  (which refuses to sign a transaction that violates a policy
  baked into the silicon).  The threat model is a compromised
  host: even if the host is fully owned, it can only get the chip
  to sign transactions the policy permits.

  Policy, milestone 1 (native ETH transfer):

    policyOk = (recipient ∈ allowlist) ∧ (value ≤ maxValue)

  Both the allowlist and `maxValue` are *compile-time constants*
  — they are the device's provisioned configuration, not host
  input.  A different deployment recompiles with different
  addresses; there is no runtime path to widen the policy, which
  is the whole point.

  This module is purely combinational (no registers): given a
  recipient (160-bit Ethereum address) and a value (256-bit wei),
  it produces a single `policyOk` bit.  The caller is responsible
  for feeding `recipient`/`value` from the *same* bytes it hashes
  (see `PolicySignDemo`), so a lying host cannot desync the policy
  check from the signature.

  Semantics mirror `Erc20Abi.confirmation`: for a native transfer
  the counterparty is `tx.to` and the amount is `tx.value`.  The
  ERC-20 `transfer(to, amount)` case (recipient/amount taken from
  the decoded `data` field) is a later milestone that re-muxes the
  same policy inputs; the policy predicate here is shared.
-/
import Sparkle

namespace Sparkle.IP.Crypto.TxPolicy

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### Provisioned policy configuration (compile-time constants).

    These are the device's baked-in configuration.  In a real
    deployment the provisioning step recompiles the bitstream with
    the operator's own allowlist and cap.  The addresses below are
    placeholders (well-known test vectors) so the demo is
    reproducible. -/

/-- Allowlisted recipient #0 (160-bit big-endian address).
    Placeholder: the canonical zero-nonce test recipient. -/
def allow0 : BitVec 160 := 0x70997970C51812dc3A010C7d01b50e0d17dc79C8#160
/-- Allowlisted recipient #1. -/
def allow1 : BitVec 160 := 0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC#160
/-- Allowlisted recipient #2. -/
def allow2 : BitVec 160 := 0x90F79bf6EB2c4f870365E785982E1f101E93b906#160
/-- Allowlisted recipient #3. -/
def allow3 : BitVec 160 := 0x15d34AAf54267DB7D7c367839AAf71A00a2C6A65#160

/-- Maximum permitted `value` in wei.  1 ETH = 10^18 wei; the cap
    below is 1 ETH.  Any transfer over this is rejected. -/
def maxValue : BitVec 256 := (1000000000000000000 : BitVec 256)

/-- Output record: a single policy-decision bit. -/
structure PolicyOut (dom : DomainConfig) where
  /-- High iff the transaction satisfies the baked-in policy
      (recipient allowlisted AND value within cap). -/
  policyOk : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (PolicyOut dom) dom := ⟨⟩

/-- Pure reference predicate — the golden model the HW is
    cross-checked against.  Kept next to the constants so the two
    never drift. -/
def policyRef (recipient : BitVec 160) (value : BitVec 256) : Bool :=
  (recipient == allow0 || recipient == allow1 ||
   recipient == allow2 || recipient == allow3) &&
  BitVec.ule value maxValue

/-- Combinational policy engine — bare `Signal Bool` form.

    `policyOk = (recipient matches any allowlist entry)
                 ∧ (value ≤ maxValue)`.

    Uses `==` and `BitVec.ule` (both in the synth op table) and the
    applicative `(· && ·)` / `(· || ·)` combinators — the same idiom
    `RLPHW` uses — so it lowers to a flat mux/gate tree with no
    registers.  Use THIS (not the `PolicyOut`-wrapped `txPolicyHW`)
    when embedding the policy inside a larger `circuit do`:
    projecting `.policyOk` off the record inside another circuit
    fails to lower ("PolicyOut.policyOk: not a hardware module
    definition"); the bare-signal form inlines cleanly. -/
def txPolicyOk {dom : DomainConfig}
    (recipient : Signal dom (BitVec 160))
    (value : Signal dom (BitVec 256)) :
    Signal dom Bool :=
  let a0 := (Signal.pure allow0 : Signal dom (BitVec 160))
  let a1 := (Signal.pure allow1 : Signal dom (BitVec 160))
  let a2 := (Signal.pure allow2 : Signal dom (BitVec 160))
  let a3 := (Signal.pure allow3 : Signal dom (BitVec 160))
  let vmax := (Signal.pure maxValue : Signal dom (BitVec 256))
  let eq0 := ((· == ·) <$> recipient <*> a0 : Signal dom Bool)
  let eq1 := ((· == ·) <$> recipient <*> a1 : Signal dom Bool)
  let eq2 := ((· == ·) <$> recipient <*> a2 : Signal dom Bool)
  let eq3 := ((· == ·) <$> recipient <*> a3 : Signal dom Bool)
  let or01 := ((· || ·) <$> eq0 <*> eq1 : Signal dom Bool)
  let or23 := ((· || ·) <$> eq2 <*> eq3 : Signal dom Bool)
  let inList := ((· || ·) <$> or01 <*> or23 : Signal dom Bool)
  let underCap := ((BitVec.ule · ·) <$> value <*> vmax : Signal dom Bool)
  ((· && ·) <$> inList <*> underCap : Signal dom Bool)

def txPolicyHW {dom : DomainConfig}
    (recipient : Signal dom (BitVec 160))
    (value : Signal dom (BitVec 256)) :
    PolicyOut dom :=
  { policyOk := txPolicyOk recipient value }

end Sparkle.IP.Crypto.TxPolicy
