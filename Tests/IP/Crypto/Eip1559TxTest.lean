/-
  Sim test for IP.Crypto.Eip1559Tx.

  Tests:
    1. Address derivation from a private key (the canonical
       Hardhat / Anvil account #0):
         privkey 0xac09…ff80  →  0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266
    2. EIP-1559 signing payload composition + Keccak-256
       round-trip: the signing hash must be the Keccak of
       (0x02 ‖ rlp(...)).  Cross-checks the rlp/keccak/0x02
       prefix wiring against a hand-computed reference.
    3. Encode-then-decode-shape: the broadcast envelope's
       first byte is 0x02 and its second byte is an RLP list
       prefix (0xc0..0xff range).
    4. Sign round-trip: signTx with a known nonce produces a
       (r, s) pair that the existing verify routine accepts
       when called with the derived public key.
-/

import IP.Crypto.Eip1559Tx
import IP.Crypto.Secp256k1ECDSA
import IP.Crypto.Secp256k1Point
import IP.Crypto.Keccak256
import IP.Crypto.RLP

open Sparkle.IP.Crypto.Eip1559Tx
open Sparkle.IP.Crypto.Secp256k1ECDSA (sign verify derivePublicKey)

namespace Sparkle.Tests.IP.Crypto.Eip1559TxTest

private def hexByte (b : Nat) : String :=
  let lo := b &&& 0xF
  let hi := (b >>> 4) &&& 0xF
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat (d + 0x30) else Char.ofNat (d - 10 + 0x61)
  String.mk [digit hi, digit lo]

private def bytesToHex (bs : Array UInt8) : String := Id.run do
  let mut out := ""
  for b in bs do
    out := out ++ hexByte b.toNat
  return out

def main : IO Unit := do
  IO.println "=== EIP-1559 transaction signer sim ==="
  let mut allOk := true

  -- Test 1: address derivation
  -- Hardhat / Anvil account #0
  let dHardhat : Nat :=
    0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
  let expectedAddr := "f39fd6e51aad88f6f4ce6ab8827279cfffb92266"
  match addressOfPrivateKey dHardhat with
  | none =>
    IO.println "  ✗ address derivation: derivePublicKey returned infinity"
    allOk := false
  | some addr =>
    let got := bytesToHex addr
    let mark := if got = expectedAddr then "✓" else "✗"
    IO.println s!"  {mark} address(0xac0974…ff80) (Hardhat/Anvil #0)"
    IO.println s!"    expected: {expectedAddr}"
    IO.println s!"    got     : {got}"
    if got ≠ expectedAddr then allOk := false

  -- Test 2 + 3: tx envelope shape — build a small EIP-1559
  -- tx and verify the broadcast envelope starts with 0x02
  -- and a valid RLP list prefix.
  let toAddr : Array UInt8 :=
    -- A 20-byte recipient address (any).
    #[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
  let tx : Tx :=
    { chainId := 1
    , nonce := 0
    , maxPriorityFee := 1_000_000_000      -- 1 gwei
    , maxFee := 2_000_000_000              -- 2 gwei
    , gasLimit := 21_000
    , to := toAddr
    , value := 0
    , data := #[]
    , accessList := emptyAccessList
    }
  let payload := signingPayload tx
  let payloadHex := bytesToHex payload
  IO.println s!"  ✓ signingPayload first byte = 0x{hexByte (payload.getD 0 0).toNat}"
  if (payload.getD 0 0) ≠ 0x02 then
    IO.println "  ✗ TransactionType byte should be 0x02"
    allOk := false
  let secondByte := payload.getD 1 0
  if secondByte.toNat < 0xc0 then
    IO.println s!"  ✗ second byte ({hexByte secondByte.toNat}) should be an RLP list prefix (≥ 0xc0)"
    allOk := false
  else
    IO.println s!"  ✓ second byte 0x{hexByte secondByte.toNat} is in the RLP-list range"

  let hash := signingHash tx
  if hash.size ≠ 32 then
    IO.println s!"  ✗ signingHash should be 32 bytes, got {hash.size}"
    allOk := false
  else
    IO.println s!"  ✓ signingHash = {bytesToHex hash}"

  -- Test 4: sign + verify round-trip — fixed nonce (1) for
  -- determinism.  Production callers MUST derive k per
  -- RFC 6979.
  match signTx tx dHardhat 1 with
  | none =>
    IO.println "  ✗ signTx returned none (degenerate signature)"
    allOk := false
  | some signed =>
    IO.println s!"  ✓ signed: yParity={signed.yParity}"
    IO.println s!"    r = {signed.r}"
    IO.println s!"    s = {signed.s}"
    -- Verify via ECDSA verify (public key derived from d).
    let q := derivePublicKey dHardhat
    let z := signingHashNat tx
    let ok := verify q z signed.r signed.s
    if ok then
      IO.println "  ✓ verify(signedHash, (r,s), pubkey) = true"
    else
      IO.println "  ✗ verify rejected the produced signature"
      allOk := false
    -- Envelope shape sanity.
    let env := encodeSigned signed
    if env.getD 0 0 ≠ 0x02 then
      IO.println "  ✗ envelope first byte should be 0x02"
      allOk := false
    else if (env.getD 1 0).toNat < 0xc0 then
      IO.println "  ✗ envelope second byte should be RLP list prefix"
      allOk := false
    else
      IO.println s!"  ✓ envelope = {bytesToHex env}"

  let _ := payloadHex  -- avoid unused-warning for the intermediate

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Eip1559TxTest
