/-
  Sim test for IP.Crypto.EthWallet — full end-to-end signer.

  Walks the mnemonic → broadcast envelope path the wallet UI
  consumes, using the canonical BIP-39 Trezor vector:

    mnemonic = "abandon abandon … about"  (the universal sanity check)
    passphrase = ""
    path = m/44'/60'/0'/0/0  (Ethereum default)

  For this mnemonic + path, BIP-32 derives the well-known
  address `0x9858effd232b4033e47d90003d41ec34ecaeda94`
  (verifiable on any block explorer / wallet).  We assert
  the EthWallet derives the same address.

  We then build a representative EIP-1559 tx, sign it, and
  verify the broadcast envelope starts with 0x02 (the
  TransactionType prefix) — the wire-shape sanity check.
-/

import IP.Crypto.EthWallet
import IP.Crypto.Eip1559Tx

open Sparkle.IP.Crypto.EthWallet (signFromMnemonic SignedTx)
open Sparkle.IP.Crypto.Eip1559Tx (Tx emptyAccessList)

namespace Sparkle.Tests.IP.Crypto.EthWalletTest

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
  IO.println "=== Ethereum wallet end-to-end signer sim ==="
  let mut allOk := true

  let mnemonic :=
    "abandon abandon abandon abandon abandon abandon " ++
    "abandon abandon abandon abandon abandon about"
  let toAddr : Array UInt8 := Array.replicate 20 0xff
  let tx : Tx :=
    { chainId := 1
    , nonce := 0
    , maxPriorityFee := 1_000_000_000
    , maxFee := 2_000_000_000
    , gasLimit := 21_000
    , to := toAddr
    , value := 0
    , data := #[]
    , accessList := emptyAccessList
    }

  IO.println "  Running full pipeline (BIP-39 PBKDF2 + BIP-32 derive + ECDSA sign)..."
  IO.println "  Expect 30-60 s on pure Lean."
  match signFromMnemonic mnemonic "" tx 1 with
  | none =>
    IO.println "  ✗ signFromMnemonic returned none"
    allOk := false
  | some signed =>
    let addrHex := bytesToHex signed.address
    -- Expected address for m/44'/60'/0'/0/0 from the
    -- "abandon … about" mnemonic (no passphrase):
    --   0x9858EfFD232B4033E47d90003D41EC34EcaEda94
    let expectedAddr := "9858effd232b4033e47d90003d41ec34ecaeda94"
    let mark := if addrHex == expectedAddr then "✓" else "✗"
    IO.println s!"  {mark} derived address (BIP-44 path m/44'/60'/0'/0/0)"
    IO.println s!"    expected: {expectedAddr}"
    IO.println s!"    got     : {addrHex}"
    if addrHex ≠ expectedAddr then allOk := false

    let env := signed.envelope
    if env.getD 0 0 ≠ 0x02 then
      IO.println "  ✗ envelope first byte should be 0x02"
      allOk := false
    else if (env.getD 1 0).toNat < 0xc0 then
      IO.println "  ✗ envelope second byte should be RLP list prefix"
      allOk := false
    else
      IO.println s!"  ✓ envelope shape OK (starts with 02 {hexByte (env.getD 1 0).toNat}, length {env.size})"

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.EthWalletTest
