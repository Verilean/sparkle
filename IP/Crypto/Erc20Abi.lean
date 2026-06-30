/-
  IP.Crypto.Erc20Abi — ERC-20 ABI selector recognition and
  argument decoding for the hardware wallet's confirmation
  screen.

  When a user signs an EIP-1559 transaction whose `data` field
  is non-empty, the wallet must show them WHAT they're signing
  in human terms — not just "0xa9059cbb…ff" but
  "Transfer 1.5 USDC to 0xabc…".  This file implements the
  decoder for that confirmation step.

  Decode pipeline:
    1. Read the first 4 bytes — the function selector.
    2. Match against the standard ERC-20 selector table.
    3. For each recognised method, parse the per-argument
       32-byte slots that follow.

  Selectors are the first 4 bytes of keccak256 of the
  canonical function signature (no spaces, parameter type
  names only).  We hardcode the selectors here rather than
  recompute them at run time because (a) the keccak path is
  expensive and (b) they are fixed by the ERC-20 standard and
  every wallet, block explorer, and audit tool relies on
  exactly these values.

  Spec:
    ERC-20: https://eips.ethereum.org/EIPS/eip-20
    Solidity ABI: https://docs.soliditylang.org/en/latest/abi-spec.html
-/

import IP.Crypto.Keccak256

namespace Sparkle.IP.Crypto.Erc20Abi

/-! ### Function selectors (first 4 bytes of keccak256(sig)). -/

def selTransfer     : Array UInt8 := #[0xa9, 0x05, 0x9c, 0xbb]  -- transfer(address,uint256)
def selTransferFrom : Array UInt8 := #[0x23, 0xb8, 0x72, 0xdd]  -- transferFrom(address,address,uint256)
def selApprove      : Array UInt8 := #[0x09, 0x5e, 0xa7, 0xb3]  -- approve(address,uint256)
def selBalanceOf    : Array UInt8 := #[0x70, 0xa0, 0x82, 0x31]  -- balanceOf(address)
def selAllowance    : Array UInt8 := #[0xdd, 0x62, 0xed, 0x3e]  -- allowance(address,address)

/-! ### Decoded call shape

    A decoded ERC-20 call is a tagged union of every method
    we recognise plus a fallback for unknown method-IDs.  The
    wallet's confirmation screen pattern-matches on this. -/

inductive Call where
  /-- transfer(to, amount) -/
  | transfer (to : Array UInt8) (amount : Nat) : Call
  /-- transferFrom(from, to, amount) -/
  | transferFrom (from_ : Array UInt8) (to : Array UInt8) (amount : Nat) : Call
  /-- approve(spender, amount) -/
  | approve (spender : Array UInt8) (amount : Nat) : Call
  /-- balanceOf(owner) -/
  | balanceOf (owner : Array UInt8) : Call
  /-- allowance(owner, spender) -/
  | allowance (owner : Array UInt8) (spender : Array UInt8) : Call
  /-- The first 4 bytes did not match any ERC-20 selector. -/
  | unknown (selector : Array UInt8) (rest : Array UInt8) : Call
  deriving Inhabited

/-! ### Slot decoding -/

/-- Read a 32-byte slot starting at `offset` and interpret
    the low 20 bytes as an EVM address.  ABI addresses are
    left-padded with 12 zero bytes inside the 32-byte slot. -/
def decodeAddress (data : Array UInt8) (offset : Nat) : Array UInt8 :=
  (data.toList.drop (offset + 12)).take 20 |>.toArray

/-- Read a 32-byte slot starting at `offset` as a big-endian
    unsigned 256-bit integer. -/
def decodeUint256 (data : Array UInt8) (offset : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:32] do
    acc := (acc <<< 8) ||| (data.getD (offset + i) 0).toNat
  return acc

/-! ### Selector matching -/

private def first4 (data : Array UInt8) : Array UInt8 :=
  data.toList.take 4 |>.toArray

private def selectorEq (data sel : Array UInt8) : Bool :=
  if data.size < 4 then false
  else
    data.getD 0 0 == sel.getD 0 0 &&
    data.getD 1 0 == sel.getD 1 0 &&
    data.getD 2 0 == sel.getD 2 0 &&
    data.getD 3 0 == sel.getD 3 0

/-- Decode a transaction `data` field as an ERC-20 call.  The
    leading 4 bytes select the method; the remaining payload
    is interpreted per the matched method's argument shape.
    Unknown selectors are returned as `Call.unknown` rather
    than treated as a hard error — wallets typically still
    let users sign with a "raw bytes" disclaimer. -/
def decode (data : Array UInt8) : Call :=
  if data.size < 4 then
    .unknown (first4 data) #[]
  else if selectorEq data selTransfer then
    let to := decodeAddress data 4
    let amount := decodeUint256 data (4 + 32)
    .transfer to amount
  else if selectorEq data selTransferFrom then
    let from_ := decodeAddress data 4
    let to := decodeAddress data (4 + 32)
    let amount := decodeUint256 data (4 + 32 + 32)
    .transferFrom from_ to amount
  else if selectorEq data selApprove then
    let spender := decodeAddress data 4
    let amount := decodeUint256 data (4 + 32)
    .approve spender amount
  else if selectorEq data selBalanceOf then
    .balanceOf (decodeAddress data 4)
  else if selectorEq data selAllowance then
    let owner := decodeAddress data 4
    let spender := decodeAddress data (4 + 32)
    .allowance owner spender
  else
    let sel := first4 data
    let rest := data.toList.drop 4 |>.toArray
    .unknown sel rest

/-! ### Confirmation rendering

    A human-readable rendering of a `Call`, scoped to what the
    wallet UI displays to the user before they confirm.  All
    amounts are returned as raw wei-style integers; the wallet
    is responsible for token-decimal scaling (USDC is 6
    decimals, most ERC-20s are 18 — the answer lives in
    `decimals()` on the token contract, not in the tx). -/

structure Confirmation where
  /-- One-line summary, e.g. "Transfer". -/
  action  : String
  /-- Counterparty address (recipient / spender / etc.) or
      none for methods that have no single counterparty
      (e.g. balanceOf). -/
  party   : Option (Array UInt8)
  /-- Amount in token base units (wei-shape; the wallet
      applies the decimals scaling). -/
  amount  : Option Nat

def confirmation (c : Call) : Confirmation :=
  match c with
  | .transfer to amount =>
    { action := "Transfer", party := some to, amount := some amount }
  | .transferFrom _ to amount =>
    { action := "TransferFrom", party := some to, amount := some amount }
  | .approve spender amount =>
    { action := "Approve", party := some spender, amount := some amount }
  | .balanceOf owner =>
    { action := "BalanceOf (read)", party := some owner, amount := none }
  | .allowance _ spender =>
    { action := "Allowance (read)", party := some spender, amount := none }
  | .unknown sel _ =>
    { action := s!"Unknown selector {sel}", party := none, amount := none }

/-! ### Selector verification helper

    Build the selector for an arbitrary signature by hashing.
    Used only as a one-shot sanity check / test helper — the
    standard ERC-20 selectors above are baked in. -/

def selectorOfSignature (sig : String) : Array UInt8 :=
  let h := Keccak256.keccak256OfBytes sig.toUTF8.toList.toArray
  h.toList.take 4 |>.toArray

end Sparkle.IP.Crypto.Erc20Abi
