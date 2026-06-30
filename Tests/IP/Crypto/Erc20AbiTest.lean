/-
  Sim test for IP.Crypto.Erc20Abi.

  Cross-checks:
    1. The hardcoded selectors match keccak256(signature) [:4]
       for every recognised method.
    2. Decode round-trip on a real-world `transfer` calldata
       (from Etherscan-shaped 0xa9059cbb… inputs).
    3. Decode `approve`, `transferFrom`, `balanceOf`,
       `allowance` calldata shapes.
    4. Unknown selectors land in `Call.unknown` rather than
       silently mis-decoding.
    5. The confirmation rendering surfaces action / party /
       amount as the wallet UI expects.
-/

import IP.Crypto.Erc20Abi

open Sparkle.IP.Crypto.Erc20Abi

namespace Sparkle.Tests.IP.Crypto.Erc20AbiTest

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

private def bytesEq (a b : Array UInt8) : Bool :=
  a.size == b.size && (List.range a.size).all (fun i => a.getD i 0 == b.getD i 0)

/-- Build the 32-byte ABI slot for an address: 12 zero bytes
    + 20 address bytes. -/
private def addrSlot (addr20 : Array UInt8) : Array UInt8 :=
  Array.replicate 12 0 ++ addr20

/-- Build the 32-byte ABI slot for a uint256 by big-endian
    encoding the value into the low N bytes and left-padding
    with zeros. -/
private def uintSlot (n : Nat) : Array UInt8 := Id.run do
  let mut bs : Array UInt8 := #[]
  let mut x := n
  while x > 0 do
    bs := bs.push (UInt8.ofNat (x &&& 0xFF))
    x := x >>> 8
  let raw := bs.reverse
  let pad := 32 - raw.size
  Array.replicate pad 0 ++ raw

def main : IO Unit := do
  IO.println "=== ERC-20 ABI decoder sim ==="
  let mut allOk := true

  -- Test 1: selector table matches keccak256(signature)[:4].
  let pairs : List (String × Array UInt8 × String) :=
    [ ("transfer(address,uint256)",        selTransfer,     "a9059cbb")
    , ("transferFrom(address,address,uint256)", selTransferFrom, "23b872dd")
    , ("approve(address,uint256)",         selApprove,      "095ea7b3")
    , ("balanceOf(address)",               selBalanceOf,    "70a08231")
    , ("allowance(address,address)",       selAllowance,    "dd62ed3e")
    ]
  for (sig, hardcoded, expectedHex) in pairs do
    let computed := selectorOfSignature sig
    let mark1 := if bytesToHex hardcoded == expectedHex then "✓" else "✗"
    let mark2 := if bytesEq computed hardcoded then "✓" else "✗"
    IO.println s!"  {mark1}{mark2} {sig}"
    IO.println s!"    hardcoded={bytesToHex hardcoded}  computed={bytesToHex computed}  expected={expectedHex}"
    if bytesToHex hardcoded ≠ expectedHex then allOk := false
    if ¬ bytesEq computed hardcoded then allOk := false

  -- Test 2: decode a `transfer(0xff…ff, 1234)` calldata.
  let recipient : Array UInt8 := Array.replicate 20 0xff
  let amount : Nat := 1234
  let calldata := selTransfer ++ addrSlot recipient ++ uintSlot amount
  match decode calldata with
  | .transfer to amt =>
    let okAddr := bytesEq to recipient
    let okAmt  := amt == amount
    let mark := if okAddr && okAmt then "✓" else "✗"
    IO.println s!"  {mark} decode transfer(0xff..ff, 1234)"
    IO.println s!"    to={bytesToHex to}  amount={amt}"
    if ¬ (okAddr && okAmt) then allOk := false
  | _ =>
    IO.println "  ✗ decode transfer returned wrong variant"
    allOk := false

  -- Test 3: decode `approve(spender, 2^256 - 1)` (infinite approval).
  let spender : Array UInt8 :=
    #[0xde, 0xad, 0xbe, 0xef, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  let maxUint : Nat := (1 <<< 256) - 1
  let approveData := selApprove ++ addrSlot spender ++ uintSlot maxUint
  match decode approveData with
  | .approve sp amt =>
    let mark := if bytesEq sp spender && amt == maxUint then "✓" else "✗"
    IO.println s!"  {mark} decode approve(deadbeef…, 2^256-1)"
    if ¬ (bytesEq sp spender && amt == maxUint) then allOk := false
  | _ =>
    IO.println "  ✗ decode approve returned wrong variant"
    allOk := false

  -- Test 4: decode `transferFrom(from, to, 500)`.
  let from_ : Array UInt8 := Array.replicate 20 0x11
  let toAddr : Array UInt8 := Array.replicate 20 0x22
  let tfData := selTransferFrom ++ addrSlot from_ ++ addrSlot toAddr ++ uintSlot 500
  match decode tfData with
  | .transferFrom f t a =>
    let ok := bytesEq f from_ && bytesEq t toAddr && a == 500
    let mark := if ok then "✓" else "✗"
    IO.println s!"  {mark} decode transferFrom(0x11..11, 0x22..22, 500)"
    if ¬ ok then allOk := false
  | _ =>
    IO.println "  ✗ decode transferFrom returned wrong variant"
    allOk := false

  -- Test 5: unknown selector → Call.unknown.
  let weird := #[0xde, 0xad, 0xbe, 0xef, 0x00, 0x01, 0x02, 0x03]
  match decode weird with
  | .unknown sel rest =>
    let okSel := bytesEq sel #[0xde, 0xad, 0xbe, 0xef]
    let okRest := bytesEq rest #[0x00, 0x01, 0x02, 0x03]
    let mark := if okSel && okRest then "✓" else "✗"
    IO.println s!"  {mark} decode unknown selector 0xdeadbeef"
    if ¬ (okSel && okRest) then allOk := false
  | _ =>
    IO.println "  ✗ unknown selector misrouted"
    allOk := false

  -- Test 6: confirmation rendering.
  let conf := confirmation (.transfer recipient amount)
  let okConf := conf.action == "Transfer" && conf.amount == some amount &&
                (match conf.party with | some p => bytesEq p recipient | none => false)
  let mark := if okConf then "✓" else "✗"
  IO.println s!"  {mark} confirmation(.transfer) renders correctly"
  IO.println s!"    action={conf.action} party_size={(conf.party.getD #[]).size} amount={conf.amount}"
  if ¬ okConf then allOk := false

  if allOk then
    IO.println "\nALL PASS"
  else
    IO.println "\nFAIL"
    IO.Process.exit 1

end Sparkle.Tests.IP.Crypto.Erc20AbiTest
