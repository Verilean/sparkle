# Chapter 11 — Running the web3 Signing Device on Real Hardware

The previous chapters took a *toy* design (a blinky) all the way to
silicon. This chapter does the same for a **real security product**:
the policy-enforcing Ethereum signer. You'll generate its Verilog from
Sparkle Lean source, flash it to a Tang Nano 50K, sign an Ethereum
transaction from your PC — watching the chip **refuse** to sign one that
violates its baked-in policy — and finally **broadcast a real transfer to
a local Ethereum node** (§11.7), watching the balance move on-chain.

## 11.1 What the device does

The signer (`IP/Crypto/PolicySignDemo.lean`) is a hardware security
module in miniature. Over a USB-serial link it receives a transaction,
computes the Keccak-256 signing hash **on-chip**, checks the recipient
and amount against an **on-chip allowlist + cap** — sliced from *the very
bytes it hashes* — and produces an ECDSA-secp256k1 signature **only if
the policy passes**. The private key never leaves the chip, and unlike a
"blind" signer, a compromised host **cannot** make the chip sign an
attacker-chosen transaction. This is the "clear signing" property real
HSMs and hardware wallets provide, implemented as a physically separate,
formally inspectable circuit.

Full spec: [`docs/ip-catalog/PolicySignDemo.md`](../../ip-catalog/PolicySignDemo.md).

```lean
import Sparkle
import Sparkle.Compiler.Elab
import IP.Crypto.PolicySignDemo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.PolicySignDemo

namespace Notebooks.Ch11

```
## 11.2 Generate the Verilog

The board top is `policySignDemo (uartRx) (bitDiv) : PolicyDemoOut`,
exposing `uartTx`, `signDone`, and `rejected`. For synthesis we project
each output we route to a pin. Here is the UART-TX projection — the same
`#synthesizeVerilog` you used for the blinky, now over the whole
sponge + policy + secp256k1-signer + UART stack:

```lean
-- The signer is a deep FSM stack (Keccak sponge + secp256k1 signer);
-- give the elaborator room, as the PolicySignDemo synth test does.
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

def policyTx
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (policySignDemo uartRx bitDiv).uartTx

#synthesizeVerilog policyTx

```
`lake build` on this chapter runs that elaboration and prints
`-- Verilog successfully generated!`. To capture the emitted module for
the FPGA flow, build the module and slice out the Verilog:

```bash
mkdir -p fpga/tangNano50K/build
lake build Notebooks.Gen.Ch11_Web3Signer 2>&1 \
  | sed -n '/^module /,/^endmodule/p' \
  > fpga/tangNano50K/build/policy_signer.v
```

`#synthesizeVerilog` emits several modules (the Keccak sponge, the
secp256k1 point-op / scalar-mul / mod-n / inverse engines, the UART
RX/TX, and the top). The `sed` above captures all of them. The top
module has the long `_private_…_policyTx` mangled name — we rename it in
the wrapper below.

## 11.3 Wrap with a PLL and tie-offs

Sparkle's emitted top has ports `clk`, `rst`, `uart_rx_line`,
`bit_div`, `out` (= UART TX) plus the projected `sign_done` / `rejected`
if you also synthesize those. The board wrapper drives `clk` from the
27 MHz crystal (the signer's `defaultDomain` runs comfortably at
27 MHz), hardcodes `bit_div = 233` (27 MHz / 115200 baud − 1), and
renames `out` → `uart_tx` to match the `.cst`.

Create `fpga/tangNano50K/build/policy_signer_top.v`:

```verilog
module policy_signer_top(
    input  clk,             // 27 MHz crystal
    input  rst,             // active-low reset button
    input  uart_rx_line,    // FPGA RX (from BL616 TX)
    output uart_tx,         // FPGA TX (to BL616 RX)
    output led_sign,        // pulses when a signature completes
    output led_reject       // pulses when a tx is rejected by policy
);
    // Replace the long mangled name with the one #synthesizeVerilog
    // actually emitted for `policyTx` (grep the .v for `_policyTx`).
    _private_Notebooks_Gen_Ch11_Web3Signer_0_policyTx u_core(
        .clk(clk),
        .rst(~rst),                 // synchronous, active-high inside
        ._gen_uartRx(uart_rx_line),
        ._gen_bitDiv(16'd233),      // 27 MHz / 115200 − 1
        .out(uart_tx)
    );
    // Route the status strobes to LEDs (optional). If you also synthesize
    // `(policySignDemo _ _).signDone` / `.rejected` as separate tops,
    // wire them here; otherwise tie the LEDs off.
    assign led_sign   = 1'b0;
    assign led_reject = 1'b0;
endmodule
```

(Port names such as `_gen_uartRx` / `_gen_bitDiv` are what the backend
emits for the Lean argument names — grep the generated `.v` header to
confirm the exact spelling for your build.)

## 11.4 Pin constraints

The board pin map is `fpga/tangNano50K/policy_signer.cst`: the 27 MHz
`clk`, the `rst` button, and the `uart_rx_line` / `uart_tx` pins wired to
the on-board BL616 CDC-ACM bridge (so the PC sees the FPGA as
`/dev/ttyACM*`). The two LED lines are placeholders — fill in your
board revision's user-LED pins or drop them.

## 11.5 Synthesize, place-and-route, flash

Same open-source Gowin flow as the other Tang Nano demos (all tools are
in the Ch 0 Docker image):

```bash
cd fpga/tangNano50K
yosys -p "read_verilog -sv build/policy_signer.v; \
          read_verilog -sv build/policy_signer_top.v; \
          synth_gowin -top policy_signer_top -json build/policy_signer.json"

nextpnr-himbaechel --device GW5AT-LV60PG484C \
    --vopt cst=policy_signer.cst \
    --json build/policy_signer.json \
    --write build/policy_signer_pnr.json

gowin_pack -d GW5A-60 -o build/policy_signer.fs build/policy_signer_pnr.json

openFPGALoader -b tangnano50k build/policy_signer.fs
```

The signer is large (Keccak + a full secp256k1 signer), but fits the
GW5A-60 comfortably. After `openFPGALoader` finishes, the board is
listening on its USB-serial port.

## 11.6 Sign a transaction from the host

The host driver [`host/policy_signer/sign_tx.py`](../../../host/policy_signer/sign_tx.py)
frames `d‖k‖to‖value` (128 bytes), reads back `r‖s`, and verifies the
signature against `Q = d·G`. It is **dependency-free** — it implements
secp256k1 and Keccak-256 in pure Python — so you can first check
everything end-to-end **without a board**:

```bash
python3 host/policy_signer/sign_tx.py --selftest
```

That reproduces `Tests/IP/Crypto/PolicySignDemoTest.lean`: an allowlisted,
under-cap transaction signs and verifies; over-cap and non-allowlisted
transactions are rejected. The sample `r` it prints is bit-for-bit the
value the chip computes.

On real hardware (needs `pip install pyserial`):

```bash
# Allowlisted recipient, 0.5 ETH (< 1 ETH cap) → the chip SIGNS.
python3 host/policy_signer/sign_tx.py --port /dev/ttyACM0 \
    --to 0x70997970C51812dc3A010C7d01b50e0d17dc79C8 \
    --value 500000000000000000 \
    --key   0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721 \
    --nonce 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
# → prints r, s, and "signature verifies against Q = d*G : YES"; led_sign pulses.

# Same key/nonce but a non-allowlisted recipient → the chip REFUSES.
python3 host/policy_signer/sign_tx.py --port /dev/ttyACM0 \
    --to 0x000000000000000000000000000000000000dEaD \
    --value 500000000000000000 \
    --key   0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721 \
    --nonce 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
# → "device REJECTED the transaction (0xEE) — policy violation"; led_reject pulses.
```

The reject path is the whole point: even with the correct private key on
the wire, the chip will not sign a transaction its baked-in policy
forbids. In a real deployment the key is baked in and never travels the
wire at all.

> **DEMO-ONLY / INSECURE:** this milestone sends `d` and `k` over the
> wire. A production device keeps `d` on-chip (fuse/PUF) and derives the
> nonce `k` via RFC-6979. See the ip-catalog note.

## 11.7 Test against a local Ethereum node (anvil)

The §11.6 demo hashes a fixed `to‖value` — a stand-in, not a real
Ethereum transaction. To see the device's signature actually *land on a
chain*, the **M2** path signs a genuine EIP-1559 transaction hash
(`keccak256(0x02‖rlp([...]))`) that a real node accepts. We test it
against a local [Foundry](https://getfoundry.sh) **anvil** node.

### Install and start anvil (macOS)

```bash
curl -L https://foundry.paradigm.xyz | bash
foundryup                 # installs forge / cast / anvil
anvil                     # starts a local chain on http://localhost:8545
```

anvil prints ten funded accounts. By design, **accounts #1–#4 are exactly
the device's baked-in allowlist** (`IP/Crypto/TxPolicy.lean`):

```
(1) 0x70997970C51812dc3A010C7d01b50e0d17dc79C8   ← allow0 (the signer)
(2) 0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC   ← allow1
(3) 0x90F79bf6EB2c4f870365E785982E1f101E93b906   ← allow2
(4) 0x15d34AAf54267DB7D7c367839AAf71A00a2C6A65   ← allow3
```

The device's private key `d` is account #1's key, so its signatures come
*from* `allow0` — an allowlisted sender signing to an allowlisted
recipient.

### Broadcast a real transfer

`host/policy_signer/sign_tx.py --send` builds a canonical EIP-1559
transfer, has it signed (on the device, or in pure Python with
`--dry-run`), assembles the signed transaction, and broadcasts it over
JSON-RPC — all with **zero dependencies** beyond stdlib (`urllib` for
RPC; no `web3`). `--dry-run` signs with the same pure-Python secp256k1 +
Keccak the device uses (byte-for-byte identical), so you can run the full
round-trip **without a board**:

```bash
# From allow0 → allow1, 0.001 ETH. --dry-run signs in-process (no board).
python3 host/policy_signer/sign_tx.py --send --dry-run \
    --rpc http://localhost:8545 \
    --to 0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC \
    --value 1000000000000000
```

Output — a real transaction, mined, funds moved:

```
broadcast tx 0xbd5b302a246aaf944c0d83f2fa1adaa50caba4a511a349b649f5364f0c441a15
receipt status: 0x1
recipient 0x3c44…293bc balance: 10000.000000 -> 10000.001000 ETH (+0.001000)
```

Confirm the sender is the allowlisted account with `cast`:

```bash
cast tx 0xbd5b302a…1a15 --rpc-url http://localhost:8545 | grep -E 'from|type'
# from  0x70997970C51812dc3A010C7d01b50e0d17dc79C8   ← allow0
# type  2                                             ← EIP-1559
```

To sign on the **real board** instead of `--dry-run`, drop `--dry-run`
and add `--port /dev/ttyACM0` (needs `pip install pyserial`). The host
frames `d‖k‖to‖value‖paddedPreimage` to the M2 bitstream, reads back
`r‖s`, and broadcasts exactly the same transaction.

### The policy still bites

Point the transfer at a **non-allowlisted** recipient and the device
refuses — nothing is broadcast:

```bash
python3 host/policy_signer/sign_tx.py --send --dry-run \
    --to 0x000000000000000000000000000000000000dEaD \
    --value 1000000000000000
# policy: REJECT (recipient not allowlisted or value > cap) — not broadcasting.
# device would return 0xEE (reject byte); led_reject strobes.
```

### The honest M2 boundary

M2 signs the **real** transaction hash, so the signature is genuinely
broadcastable — that part is fully verified above. But because RLP puts
`to`/`value` at *variable* byte offsets (integer fields have no leading
zeros, so their widths shift), the device cannot slice them out of the
hashed preimage the way M1 does. So in M2 the **policy checks
host-supplied `to`/`value` fields**, and binding those fields to the
bytes actually hashed — a small on-chip RLP walk — is the **M3**
follow-up. M1's tighter guarantee (policy fields *provably* come from the
hashed bytes) is documented in
[`docs/ip-catalog/PolicySignDemo.md`](../../ip-catalog/PolicySignDemo.md).

## 11.8 Where to go next

- [`docs/ip-catalog/PolicySignDemo.md`](../../ip-catalog/PolicySignDemo.md)
  — the protocol, the on-chip policy engine, and the Keccak sponge in
  detail; and milestones M2 (on-chip RLP so the host sends *fields*, not
  bytes) and M3 (ERC-20 `transfer` decode).
- [`docs/ip-catalog/Fido2Demo.md`](../../ip-catalog/Fido2Demo.md) — the
  same device-top pattern applied to a **FIDO2 security key** (P-256,
  CTAPHID) for Google / GitHub login.
- Chapter 6/7 — prove properties of the field arithmetic the signer
  computes over (`IP/Crypto/Proof/P256FieldTheorems.lean` shows the
  `∀`-quantified algebraic-law style).

```lean
end Notebooks.Ch11
```
