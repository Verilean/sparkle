# Policy-enforcing Ethereum signer — host driver

Drives the Tang Nano 50K policy signer (`IP/Crypto/PolicySignDemo.lean`) over the
BL616 CDC-ACM UART bridge. See **tutorial Ch11** for the full flash-and-run
walkthrough, and `docs/ip-catalog/PolicySignDemo.md` for the protocol spec.

## No-hardware self-test (zero dependencies)

`sign_tx.py` implements secp256k1 and Keccak-256 in pure Python, so the
self-test runs on any stock Python 3 — no `pip install`:

```
python3 sign_tx.py --selftest
```

It reproduces `Tests/IP/Crypto/PolicySignDemoTest.lean`: an allowlisted +
under-cap transaction signs and verifies, and over-cap / non-allowlisted
transactions are rejected. The sample `r` printed matches the on-chip value
bit-for-bit — the host reference and the device compute the same thing.

## Signing on real hardware

Needs `pyserial` (only for the serial I/O):

```
pip install pyserial
python3 sign_tx.py --port /dev/ttyACM0 \
    --to 0x70997970C51812dc3A010C7d01b50e0d17dc79C8 \
    --value 500000000000000000 \
    --key   0xC9AFA9D8...F6721 \
    --nonce 0x9E56F509...A6DECE
```

- **PASS** → prints `r`, `s`, and `signature verifies ... : YES` (the `signDone`
  LED strobes on the board).
- **REJECT** (recipient not allowlisted, or value > 1 ETH cap) → prints
  `device REJECTED the transaction (0xEE)` (the `rejected` LED strobes).

The allowlist (`ALLOWLIST`) and cap (`MAX_VALUE = 1 ETH`) mirror the constants
baked into `IP/Crypto/TxPolicy.lean`; a real deployment recompiles the bitstream
with its own values.

> **DEMO-ONLY / INSECURE:** `--key` (d) and `--nonce` (k) are sent over the wire
> here for the demo. A production device keeps `d` on-chip (fuse/PUF) and derives
> `k` via RFC-6979 — never over the wire.

## Broadcast a real transaction to a local anvil node

The `--send` path builds a genuine **EIP-1559** transfer, signs its real hash
(`keccak256(0x02‖rlp([...]))`), and broadcasts it over JSON-RPC — dependency-free
(stdlib `urllib`, no `web3`). `--dry-run` signs in pure Python (byte-identical to
the device), so the whole round-trip runs **without a board**:

```
curl -L https://foundry.paradigm.xyz | bash && foundryup   # installs anvil
anvil                                                       # localhost:8545

# From allow0 (anvil acct #1) → allow1, 0.001 ETH:
python3 sign_tx.py --send --dry-run \
    --to 0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC --value 1000000000000000
# → broadcast tx 0x…, receipt status 0x1, recipient balance +0.001 ETH.
```

anvil's default accounts #1–#4 are exactly the device's baked-in allowlist, so
the demo works with no extra setup. A non-allowlisted `--to` is rejected and
never broadcast. On real hardware, drop `--dry-run` and add `--port /dev/ttyACM0`
(the host frames `d‖k‖to‖value‖paddedPreimage` to the **M2** bitstream).

See **tutorial Ch11 §11.7** for the full walkthrough and the honest M2 policy
boundary (real hash signed; policy on host-supplied fields; on-chip field-binding
is M3).
