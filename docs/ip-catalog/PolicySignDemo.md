# Policy-Enforcing Ethereum Signer (Tang Nano 50K)

A **security** signing device: the chip receives a transaction, computes
the Keccak-256 signing hash **on-chip**, checks the recipient/amount
against an **on-chip policy** sliced from the *same bytes it hashes*, and
produces an ECDSA signature **only if the policy passes**. The private key
never leaves the chip, and — unlike a blind signer — a compromised host
**cannot** make the chip sign an attacker-chosen transaction.

This is the "clear signing" property real HSMs and hardware wallets
provide, implemented as a physically-separate, formally-inspectable
circuit rather than as software inside a general-purpose CPU enclave.

## Modules

| File | Role |
|------|------|
| `IP/Crypto/TxPolicy.lean` | Combinational policy engine: `recipient ∈ allowlist ∧ value ≤ maxValue`. Allowlist + cap are compile-time (provisioned) constants. |
| `IP/Crypto/Keccak256Sponge.lean` | Full Keccak-256 sponge FSM (multi-block absorb) on top of `keccakF1600HW`. Digest exposed as 4× `BitVec 64` lanes + `done`. |
| `IP/Crypto/PolicySignDemo.lean` | Tang Nano top: UART RX → on-chip Keccak → policy check → gated `signCore` → UART TX (`r‖s` or reject byte). |

The signer core (`signCore`), UART engines (`wRx`/`wTx`), and the secp256k1
engines are reused verbatim from `IP/Crypto/EcdsaSignDemo.lean` (PR #94).

## Frame protocol (Milestone 1)

UART, 115200 8-N-1, `bitDiv = clk/baud − 1` (≈ 233 @ 27 MHz).

The host sends a fixed **128-byte** frame, MSB byte first:

```
d (32)  ‖  k (32)  ‖  to (32, address in low 20)  ‖  value (32)
```

* `d`, `k` — the ECDSA signing secrets (baked into the device in a real
  deployment; host-supplied here for the demo).
* The chip hashes the 64-byte tail `to‖value` (a single Keccak rate block)
  and slices `recipient = to[159:0]` / `value` from the **same** buffered
  bytes for the policy check.

Response:
* **policy PASS** → 64 bytes `r‖s` streamed back, `signDone` LED strobes.
* **policy FAIL** → one reject byte `0xEE`, `rejected` LED strobes; no signature.

Milestone 2 moves the RLP serialization on-chip (host sends field *values*,
chip builds `0x02‖rlp([...])`), so `hash(fields) == policy(fields)` by
construction. Milestone 3 adds ERC-20 `transfer` decode.

## Verification

* **Dataflow sim** (`policy-sign-demo-test`): cross-checks `z =
  keccak256(to‖value)`, `(r,s) = Secp256k1ECDSA.sign d k z`, and the policy
  gate against pure references — including policy-pass and both reject cases.
* **Synthesis** (`#synthesizeVerilog` in the test): the whole
  sponge + policy + signer + UART top lowers to Verilog.
* **iverilog**: the emitted 13-module design elaborates cleanly under
  `iverilog -g2012 -s policyTop` (2.5 MB → vvp).
* **Sponge** (`keccak256-sponge-test`): pure-data cross-check vs
  `keccak256OfBytes` over 1- and 2-block fixtures + `#synthesizeVerilog`.
* **JIT co-sim** (`keccak256-sponge-jit-test`): real-cycle validation of the
  sponge FSM via `#sim` → native. Opt-in / heavy (the fully-inlined Keccak
  round makes `#sim` slow); not part of the `lake test` gate. See issue #95
  for why the pure-Lean `Signal.val` interpreter can't co-sim deep FSMs.

## Notes for HW writers (synth-elaborator gotchas hit here)

* A `.map` lambda lowers only for a **single** `extractLsb'` or a
  constant-prefix `append` — composed bit-ops, nested `append`, or a
  `let`-bound helper inside the lambda do **not** lower. Byte-swaps /
  byte-packs must be built at the Signal level with
  `BitVec.append <$> _ <*> _` over single-extract maps, spelled out inline.
* A 4-argument applicative (`(fun a b c d => …) <$> _ <*> _ <*> _ <*> _`)
  fails (`Seq.seq: not a hardware module`); nest 2-way appends instead.
* A **combinational** (register-free) module cannot be a `@[hardware_module]`
  sub-instance — projecting its output record fails. Expose a bare
  `Signal` (see `TxPolicy.txPolicyOk`) and inline it.
* Related compiler fix: issue #67 (O(N²) sub-module re-synth) was resolved
  so the 25-lane-projection sponge synthesizes in practical time.
