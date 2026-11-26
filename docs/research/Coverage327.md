# What is covered: results by circuit family (release snapshot)

> Generated file. Do not edit. Source: [`data/coverage-327.tsv`](data/coverage-327.tsv);
> generator: [`scripts/research/coverage_table.py`](../../scripts/research/coverage_table.py).
> Regenerate with `python3 -I scripts/research/coverage_table.py`. The complete row-by-row
> table, with row numbers, files and every condition, is
> [appendix F](appendix/F-AllCommandRows.md).

**What a row is.** The fixed inventory contains **327 command rows**: `#synthesizeVerilog`,
`#writeDesign` and similar commands in 136 files. They are **not 327 IPs**: one IP can own
several rows, and a row counts once however many routes prove it. A child leaf proof is never
added to its wrapper row. "Real IP" means the file lives under `IP/` or `Tests/IP/` (220 rows);
every other row is a "regression" row (107 rows: examples, tests, tutorial files).

**What "strict" means.** The original declaration, the *same run's returned IR*, the exact
statement type, only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and all
outputs. It is rung 2 of the [guarantee ladder](README.md#the-guarantee-ladder): it says
nothing about the optimiser, the printed SystemVerilog or performance (those columns of the
ledger read "not-evaluated").

## Results by circuit family

A row is *strict* when the checker returned a kernel-checked theorem for it, and *not strict*
when it refused (no claim) or could not be run. The last column is the stage at which the most
rows of the family were stopped on the main route; the stage names are explained below.

| Circuit family | What is in it | Rows | Strict | Not strict | Most common stopping stage |
|---|---|---|---|---|---|
| Finite-field and modular arithmetic | multipliers, modular inverse and field towers for the P-256, secp256k1, Ed25519, BLS12-381 and Goldilocks fields | 24 | 21 | 3 | `proof` (3) |
| Elliptic-curve point operations and pairings | one point double-or-add, scalar multiplication, pairing steps | 22 | 11 | 11 | `proof` (10), `signal` (1) |
| Signature engines and signing demos | ECDSA and Ed25519 signers, BIP-32 key derivation, signing demos | 19 | 12 | 7 | `order` (7) |
| Hash functions, MACs and key derivation | SHA-256, SHA-512, Keccak-256, HMAC, HKDF, Merkle trees | 17 | 13 | 4 | `order` (4) |
| Block cipher and authenticated encryption | AES, AES-GCM, GHASH | 7 | 7 | 0 | - |
| Blockchain transaction encoding | RLP, EIP-1559 envelope, transaction policy | 7 | 7 | 0 | - |
| Network packet parsers and protocol state machines | Ethernet, ARP, IPv4, ICMP, TCP, HTTP, SLIP, CRC-32, UART, market-data quote and strategy blocks | 37 | 31 | 6 | `order` (6) |
| Field buses and serial links | CAN, CANopen, DroneCAN, I2C, SPI, LIN, MIL-STD-1553, SBUS, CRSF, PCIe, USB | 24 | 22 | 2 | `order` (2) |
| Controllers and filters | PID, LQR, observer, IIR biquad, precision sweeps | 15 | 9 | 6 | `signal` (2), `external-timeout` (2) |
| Processor and SoC building blocks | RV32 core, pipeline, CSR, MMU, CLINT, UART, divider, AXI4-Lite, arbiter, SoC top | 20 | 16 | 4 | `multi-output` (3), `order` (1) |
| Video codec (H.264) | DCT, quantisation, entropy coding, NAL packing, encoder and decoder tops | 12 | 6 | 6 | `multi-output` (6) |
| Neural-network accelerator (YOLOv8) | convolution engine, activation, pooling, residual blocks, backbone, neck, head, top | 16 | 13 | 3 | `multi-output` (2), `order` (1) |
| Language, compiler and example regressions | tests of the Signal DSL and the compiler, tutorial and example circuits | 107 | 75 | 32 | `table` (7), `unsupported-invocation` (6) |

## Summary (computed from the TSV)

| | strict | refused | unmeasured | total |
|---|---|---|---|---|
| real IP | 168 | 52 | 0 | 220 |
| regression | 75 | 22 | 10 | 107 |
| **all** | 243 | 74 | 10 | 327 |

Stage that stopped the main route first, for the not-strict rows:

| cause | rows |
|---|---|
| `order` | 24 |
| `proof` | 17 |
| `multi-output` | 15 |
| `table` | 7 |
| `case-error` | 6 |
| `unsupported-invocation` | 6 |
| `source-missing` | 4 |
| `signal` | 3 |
| `external-timeout` | 2 |

## How to read the stage names

The stage is the point of the entry's refusal pipeline at which the entry stopped. `proof`: the
generated proof did not check within the fixed budgets (the common case for large arithmetic
cones). `multi-output` and `packed`: the result shape (several outputs, a tuple) is not one the
route handles. `table`: the declaration shape is not one the port table can read. `order`: no
well-ordered arrangement of the body exists (for example a combinational cycle). `hier-shape`,
`scope`, `conns`, `open`: obligations of hierarchies (instances) that the route does not cover.
`shape`: a memory shape that is not supported. `signal`: the process ended by a signal.
`prep`: the preparation command of the deep route did not succeed. `external-timeout`: the harness
time limit. `case-error`, `unsupported-invocation`, `source-missing`: the row could not be driven
by the route (a Lean error outside the checked block, a command form the route cannot drive, a
declaration that cannot be resolved). The complete definitions are
in [appendix F](appendix/F-AllCommandRows.md#how-to-read-the-table).

## Which code these numbers are for

The commits (code, measurement, earlier baseline, `main`) are listed in the
[snapshot box](README.md#snapshot-box) of the overview and in the provenance table of
[appendix F](appendix/F-AllCommandRows.md#provenance).

A later, unmerged development snapshot is kept on its own page,
[appendix/E-DevelopmentSnapshot.md](appendix/E-DevelopmentSnapshot.md). Nothing from it is counted
in this page, and nothing on this page changes if it is revised.
