# TODO

Open work items captured across active development sessions.
Keep entries scoped (one item = one self-contained PR-worth of
work) and add an "Owner / status" line once someone picks one up.

---

## High priority — production blockers

### memcached server top-level synth still hangs
- Current state: `lake exe memcached-server-test` passes (sim
  end-to-end works); `lake exe memcached-oracle-test` and
  `lake exe memcached-hw-test` both pass.  But
  `#synthesizeVerilog (memcachedServer …).outByte` doesn't
  complete — even with `SPARKLE_TRANSLATE_LIMIT=2_000_000` it
  runs out of budget rather than emitting Verilog.
- Root cause: Lean elaborator re-walks structurally-identical
  sub-expressions because pointer-equality differs (`HashMap
  Lean.Expr String` keyed on `Expr.eqv` hits only ~8% of the
  time on FSM-shape circuits).  Per-leaf time grows
  super-linearly (`leaf 0 = 491 ms → leaf 5 = 32.7 s`, same
  Δcalls = 2855).
- Likely fix path:
  1. Audit `module.wires` / `module.body` data structure —
     they're `List` and `++ append` is O(n).  Switching to
     `Array` (or a back-of-list pointer) is the prime
     candidate.
  2. Add per-handler memoisation in `handleTupleProjections`
     keyed by `(source wire name, fst/snd, width)` — that's
     the unique-result key, independent of Expr identity.
- See `~/.claude/projects/.../memory/project_memcached_status.md`
  for the full debugging history (8 attempts logged).

### Compiler perf — beyond what `195a893` already shipped
- `getWireWidth` is now O(1) via cache.  Next prime targets
  found via `SPARKLE_PROFILE=1` profile dump:
  - `handleTupleProjections`: 4816 calls / 1.17 M ms (243 ms
    avg).  Most of this is recursive children; the local
    handler is dominated by `getWireWidth` calls (now O(1))
    + `inferHWTypeFromSignal` (relatively cheap).
  - `handleCircuitMonad`: 5767 calls / 282k ms.  Mostly
    children; entry path is `Bind/Pure` reduction.
- Bench harness needed (see "Tooling" below) so we can quote
  before/after numbers in PRs.

---

## Medium priority — feature work in progress

### Ethereum signing device (`eth-wallet` tasks 422–427)
Goal: a remote-signer FPGA that **holds the private key
in BRAM and never exposes it** — replacing the all-too-common
"plaintext private key in the web3 backend" pattern.
Tier-C scope (full HD wallet): BIP39 → BIP32 → secp256k1
ECDSA → EIP-1559 tx sign → ERC-20 ABI decode for confirmation.

Sub-tasks (see TaskList):
- 422 ✅ Keccak-256 + RLP encoder (pure-data + sim)
- 423 ✅ EIP-1559 tx signer (raw, secp256k1 ECDSA)
- 424 ✅ ERC-20 ABI decode (transfer / approve / transferFrom)
- 425 ✅ BIP39 mnemonic → seed (PBKDF2-HMAC-SHA512, 2048 iters)
- 426 ✅ BIP32 HD wallet child key derivation
- 427 ✅ Pure-data end-to-end signer (mnemonic → broadcast envelope)

Status (2026-06-28): pure-data half complete.
`IP/Crypto/EthWallet.lean::signFromMnemonic` derives the
canonical Hardhat / MetaMask address from the BIP-39 Trezor
mnemonic and emits a valid EIP-1559 envelope.  Byte-exact
cross-compatible with every reference wallet.

Signal-domain HW signer FSM + Tang Nano 50K bring-up
tracked separately in Issue #68 (10-brick decomposition).
RFC 6979 deterministic nonce derivation also deferred to #68.

### HSM-style signer (high throughput)
Different from a Ledger-style personal wallet: server-side
remote signer that auto-approves under an authentication
gate, target **thousands of signatures per second**.

- Reuse existing TLS 1.3 stack for the host channel.
- Need HW-accelerated secp256k1 ECDSA (current
  `IP/Crypto/Secp256k1ECDSA.lean` is pure-data only).
  Target: ~100 μs per sign on Tang Nano 50K — feasible if
  the scalar-mult inner loop is a `Signal.loop`-based
  Montgomery ladder.
- Optional: BLS12-381 sign for Ethereum validator use cases
  (32-byte attestation every 12 s, 96-byte signature).

### Tang Nano 50K USB Web server — hardware bring-up
- Verilog generation works (`lake build
  Tests.IP.Net.UsbWebServerSynth`).
- `.cst` + bring-up README exist (`fpga/tangNano50K/`).
- Not yet tried on real silicon (no hardware in hand for the
  authoring sessions).  Next: actually flash + run
  `curl http://192.168.7.2/`.

### macOS `pppd` SLIP fallback
`pppd`'s SLIP mode varies by build on macOS; bring-up
README documents this.  Need a 100-line Python TUN bridge
as a guaranteed-working alternative.

---

## Tooling

### Build perf benchmark harness
Today the only perf signal is "SPARKLE_PROFILE=1 → tail
/tmp/sparkle-profile.log → eyeball it".  Build a small
benchmark suite that:
- Synthesises a fixed set of IPs (sha256Block, ghashFullHW,
  ethTxByte, kvHw, …) with `SPARKLE_PROFILE=1`.
- Parses the per-handler tick lines.
- Emits a markdown table comparing before/after.
- Optionally fails CI on >10% regression on the hottest
  handler.

Reason: improvements like `195a893` (getWireWidth O(n→1))
have NO way to be quoted in numbers right now — we'd have
to manually diff profile logs.  A benchmark harness turns
this into a single number per PR.

### Lean upstream PR candidates
Things found while debugging Sparkle but rooted in Lean
itself:
- **`Std.HashMap` + `IO.Ref.modify` quadratic trap**:
  when the IO.Ref's HashMap has another live handle (e.g.
  a `let cache ← ref.get` immediately above the
  `ref.modify`), every `.modify` triggers a full table
  copy.  Should be either documented or hot-patched.
- **Elaborator re-elaborates structurally-equal sub-trees
  into fresh Expr nodes**: defeats `HashMap Expr` caches.
  An `Expr.shareCommon`-style eager pass at synth entry
  could help.

---

## Documentation

### CONTRIBUTING.md — new IP add procedure
Documented in this PR (the one shipping
`feat/ip-net-hft-tcpip`).  See `CONTRIBUTING.md` for the
required checklist when adding a new IP.

### docs/architecture/* — Compiler internals
The Sparkle compiler (`Sparkle/Compiler/Elab.lean`) has
grown ~2800 lines with no high-level architecture doc.
Worth writing up:
- The translateExprToWire mutual block + handler order.
- The sub-module instance code path (multi-output sub-
  modules added in `b9899bf`).
- The cache layers (exprCache, sparkleTypeCache,
  sparkleSubModuleCache, sparkleSubInstanceOutputs,
  sparkleFvarValueMap, sparkleWireWidthCache).
- Known gotchas (the synth-elaborator-gotchas note in
  the user's auto-memory).

---

## Tests previously orphaned from CI
Fixed in the PR shipping this TODO.md (the per-feature
test executables were defined in `lakefile.lean` but never
called from `Tests.AllTests.lean`, so `lake exe test`
skipped them).  See `Tests/AllTests.lean` for the new
entries.
