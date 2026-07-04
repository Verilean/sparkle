# FIDO2 Authenticator (Tang Nano 50K) — M1–M3

A FIDO2/CTAP2 security key (Google/GitHub passkey login) built on the
Sparkle crypto stack, phased M1→M3 (of a 5-milestone plan; M4 native
soft-USB-FS and M5 PIN/hmac-secret are deferred).

## M1 — pure CTAP2 data layer (PR #97)

`P256ECDSA.sign`, `DerSig` (ECDSA→DER), `CBOR` (CTAP2-canonical subset),
`CTAP2Data` (COSE key / authenticatorData / make+get responses). Locks
the exact byte layouts; end-to-end `verify(Q, SHA256(authData‖cdh), r,s)`.

## M2 — P-256 HW sign stack (PR #98)

`P256PointJac` (a=−3 Jacobian ref), `P256PointOpHW` (a=−3 DOUBLE),
`P256ScalarMulHW`, `P256OrderHW`, `P256ECDSAHW`, `p256SignCore`,
`SHA256Stream`. iverilog-clean; sign core == `P256ECDSA.sign`.

## M3 — CTAPHID + CBOR emit + UART-bridge getAssertion top

| File | Role |
|------|------|
| `IP/USB/CTAPHID.lean` | 64-byte HID-report framer/deframer (INIT+CONT reassembly); pure oracles `ctapHidFrame`/`ctapHidDeframe`. |
| `IP/USB/CBOREmitHW.lean` | byte-serial CBOR head emitter (RLPHW-style; shortest-form 1/2/3/5-byte heads). |
| `IP/USB/Fido2Demo.lean` | Tang Nano getAssertion top: UART RX fixed frame → on-chip SHA-256(authData‖cdh) → `p256SignCore` → UART TX r‖s. |
| `host/fido2/` | Python host shim + README (frame builder / DER encode / verify; `--selftest`). |

Also (prerequisite): made `SHA256.sha256Block` synthesizable — the
Σ/σ/Ch/Maj bit-functions are now fully inlined at their call sites (a
named `Signal→Signal` def, and even a local lambda that *returns* an
applicative chain, is opaque to `#synthesizeVerilog`).

### getAssertion signing operation

    signature = ECDSA-P256(d, SHA-256(authenticatorData ‖ clientDataHash))

computed with the hash produced **on-chip** — the exact value a WebAuthn
assertion carries.

### Wire framing (M3 simplification)

A host shim sends a fixed **133-byte** frame (`d ‖ authData(37) ‖
clientDataHash(32) ‖ k(32)`) and reads back 64-byte `r‖s`. A full HW
CTAPHID+CBOR *parser* into the top is M4/M5; the CTAPHID framer/deframer
and CBOR emitter are verified as standalone hardware modules here.
`d`/`k` over the wire are DEMO-ONLY (insecure nonce); a real device keeps
`d` on-chip and derives `k` via RFC-6979.

### Verification

- `ctap2-data-test`, `fido2-demo-test` — ALL PASS (end-to-end assertion
  verify; CTAPHID frame round-trip; on-chip hash contract).
- `#synthesizeVerilog` on `fido2Demo.uartTx` + `.assertionDone`, the
  CTAPHID deframer, and the CBOR head emitter — all generate Verilog.
- `iverilog -g2012 -s fido2Top` elaborates the full 13-module design
  (4.7 MB vvp).
- `host/fido2/fido2_shim.py --selftest` — independent Python verify of
  the same vector.
