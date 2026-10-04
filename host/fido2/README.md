# FIDO2 getAssertion host shim (M3)

The Tang Nano `fido2Demo` top implements the core FIDO2 getAssertion
crypto over the BL616 CDC-ACM UART bridge:

    signature = ECDSA-P256(d, SHA-256(authenticatorData ‖ clientDataHash))

computing the SHA-256 signing hash **on-chip** and signing it with the
on-chip P-256 signer. This is the exact value a WebAuthn assertion
carries; the host DER-encodes `r‖s` and wraps the CTAP2 response.

## Wire framing (M3 simplification)

A full HW CTAPHID + CBOR parser is deferred (M4/M5). For M3 the host
sends a **fixed 133-byte frame**, MSB byte first, over the serial port:

    d(32) ‖ authenticatorData(37) ‖ clientDataHash(32) ‖ k(32)

and reads back the 64-byte raw signature `r‖s`. The CTAPHID framer/
deframer (`IP.USB.CTAPHID`) and CBOR head emitter (`IP.USB.CBOREmitHW`)
are verified as standalone hardware modules; wiring the full 64-byte
report + CBOR-streaming layer into the top is a later milestone.

`d` and `k` are sent over the wire for the demo. A production device
keeps `d` on-chip (stateless-credential AES-wrap, see the plan) and
derives `k` via RFC-6979 (M5) — **the wire-supplied nonce path here is
insecure and DEMO-ONLY.**

## Usage

```
pip install pyserial fido2 cryptography
python fido2_shim.py --port /dev/ttyACM0
```

`fido2_shim.py`:
1. builds `authenticatorData` (rpIdHash ‖ flags ‖ signCount) and
   `clientDataHash` from a WebAuthn request (or a self-test vector),
2. sends the 133-byte frame, reads back `r‖s`,
3. DER-encodes the signature and (optionally) verifies it against the
   public key `Q = d·G` — the same end-to-end check the Lean test runs.

Run `python fido2_shim.py --selftest` to exercise the flow against a
fixed vector without hardware (uses the `cryptography` library as the
reference verifier). This mirrors `Tests/IP/USB/Fido2DemoTest.lean`.
