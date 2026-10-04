# Tang Nano 50K — secp256k1 ECDSA signing demo

`IP/Crypto/EcdsaSignDemo.lean` is a self-contained, synthesizable
top-level that signs a message hash on the FPGA and streams the
signature back over UART. It wires the full eth-wallet secp256k1 ECDSA
signer stack — scalar-mul ladder → Jacobian point-op → bit-serial field
multiplier, plus two Fermat modular inverses (mod p and mod n) — into a
single closed-loop `circuit do`, fronted by a UART byte protocol.

## What it does

```
Host ── UART RX (96 bytes, big-endian) ──▶ FPGA
          d[32] ‖ k[32] ‖ z[32]
            d = private key
            k = per-signature nonce
            z = message hash (32-byte)

FPGA ── UART TX (64 bytes, big-endian) ──▶ Host
          r[32] ‖ s[32]      (the ECDSA signature)
```

RFC 6979 deterministic-`k` derivation and the SHA-256 of the message are
**host concerns** — the FPGA takes the three 256-bit scalars directly,
exactly as the pure-data `Secp256k1ECDSA.sign d k z` reference does. This
keeps the demo focused on the elliptic-curve datapath (the expensive,
security-critical part) and off-loads hashing to the host.

## Timing & resources

* **Latency:** one signature ≈ **1.8 M cycles** (a 256-bit double-and-add
  ladder over a 258-cycle/multiply bit-serial field multiplier, plus two
  Fermat inverses). At a **27 MHz** Tang Nano clock that is ≈ **67 ms per
  signature** — comfortable for a hardware-wallet "press-to-sign" UX.
* **Fit estimate (Tang Nano 50K, GW5AST-138, ~50K+ LUT):** the datapath
  is dominated by a handful of bit-serial multipliers (each ~a few hundred
  LUTs) plus the orchestration FSMs and a few thousand flip-flops of state
  (256-bit registers). Estimated well under half the fabric — comfortable
  fit with room to spare. (Run the vendor place-and-route for the exact
  number; this design is intentionally area-light, trading cycles for LUTs.)

## Baud / clock

8-N-1, **115200 baud**. `bitDiv = clk / baud − 1`:

| Clock   | bitDiv |
|---------|--------|
| 27 MHz  | 233 (`0xE9`) — `EcdsaSignDemo.bitDiv27M115200` |

Pass whatever `bitDiv` matches your board clock as the top-level input.

## Top-level ports

```lean
def ecdsaSignDemo (uartRx : Signal dom Bool) (bitDiv : Signal dom (BitVec 16)) : DemoOut
  -- DemoOut { uartTx : Bool, signDone : Bool }
```

* `clk`   — implicit via the Signal domain (drive from the 27 MHz oscillator).
* `rst`   — the domain reset (wire to a button; active per your domain config).
* `uartRx` — from the BL616 CDC-ACM bridge TX → FPGA input.
* `uartTx` — FPGA output → bridge RX.
* `signDone` — one-cycle strobe when a signature completes; wire to an LED
  for a visible "done" blink (latch it in your board wrapper if you want it
  to stay lit).

## Pin constraints (`.cst`) — placeholder

Adjust to your board revision; reuse the same UART pins as the
usb-webserver bring-up (BL616 CDC-ACM bridge). Example skeleton:

```
// 27 MHz oscillator
IO_LOC  "clk"    52;
IO_PORT "clk"    IO_TYPE=LVCMOS33;

// reset button
IO_LOC  "rst"    3;
IO_PORT "rst"    IO_TYPE=LVCMOS33 PULL_MODE=UP;

// UART to the on-board BL616 USB-serial bridge
IO_LOC  "uartRx" 18;   // bridge TX  -> FPGA
IO_PORT "uartRx" IO_TYPE=LVCMOS33;
IO_LOC  "uartTx" 17;   // FPGA       -> bridge RX
IO_PORT "uartTx" IO_TYPE=LVCMOS33;

// done LED
IO_LOC  "signDone" 10;
IO_PORT "signDone" IO_TYPE=LVCMOS33;
```

> **TODO (board-specific):** the pin numbers above are placeholders. Fill
> in the actual Tang Nano 50K pin map for your revision (the UART bridge
> pins and 27 MHz clock pin are documented in the Sipeed Tang Nano 50K
> schematic / the usb-webserver bring-up).

## Host-side usage (sketch)

```python
import serial
ser = serial.Serial("/dev/ttyACM0", 115200, timeout=5)

d = bytes.fromhex("...")  # 32-byte private key
k = bytes.fromhex("...")  # 32-byte nonce (RFC 6979 on the host)
z = bytes.fromhex("...")  # 32-byte message hash (SHA-256 on the host)
assert len(d) == len(k) == len(z) == 32

ser.write(d + k + z)          # 96 bytes, big-endian
sig = ser.read(64)            # r ‖ s, big-endian
r, s = sig[:32], sig[32:]
print("r =", r.hex(), "\ns =", s.hex())
```

Cross-check the returned `(r, s)` against any secp256k1 library
(`sign(d, z)` with the same `k`) — they match the pure-data
`Secp256k1ECDSA.sign` reference, which is validated against the SEC1 /
RFC-6979 test vector in `Tests/IP/Crypto/EcdsaSignDemoTest.lean`.

## How to regenerate the Verilog

```
#synthesizeVerilog on `ecdsaSignDemo` (via
Tests/IP/Crypto/EcdsaSignDemoTest.lean's SynthesisChecks) emits the
SystemVerilog. `lake build Tests.IP.Crypto.EcdsaSignDemoTest` regenerates
it as part of the build.
```

## Architecture note

The signer is a deep stack of start/done handshakes:

```
signHW ─┬─▶ scalarMulHW ─▶ pointOpHW ─▶ mulHW        (k·G)
        ├─▶ modInvHW(p) / mulHW         (mod-p inverse + muls)
        └─▶ modInvHW(n) / mulModNHW     (mod-n inverse + muls)
```

Each sub-engine exposes its "drive" side as **output ports** and takes the
result back as **input ports**. The demo closes every loop with a
one-cycle feedback register inside a single `circuit do` (a `reg` handle
used before its `<~`), which is the standard clocked-feedback closure and
synthesizes cleanly. Each engine is called through a thin
`@[hardware_module]` wrapper so the synth elaborator emits it as a Verilog
sub-module instance (letting the top project the engine's output-record
fields).
