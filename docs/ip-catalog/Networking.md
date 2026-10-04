# Networking Stack — Sparkle IP Catalog

Sparkle ships an end-to-end networking stack that goes from bit-level
UART all the way up to HTTP/1.0 and a memcached ASCII server.
The pieces compose: every layer is `@[hardware_module]` and can be
instantiated either standalone (unit-tested with iverilog round-trip)
or as part of the top-level `usbWebServer` demo running on Tang Nano 50K.

## Layer stack

```
    application  │ USB Web server   memcached ASCII server (Tier-1)
    ─────────────┼─────────────────────────────────────────────
    transport    │ HTTP/1.0         (custom byte-stream ↔ kvHw BRAM)
    ─────────────┼─────────────────────────────────────────────
    session      │ TCP header + FSM (loopback + retransmit + dup-ACK)
    ─────────────┼─────────────────────────────────────────────
    network      │ IPv4  ARP  ICMP  (RFC 791 / 826 / 792)
    ─────────────┼─────────────────────────────────────────────
    link         │ Ethernet framer  (DMAC/SMAC/EtherType + payload)
    ─────────────┼─────────────────────────────────────────────
    serial       │ UART (8-N-1)  SLIP (RFC 1055, END/ESC escaping)
    ─────────────┼─────────────────────────────────────────────
    physical     │ USB-C via BL616 CDC-ACM bridge on Tang Nano 50K
```

## Files

| File | What it defines |
|------|-----------------|
| `IP/Net/UART.lean`             | 8-N-1 bit-level RX / TX, configurable `bitDiv` (99 for 100 MHz / 1 Mbps) |
| `IP/Net/SLIP.lean`             | RFC 1055 framer + deframer (END = 0xC0, ESC = 0xDB) |
| `IP/Net/Ethernet.lean`         | MAC framer + RX / TX header extract + payload streaming |
| `IP/Net/CRC32.lean`            | Bit-serial IEEE 802.3 CRC-32 engine (reference vs HW parity in `crc32-jit-test`) |
| `IP/Net/IPv4.lean`             | RFC 791 IPv4 parser + emitter (checksum, TTL, header options) |
| `IP/Net/ARP.lean`              | ARP requester + responder |
| `IP/Net/ICMP.lean`             | ICMP echo request / reply |
| `IP/Net/TCP.lean`              | TCP header + connection state machine (loopback, retransmit, dup-ACK) |
| `IP/Net/TCPState.lean`         | Formal TCP state machine + invariants |
| `IP/Net/HTTP.lean`             | HTTP/1.0 emitter + parser + iverilog loopback |
| `IP/Net/UsbWebServer.lean`     | Top-level `usbWebServer` wiring UART→SLIP→IPv4→TCP→HTTP and back |
| `IP/Net/Memcached.lean`        | Pure-data memcached parser + KV oracle (reference semantics) |
| `IP/Net/MemcachedHW.lean`      | `kvHw` BRAM-backed engine (3 `Signal.memory` instances) |
| `IP/Net/MemcachedServer.lean`  | Byte-stream FSM driving the KV engine, `@[hardware_module]` |
| `IP/Net/HFTOverTLS.lean`       | HFT-over-TLS transport (TCP + TLS + custom framing) |
| `IP/Net/HFTStrategy.lean`      | HFT strategy state machine reference |

## Tang Nano 50K bring-up (`usbWebServer`)

```
USB-C (BL616 CDC-ACM bridge) ──UART──> FPGA
                                         │
                          UART → SLIP → IPv4 → TCP → HTTP
                                         │
                          HTTP → TCP → IPv4 → SLIP → UART
                                         │
                                       USB-C ──> host
```

- Pin constraints: `fpga/tangNano50K/usb_webserver.cst`.
- Step-by-step bring-up (macOS pppd / Linux slattach):
  `fpga/tangNano50K/README.md`.
- Resource fit: ~20 `always_ff` regs, **LUT 2% / BRAM 0%** on Tang
  Nano 50K.

## memcached ASCII server (Tier-1)

Tier-1 supports `get` / `set` / `add` / `delete`, key ≤ 8 B, value
≤ 16 B, 16 BRAM slots.  Both the pure-data reference (`kvOracle`)
and the hardware engine (`kvHw`) are byte-exact against the same
Lean spec.

End-to-end sim (JIT-backed, ~3 s):

```bash
lake exe memcached-server-jit-test
```

Round-trips
```
input:  "set foo 0 0 5\r\nhello\r\nget foo\r\n"
output: "STORED\r\nVALUE k 0 16\r\n…hello\r\nEND\r\n"
```

Resource fit: **LUT 1% / BRAM 25% / Fmax ≈ 57 MHz** on Tang Nano 50K.

## Sim entry points

Every layer has both a JIT-backed and a pure-Lean simulator:

| Command | Backend | When to use |
|---------|---------|-------------|
| `lake exe usb-webserver-jit-test`      | JIT     | CI gate, byte-exact round-trip |
| `lake exe usb-webserver-sim`           | Lean    | Debug introspection (slower, per-cycle `Signal.val`) |
| `lake exe memcached-server-jit-test`   | JIT     | CI gate, byte-exact `STORED/VALUE/…/END` |
| `lake exe memcached-server-test`       | Lean    | Debug introspection |
| `lake exe memcached-oracle-test`       | Lean    | Pure-data KV oracle unit tests |
| `lake exe memcached-hw-test`           | Lean    | `kvHw` sim vs oracle (128-bit BitVec, minutes) |
| `lake exe uart-test` / `slip-test`     | Lean    | Byte-stream primitives |
| `lake exe ethernet-test` / `arp-test`  | Lean    | Layer-2 header extraction |
| `lake exe ipv4-jit-test`               | JIT     | IPv4 parser byte-exact |
| `lake exe tcp-loopback-test`           | Lean    | TCP FSM loopback |
| `lake exe http-test`                   | Lean    | HTTP request/response emit + parse |
| `lake exe crc32-jit-test`              | JIT     | CRC-32 engine parity with reference |

## Verilog output

Every layer's top module is `@[hardware_module]` and produces
synthesizable SystemVerilog via `#synthesizeVerilog` (or the
matching `#writeDesign`).  Byte-exactness against the Lean
reference is checked cycle-by-cycle in the JIT tests above.
