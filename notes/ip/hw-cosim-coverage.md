# HW-level (cycle-accurate JIT co-sim) coverage of handshake outputs

Scope: every hardware module under `IP/` with a done / valid / strobe / ready /
busy-like output. "Co-sim" means the generated hardware is run through
`#sim` / the JIT cycle by cycle and the handshake outputs are checked against
a reference (exactly once per request, none before the first request or after
the last, stable while valid).

Test classes:
- **P**  pure-data test only (no `Signal` hardware run)
- **S**  `Signal`-level interpreter run of the hardware (`Signal.val t`), done
  waited for and value compared; handshake checks are "seen at least once"
- **J**  JIT run, values compared, handshake not checked per cycle
- **C**  JIT co-sim with strict handshake / framing checks

| IP file | Top(s) | Handshake outputs | Existing tests | Class | Priority |
|---|---|---|---|---|---|
| IP/Net/UART.lean | `uartTxHW`, `uartRxHW` | `txReady`, `rxValid` | UARTTest (S, loopback happy path only); UsbWebServerJITTest (indirect); **uart-hw-jit-test (C)** | C | was **high** (every UART top is built on it; user-facing serial protocol) |
| IP/Bus/SPIHW.lean | `spiMasterHW` | `done`, `cs` | SPIHWTest (S: "done seen"); **spi-hw-jit-test (C)** | C | was **high** (multi-cycle FSM, `done` exactly-once never checked) |
| IP/Net/SLIP.lean | `slipFramerHW`, `slipDeframerHW` | `txValid`, `txReady`, `outValid`, `frameDone` | SLIPTest (P + S loopback); **slip-hw-jit-test (C)** | C | was **high** (framing/escape protocol) |
| IP/Bus/I2CHW.lean | `i2cMasterHW` | `busy` | I2CHWTest (S state trajectory, eyeballed); **i2c-hw-jit-test (C)** | C | was medium |
| IP/Bus/CANHW, CANopenHW, DroneCANHW | `crc15HW`, `nmtStateFsmHW`, `transferIdTrackerHW` (no CAN frame controller exists) | crc start/valid, NMT state, tracker `error` strobe | `*HWTest` (S); **can-family-hw-jit-test (C)** | C | was medium |
| IP/Bus/LINHW, MIL1553HW, SBUSHW, CRSFHW | per file | frame-done / error strobes | `*HWTest` (S) | S | medium |
| IP/Net/MemcachedHW.lean | memcached HW | `replyValid`, `busy` | MemcachedHWTest (S), MultiOutputSubModuleHangRepro; **memcached-hw-jit-test (C)** | C | was medium |
| IP/Net/MemcachedServer.lean | server top | `outValid` | MemcachedServerJITTest | J | medium |
| IP/Net/UsbWebServer.lean | web server top | `valid` | UsbWebServerSimTest (S), UsbWebServerJITTest (J) | J | medium |
| IP/Net/ARP, Ethernet, ICMP, IPv4, TCP, HTTP, HFTStrategy | parsers/builders | `done`, `valid`, `hdrDone`, `payloadValid`, `txValid`, `outValid` | per-file tests (S); IPv4JITTest (J) | S/J | medium |
| IP/Bus/PCIe, PCIeHFT | | `valid`, `cplValid`, `writePulse`, `outValid` | PCIeTest, PCIeHFTTest (S) | S | low |
| IP/USB/Fido2Demo.lean (+CTAPHID, CBOREmitHW) | `fido2Demo` UART top | `assertionDone`, `msgDone`, `headValid` | Fido2DemoHWJITTest | **C** | done |
| IP/Crypto/PolicySignDemo, PolicySignDemoM2 | UART tops | `signDone`, `rejected` | `*HWJITTest` | **C** | done |
| IP/Crypto/EcdsaSignDemo, P256SignDemo, EcdsaSign cores | sign cores / UART top | `done`, `signDone` | `*HWJITTest` | **C** | done |
| IP/Crypto/EcdsaSignSmall(+Demo) | small sign core | `done`, `busy` | Drivers/EcdsaSignSmallSim (S/driver) | S | low (driver-only, not in CI) |
| IP/Crypto/SHA256, SHA256Stream, Keccak256Sponge, HMACSHA256HW, Rfc6979HW | | `done` | `*JITTest`; **`*-done-hw-jit-test` (C)** | C | was medium |
| IP/Crypto/{AES,AESGCM,GHASH,Keccak256,SHA512Block,HMACSHA512,HKDF,Merkle,RLP,Eip1559Envelope,BIP32CKD,ModInv,Goldilocks}HW | | `done`, `ready`, `headerValid` | `*HWTest` (S) | S | low-medium (data-heavy; `done` waited, values compared) |
| IP/Crypto/{Secp256k1,P256,Ed25519,BLS12-381,G2}* HW (Field/Order/PointOp/ScalarMul/ECDSA/Sign, Fp2/6/12) | | `done` | `*HWTest` (S) | S | low (reusable `SignHWJITHarness` covers sign cores already) |
| IP/Control, IP/Drone, IP/Humanoid, IP/YOLOv8, IP/BitNet, IP/RV32 | datapaths / SoCs | internal `done`/`valid` of sub-blocks; no top-level protocol | pure-data / SoC tests | P/S | out of scope (SoC-level tests) |

## Chosen for this issue (top priority lacking HW co-sim)

1. UART transmitter + receiver (`uartTxHW` / `uartRxHW`)
2. SPI master (`spiMasterHW`)
3. SLIP framer + deframer, if time allows (`slipFramerHW` / `slipDeframerHW`)

Added (all in CI, with synthetic negative controls): `uart-hw-jit-test`
(group usb-webserver), `spi-hw-jit-test` (group bus-hw), `slip-hw-jit-test` (group
usb-webserver).  The three defects they found are fixed, and every probe is now in CI:
- UART: `uartRxHW` waits for the idle line after a framing error;
  `uart-rx-framing-error-hw-jit-test` is in CI (group usb-webserver).
- SPI: `spiMasterHW` accepts start on any idle cycle, MOSI is valid at its sampling edge, CPHA 0/1 is
  implemented; the probe cases are folded into `spi-hw-jit-test` (MOSI/MISO at the sampling edge for
  modes 0-3).
- SLIP: see below.
Before the fixes, each probe header described inputs, cycle, expected vs
observed and the suspected source.

The SLIP defect (deframer in idle took ESC as data, so a frame whose first
payload byte is C0/DB decoded wrongly) is fixed in `slipDeframerHW`; its
probe is folded into `slip-hw-jit-test` together with a framer→deframer
loopback over every first byte.

## Batch 2

### I2C master (`i2cMasterHW`) — `i2c-hw-jit-test` (group bus-hw)
Checks, per cycle on the JIT: `busy` rises once per start at start+1 and is
39 half-periods wide (never before the first / after the last start); state, SCL
and SDA per half-period against the documented FSM (START half, 18 bit slots of an
SCL-low + SCL-high half, STOP); an independent I2C slave view of every live
transaction (START = SDA falls while SCL high, 18 bits 101000001101001011 sampled at
SCL rises, SDA stable while SCL high, STOP = SDA rises while SCL high); start pulse
on every cycle of the divider period (bitDiv 1/3/5); extra start while busy
ignored; start held 3 cycles; back-to-back transactions; bitDiv 0/1/2/3/5.
Controls: synthetic (checker accepts ideal, rejects each defect incl. missing
START / STOP, wrong bit, SDA changing while SCL high, the old toggling waveform) and
live (the same defects injected into the real trace, bitDiv 1/3; at bitDiv 0 a
one-sample SCL-high half cannot show a change inside it).
Not checked: slave ACK (latched internally, never checked: no ACK-error output, so a NACK is invisible), read data (none), hold time
between SCL fall and SDA change (same cycle), clock stretching / arbitration (no SCL input).

Fixed (was: probe `i2c-bus-protocol-hw-jit-test`, rc=1; its cases are now in
`i2c-hw-jit-test`, rc=0): SCL toggled at every slot boundary together with SDA
(no START / STOP, 9 SCL pulses for 18 bits) → each bit slot is now an SCL-low and
an SCL-high half, START/STOP slots added; and a one-cycle `start` off a divider
tick was lost (`stNext := mux tick …` in idle) → idle accepts `start` on any cycle,
reloads the divider and latches addr/rw/data at that pulse.

### Memcached KV engine (`kvHw`) — `memcached-hw-jit-test` (group memcached)
63 commands (set/add/get/del, hits, misses, overwrite, FIFO wrap over 20 keys)
vs `applyCommand`, four start schedules, op inputs garbage except on the start
pulse.  Checks `replyValid` exactly once per command at start+4+slot (hit) /
start+19 (miss), nothing before the first start / after the last reply, `busy`
window per command, kind and VALUE key/flags/value; synthetic + live controls.
Not checked: reply fields of non-VALUE replies (don't care), `memcachedServer`
byte stream (MemcachedServerJITTest).
`memcached-hw-busy-start-probe` (CI group memcached): an `opStart` pulse while busy
must be ignored.  Cause of the former failure: op fields, scan index and hit flags
were reloaded on every `opStart`, not only in idle.  Fix: all `opStart` uses in
`kvHw` (IP/Net/MemcachedHW.lean) are gated by `startOk = opStart && isIdle`.  Probe: get
key1 started, del key1 pulse mid-command -> still one reply of kind VALUE.

### CAN family — `can-family-hw-jit-test` (group bus-hw)
`IP/Bus/CANHW.lean` holds only the CRC-15 LFSR (no frame controller). Covered per
cycle on the JIT: `crc15HW` (start priority, valid gating, hold; 4x3000 random
cycles vs `crc15Step`; 7 real classic frames: CRC field and residue 0),
`nmtStateFsmHW` (vs the `NmtCommand` table, reset priority, unknown bytes hold),
`transferIdTrackerHW` (sticky `error` strobe by construction: rises the cycle
after the first bad mid frame incl. lost frame, cleared by the next SOT, ignores
garbage while `valid` is low; plus 3x3000 random cycles vs the documented model).
Synthetic + live controls for each.  Not checked: CAN-FD CRCs (no HW), frame
parsing (no HW).  No defect found.

### Generic done-once-per-request harness (crypto cores) — group crypto-hw
`Tests/IP/Crypto/DoneHWJITHarness.lean`: a `Dut` (apply request + start, junk
inputs, sample) and a pure checker `doneErrors` (exactly one `done` run per
request in [minLat, maxLat], width, value at `done` = reference, outputs stable
until the next start, optional fixed latency, no `done` before the first start /
after the last request).  Controls: `done-hw-jit-harness-test` (synthetic) plus
live controls in every instance.  Instances (all pass, ~35 s each incl. build):
`sha256-block-done-hw-jit-test` (latency 66, block held or garbage after start),
`sha256-stream-done-hw-jit-test` (68 / 135), `hmac-sha256-done-hw-jit-test`
(269 / 336), `keccak256-sponge-done-hw-jit-test` (27 / 54; done 1 cycle wide,
digest held), `rfc6979-done-hw-jit-test` (1486, d = 1).  Not covered: the
Secp256k1/P256/Ed25519/BLS cores (`*HWTest`, S) — same harness applies.
