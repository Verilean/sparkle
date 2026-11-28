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
| IP/Bus/CANHW, CANopenHW, DroneCANHW, LINHW, MIL1553HW, SBUSHW, CRSFHW | per file | frame-done / error strobes | `*HWTest` (S) | S | medium |
| IP/Net/MemcachedHW.lean | memcached HW | `replyValid`, `busy` | MemcachedHWTest (S), MultiOutputSubModuleHangRepro | S | medium |
| IP/Net/MemcachedServer.lean | server top | `outValid` | MemcachedServerJITTest | J | medium |
| IP/Net/UsbWebServer.lean | web server top | `valid` | UsbWebServerSimTest (S), UsbWebServerJITTest (J) | J | medium |
| IP/Net/ARP, Ethernet, ICMP, IPv4, TCP, HTTP, HFTStrategy | parsers/builders | `done`, `valid`, `hdrDone`, `payloadValid`, `txValid`, `outValid` | per-file tests (S); IPv4JITTest (J) | S/J | medium |
| IP/Bus/PCIe, PCIeHFT | | `valid`, `cplValid`, `writePulse`, `outValid` | PCIeTest, PCIeHFTTest (S) | S | low |
| IP/USB/Fido2Demo.lean (+CTAPHID, CBOREmitHW) | `fido2Demo` UART top | `assertionDone`, `msgDone`, `headValid` | Fido2DemoHWJITTest | **C** | done |
| IP/Crypto/PolicySignDemo, PolicySignDemoM2 | UART tops | `signDone`, `rejected` | `*HWJITTest` | **C** | done |
| IP/Crypto/EcdsaSignDemo, P256SignDemo, EcdsaSign cores | sign cores / UART top | `done`, `signDone` | `*HWJITTest` | **C** | done |
| IP/Crypto/EcdsaSignSmall(+Demo) | small sign core | `done`, `busy` | Drivers/EcdsaSignSmallSim (S/driver) | S | low (driver-only, not in CI) |
| IP/Crypto/SHA256, SHA256Stream, Keccak256Sponge, HMACSHA256HW, Rfc6979HW | | `done` | `*JITTest` | J | medium (value + done wait; no exact-once check) |
| IP/Crypto/{AES,AESGCM,GHASH,Keccak256,SHA512Block,HMACSHA512,HKDF,Merkle,RLP,Eip1559Envelope,BIP32CKD,ModInv,Goldilocks}HW | | `done`, `ready`, `headerValid` | `*HWTest` (S) | S | low-medium (data-heavy; `done` waited, values compared) |
| IP/Crypto/{Secp256k1,P256,Ed25519,BLS12-381,G2}* HW (Field/Order/PointOp/ScalarMul/ECDSA/Sign, Fp2/6/12) | | `done` | `*HWTest` (S) | S | low (reusable `SignHWJITHarness` covers sign cores already) |
| IP/Control, IP/Drone, IP/Humanoid, IP/YOLOv8, IP/BitNet, IP/RV32 | datapaths / SoCs | internal `done`/`valid` of sub-blocks; no top-level protocol | pure-data / SoC tests | P/S | out of scope (SoC-level tests) |

## Chosen for this issue (top priority lacking HW co-sim)

1. UART transmitter + receiver (`uartTxHW` / `uartRxHW`)
2. SPI master (`spiMasterHW`)
3. SLIP framer + deframer, if time allows (`slipFramerHW` / `slipDeframerHW`)

Added (all in CI, with synthetic negative controls): `uart-hw-jit-test`
(group ethernet), `spi-hw-jit-test` (group bus-hw), `slip-hw-jit-test` (group
ethernet).  The three defects they found are fixed, and every probe is now in CI:
- UART: `uartRxHW` waits for the idle line after a framing error;
  `uart-rx-framing-error-hw-jit-test` is in CI (group ethernet).
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
20 slots wide (never before the first / after the last start), state, SCL and SDA
per slot against the documented FSM, extra start while busy ignored, start held
3 cycles, back-to-back transactions, bitDiv 0/1/2/3/5; synthetic + live controls.
Not checked: slave ACK (internal only), read data (none).

Defects found (design untouched; probes NOT in CI):
- `i2c-bus-protocol-hw-jit-test`: the SDA/SCL waveform is not I2C. SCL toggles
  once per slot and SDA changes on the same slot boundary, so 18 bits take 9 SCL
  pulses (10 rises incl. start/stop slots); there is no START (SDA never falls while SCL
  high) and no STOP (SDA never rises while SCL high).
- (see report) with bitDiv > 0, a `start` pulse that is not on a divider tick
  is dropped (state only leaves idle on a tick).
