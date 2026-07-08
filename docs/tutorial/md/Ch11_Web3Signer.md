# Chapter 11 — Running the web3 Signing Device on Real Hardware

The previous chapters took a *toy* design (a blinky) all the way to
silicon. This chapter does the same for a **real security product**: a
secp256k1 Ethereum signer whose private key never leaves the die. You'll
generate its Verilog from Sparkle Lean source, clock it with an on-chip
**PLL**, flash it to a **Tang Nano 20K**, sign an Ethereum transaction
hash from your PC over UART, and finally **broadcast a real transfer to a
local Ethereum node** (§11.8) — watching the balance move on-chain and
`ecrecover` land on the chip's own address.

This is the **on-chip-key** signer (`IP/Crypto/EcdsaSignMsgDemo.lean`,
`signZDemo`): the key `d` is baked into the bitstream, the ECDSA nonce `k`
is derived **on-chip** via RFC-6979, and the only thing that crosses the
wire is the 32-byte transaction hash `z`. A compromised host learns
neither `d` nor `k`; and because `k` never leaves the die, it cannot back
`d` out of a signature (`d = (s·k − z)·r⁻¹`). Its policy-enforcing sibling
— PolicySignDemo, which adds an on-chip allowlist + cap — is in
[`docs/ip-catalog/PolicySignDemo.md`](../../ip-catalog/PolicySignDemo.md)
(§11.10).

Everything below was run on real hardware: a Tang Nano 20K (Gowin
GW2A-18) signing two live transfers on a local `anvil` node.

## 11.1 What the device does

`signZDemo` is a hardware security module in miniature:

- Bakes a secp256k1 private key `d` into the bitstream (the demo uses
  `d = 12345`, address `0xeb4665750b1382df4aebf49e04b429aaac4d9929`).
- Receives a 32-byte hash `z` over UART.
- Derives the nonce **on-chip**: `k = RFC-6979(d, z)`, an HMAC-SHA-256 K/V
  state machine (`IP/Crypto/Rfc6979HW.lean`) driving one on-chip SHA-256.
- Computes `(r, s)` with the on-chip secp256k1 signer — a bit-serial
  modular ALU with a **16-bit word-serial multiplier** (shifts + a 17-bit
  adder, *no DSP*) sequenced by microcode over a BRAM register file
  (`IP/Crypto/EcdsaSignSmall.lean`).
- Returns `r‖s` over UART.

The private key never travels the wire, and the nonce never leaves the
chip — the two properties a "blind" software signer can't give you.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import IP.Crypto.EcdsaSignMsgDemo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.EcdsaSignMsgDemo

namespace Notebooks.Ch11

```
## 11.2 Generate the Verilog

The Sparkle top is `signZDemo (uartRx) (bitDiv) : DemoOut`, exposing
`uartTx` and `signDone`. As in the blinky chapter, project the output you
route to a pin and hand it to `#synthesizeVerilog`:

```lean
-- The signer is a deep FSM stack (RFC-6979/SHA-256 + secp256k1 signer);
-- give the elaborator room.
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

def signZTx
    (uartRx : Signal defaultDomain Bool)
    (bitDiv : Signal defaultDomain (BitVec 16)) :
    Signal defaultDomain Bool :=
  (signZDemo uartRx bitDiv).uartTx

#synthesizeVerilog signZTx

```
`lake build` on this chapter runs that elaboration and prints
`-- Verilog successfully generated!`. For the FPGA flow we use the
**hierarchical** emitter (smaller; keeps the sub-modules as separate
Verilog modules), driven by a small script:

```bash
lake env lean fpga/tangNano20k/build/GenSignZDemoSynth.lean
# → writes fpga/tangNano20k/build/sign_z_demo.v (UART RX/TX, SHA-256, HMAC,
#   RFC-6979, the regfile + 16-bit word-serial multiplier, the ladder /
#   opctrl / signctrl engines, and the signing core signZSmallDemo).
```

The core we instantiate on the board is
`Sparkle_IP_Crypto_EcdsaSignMsgSmall_signZSmallDemo`, whose parallel
interface is `(_gen_start, _gen_z[255:0], clk, rst) → (rOut[255:0],
sOut[255:0], done)` — the board wrapper feeds it `z` from its own UART RX
and streams `r‖s` back from its own UART TX (§11.4).

## 11.3 Clock it with an rPLL — not fabric logic

On the small Gowin parts you **must** generate the core clock with the
PLL primitive. Two natural-looking alternatives both fail on the GW2A-18:

- Clocking the core straight off the 27 MHz crystal pin explodes the
  wide-mux mapping (~69 % LUT4, unroutable on this dense design).
- A ÷2 clock made from a fabric flip-flop and buffered through a `BUFG`
  is **dead** — an LED probe on that clock never toggles, so the core
  never runs and the UART only spits noise.

A Gowin **`rPLL`** (27 → 13.5 MHz) fixes both: its output is a genuine
global clock, *and* the netlist packs ~49 % LUT4 (0 hold violations,
Fmax ≫ 13.5 MHz). The board wrapper
(`fpga/tangNano20k/sign_z_uart_top.v`) instantiates it:

```verilog
wire clk_div, pll_lock;
rPLL #(.FCLKIN("27.0"), .IDIV_SEL(1), .FBDIV_SEL(0), .ODIV_SEL(64),  // 27*1/2 = 13.5 MHz
       .CLKFB_SEL("internal"), /* … */)
  pll (.CLKOUT(clk_div), .LOCK(pll_lock), .CLKIN(clk), .CLKFB(1'b0), /* … */);
// bit_div = 13.5 MHz / 115200 − 1 = 116
```

(The larger GW5A parts close timing straight off the crystal, so the
50K/PolicySignDemo wrapper skips the PLL — but on the 20K, use it.)

## 11.4 The framed UART protocol

Give the device a **framed request → response with a status byte** from
the start — don't stream raw bytes and make the host guess boundaries
(§11.9 explains why). The board wrapper's UART front-end speaks:

```
request :  z            (32 bytes, big-endian)
response:  A5 5A         (2-byte sync marker)
           01            (status: 01 = signature ready; reserve EE = error)
           r  (32 bytes) s (32 bytes)
```

The device signs on receiving 32 bytes and then repeats the 67-byte
response frame; the host syncs on `A5 5A`, checks the status, and reads
`r‖s`. `fpga/tangNano20k/sign_z_uart_top.v` emits the frame;
`host/sign_z/sign_z.py` parses it.

## 11.5 Pin constraints

`fpga/tangNano20k/sign_z_uart.cst` maps the 27 MHz `clk` (pin 4), the
`rst` button (pin 88), `uart_rx_line`/`uart_tx` (pins 70/69, wired to the
on-board BL616 bridge), and six user LEDs (pins 15–20; the wrapper blinks
a heartbeat on three and lights the other three when a signature is
ready — a handy "is the clock alive / did it sign" probe).

## 11.6 Synthesize, place-and-route, flash

Same open-source Gowin flow as the other Tang Nano demos. The signer core
is dense, so use the flat ABC9 packing (as `sign_z_uart` does):

```bash
cd fpga/tangNano20k
yosys -p "read_verilog -sv sign_z_uart_top.v; read_verilog -sv build/sign_z_demo.v; \
          synth_gowin -top sign_z_uart_top -run :map_luts; \
          read_verilog -icells -lib -specify +/abc9_model.v; abc9 -maxlut 8; \
          synth_gowin -top sign_z_uart_top -run map_cells:; \
          write_json build/sign_z_uart.json"
nextpnr-himbaechel --device GW2AR-LV18QN88C8/I7 --vopt family=GW2A-18C \
    --vopt cst=sign_z_uart.cst --json build/sign_z_uart.json --write build/sign_z_uart_pnr.json
gowin_pack -d GW2A-18C -o build/sign_z_uart.fs build/sign_z_uart_pnr.json

# Flash to SPI flash (-f) so the design is PERSISTENT — see §11.9.
openFPGALoader -f -b tangnano20k build/sign_z_uart.fs
```

(Routing is slow on this arithmetic-dense design — the himbaechel router
grinds down the last congestion over many minutes — but it closes at
~49 % LUT4 with 0 hold violations.)

## 11.7 Sign a hash from the host

`host/sign_z/sign_z.py` is dependency-free (pure-Python secp256k1 + raw
`termios`), so `--selftest` checks the crypto with no board:

```bash
python3 host/sign_z/sign_z.py --selftest         # pubkey + a sample signature
python3 host/sign_z/sign_z.py --port /dev/ttyUSB1 --z 123456789
# → sends z, reads the framed r‖s, prints "signature verifies against Q = 12345·G : YES ✓"
```

The FPGA UART is the **interface-1** node — `/dev/ttyUSB1`, *not*
`ttyUSB0` (that's JTAG; opening it as a serial port wedges JTAG). The
driver handles the two on-board-bridge quirks for you (§11.9): it pulses
DTR/RTS to enable host→FPGA, and reads on a fresh fd after the write.

## 11.8 Broadcast a real transfer to a local node (anvil)

`host/sign_z/eth_sign_tx.py` builds a canonical EIP-1559 transfer **from
the signer's address**, gets `(r,s)` from the FPGA over UART, normalizes
to low-`s` (EIP-2), recovers the y-parity, assembles the signed raw
transaction, and broadcasts it over JSON-RPC — **zero dependencies**
beyond stdlib (`urllib`; no `web3`).

```bash
# start a local chain (chainId 31337)
anvil                 # (nix: `nix-shell -p foundry --run anvil`)

# fund the FPGA signer's address from a pre-funded anvil account
cast send --private-key 0xac09…bacb478… 0xeb4665750b1382df4aebf49e04b429aaac4d9929 --value 100ether

# the FPGA signs a real EIP-1559 tx hash and broadcasts the transfer
python3 host/sign_z/eth_sign_tx.py --port /dev/ttyUSB1 \
    --to 0x70997970C51812dc3A010C7d01b50e0d17dc79C8 --value 1000000000000000000
```

Output — a real transaction, signed on the chip, mined, funds moved:

```
from      0xeb4665750b1382df4aebf49e04b429aaac4d9929   ← the FPGA (d=12345)
z         0x9b6d55a5…256c8731        keccak256(0x02‖rlp([…]))
signature: from the FPGA (over UART)
r         0x8bce3d8d…4a5ac30f
s         0x67d73d9f…527ab1f9
y_parity  1   (ecrecover → 0xeb46…4d9929 ✓)
broadcast tx 0xc7d826d8…802c5edf
receipt status 0x1
recipient 10001.0000 → 10002.0000 ETH  (+1.0)
```

`ecrecover` returning the baked key's address is the whole point: the
signature that moved on-chain funds was produced by the physical chip,
from a key that never left it. To run the pipeline **without a board**,
swap `--port …` for `--ref` — it signs with the same RFC-6979 in pure
Python, byte-for-byte identical to the chip (verified against the chip's
signature for `z = 123456789`).

## 11.9 Field notes: bringing the 20K up on real silicon

Simulation never shows these; each cost real time on the bench.

- **Generate the core clock with the rPLL** (§11.3). A fabric-÷2 → BUFG
  clock is dead on the GW2A-18; crystal-direct won't route.
- **Talk to the right node, and pulse DTR/RTS.** The Sipeed BL616 exposes
  interface 0 = JTAG and interface 1 = the FPGA UART (`ttyUSB0`/`ttyUSB1`
  on the 20K). Use the UART node only. The bridge forwards **host→FPGA**
  only after DTR/RTS are *pulsed* through a few transitions — a static
  level doesn't enable it.
- **You can't read while a write is in flight.** The FTDI channel
  withholds read bytes until the write drains — write the request on one
  fd, **close it**, then read on a fresh fd.
- **Flash to SPI, expect to re-plug.** SRAM config is volatile and every
  `openFPGALoader` run churns USB; use `-f` (SPI) so the design survives,
  and after heavy JTAG use a physical re-plug is the only reliable
  recovery. (`host/sign_z/sign_z.py` bakes the DTR/RTS pulse, the
  two-fd write/read, and retries in — full-entropy `z` may need a couple
  of tries.)

## 11.10 Where to go next

- [`docs/ip-catalog/EcdsaSignDemo.md`](../../ip-catalog/EcdsaSignDemo.md)
  — the on-chip-key signer's protocol and the RFC-6979 / signer internals.
- [`docs/ip-catalog/PolicySignDemo.md`](../../ip-catalog/PolicySignDemo.md)
  — the **policy-enforcing** sibling: an on-chip allowlist + cap sliced
  from the very bytes it hashes, so a compromised host can't make the chip
  sign an attacker-chosen transfer ("clear signing"). Runs on the larger
  Tang Nano 50K (GW5A-60), which closes timing straight off the crystal.
- [`docs/ip-catalog/Fido2Demo.md`](../../ip-catalog/Fido2Demo.md) — the
  same device-top pattern applied to a **FIDO2 security key** (P-256,
  CTAPHID) for Google / GitHub login.
- Chapter 6/7 — prove properties of the field arithmetic the signer
  computes over (`IP/Crypto/Proof/P256FieldTheorems.lean`).

```lean
end Notebooks.Ch11
```
