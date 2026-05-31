
# Chapter 9 — FPGA Bring-Up

An FPGA bitstream is what gets uploaded to a physical board.
This chapter takes you from Sparkle Lean source to a blinking
LED on real silicon, using **only open-source tools** —
`yosys` for synthesis, `nextpnr` for place-and-route, and
vendor-specific `*pack` / `*prog` for bitstream packing and
upload.

## Targets covered

| Target            | Synth          | P&R              | Pack    | Upload   |
|-------------------|----------------|------------------|---------|----------|
| Lattice iCE40     | `synth_ice40`  | `nextpnr-ice40`  | `icepack`| `iceprog`|
| Lattice ECP5      | `synth_ecp5`   | `nextpnr-ecp5`   | `ecppack`| `ecpprog`|

Recommended boards:

- **iCEstick** (iCE40-HX1K, Lattice's USB stick — ~$30,
  widely available)
- **TinyFPGA-BX** (iCE40-LP8K)
- **ULX3S** (ECP5-LFE5U-85F, ~$85, has HDMI / SDRAM / PMOD)

The Sparkle Docker image (Ch 0) ships all toolchains
pre-installed.  No host-side dependency juggling.

```lean
import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch09

```
## 9.1 The blinky design

A 24-bit counter divides a 12 MHz iCEstick clock down to a
comfortable ~0.7 Hz LED blink (toggle when bit 23 changes,
so half a period ≈ 2²³ / 12 MHz ≈ 0.7 s).

```lean
def blinky {dom : DomainConfig} : Signal dom Bool :=
  circuit do
    let count ← Signal.reg 0#24
    count <~ count + 1#24
    -- LED follows the top bit of the counter.  Mask off the top
    -- bit and compare against 0 to get a Bool signal.
    let topBit := (count &&& 0x800000#24) === 0x800000#24;
    return topBit

#synthesizeVerilog blinky

```
## 9.2 iCE40 toolchain — full pipeline

Save the SystemVerilog from §9.1 to `/tmp/blinky.sv` (see Ch 8
§8.2 for how).  Then:

```bash
# 1. Synthesise to iCE40 primitives.
yosys -p "read_verilog -sv /tmp/blinky.sv; \
          synth_ice40 -top blinky -json /tmp/blinky.json"

# 2. Place-and-route on iCE40-HX1K (iCEstick).
#    Pin constraints come from a .pcf file (next section).
nextpnr-ice40 --hx1k --package tq144 \
              --json /tmp/blinky.json \
              --pcf /tmp/icestick.pcf \
              --asc /tmp/blinky.asc

# 3. Pack the .asc into a .bin bitstream.
icepack /tmp/blinky.asc /tmp/blinky.bin

# 4. Upload via USB (board must be connected).
iceprog /tmp/blinky.bin
```

The first three steps work entirely offline; only `iceprog`
needs the board plugged in.

## 9.3 The constraint file (`icestick.pcf`)

iCE40 uses a `.pcf` (Physical Constraints File) to bind
top-level Verilog ports to physical pins.  For the iCEstick:

```
# /tmp/icestick.pcf
# Clock — onboard 12 MHz oscillator on pin 21.
set_io clk 21

# On-board LEDs.  We light up D1 (red).
set_io led 99
```

The pin numbers are board-specific — see the iCEstick user
guide (Lattice TN1248).  Sparkle's generated module
(`module blinky (input clk, input rst, output out);`)
exposes `clk` and `out`; if your `.pcf` names the LED `led`,
adjust the module's port name (or wrap in a small Verilog
shim that maps `out` → `led`).

## 9.4 ECP5 toolchain

The ECP5 flow is structurally identical, just different
tool names:

```bash
yosys -p "read_verilog -sv /tmp/blinky.sv; \
          synth_ecp5 -top blinky -json /tmp/blinky.json"

nextpnr-ecp5 --85k --package CABGA381 \
             --json /tmp/blinky.json \
             --lpf /tmp/ulx3s.lpf \
             --textcfg /tmp/blinky.config

ecppack /tmp/blinky.config /tmp/blinky.bit

ecpprog /tmp/blinky.bit
```

The constraint format is `.lpf` (Lattice Preference File),
not `.pcf`:

```
# /tmp/ulx3s.lpf — for the ULX3S board (revision 3.0+).
LOCATE COMP "clk" SITE "G2";
IOBUF  PORT "clk" IO_TYPE=LVCMOS33;

LOCATE COMP "led" SITE "B2";
IOBUF  PORT "led" IO_TYPE=LVCMOS33;
```

## 9.5 Top-level wrapper for FPGA boards

The Sparkle-generated module has `clk`, `rst`, and the
design's own outputs.  Real boards usually need a small
top-level Verilog wrapper that:

1. Maps board-specific pin names (`led_0`, `clk_25mhz`) to
   Sparkle's port names (`out`, `clk`).
2. Ties `rst` to a button (or to a always-asserted constant
   if there's no reset button).
3. Optionally adds a PLL to derive a different clock from
   the board oscillator.

A minimal iCEstick wrapper:

```verilog
// /tmp/iceblinky_top.sv
module iceblinky_top(input clk, output led);
  blinky inst(.clk(clk), .rst(1'b0), .out(led));
endmodule
```

Pass *both* `.sv` files to Yosys:

```bash
yosys -p "read_verilog -sv /tmp/blinky.sv; \
          read_verilog -sv /tmp/iceblinky_top.sv; \
          synth_ice40 -top iceblinky_top -json /tmp/blinky.json"
```

## 9.6 Optional exercise — port to ULX3S

1. Take the blinky from §9.1.
2. Write an ECP5 top-level wrapper analogous to §9.5.
3. Use the `ulx3s.lpf` from the ULX3S
   [pinout repo](https://github.com/emard/ulx3s).
4. Run the §9.4 pipeline.  Verify on hardware that the LED
   blinks at the expected rate (clock is 25 MHz on ULX3S, so
   bit 24 toggles at ~0.75 Hz).

## 9.7 Where to go next

- **Ch 10 — Architecture**: how the Sparkle compiler
  produces the SystemVerilog you've been feeding to Yosys.
- `docs/ip-catalog/RV32.md` — a full RISC-V SoC built in
  Sparkle, synthesised through the same flow on a real
  FPGA.
- `fpga/U280/` — Xilinx UltraScale+ scaffolding (Vivado-only,
  out of scope for the open-source flow in this chapter).

end Notebooks.Ch09
