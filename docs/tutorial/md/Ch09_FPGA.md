
# Chapter 9 — FPGA Bring-Up

An FPGA bitstream is what gets uploaded to a physical board.
This chapter takes you from Sparkle Lean source to a blinking
LED on real silicon, using **only open-source tools** —
`yosys` for synthesis, `nextpnr` for place-and-route, and
vendor-specific `*pack` / `*prog` for bitstream packing and
upload.

## The board — Tang Nano 20K

This chapter targets the **Sipeed Tang Nano 20K** (Gowin
GW2AR-18, ~$30) — the board the Sparkle crypto IP was actually
brought up on (a live on-chip secp256k1 signer; see Ch 11). The
whole flow is open-source:

| Step  | Tool                 | Key argument                         |
|-------|----------------------|--------------------------------------|
| Synth | `yosys synth_gowin`  | flat ABC9 LUT packing                |
| P&R   | `nextpnr-himbaechel` | `--device GW2AR-LV18QN88C8/I7`       |
| Pack  | `gowin_pack`         | `-d GW2A-18C` → `.fs` bitstream      |
| Load  | `openFPGALoader`     | `-b tangnano20k` (SRAM, or `-f` for SPI flash) |

Part budget (what `#verify_fpga tangNano20K` checks against, §9.7):
**20 736 LUT4, 15 552 FF, 46 × 18 Kb BSRAM, 48 DSP**, driven by an
on-board **27 MHz** crystal. The Sparkle Docker image (Ch 0) ships the
whole toolchain pre-installed — no host-side dependency juggling.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Verification.CostCmd

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Verification.Cost.Targets

namespace Notebooks.Ch09

```
## 9.1 The blinky design

A 24-bit counter divides the Tang Nano 20K's 27 MHz crystal down
to a visible LED blink: bit 23 flips every 2²³ / 27 MHz ≈ 0.31 s,
so the LED blinks at ~1.6 Hz.

```lean
def blinky {dom : DomainConfig} : Signal dom Bool :=
  circuit do
    let count ← Signal.reg 0#24
    count <~ count + 1#24
    -- LED follows the top bit of the counter.  Project the
    -- register handle to its underlying `Signal` so the
    -- `&&&` / `===` chain stays in `Signal` land.
    let countSig := count.1
    let topBit := (countSig &&& 0x800000#24) === 0x800000#24;
    return topBit

#synthesizeVerilog blinky

```
## 9.2 Gowin toolchain — full pipeline

Save the SystemVerilog from §9.1 to `/tmp/blinky.v` (see Ch 8
§8.2 for how). Then:

```bash
# 1. Synthesise to Gowin primitives.  synth_gowin is split around
#    an explicit ABC9 pass for flat LUT4 packing (the same recipe
#    the crypto IP uses to hit ~50% LUT4 instead of ~70%).
yosys -p "read_verilog -sv /tmp/blinky.v; \
          synth_gowin -top blinky -run :map_luts; \
          read_verilog -icells -lib -specify +/abc9_model.v; \
          abc9 -maxlut 8; \
          synth_gowin -top blinky -run map_cells:; \
          write_json /tmp/blinky.json"

# 2. Place-and-route on the GW2AR-18.  Pin constraints come from
#    a .cst file (next section).
nextpnr-himbaechel --device GW2AR-LV18QN88C8/I7 \
                   --vopt family=GW2A-18C --vopt cst=/tmp/blinky.cst \
                   --json /tmp/blinky.json \
                   --write /tmp/blinky_pnr.json

# 3. Pack the routed netlist into a .fs bitstream.
gowin_pack -d GW2A-18C -o /tmp/blinky.fs /tmp/blinky_pnr.json

# 4a. Load to SRAM — fast, but volatile (lost on power-cycle).
openFPGALoader -b tangnano20k /tmp/blinky.fs
# 4b. …or persist to the on-board SPI flash (survives replug).
openFPGALoader -b tangnano20k -f /tmp/blinky.fs
```

The first three steps run entirely offline; only `openFPGALoader`
needs the board plugged in. SRAM load is instant for the
edit-flash-look loop; flash (`-f`) is for a design you want to
keep across power cycles.

## 9.3 The constraint file (`blinky.cst`)

Gowin uses a `.cst` (Constraints file) to bind top-level Verilog
ports to physical pins and set their I/O standard. For the Tang
Nano 20K:

```
// /tmp/blinky.cst
// 27 MHz crystal on pin 4.
IO_LOC  "clk" 4;
IO_PORT "clk" IO_TYPE=LVCMOS33 PULL_MODE=UP BANK_VCCIO=3.3;

// Reset button on pin 88.
IO_LOC  "rst" 88;
IO_PORT "rst" IO_TYPE=LVCMOS33 PULL_MODE=UP;

// On-board LED (leftmost of the six) on pin 15.
IO_LOC  "out" 15;
IO_PORT "out" IO_TYPE=LVCMOS33 PULL_MODE=UP DRIVE=8;
```

Sparkle's generated module is `module blinky (input clk, input
rst, output out);`, so the `.cst` names must match those ports
(`clk`, `rst`, `out`). The pin numbers are board-specific — see
the Sipeed Tang Nano 20K schematic. Real `.cst` files for the
crypto IP live under `fpga/tangNano20k/*.cst`.

## 9.4 Field notes from real bring-up

Two gotchas cost real hours on the GW2A-18 during the crypto-IP
bring-up — worth knowing before you debug a dead board:

- **Divided clocks: use an `rPLL`, not a fabric-flop `BUFG`.**
  Driving a global-clock buffer (`BUFG`) from a fabric
  flip-flop (`reg clk_div; always @(posedge clk) clk_div <= ~clk_div;`)
  produces a clock that **never toggles** on this part — the
  divided-clock domain is silently dead. Instantiate a Gowin
  `rPLL` primitive instead (e.g. 27 MHz → 13.5 MHz with
  `IDIV_SEL=1, FBDIV_SEL=0, ODIV_SEL=64, CLKFB_SEL="internal"`).
  The rPLL output routes on the global spine and actually clocks.

- **SRAM load is volatile and churns USB; flash to persist.**
  Every `openFPGALoader` SRAM run re-enumerates the USB bridge.
  For a design you want to keep — or when the read-back path gets
  wedged — flash to SPI (`-f`) and **physically replug** the
  board; that is the only reliable way to recover a stuck USB
  bridge (a `USBDEVFS_RESET` ioctl only half-works).

If your design talks UART over the on-board debugger, note the
two `ttyUSB` devices are **interface 01 = UART, interface 00 =
JTAG** (opening the JTAG one as a serial port wedges JTAG). See
Ch 11 §11.9 for the full host-side UART recipe.

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

A minimal Tang Nano 20K wrapper (`out` here already matches the
`.cst`, so the wrapper is only needed when you want to rename
ports or drive several LEDs):

```verilog
// /tmp/tnblinky_top.v
module tnblinky_top(input clk, output led);
  blinky inst(.clk(clk), .rst(1'b0), .out(led));
endmodule
```

Pass *both* `.v` files to Yosys (top = the wrapper):

```bash
yosys -p "read_verilog -sv /tmp/blinky.v; \
          read_verilog -sv /tmp/tnblinky_top.v; \
          synth_gowin -top tnblinky_top -run :map_luts; \
          read_verilog -icells -lib -specify +/abc9_model.v; \
          abc9 -maxlut 8; \
          synth_gowin -top tnblinky_top -run map_cells:; \
          write_json /tmp/blinky.json"
```

## 9.6 Optional exercise — light all six LEDs

1. Take the blinky from §9.1 and widen it: instead of one LED,
   drive the six on-board LEDs (pins 15–20) from six different
   counter bits so they blink at different rates.
2. Add the corresponding `IO_LOC`/`IO_PORT` lines to the `.cst`.
3. Bonus: clock the counter from a 13.5 MHz `rPLL` (§9.4) instead
   of the raw 27 MHz crystal, and confirm the blink rate halves.

## 9.7 Will it fit? — sizing before you synthesise

The pipelines above take **minutes** (`yosys` + `nextpnr`). Before
committing to one, you can size a design against a specific part in
**seconds**, without running any of them — the compiler already knows
every register width and every operator, so it counts LUT / FF / BSRAM
/ DSP straight off the IR.

`#verify_fpga <design> <target>` estimates the four resource pools and
checks them against a part's published ceilings:

```lean
#verify_fpga blinky tangNano20K
```

⇒ `✅ fits Tang Nano 20K (GW2AR-18): blinky — LUT …, FF 24/15552, …` (a
24-bit counter, so 24 FFs). Overflow logs `❌` with the offending pool.
The part table lives in `CostTargets` (`tangNano9K`, `tangNano20K`,
`tangNano50K`); `tangNano20K.withMargin 80` budgets only 80 % of each
resource to leave routing headroom. For a raw area/depth budget instead
of a named part, use `#verify_cost <design> { area := …, depth := … }`.

**Why the estimate is trustworthy.** It runs the *same optimiser passes
synthesis does* before counting: constant-folding makes constant
shifts/rotations free (they are pure rewiring — an on-chip SHA-256
estimates 5 966 LUT4 vs. ~6 000 from `yosys`, within ~1 %), and CSE +
dead-code elimination collapse the shared and dead logic a raw node
count would double-count. FF counts are exact (Σ register widths).

**The payoff — turnaround.** Iterate against the instant estimate —
shrink the design until it fits with margin — then run the minutes-long
toolchain **once**. A design that obviously overflows (more registers
than the part physically has) is rejected before `yosys` ever starts.
This is a check the RTL-then-synthesise loop can't give you cheaply: the
typed IR is countable without lowering to a netlist.

> Caveat: this is an *upper-bound fit check*, not a substitute for
> place-and-route. Timing closure, routing congestion, and clock-domain
> crossings are not modelled — a green `#verify_fpga` means "the logic
> fits", not "it closes timing".

## 9.8 Where to go next

- **Ch 10 — Architecture**: how the Sparkle compiler
  produces the SystemVerilog you've been feeding to Yosys.
- `docs/ip-catalog/RV32.md` — a full RISC-V SoC built in
  Sparkle, synthesised through the same flow on a real
  FPGA.
- `fpga/U280/` — Xilinx UltraScale+ scaffolding (Vivado-only,
  out of scope for the open-source flow in this chapter).

end Notebooks.Ch09
