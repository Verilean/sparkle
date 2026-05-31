
# Chapter 8 — Netlist Generation with Yosys

`#synthesizeVerilog` (Ch 5) hands you SystemVerilog.  The
next step is feeding that to **Yosys** — an open-source
synthesis tool that produces a *netlist* (a graph of
gates / LUTs / flip-flops) you can analyse, optimise, and
ultimately turn into a bitstream for an FPGA (Ch 9) or a
mask layout for an ASIC.

This chapter is **driving Yosys from the outside**.  The
Sparkle Lean code only writes `.v` files; the actual `yosys`
invocation runs in your shell (or in the bundled Docker
image).

## What you need

- Yosys ≥ 0.39 — `apt install yosys`, `brew install yosys`,
  or `nix-shell -p yosys`.
- GTKWave (optional, for waveform inspection) — `apt install
  gtkwave`.

The Sparkle Docker image (Ch 0) has both pre-installed.

```lean
import Sparkle
import Sparkle.Compiler.Elab
import Display

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch08

```
## 8.1 The design we'll synthesise

Reuse the 8-bit counter from Ch 3.  Concrete enough to count
gates against, small enough to read the netlist by eye.

```lean
def counter8 {dom : DomainConfig} : Signal dom (BitVec 8) :=
  circuit do
    let count ← Signal.reg 0#8
    count <~ count + 1#8
    return count

#synthesizeVerilog counter8

```
## 8.2 Writing the Verilog to a file

The `#synthesizeVerilog` macro prints the SystemVerilog to
stdout as part of its info diagnostic.  For a real Yosys
workflow you want it on disk.  Use `Sparkle.Backend.Verilog.synthesizeToString`
(the same path the macro uses) and write it out:

```text
#eval do
  let sv := Sparkle.Backend.Verilog.synthesizeToString
              (counter8 (dom := defaultDomain))
  IO.FS.writeFile "/tmp/counter8.sv" sv
```

Or simply redirect from your shell — `lake exe sparkle-emit
counter8 > /tmp/counter8.sv`.  We omit the `#eval` here so
the chapter builds without write-access to /tmp under CI.

## 8.3 Yosys script — generic synthesis

Once `counter8.sv` is on disk, run Yosys with a 4-step
script: read, synth, optimise, write.

```bash
yosys -p "
  read_verilog -sv /tmp/counter8.sv
  hierarchy -top counter8
  synth_generic -top counter8
  write_json /tmp/counter8.json
  stat
"
```

Each step:

- **`read_verilog -sv`** — parse the SystemVerilog into
  Yosys's internal RTLIL representation.  The `-sv` flag
  enables SystemVerilog features (`logic`, `always_ff`).
- **`hierarchy -top`** — find the top module and prune
  anything not reachable from it.
- **`synth_generic`** — run the generic synthesis pass:
  technology-independent gate-level netlist (AND/OR/NOT/MUX/
  DFF), no specific FPGA primitives yet.
- **`write_json`** — emit the netlist as JSON, easy to feed
  into nextpnr (Ch 9) or other tools.
- **`stat`** — print the gate count.  For our counter you'll
  see something like:

  ```
  Number of cells: 24
    $_DFF_P_   8     <- 8 flip-flops
    $_AND_     5
    $_OR_      6
    $_XOR_     5
  ```

## 8.4 Targeting an FPGA family

`synth_generic` gives you abstract gates.  To target a
specific FPGA, swap in the right `synth_*` pass:

| Target              | Yosys pass            |
|---------------------|----------------------|
| iCE40 (Lattice)     | `synth_ice40`        |
| ECP5 (Lattice)      | `synth_ecp5`         |
| Xilinx 7-series     | `synth_xilinx`       |
| NX (Nexus / Crosslink) | `synth_nexus`     |
| Generic CMOS ASIC   | `synth -lib LIB.lib` |

The Sparkle FPGA chapter (Ch 9) walks through `synth_ice40`
and `synth_ecp5` end-to-end, including pin assignment and
bitstream generation.

## 8.5 GTKWave — inspecting a VCD trace

Sparkle can also dump VCD waveform files via
`Sparkle.Backend.VCD`.  Together with Yosys, the loop is:

1. Sparkle → Verilog (`counter8.sv`)
2. Verilator (or iverilog) compiles `counter8.sv` and a
   test-bench, runs the simulation, and dumps `counter8.vcd`.
3. `gtkwave counter8.vcd` opens the trace.

The `verilator/Makefile` in the Sparkle repo wires this up
for the SoC; the same recipe scales down to a single counter.

## 8.5b Multi-million-tick traces — VGA hsync/vsync in a `.wdb`

A 25 MHz VGA frame is roughly 420 000 cycles long; a few frames
cross the million-tick mark.  Plain `Display.waveform` would
choke (we'd be embedding a megabyte of SVG into a notebook
cell), so xeus-lean ships a *streaming* viewer backed by a
binary `.wdb` (Waveform DataBase) file:

1. **`Display.writeWdb`** dumps each lane as a `Nat → Bool`
   sampler plus a tick budget into a compressed file.
2. **`Display.waveformFromWdb`** opens the file and renders only
   the visible window — pan / zoom is a re-read, not a re-emit.

In the kernel you get an interactive viewer; in `lake build`
the shim writes a tiny JSON placeholder so the API call
typechecks and the rest of the chapter still builds.

```lean
-- VGA 640×480 @ 60 Hz, 25 MHz pixel clock, standard timings:
--   horizontal: 640 visible + 16 front + 96 sync + 48 back = 800 px
--   vertical:   480 visible + 10 front +  2 sync + 33 back = 525 lines
def H_VIS  : Nat := 640
def H_FP   : Nat := 16
def H_SYNC : Nat := 96
def H_TOTAL : Nat := 800
def V_TOTAL : Nat := 525
def FRAME : Nat := H_TOTAL * V_TOTAL          -- = 420_000

def hsyncSample (t : Nat) : Bool :=
  let x := t % H_TOTAL
  ¬ (x ≥ H_VIS + H_FP ∧ x < H_VIS + H_FP + H_SYNC)
def vsyncSample (t : Nat) : Bool :=
  let y := (t / H_TOTAL) % V_TOTAL
  ¬ (y ≥ 480 + 10 ∧ y < 480 + 10 + 2)

def vgaLanes : List Display.WaveformSession.Lane :=
  [ { name := "hsync", sample := hsyncSample },
    { name := "vsync", sample := vsyncSample } ]

#eval Display.writeWdb "/tmp/vga.wdb" vgaLanes (3 * FRAME)
#eval Display.waveformFromWdb "VGA 3 frames" "/tmp/vga.wdb"
```

The two `#eval`s are cheap under the shim (one tiny JSON
write, one HTML preview); under xeus-lean they exercise the
full streaming path.

## 8.6 Exercise — count the gates

1. Synthesise the 4-bit ALU from Ch 4 (`alu4`) into
   `/tmp/alu4.sv`.
2. Run `synth_generic` and read the `stat` output.
3. How many `$_DFF_P_` cells?  (Hint: it's 0 — the ALU is
   purely combinational.)
4. How many `$_MUX_` cells?  Compare against the source
   (the chained `Signal.mux`s in Ch 4 §4.5).

No reference solution for this one — it depends on your
Yosys version's exact pass output.  The point is to read
the stats and connect them back to the Lean source.

end Notebooks.Ch08
