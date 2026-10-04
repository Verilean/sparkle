
# Chapter 8c — From Signal to Silicon

The `Signal` and `Signal.reg` you have been writing are not just Lean
values — each one corresponds to a real piece of hardware. This chapter
connects the abstraction to the physical element level: what a register,
a clock, and a gate actually *are*, how a design's speed (static timing
analysis) and size (gate count) are measured, and how the same design
maps onto **ASIC standard cells** versus **FPGA** primitives (LUT4, DFF,
BSRAM, DSP). It is the conceptual bridge between Ch 8 (Yosys netlists),
Ch 8b (simulation), and Ch 9 (`#verify_fpga` + FPGA bring-up).

```lean
import Sparkle

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Notebooks.Ch08c

```
## 8c.1 The register is a D flip-flop

Every `Signal.reg` (and the lower-level `Signal.register init d`) becomes
one **D flip-flop** (DFF) per stored bit. A DFF samples its `D` input on
the rising clock edge and holds it on `Q` until the next edge:

<svg viewBox="0 0 340 160" width="340" xmlns="http://www.w3.org/2000/svg" font-family="system-ui,sans-serif" font-size="13">
  <rect x="110" y="30" width="120" height="90" fill="#f4f8ff" stroke="#333" stroke-width="1.5"/>
  <text x="170" y="22" text-anchor="middle" fill="#555">DFF</text>
  <line x1="60" y1="55" x2="110" y2="55" stroke="#333"/>
  <text x="55" y="59" text-anchor="end">D</text>
  <line x1="230" y1="55" x2="285" y2="55" stroke="#333"/>
  <text x="292" y="59">Q</text>
  <polyline points="110,95 125,105 110,115" fill="none" stroke="#333" stroke-width="1.5"/>
  <line x1="60" y1="105" x2="110" y2="105" stroke="#333"/>
  <text x="55" y="109" text-anchor="end">clk</text>
  <text x="170" y="72" text-anchor="middle" fill="#0366d6">Q(t+1)</text>
  <text x="170" y="90" text-anchor="middle" fill="#0366d6">= D(t)</text>
</svg>

That defining behaviour is *exactly* the `.val` semantics of the
register: the value at reset is `init`, and the value at cycle `t+1` is
the input sampled at cycle `t`. Both hold by `rfl` — the register
literally is a DFF.

```text
-- Q at reset is `init`.
example {dom : DomainConfig} (init : BitVec 8) (d : Signal dom (BitVec 8)) :
    (Signal.register init d).val 0 = init := rfl

-- Q at cycle t+1 is D sampled at cycle t.
example {dom : DomainConfig} (init : BitVec 8) (d : Signal dom (BitVec 8))
    (t : Nat) :
    (Signal.register init d).val (t + 1) = d.val t := rfl
```
The `init` is the DFF's **reset value**. On real hardware that reset is
either *synchronous* (applied on a clock edge) or *asynchronous*
(applied immediately) — a choice carried by the `DomainConfig`, not by
the register itself.

## 8c.2 The clock and clock domains

There is no explicit clock wire in a Sparkle expression, and that is
deliberate: the **cycle index `t` is the clock**. One rising edge
advances `t → t+1`; every register samples its input at that edge.

<svg viewBox="0 0 420 120" width="420" xmlns="http://www.w3.org/2000/svg" font-family="system-ui,sans-serif" font-size="12">
  <polyline points="20,80 60,80 60,40 100,40 100,80 140,80 140,40 180,40 180,80 220,80 220,40 260,40 260,80 300,80 300,40 340,40 340,80 380,80"
            fill="none" stroke="#333" stroke-width="1.5"/>
  <text x="10" y="62" text-anchor="end" fill="#555">clk</text>
  <g fill="#0366d6" text-anchor="middle">
    <line x1="60" y1="30" x2="60" y2="95" stroke="#cbd5e0"/><text x="60" y="112">t=0</text>
    <line x1="140" y1="30" x2="140" y2="95" stroke="#cbd5e0"/><text x="140" y="112">t=1</text>
    <line x1="220" y1="30" x2="220" y2="95" stroke="#cbd5e0"/><text x="220" y="112">t=2</text>
    <line x1="300" y1="30" x2="300" y2="95" stroke="#cbd5e0"/><text x="300" y="112">t=3</text>
  </g>
  <text x="200" y="18" text-anchor="middle" fill="#555">each ↑ edge: every register samples, t advances by one</text>
</svg>

A `DomainConfig` *is* a clock domain. A design with two domains has two
independent clocks, and any signal crossing between them is a
clock-domain crossing (CDC) that needs a synchroniser — the reason
domains are tracked in the type. On the FPGA the clock is not free-
running math: it comes from the board crystal, optionally through a PLL
(the Tang Nano 20K's 27 MHz crystal → `rPLL` → 13.5 MHz in Ch 9 §9.4).

## 8c.3 Combinational logic is gates

Between any two registers sits a **combinational cloud** — pure logic
with no state. Each Sparkle operator lowers to gates: `&&& ||| ^^^ ~~~`
to AND/OR/XOR/INV, `Signal.mux` to a 2:1 multiplexer, `+`/`-` to an
adder built from those. The cloud has no clock and no memory: its output
is a function of its inputs *right now*.

<svg viewBox="0 0 440 120" width="440" xmlns="http://www.w3.org/2000/svg" font-family="system-ui,sans-serif" font-size="12">
  <rect x="20" y="45" width="60" height="40" fill="#f4f8ff" stroke="#333"/><text x="50" y="69" text-anchor="middle">reg</text>
  <rect x="160" y="30" width="120" height="70" rx="35" fill="#fff8f0" stroke="#333" stroke-dasharray="4 3"/>
  <text x="220" y="60" text-anchor="middle" fill="#555">combinational</text>
  <text x="220" y="76" text-anchor="middle" fill="#555">cloud (gates)</text>
  <rect x="360" y="45" width="60" height="40" fill="#f4f8ff" stroke="#333"/><text x="390" y="69" text-anchor="middle">reg</text>
  <line x1="80" y1="65" x2="160" y2="65" stroke="#333"/>
  <line x1="280" y1="65" x2="360" y2="65" stroke="#333"/>
</svg>

## 8c.4 Static timing analysis (STA)

How fast can you clock the design? The **critical path** is the longest
combinational path between two registers. The clock period must be
longer than everything that path costs:

<div style="overflow-x:auto">
<svg viewBox="0 0 560 130" width="560" xmlns="http://www.w3.org/2000/svg" font-family="system-ui,sans-serif" font-size="12">
  <rect x="20" y="45" width="55" height="40" fill="#f4f8ff" stroke="#333"/><text x="47" y="69" text-anchor="middle">reg A</text>
  <rect x="230" y="30" width="120" height="70" rx="35" fill="#fff8f0" stroke="#333" stroke-dasharray="4 3"/>
  <text x="290" y="69" text-anchor="middle" fill="#555">logic depth</text>
  <rect x="500" y="45" width="55" height="40" fill="#f4f8ff" stroke="#333"/><text x="527" y="69" text-anchor="middle">reg B</text>
  <line x1="75" y1="65" x2="230" y2="65" stroke="#c00" stroke-width="2"/>
  <line x1="350" y1="65" x2="500" y2="65" stroke="#c00" stroke-width="2"/>
  <text x="150" y="55" text-anchor="middle" fill="#c00">t_clk→q</text>
  <text x="290" y="118" text-anchor="middle" fill="#c00">t_comb</text>
  <text x="425" y="55" text-anchor="middle" fill="#c00">t_setup</text>
  <text x="290" y="18" text-anchor="middle" fill="#555">clock period ≥ t_clk→q + t_comb + t_setup ⇒ Fmax = 1 / period</text>
</svg>
</div>

Deeper logic between registers → longer `t_comb` → lower `Fmax`. The fix
is **pipelining**: insert a register partway through the cloud, halving
the depth (at the cost of one cycle of latency). Sparkle's cost model
approximates the critical path with a `depth` metric, and
`#verify_fpga` (Ch 9 §9.7) turns it into an `Fmax_est ≈ 1 / (depth ×
picoSecPerUnit)` — a "right order of magnitude" number, not a substitute
for the vendor timing report, but enough to catch a design that clearly
won't close timing before you run place-and-route.

## 8c.5 Gate count and area

Area is counted in *cells*. `yosys stat` (Ch 8) prints them after
synthesis; for the Tang Nano 20K flow it reports `LUT1..4`, `MUX2_LUT*`,
`ALU`, and `DFF*` counts. `#verify_fpga` estimates the same four pools
(LUT4 / FF / BSRAM / DSP) straight off the IR, before synthesis — that
is what its calibration against real Yosys numbers (Ch 9 §9.7) is for.
FF count is exact (one flip-flop per register bit); LUT count is the
estimate the optimiser-aware cost model produces.

## 8c.6 Mapping: ASIC vs FPGA

The same `Signal` netlist targets two very different fabrics. On an
**ASIC** it is mapped to a standard-cell library; on an **FPGA** to a
fixed set of configurable primitives. On the FPGA the basic logic
element is a **LUT4 feeding a DFF** — a 4-input lookup table (which can
implement *any* Boolean function of 4 inputs) with a flip-flop on its
output:

<svg viewBox="0 0 360 130" width="360" xmlns="http://www.w3.org/2000/svg" font-family="system-ui,sans-serif" font-size="12">
  <rect x="90" y="30" width="90" height="70" fill="#f4f8ff" stroke="#333"/>
  <text x="135" y="60" text-anchor="middle">LUT4</text>
  <text x="135" y="78" text-anchor="middle" fill="#555" font-size="10">any 4-in fn</text>
  <g stroke="#333"><line x1="40" y1="42" x2="90" y2="42"/><line x1="40" y1="56" x2="90" y2="56"/><line x1="40" y1="70" x2="90" y2="70"/><line x1="40" y1="84" x2="90" y2="84"/></g>
  <text x="34" y="67" text-anchor="end" fill="#555">4 inputs</text>
  <rect x="230" y="45" width="70" height="40" fill="#f4f8ff" stroke="#333"/>
  <text x="265" y="69" text-anchor="middle">DFF</text>
  <line x1="180" y1="65" x2="230" y2="65" stroke="#333"/>
  <line x1="300" y1="65" x2="345" y2="65" stroke="#333"/>
  <text x="352" y="69">Q</text>
  <polyline points="230,78 240,85 230,92" fill="none" stroke="#333"/>
</svg>

| Sparkle construct | ASIC (standard cells) | FPGA (Gowin GW2A-18) |
|---|---|---|
| `&&& \|\|\| ^^^ ~~~`, `Signal.mux` | NAND / NOR / INV / AOI cells | **LUT4** — any ≤4-input function is one LUT4 |
| `+`, `-` (arithmetic) | adder cells + carry chain | dedicated **carry chain** (`ALU` cells) + LUT4 |
| `*` (multiply) | synthesised Booth/Wallace tree, or a hard macro | **DSP** block (18×18 multiplier) |
| `Signal.reg` (a register bit) | **DFF** standard cell | dedicated **DFF** (one per LUT slice) |
| an array / memory | **SRAM** compiler macro | **BSRAM** (18 Kb block); tiny ones as LUT-RAM |
| the clock | clock tree + PLL | global clock net + PLL / **rPLL** |
| *area unit* | gate-equivalents (NAND2) / µm² | LUT4 + FF + BSRAM + DSP counts |

So when `#verify_fpga` reports `LUT 5966, FF 1032, BSRAM 0, DSP 0`, it is
literally counting how many of each of these fabric primitives your
`Signal` design will occupy — the FPGA-side of this table, tallied
without running the toolchain.

end Notebooks.Ch08c
