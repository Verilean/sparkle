# SystemVerilog interoperability examples

Sparkle next to designs and verification flows that are written in
SystemVerilog — in both directions:

| direction | example | where |
|---|---|---|
| an existing SV design, tested from Lean with transactions | AXI4-Lite register block (`rtl/axil_regs.sv`) | `Tests/SvInteropTest.lean` §1 |
| | verilog-axi `axil_ram`, verilog-axis `axis_adapter` | §4, §5 |
| | PicoRV32 (`picorv32_axi`, an AXI4-Lite master) running a program out of a Lean-side RAM | §6 |
| a Sparkle design, used from SV | the DSL stage `axisScale` under AXI4-Stream port names (`SvWrapper`) | §3 |
| | … instantiated from an SV top between two third-party adapters (`rtl/sparkle_in_sv_top.sv`) | §7 |
| the same tests as a UVM environment | generated agents, sequences and scoreboards for all of the above | `lake exe tlm-uvm-test` |

## Running

```bash
lake exe sv-interop-test                 # needs verilator; in-repo designs only
bash Examples/SvInterop/fetch.sh         # third-party designs, pinned commits
lake exe sv-interop-test                 # … now also verilog-axi/axis and PicoRV32

# the generated UVM testbenches (Verilator 5 + a UVM library source tree)
git clone https://github.com/accellera-official/uvm-core
SPARKLE_UVM_HOME=$PWD/uvm-core lake exe tlm-uvm-test
```

`fetch.sh` clones into `third_party/` (git-ignored). Nothing from those
repositories is committed here:

| repository | licence | used |
|---|---|---|
| alexforencich/verilog-axi | MIT | `rtl/axil_ram.v` |
| alexforencich/verilog-axis | MIT | `rtl/axis_adapter.v` |
| YosysHQ/picorv32 | ISC | `picorv32.v` |

## What "transaction" means here

The vocabulary is the one SystemVerilog verification engineers use, taken
from the documents they learn it from:

* **UVM User's Guide** (Accellera, 1.2), chapter 3 — a *data item*
  (transaction) is a record of the protocol's fields; a *driver* turns items
  into pin activity; a *monitor* turns pin activity back into items and
  publishes them on an *analysis port*; a *scoreboard* subscribes. Chapter 2
  — blocking put/get, analysis ports, and the TLM-2 generic payload (command,
  address, data, byte enables, response).
* **cocotbext-axi** — the same idea driven from a host language, which is
  Lean's position here. The API follows it.
* **AMBA AXI / AXI4-Stream specifications** — the handshake rules the
  monitors check.

| UVM | cocotbext-axi | here (`Sparkle.Verification.Tlm`) |
|---|---|---|
| sequence item | `AxiStreamFrame`, read/write result | `AxiStreamFrame`, `AxiLiteTxn` |
| virtual interface | `AxiLiteBus.from_prefix(dut, "s_axil")` | `AxiLiteBus.fromPrefix dut.pins "s_axil"` |
| driver + sequencer | `AxiLiteMaster`, `AxiStreamSource` | `AxiLiteMaster`, `AxiStreamSource` |
| sequence | `await master.write(addr, data)` | `m.write addr bytes`, `m.run [txns]` |
| monitor + analysis port | `AxiStreamMonitor` | `AxiLiteMonitor`, `AxiStreamMonitor` → `AnalysisPort` |
| responder / slave | `AxiStreamSink`, `AxiLiteRam` | `AxiStreamSink`, `AxiLiteRam` |
| scoreboard | (user code) | `AxiLiteMonitor.memoryScoreboard`, list comparison |
| pause / back-pressure | `set_pause_generator` | `Pace` |

## Files

* `rtl/axil_regs.sv` — AXI4-Lite register block in ordinary SystemVerilog
  (`aclk`, active-low `aresetn`, SLVERR on bad addresses). `HONOR_WSTRB=0`
  builds a deliberately wrong one for the scoreboard to catch.
* `rtl/sparkle_in_sv_top.sv` — SV top instantiating two verilog-axis
  adapters around the Sparkle stage.
* `fetch.sh` — third-party sources at pinned commits.

## Limits

One clock per design. Ports of an SV `interface` type are not supported
(the design needs flat ports). AXI4-Lite and AXI4-Stream only — no AXI4
bursts or IDs, no APB. The generated UVM is directed (no constrained-random
stimulus, no coverage) and was run with Verilator 5 and Accellera's uvm-core
only.
