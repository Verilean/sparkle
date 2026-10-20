# Files that depend on the text of the switched design commands

Round par/a-1, worker A. PREDICTIONS BY READING — nothing below was run.
The switched commands: `#synthesizeVerilogDesign`, `#writeVerilogDesign`,
`#writeDesign` (its `.sv` only; its C simulation and JIT wrapper are still
`toCDesign` / `toCJIT` of `optimizeDesign design`). `#sim` is not switched.

## What changes in the text, from the writer's definition

Old: every module `emitModule (optimizeModule m)`. New
(`Sparkle/Backend/VerilogDesign.lean`): the module named `design.topModule`
is `emitModule (checkedOptimize m)`, every other module `emitModule m`.

| | top module | other modules |
|---|---|---|
| module header, port list | same (`checkedOptimize_name`; ports kept in every branch) | same |
| instance statements `<mod> <inst> (…)` | same module and instance NAMES and the same instances, unless the unchecked optimizer merged duplicate instances (`cseAndMergeInstances`): then the new text keeps them all (the check `instsKept` both ways refuses a merge, fallback to the input). Connections of a kept candidate read the input's wire names again (`deinline`), preceded by `assign <wire> = …` | same statements as before optimization |
| internal wires and assignments | accepted candidate without instances (`optCheck` / `refineCheck`): IDENTICAL text to the old one. With instances: the optimizer's body plus the named connections. Fallback: the unoptimized module | unoptimized: every wire of the full entry's module is declared and assigned (the old text inlined single-use wires, dropped aliases and dead registers) |
| a module with a memory statement (not instance/assign/register only) | `optimizeModule m` unchecked: IDENTICAL to the old text | unoptimized |

Consequence used below: **every identifier of the old text occurs in the
new text** (the optimizer invents no name; a kept candidate's wire list is
`m.wires.filter (o.wires.contains · || named)`; the fallbacks and the
children are the unoptimized modules). Instance names are never renamed by
`optimizeModule`, `deinline` or the fallbacks. So a test that asks for the
PRESENCE of a module header, an instance name or a wire name keeps its
verdict or goes from fail to pass; a test that asks for ABSENCE of a name or
for an exact count of something the optimizer used to remove can change.

## Per file

### 1. `Tests/Tutorial/HierarchyTest.lean` 68–90 (`lake exe tutorial-hierarchy`)

Writes `/tmp/sparkle_hier_test_x2.sv` (`latch8x2`) and
`/tmp/sparkle_hier_test_x2_mod.sv` (`latch8modx2`) by `#writeVerilogDesign`;
`main` asks: no `module latch8 (` in the first; `module latch8mod (` in the
second; exactly 2 occurrences of `latch8mod _tmp_inst_latch8mod` in the
second.

Prediction: SAME verdict as before the switch.
* `module latch8 (` absent: `latch8` has no `@[hardware_module]`, the design
  has one module either way.
* `module latch8mod (`: the child's header; the child is printed unoptimized,
  its name unchanged.
* the count: the two instance statements are in the top `latch8modx2`. Old:
  `optimizeModule` keeps both (different input connections, no merge). New:
  the second instance reads the first one's output wire directly, so if
  `hierBinds` holds the guard G2 (`linkedWFX`, an over-approximation) refuses
  the candidate and the input module is printed; otherwise the input module
  is printed by the does-not-bind fallback. Either way both instance
  statements are printed under the names the entry gave them.
* NOT determined by reading: whether those names start with `_tmp_inst_`
  (the legacy translator's `freshName "inst_…"`, `Elab.lean` 6642–6658, 8502,
  8564) or are the machine routes' `inst{k}_<module>`
  (`Sparkle/IR/Machine.lean` 283, `MachineInstG.lean` 46) on this tree. That
  is the entry's choice, independent of the writer: if the count check fails
  it fails on the base as well.

Cheap (one Lean process, no exe link; runs `main` in the interpreter):

    scripts/shipping-coverage/cgrun.sh -n hiertest -m 3G -t 600 -- \
      lake env lean --run Tests/Tutorial/HierarchyTest.lean

Expected last line: `HierarchyTest: PASS`. If `--run` is refused, elaborate
the file (`lake env lean Tests/Tutorial/HierarchyTest.lean`) and check by
hand: `grep -c 'module latch8 (' /tmp/sparkle_hier_test_x2.sv` (0),
`grep -c 'module latch8mod (' /tmp/sparkle_hier_test_x2_mod.sv` (≥ 1),
`grep -o 'latch8mod _tmp_inst_latch8mod' /tmp/sparkle_hier_test_x2_mod.sv | wc -l` (2).

### 2. `Tests/run_tests.sh` 14, 72–75 through `Tests/VerifyVerilog.lean` 95

`#synthesizeVerilogDesign test_hierarchical_alu`; the script greps the
output for `module test_hierarchical_alu`, `test_add inst_test_add`,
`test_sub inst_test_sub`, `_gen_addResult_`. All its other checks are on
`#synthesizeVerilog` (single-module command, not switched).

Prediction: no check goes from pass to fail.
* `test_add` / `test_sub` carry no `@[hardware_module]`: the design is ONE
  module. Its text is the old text when `checkedOptimize` accepts the
  optimizer's candidate (`optCheck` / `refineCheck`), the unoptimized module
  otherwise.
* `module test_hierarchical_alu`: present either way.
* `test_add inst_test_add`, `test_sub inst_test_sub`: there is no instance in
  either text (the calls are inlined); these two checks do not depend on the
  writer.
* `_gen_addResult_`: present in the old text only if the optimizer kept the
  named wire; in the new text if the candidate is accepted and kept it, or
  on the fallback. It can go from absent to present, not the reverse.
* The script itself is not a reliable gate on this tree whatever the writer
  (`set -e` with `((PASSED++))` on a zero counter; `always @(posedge clk)`
  against the emitter's `always_ff`): compare the four greps, not its exit
  code.

Cheap:

    scripts/shipping-coverage/cgrun.sh -n verifyverilog -m 3G -t 600 -- \
      bash -c 'lake env lean Tests/VerifyVerilog.lean > /tmp/verilog_test_output.txt 2>&1; for p in "module test_hierarchical_alu" "test_add inst_test_add" "test_sub inst_test_sub" "_gen_addResult_"; do printf "%s: " "$p"; grep -c -- "$p" /tmp/verilog_test_output.txt; done'

(`Tests/SynthesisTests.lean` 68 has the same command; no script reads its
output.)

### 3. `fpga/tangNano20k/blinky/blinky.v` (TRACKED), from `fpga/tangNano20k/blinky/GenBlinky.lean` 12

`#writeVerilogDesign blinkyTop "fpga/tangNano20k/blinky/blinky.v"`.
`GenBlinky.lean` is not a `lakefile.lean` target: no build regenerates the
file. DO NOT elaborate `GenBlinky.lean` as it is — it overwrites a tracked
file that the FPGA flow uses.

Prediction: `blinkyTop` is one assign + register module (no instance). New
text = `emitModule (if refineCheck m o then o else m)`: the old text when
the check accepts, the unoptimized module otherwise. The tracked file is
already not what the base writer prints: it contains alias assignments
(`assign _tmp_a_1 = _tmp_a_6;`, `assign out = _gen_out;`) that
`optimizeModule` propagates away — it was generated by an earlier compiler.
So regenerating changes the tracked file with either writer; the switch
adds nothing to that.

Cheap, without touching the tracked file:

    scripts/shipping-coverage/cgrun.sh -n blinkyprobe -m 3G -t 600 -- \
      bash -c 'mkdir -p .lake/build/gen/writer-sim && sed "s#fpga/tangNano20k/blinky/blinky.v#.lake/build/gen/writer-sim/blinky_new.v#" fpga/tangNano20k/blinky/GenBlinky.lean > .lake/build/gen/writer-sim/GenBlinkyProbe.lean && lake env lean .lake/build/gen/writer-sim/GenBlinkyProbe.lean; diff fpga/tangNano20k/blinky/blinky.v .lake/build/gen/writer-sim/blinky_new.v | head -40; git status --short fpga/'

Expected: a non-empty diff (see above) and NO change under `fpga/`.

## NOT to run (too heavy), with the prediction

### 4. `Tests/RV32/TestFlow.lean` 39–56 and `Tests/Integration/BitNetSoCTest.lean` 66–80

Both read `verilator/generated_soc.sv`, written by
`#writeDesign rv32iSoCSynth … SoCOutput.wireNames`
(`IP/RV32/SoCVerilog.lean` 80): building it is the synthesis of the whole
RV32 SoC (minutes, and the largest memory user of the tree).

Their checks are all PRESENCE checks: the file exists and is not empty;
`module Sparkle_IP_RV32_SoCVerilog_rv32iSoCSynth`; `input logic clk`;
`always_ff`; `_gen_imem_wr_en`; `_gen_gateAcc`; `sext_msb`. Prediction: all
keep their verdict (module header and ports unchanged; `always_ff` is
printed for every register of either text; the three names are identifiers
of the old text, hence of the new one).

### 5. `verilator/tb_soc.cpp` 172–383 (internal signal names), `verilator/Makefile` 25

Reads `rv32i_soc.gen_soc.<name>` for `_gen_byte{0..3}_rdata`,
`_gen_actual_dmem_write_addr`, `_gen_actual_byte{0..3}_we`,
`_gen_trap_taken`, `_gen_trapCause` — wires of the generated TOP module.
Needs the SoC synthesis and a Verilator build of the SoC: not to run.

Prediction: the names exist in the new top (identifiers of the old top). If
the SoC top has a memory statement of its own, its text is IDENTICAL to the
old one (last branch of `checkedOptimize`); only the `@[hardware_module]`
children change (unoptimized).
UNVERIFIED RISKS, to be settled by one SoC run when the queue allows:
(a) which branch of `checkedOptimize` the SoC top takes was not determined;
(b) Verilator sees larger child modules (compile time; more signals);
(c) a child whose printed text was only correct AFTER an optimizer pass —
the comment on `toVerilogDesign` (`Sparkle/Backend/Verilog.lean` 484–498)
records one such history (zero-width concat tails freezing a register of
`uartRxHW`). The children now come from their own full entry, which runs
`dropZeroWidthModule`; on the 37 measured designs no child keeps a
zero-width wire, but the SoC's and the H.264 children were not in that
census.

### 6. The H.264 `#writeDesign` files (`IP/Video/H264/*Synth.lean`, 12 commands) and `.github/workflows/build.yml` 96–107

The workflow tests that the `.sv` files EXIST (`test -f`): unchanged. No
file of the tree reads their text. Their C simulation / JIT wrapper do not
come from the writer. Building them is the H.264 synthesis: not to run for
this.

### 7. Not affected

`Examples/HierarchicalCPU.lean` 117, 135 (`#synthesizeVerilogDesign`, prints
only), `Examples/CDC/MultiClockSim.lean` 62, 94 (`#writeDesign`; its
simulation uses the C output), the seven `#sim` users
(`Tests/IP/**/*JITTest.lean`, `Tests/Synthesis/TopLevelSimJITTest.lean`:
`#sim` is not switched).
