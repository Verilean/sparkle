# Simulator instruction-count gate

`bench/gate/run.sh` answers one question on every change: **did the
generated simulator get slower?**  It does so without a stopwatch.

## Why not wall-clock

The CI benchmark steps measured cycles per second.  That number moves
±25 % between two runs of the same commit on shared runners, the
comparison history stopped being stored, and the alert was configured not
to fail.  Meanwhile the single-core LiteX JIT went from "1.13× Verilator"
in `bench/README.md` to about 0.45× in CI.  Most of that was the price of
fixing an unsound model, some of it was an optimisation dropped as "no
behavior change" — and nobody could tell which, because nothing that
was recorded could be compared.

Executed instructions per simulated cycle do not have that problem.  The
count is exact and repeatable, and on this workload it predicts wall
time: Verilator, the JIT and the older JIT all retire instructions at
about the same rate on the host, so the ratio of the counts is the ratio
of the run times.

A *static* count — lines of C, instructions in the object file — is not a
substitute.  A model that keeps `if`/`else` has more code and executes
less of it.

## What is compared with what

The gate does not compare against a number.  A number would be tied to
the compiler that produced it, and every runner image update would break
it.  It compares two C files, compiled side by side by the same compiler:

* **head** — the CSim JIT C generated from the current tree;
* **golden** — `golden/litex_jit.c`, the C a previous tree generated.

The design is the LiteX PicoRV32 SoC (`Tests/SVParser/fixtures/
litex_sim_minimal.v` + PicoRV32 at a pinned commit), running
`fw/litex_bench.hex`: sort, byte/half-word stores, multiply, divide, the
timer and the UART, forever, with a checksum line per round.

head must stay within ±3 % of the golden.  Slower fails.  Faster fails
too: an improvement that is not recorded is one the next regression can
eat unnoticed.  Either way the fix is

    bench/gate/run.sh --update
    git add -f bench/gate/golden/litex_jit.c

in the same change, so the diff of the golden is the record of when the
cost moved and why.

## Correctness comes first

A simulator can always be made faster by computing the wrong thing, so
before anything is counted the script co-simulates head against Verilator
on the same RTL and firmware: each UART byte must leave on the same
cycle.  head and golden must agree in the same way.

This check is what found that the previous benchmark was not measuring a
running CPU at all: the ROM was empty, PicoRV32 trapped on the first
instruction, and three lowering bugs (multi-bit `if` conditions,
`reg x = v;` initializers, memory reads into internal wires) meant the
JIT model was not even trapping the way Verilator did.

## What is generated

`gen.lean` asks for the fast configuration, `toCJIT design
(fusedLocalWires := true)`: inside `eval_tick` internal wires are stack
locals, so the C compiler drops what nothing reads and computes a wire
only on the branch that uses it.  After `eval_tick` such a wire's
`get_wire` value is stale until `eval` is called; registers, memories and
outputs are unaffected.  This is the like-for-like comparison with
Verilator, whose default also exposes no internal signals.  The default
configuration (every named wire current after `eval_tick`) costs about
45 % more instructions on this design.

## Running it

    bench/gate/run.sh              # needs lake, cc, verilator, and valgrind or perf

`valgrind --tool=cachegrind` is used when installed (exact); `perf stat`
otherwise.  `NO_VERILATOR=1` skips the co-simulation for a quick local
look; CI never sets it.  The script prints, and in CI adds to the job
summary, instructions per cycle for head, golden and Verilator.

`fw/build.sh` rebuilds the firmware (riscv32 bare-metal gcc).  The hex is
committed, so neither CI nor the gate needs the toolchain; rebuilding it
changes the workload and therefore needs `--update` as well.
