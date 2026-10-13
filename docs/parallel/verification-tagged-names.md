# Tagged module names under the tools available here (2026-10-14, ruling item 6) — PARTIAL

Tools on this machine (nix shell; nothing installed for this check): Yosys 0.69, Verilator 5.052,
iverilog 13.0, gcc / g++ 15.3.0. Run `names` under cgrun (script `~/sparkle-work/hfix-sample/names.sh`,
outputs `~/sparkle-work/names/`), on the writer outputs that `module_name_sim.sh` generates on poc
b155bbbb (the four Finding H tops: modules named `Sp$D$_35_ccp_46_k`, `Sp$D$_35_ccp$k`,
`Sp$D$SparkleMem__combo__4__8`, … next to plain names).

| input | yosys `read_verilog -sv; hierarchy -check -top; proc; opt; stat` | verilator `--lint-only -sv --top-module` |
|---|---|---|
| nTop_cmd.sv (6 lines with tagged names) | exit 0 | exit 0 |
| nDirect_cmd.sv (6) | exit 0 | exit 0 |
| mTop_cmd.sv (6) | exit 0 | exit 0 |
| mmTop_cmd.sv (3; a declaration named like a memory) | exit 0 | exit 0 |
(The `*_tb.sv` files are iverilog testbenches without their DUT and were not meant to be read alone.)
iverilog: accepted (the simulations of verification-h-fix.md).
C side: `gcc -std=c11`, `gcc -std=c11 -pedantic-errors` and `g++ -std=c++17` accept `$` in struct and
function identifiers (a 3-line program, exit 0, runs).
By reading: the C backend's `Sparkle.Backend.CSim.sanitizeName` (CSim.lean 74) keeps alphanumerics, `_`
and `$`, so it is the IDENTITY on every encoded module name — no new collision among module/class names
there; for other names it deletes `#` and maps `.`, `-`, space to `_`, which is not injective in general
(wire names, not module names; not examined further).

NOT done (still unverified): a `private` declaration and a reserved-word declaration (`module`, `1bad`)
taken through yosys / Verilator as real compiler output (only the constructed `#ccp.k`-style names were);
the repository's actual C JIT flow on a design with a tagged module name (only the identifier rule was
tried); the FPGA flows under `fpga/` and `hw/synth/synth.ys` (vendor tools not run); any tool not listed.
