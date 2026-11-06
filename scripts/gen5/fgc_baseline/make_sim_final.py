#!/usr/bin/env python3
"""S0: fix the final simulation-check table (sim_final.tsv) from the saved sim results.

usage: make_sim_final.py BABB_SIM_RESULTS_TSV > sim_final.tsv
BABB_SIM_RESULTS_TSV = kjob-run-src-fgc-s0run-babb/fgc_sim/sim_results.tsv (the first run: 147 attempt rows,
name / exit / seconds; `exe-test` appears twice = two attempts of one check).  The overrides below are the
later runs (sim_rerun.sh) read from their sim_rerun/*.tsv; each is (final job, exit, result, note).
Result values: PASS | KNOWN-FAIL (pre-existing defect, kept as failing) | REPLACED-BY-JIT (see jit_substitute).
"""
import collections, sys

FIRST = 'kjob-run-src-fgc-s0run-babb'
over = {
    'exe-test': ('kjob-run-src-fgc-s0r-249c', 0, 'PASS', 'rerun as exe-test-rerun after writing verilator/generated_soc{.sv,_cppsim.h}; the 15 failed assertions were those missing files', ''),
    'exe-cdc-multi-clock-test': ('kjob-run-src-fgc-s0r-0a87', 0, 'PASS', 'needed c_src/cdc cdc_runner.so (make -C c_src/cdc cdc_runner.so)', ''),
    'exe-sim-runner-test': ('kjob-run-src-fgc-s0r-0a87', 0, 'PASS', 'needed cdc_runner.so', ''),
    'exe-bitnet-soc-test': ('kjob-run-src-fgc-s0r-0a87', 0, 'PASS', 'needed verilator/generated_soc.sv (lean IP/RV32/SoCVerilog.lean writes it)', ''),
    'exe-rv32-flow-test': ('kjob-run-src-fgc-s0r-0a87', 0, 'PASS', 'needed verilator/generated_soc.sv', ''),
    'verify-parameterized-csim': ('kjob-run-src-fgc-s0r-0a87', 0, 'PASS', 'script now uses LEAN/LEAN_PATH directly (no nested lake env)', ''),
    'exe-toplevel-sim-test': ('kjob-run-src-fgc-s0r-38fb', 124, 'REPLACED-BY-JIT', 'pure-Lean Signal evaluation is O(t^2): no output in 900 s in both runs (babb, 38fb)', 'exe-toplevel-sim-jit-test'),
    'exe-h264-bitstream-test': ('kjob-run-src-fgc-s0r-bd46', 1, 'KNOWN-FAIL', 'JIT: wire _gen_done not found (pre-existing keep-wire defect; same in poc kjob-run-src-cavlc-poc-bc79)', ''),
    'exe-h264-playable-test': ('kjob-run-src-fgc-s0r-bd46', 1, 'KNOWN-FAIL', 'JIT: wire _gen_done not found (same defect)', ''),
    'exe-h264-frame-encoder-test': ('kjob-run-src-fgc-s0r-bd46', 1, 'KNOWN-FAIL', 'JIT: wire _gen_cavlcBitBuffer not found (same defect)', ''),
}
extra = [('exe-toplevel-sim-jit-test', 'kjob-run-src-fgc-s0r-38fb', 0, 'PASS', 'substitute for exe-toplevel-sim-test: same 50-cycle stimulus via JIT, ALL PASS', '')]
att = collections.OrderedDict()
for l in open(sys.argv[1]).read().split('\n'):
    if l:
        n, rc, secs = l.split('\t'); att.setdefault(n, []).append((int(rc), int(secs)))
cols = ['check', 'kind', 'first_job', 'first_exit', 'first_attempts', 'final_job', 'final_exit', 'result', 'existing_failure', 'jit_substitute', 'note']
print('\t'.join(cols))
def kind(n):
    return 'build' if n.startswith('build-') else 'script' if n == 'verify-parameterized-csim' else 'exe'
for n, a in att.items():
    first = a[0][0]
    if n in over:
        fj, fe, res, note, sub = over[n]
    else:
        fj, fe, res, note, sub = FIRST, a[-1][0], 'PASS' if a[-1][0] == 0 else 'UNEXPLAINED', '', ''
    assert res != 'UNEXPLAINED', n
    print('\t'.join(map(str, [n, kind(n), FIRST, first, len(a), fj, fe, res, 'yes' if res == 'KNOWN-FAIL' else 'no', sub, note])))
for n, fj, fe, res, note, sub in extra:
    print('\t'.join(map(str, [n, 'exe', '-', '-', 0, fj, fe, res, 'no', '', note])))
