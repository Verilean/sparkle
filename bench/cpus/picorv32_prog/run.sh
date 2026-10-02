#!/usr/bin/env bash
# usage: run.sh <original picorv32.v> <round-tripped dir (with picorv32.sv)> [workdir]
# Builds fw.S, runs it on both cores under iverilog, and diffs the bus traces.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
orig="$1"; rtdir="$2"; work="${3:-$(mktemp -d)}"
mkdir -p "$work"; cd "$work"
riscv32-none-elf-gcc -march=rv32i -mabi=ilp32 -nostdlib -Wl,-Ttext=0 -o fw.elf "$here/fw.S"
riscv32-none-elf-objcopy -O binary fw.elf fw.bin
python3 - <<'PY'
import struct
d = open('fw.bin', 'rb').read(); d += b'\0' * (-len(d) % 4)
open('fw.hex', 'w').write('\n'.join('%08x' % w for w in struct.unpack('<%dI' % (len(d) // 4), d)) + '\n')
PY
iverilog -g2012 -s prog_tb -o orig.vvp "$here/tb.v" "$orig"
iverilog -g2012 -s prog_tb -o rt.vvp "$here/tb.v" -y "$rtdir" -Y .sv "$rtdir/picorv32.sv"
vvp -n orig.vvp | grep -E '^(R|W|TRAP|TIMEOUT)' > orig.trace
vvp -n rt.vvp   | grep -E '^(R|W|TRAP|TIMEOUT)' > rt.trace
echo "original: $(wc -l < orig.trace) trace lines, last: $(tail -1 orig.trace)"
echo "roundtrip: $(wc -l < rt.trace) trace lines, last: $(tail -1 rt.trace)"
grep -q '^TRAP' orig.trace || { echo "FAIL: original did not reach ebreak"; exit 1; }
if cmp -s orig.trace rt.trace; then echo "PASS: bus traces identical"; else
  echo "FAIL: traces differ"; diff orig.trace rt.trace | head -10; exit 1; fi
