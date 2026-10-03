#!/usr/bin/env bash
# Rebuild litex_bench.hex (needs a riscv32 bare-metal gcc; the hex is
# committed so CI and the gate never need the toolchain).
set -euo pipefail
cd "$(dirname "$0")"
CROSS=${CROSS:-riscv32-none-elf-}
${CROSS}gcc -march=rv32im -mabi=ilp32 -O2 -ffreestanding -nostdlib -nostartfiles \
  -fno-builtin -Wl,-T,link.ld -Wl,--build-id=none -o litex_bench.elf start.S main.c
${CROSS}objcopy -O binary litex_bench.elf litex_bench.bin
python3 - <<'PY'
import struct
d = open('litex_bench.bin', 'rb').read()
d += b'\0' * (-len(d) % 4)
with open('litex_bench.hex', 'w') as f:
    for (w,) in struct.iter_unpack('<I', d):
        f.write('%08x\n' % w)
print(len(d) // 4, 'words')
PY
rm -f litex_bench.elf litex_bench.bin
