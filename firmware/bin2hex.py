#!/usr/bin/env python3
"""
Convert a raw binary file to Verilog $readmemh hex format.

Output format:
    @00000000       <- word address (optional, included for clarity)
    DEADBEEF        <- 32-bit word in hex (little-endian binary → big-endian hex)
    CAFEBABE
    ...

Usage:
    python3 bin2hex.py firmware.bin firmware.hex
"""

import sys
import struct


def bin2hex(input_path: str, output_path: str) -> None:
    with open(input_path, "rb") as f:
        data = f.read()

    # Pad to 4-byte alignment
    pad = (4 - len(data) % 4) % 4
    data += b"\x00" * pad

    with open(output_path, "w") as f:
        f.write("@00000000\n")
        for i in range(0, len(data), 4):
            word = struct.unpack_from("<I", data, i)[0]  # Little-endian
            f.write(f"{word:08X}\n")

    num_words = len(data) // 4
    print(f"[bin2hex] {input_path} -> {output_path}: {num_words} words ({len(data)} bytes)")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <input.bin> <output.hex>", file=sys.stderr)
        sys.exit(1)
    bin2hex(sys.argv[1], sys.argv[2])
