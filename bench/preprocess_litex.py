#!/usr/bin/env python3
"""Preprocess LiteX Verilog for Sparkle JIT parsing.

Handles LiteX/Migen idioms:
- @(*) → @*
- begin : name → begin (named blocks)
- integer declarations → remove
- for-loop byte-lane writes → unroll + whole-word conversion
"""
import re
import sys
import os

def preprocess(input_path, pico_path, output_path):
    with open(input_path) as f:
        litex = f.read()
    pico = ""
    if os.path.exists(pico_path):
        with open(pico_path) as f:
            pico = f.read()
    c = litex + "\n" + pico
    c = c.replace("@(*)", "@*")

    # Named blocks + integer
    lines = c.split("\n")
    r = []
    for l in lines:
        stripped = l.lstrip()
        if stripped.startswith("integer "):
            r.append("")
        elif "begin : " in l:
            r.append(l.split("begin : ")[0] + "begin")
        else:
            r.append(l)
    c = "\n".join(r)

    # For-loop unroll
    pat = r'for\s*\((\w+)\s*=\s*0\s*;\s*\1\s*<\s*4\s*;\s*\1\s*=\s*\1\s*\+\s*1\)\s*\n((?:\t\t|\s{8}).*(?:\n(?:\t\t\t|\s{12}).*)*)'
    def unroll(m):
        var, body = m.group(1), m.group(2)
        return "\n".join(
            body.replace(f"{var}*8", f"{i*8}").replace(f"{var}]", f"{i}]")
            for i in range(4)
        )
    c = re.sub(pat, unroll, c)

    # Byte-lane → whole-word
    p2 = r'if \((\w+)\[0\]\)\s*\n\s*(\w+)\[(\w+)\]\[0 \+: 8\] <= (\w+)\[0 \+: 8\];'
    for m in re.finditer(p2, c):
        we, arr, addr, data = m.group(1), m.group(2), m.group(3), m.group(4)
        rep = f"\tif ({we}) {arr}[{addr}] <= {data};"
        for i in range(4):
            old = f"\tif ({we}[{i}])\n\t\t\t{arr}[{addr}][{i*8} +: 8] <= {data}[{i*8} +: 8];"
            c = c.replace(old, rep if i == 0 else "")

    with open(output_path, "w") as f:
        f.write(c)
    print(f"Preprocessed: {output_path} ({len(c)} chars)")

if __name__ == "__main__":
    base = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(base)
    input_v = os.path.join(root, "Tests/SVParser/fixtures/litex_sim_minimal.v")
    pico_v = "/tmp/picorv32.v"
    output_v = "/tmp/litex_pp.v"
    if len(sys.argv) > 1:
        output_v = sys.argv[1]
    preprocess(input_v, pico_v, output_v)
