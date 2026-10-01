#!/usr/bin/env python3
"""Split a multi-module Verilog file into <out>/<Module>.sv (one module per
file, the layout sv-roundtrip / sv-cosim --hier expect).  Top-of-file
`define / `timescale lines are copied into every piece."""
import re, sys, os
src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
text = open(src).read()
first = re.search(r'^\s*module\b', text, re.M)
prelude = ''.join(l for l in text[:first.start()].splitlines(True)
                  if l.lstrip().startswith(('`define', '`timescale')))
for m in re.finditer(r'^\s*module\s+(\w+).*?^\s*endmodule\b[^\n]*\n?', text, re.M | re.S):
    open(os.path.join(out, m.group(1) + '.sv'), 'w').write(prelude + m.group(0).lstrip('\n') + '\n')
