#!/usr/bin/env python3
"""FAKE yosys for the size harness tests: `fake_yosys.py -q -s SCRIPT -l LOG`.  Reads the script
(read_verilog / hierarchy -top T / synth | synth_gowin / tee -q -o STAT stat), writes a log with the
version banner and a canned `stat` whose size is the byte length of the first SV file (so identical SV
gives identical numbers).  Plan $FAKE_YS (JSON): missing [tops], timeout [flows], fail [flows],
nostat [flows], garbage [flows], hier [flows] (print a design-hierarchy stat).  Flow = generic|fpga.
"""
import json
import os
import re
import sys
import time

GENERIC = """
4. Printing statistics.

=== {top} ===

        +----------Local Count, excluding submodules.
        | 
        7 wires
       19 wire bits
        3 public wires
        4 ports
{cells:>9} cells
{and_:>9}   $_AND_
{dffe:>9}   $_DFFE_PP_
{dff:>9}   $_DFF_P_
        1   $_XOR_

"""
FPGA = """
4. Printing statistics.

=== {top} ===

        +----------Local Count, excluding submodules.
        | 
      294 wires
        4 ports
{cells:>9} cells
{ff:>9}   DFF
        1   GND
        8   IBUF
{lut:>9}   LUT4
        3   LUT2
        1   MUX2_LUT5
        8   OBUF
{bram:>9}   SP
        1   VCC

"""
HIER = """
=== {top} ===

        +----------Local Count, excluding submodules.
        | 
        4 wires
        2 submodules
        2   sub

=== sub ===

        +----------Local Count, excluding submodules.
        | 
        7 wires
{cells:>9} cells
        4   $_DFF_P_
        6   $_XOR_

=== design hierarchy ===

        +----------Count including submodules.
        | 
       20 top
       10 sub

        +----------Count including submodules.
        | 
       18 wires
        - memories
{tot:>9} cells
        8   $_DFF_P_
       12   $_XOR_
        2 submodules
        2   sub

"""


def main():
    a = sys.argv[1:]
    script = open(a[a.index("-s") + 1]).read()
    logp = a[a.index("-l") + 1]
    plan = json.loads(os.environ.get("FAKE_YS", "{}"))
    flow = "fpga" if "synth_gowin" in script else "generic"
    top = re.search(r"hierarchy -top (\S+)", script).group(1)
    stat = re.search(r"tee -q -o (\S+) stat", script).group(1)
    files = re.search(r"read_verilog -sv (.+)", script).group(1).split()
    with open(os.environ.get("FAKE_YS_LOG", os.devnull), "a") as f:
        f.write(json.dumps({"flow": flow, "top": top, "files": [os.path.basename(x) for x in files]}) + "\n")
    open(logp, "w").write(" Yosys 0.70+post (git sha1 v0.70, FAKE)\n")
    if flow in plan.get("timeout", []):
        time.sleep(60)
    if top in plan.get("missing", []):
        print(f"ERROR: Module `{top}' not found!")
        sys.exit(1)
    if flow in plan.get("fail", []):
        print("ERROR: syntax error, unexpected '}'")
        sys.exit(1)
    if flow in plan.get("nostat", []):
        return
    n = len(open(files[0]).read())
    if flow in plan.get("garbage", []):
        open(stat, "w").write("nothing useful\n")
    elif flow in plan.get("hier", []):
        open(stat, "w").write(HIER.format(top=top, cells=n, tot=n * 2))
    elif flow == "generic":
        open(stat, "w").write(GENERIC.format(top=top, cells=n + 10, and_=n, dffe=2, dff=4))
    else:
        open(stat, "w").write(FPGA.format(top=top, cells=n + 20, ff=6, lut=n, bram=1))


if __name__ == "__main__":
    main()
