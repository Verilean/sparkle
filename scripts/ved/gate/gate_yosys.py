#!/usr/bin/env python3
"""VED release gate, circuit-size stage: yosys statistics per row.

Run from this directory through the pinned tools (flake.nix here):

    kjob dev -- python3 -I gate_yosys.py --sv DIR --out OUT.tsv [--gowin ROWS] [--jobs N]

For every DIR/R<n>.sv: `read_verilog -sv; hierarchy -auto-top; synth -run coarse;
stat -json` (the flow of bench/xiangshan/compare_stat.sh), and records the total
cell count, the cells by type (JSON), and the wire bits.  For the rows listed in
--gowin (comma-separated row numbers) it also runs `synth_gowin` (the Tang Nano
20k flow of fpga/tangNano20k) and records the mapped cells by type.
A yosys failure is recorded as `error` with its exit status; nothing is skipped.
"""
import argparse
import concurrent.futures as cf
import csv
import json
import os
import re
import subprocess
import tempfile


def run(script, sv):
    with tempfile.TemporaryDirectory() as td:
        js = os.path.join(td, "stat.json")
        p = subprocess.run(["yosys", "-q", "-p", f"read_verilog -sv {sv}; hierarchy -auto-top; {script}; "
                            f"tee -q -o {js} stat -json"], capture_output=True, text=True, timeout=3600)
        if p.returncode != 0 or not os.path.isfile(js):
            return {"status": "error", "exit": p.returncode, "msg": (p.stderr or p.stdout)[-300:].replace("\n", " ")}
        d = json.load(open(js))
    des = d.get("design", {})
    return {"status": "ok", "cells": des.get("num_cells", ""), "wire_bits": des.get("num_wire_bits", ""),
            "by_type": json.dumps(des.get("num_cells_by_type", {}), sort_keys=True)}


def one(sv, gowin):
    row = re.sub(r"\D", "", os.path.basename(sv))
    rec = {"row": row}
    c = run("synth -run coarse", sv)
    rec.update({f"coarse_{k}": v for k, v in c.items()})
    if row in gowin:
        g = run("synth_gowin", sv)
        rec.update({f"gowin_{k}": v for k, v in g.items()})
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sv", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--gowin", default="")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    a = ap.parse_args()
    gowin = {x for x in a.gowin.split(",") if x}
    svs = sorted((os.path.join(a.sv, f) for f in os.listdir(a.sv) if f.endswith(".sv")),
                 key=lambda p: int(re.sub(r"\D", "", os.path.basename(p))))
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        recs = list(ex.map(lambda s: one(s, gowin), svs))
    cols = ["row"] + [f"{p}_{k}" for p in ("coarse", "gowin")
                      for k in ("status", "exit", "cells", "wire_bits", "by_type", "msg")]
    with open(a.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter="\t", extrasaction="ignore")
        w.writeheader()
        for r in recs:
            w.writerow(r)
    ver = subprocess.run(["yosys", "-V"], capture_output=True, text=True).stdout.strip()
    print(f"GATEYOSYS rows={len(recs)} errors={sum(r.get('coarse_status') != 'ok' for r in recs)} yosys={ver}")


if __name__ == "__main__":
    main()
