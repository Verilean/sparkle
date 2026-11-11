#!/usr/bin/env python3
"""Print the modules the U1 cases import (MEASUREMENT ONLY): the direct imports
of each listed row's source file plus the U1 tools, one per line, for
`kjob lake build $(...)` before running cases.  Rows are read from a
"ROW ROUTE" list (as u1_full.sh writes) or all 327 with --all."""
import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import u0_gen  # noqa: E402

TOOLS = ["Tools.VedU1Entry", "Tools.VedU1Deep", "Tools.VedU1HierEntry", "Tools.VedStrictAudit", "Tools.DeepElab"]


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--repo", default=".")
    p.add_argument("--list")
    p.add_argument("--all", action="store_true")
    a = p.parse_args()
    rows = u0_gen.git_show_inventory(a.repo, u0_gen.INV_COMMIT, u0_gen.INV_BLOB)
    lines = [] if a.all else [ln.split() for ln in open(a.list) if ln.strip()]
    want = None if a.all else {p[0] for p in lines}
    mods = set(TOOLS)
    if a.all or any(len(p) > 1 and p[1] == "u1_packed" for p in lines):
        mods.add("Tools.VedU1PackedEntry")
    for r in rows:
        if want is not None and r["row"] not in want:
            continue
        path = os.path.join(a.repo, r["file"])
        if not os.path.exists(path):
            continue
        for ln in u0_gen.blank_comments(open(path, errors="replace").read()).splitlines():
            m = re.match(r"^\s*(?:public\s+)?import\s+(.+)", ln)
            if m:
                mods.update(m.group(1).split())
            elif ln.strip() and not re.match(r"^\s*(module|prelude)\s*$", ln):
                break
    print("\n".join(sorted(mods)))


if __name__ == "__main__":
    main()
