#!/usr/bin/env python3
"""OldEqV drift check -- a COMPARISON AID, not a correctness proof.

`Tools/ShippingReaderFuelVerbatim.lean` (`OldEqV`, `OldEqNV`),
`Tools/ShippingReaderFuelOldEq.lean` (`OldEq`, `OldEqN`), the fuel bodies of
`Tools/ShippingReaderFuelDefs.lean` and the wrapper fragments of
`Tools/ShippingReaderFuelShape.lean` COPY the source text of the reader's
`partial def`s in `Sparkle/Compiler/Elab.lean` (and the local `let rec`s /
`foldlM` / `findSome?` functions inside them, which are covered by the text of
the enclosing definition).  Lean cannot check that the copy still matches the
compiled `partial` constants (they are opaque).  This script extracts the text
of those definitions from the CURRENT Elab.lean and compares it with the
snapshot taken when the copies were made
(`scripts/shipping-coverage/oldeqv_snapshot.txt`).

Exit status: 0 = no drift; 1 = drift (the differing definition names are
printed); 2 = a definition was not found / usage error.

A clean result says only that the source TEXT of the listed definitions is
unchanged since the snapshot.  It does not say the copies were right (that is
what `oldEq_of_oldEqV` / `step_tot` are about, against the copies) nor that
the compiled code satisfies its equations (O2, outside the kernel).  On drift,
the copies must be re-examined and re-proved; only then regenerate the
snapshot with `--update`.

Usage:
  oldeqv_drift.py [--elab PATH] [--snapshot PATH] [--diff] [--update]
"""
import argparse
import difflib
import hashlib
import os
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
DEFAULT_ELAB = os.path.join(ROOT, "Sparkle", "Compiler", "Elab.lean")
DEFAULT_SNAP = os.path.join(os.path.dirname(os.path.abspath(__file__)), "oldeqv_snapshot.txt")

# The copied definitions.  The first eight are the ones OldEqV / OldEqNV copy
# (with their local `let rec bundle` / `let rec inst` and the `foldlM` /
# `findSome?` functions, all inside these texts); `machineShape?` is the
# wrapper whose fragments `…FuelShape.lean` copies (shapePre / shapeMid /
# shapePost / shapeStart / shapeRootLet / shapeBody).
NAMES = [
    "machConv",
    "machNested",
    "machInstance",
    "machInstanceS",
    "machChain",
    "machLoopBody",
    "machLoopRoot",
    "machNorm",
    "machineShape?",
]

HEADER = re.compile(r"^(?:private |protected )?(?:partial |noncomputable )?def (\S+)")


def extract(lines, name):
    """Text of `def name` from its header line up to (excluding) the next line
    that starts at column 0 (the next declaration, docstring, `end`, ...),
    trailing blank lines dropped."""
    start = None
    for i, ln in enumerate(lines):
        m = HEADER.match(ln)
        if m and m.group(1) == name:
            if start is not None:
                raise SystemExit(f"oldeqv_drift: '{name}' defined twice")
            start = i
    if start is None:
        return None
    end = start + 1
    while end < len(lines):
        ln = lines[end]
        if ln.strip() and not ln[0].isspace():
            break
        end += 1
    body = lines[start:end]
    while body and not body[-1].strip():
        body.pop()
    return "\n".join(l.rstrip() for l in body) + "\n"


def snapshot_text(elab_path):
    with open(elab_path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    out = {}
    for n in NAMES:
        t = extract(lines, n)
        if t is None:
            print(f"oldeqv_drift: definition '{n}' NOT FOUND in {elab_path}", file=sys.stderr)
            sys.exit(2)
        out[n] = t
    return out


def render(defs):
    parts = []
    for n in NAMES:
        t = defs[n]
        h = hashlib.sha256(t.encode("utf-8")).hexdigest()
        parts.append(f"=== {n} {h} {t.count(chr(10))}\n{t}")
    return "".join(parts)


def parse(snap_path):
    defs = {}
    cur = None
    buf = []
    with open(snap_path, encoding="utf-8") as f:
        for ln in f:
            if ln.startswith("=== "):
                if cur is not None:
                    defs[cur] = "".join(buf)
                cur = ln[4:].split(" ")[0]
                buf = []
            elif cur is not None:
                buf.append(ln)
    if cur is not None:
        defs[cur] = "".join(buf)
    return defs


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--elab", default=DEFAULT_ELAB)
    ap.add_argument("--snapshot", default=DEFAULT_SNAP)
    ap.add_argument("--diff", action="store_true", help="print a unified diff per drifted definition")
    ap.add_argument("--update", action="store_true",
                    help="rewrite the snapshot from the current Elab.lean (only after re-checking the copies)")
    a = ap.parse_args()

    cur = snapshot_text(a.elab)
    if a.update:
        with open(a.snapshot, "w", encoding="utf-8") as f:
            f.write(render(cur))
        print(f"oldeqv_drift: snapshot written ({len(NAMES)} definitions) -> {a.snapshot}")
        return 0

    if not os.path.exists(a.snapshot):
        print(f"oldeqv_drift: snapshot {a.snapshot} missing", file=sys.stderr)
        return 2
    old = parse(a.snapshot)
    drifted = []
    for n in NAMES:
        if n not in old:
            drifted.append(n)
            if a.diff:
                print(f"--- {n}: not in snapshot")
            continue
        if old[n] != cur[n]:
            drifted.append(n)
            if a.diff:
                sys.stdout.writelines(difflib.unified_diff(
                    old[n].splitlines(True), cur[n].splitlines(True),
                    fromfile=f"snapshot/{n}", tofile=f"Elab.lean/{n}"))
    if drifted:
        print("oldeqv_drift: DRIFT in: " + " ".join(drifted))
        print("  (comparison aid only: re-examine the copies in Tools/ShippingReaderFuel*.lean)")
        return 1
    print(f"oldeqv_drift: no drift ({len(NAMES)} definitions match the snapshot)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
