#!/usr/bin/env python3
"""Extract ```lean fenced blocks from a Markdown file into standalone .lean files.

Each block becomes `block_NN.lean` with a shared preamble so every block can be
type-checked in isolation via `lake env lean`.

Opt-out: annotate a block with an HTML comment `<!-- no-compile -->` on the
line immediately before the fence (or `<!-- no-compile: reason -->`).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

PREAMBLE = """\
import Sparkle
open Sparkle.Core.Domain
open Sparkle.Core.Signal
"""

FENCE_OPEN = re.compile(r"^```lean\s*$")
FENCE_CLOSE = re.compile(r"^```\s*$")
NO_COMPILE = re.compile(r"<!--\s*no-compile")


def main() -> int:
    if len(sys.argv) != 3:
        print(f"usage: {sys.argv[0]} <markdown> <outdir>", file=sys.stderr)
        return 2

    md_path = Path(sys.argv[1])
    out_dir = Path(sys.argv[2])
    out_dir.mkdir(parents=True, exist_ok=True)

    lines = md_path.read_text().splitlines()

    blocks: list[tuple[int, list[str]]] = []
    i = 0
    block_idx = 0
    while i < len(lines):
        line = lines[i]
        if FENCE_OPEN.match(line):
            # look back one non-blank line for a no-compile marker
            j = i - 1
            while j >= 0 and lines[j].strip() == "":
                j -= 1
            skip = j >= 0 and NO_COMPILE.search(lines[j]) is not None

            body: list[str] = []
            i += 1
            while i < len(lines) and not FENCE_CLOSE.match(lines[i]):
                body.append(lines[i])
                i += 1
            if not skip:
                blocks.append((block_idx, body))
            block_idx += 1
        i += 1

    # If a block already begins with `import`/`open` lines, let them stand and
    # skip the preamble (avoids "import after first command" errors and
    # duplicate opens).
    for idx, body in blocks:
        out = out_dir / f"block_{idx:02d}.lean"
        has_header = any(
            ln.startswith("import ") or ln.startswith("open ")
            for ln in body[:5]
        )
        text = "\n".join(body) + "\n"
        if not has_header:
            text = PREAMBLE + "\n" + text
        out.write_text(text)

    print(f"Extracted {len(blocks)} block(s) into {out_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
