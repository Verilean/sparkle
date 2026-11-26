#!/usr/bin/env python3
"""Check every relative link and anchor in the research docs.

Usage: python3 -I scripts/research/check_links.py

Checked files: docs/research/*.md, docs/research/appendix/*.md,
docs/tutorial/md/Ch07c_VerifiedSynthesis.md, docs/tutorial/README.md.
A link `[text](target#anchor)` passes when `target` exists in the tree (file or directory,
resolved relative to the linking file) and, for a markdown target with an anchor, the anchor
equals the GitHub-style slug of one of its headings. http(s) and mailto links are not fetched.
Links inside code fences and inline code are ignored. Exit 0 when all pass, 1 otherwise.
"""
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FILES = (sorted(glob.glob(os.path.join(ROOT, "docs/research/*.md")))
         + sorted(glob.glob(os.path.join(ROOT, "docs/research/appendix/*.md")))
         + [os.path.join(ROOT, "docs/tutorial/md/Ch07c_VerifiedSynthesis.md"),
            os.path.join(ROOT, "docs/tutorial/README.md")])
LINK = re.compile(r"(?<!!)\[[^\]]*\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")


def strip_code(text):
    out, fence = [], False
    for line in text.split("\n"):
        if line.lstrip().startswith("```"):
            fence = not fence
            out.append("")
        elif fence:
            out.append("")
        else:
            out.append(re.sub(r"`[^`]*`", "", line))
    return out


def slug(h):
    h = re.sub(r"`", "", h.strip().lower())
    h = re.sub(r"[^\w\- ]", "", h)
    return h.replace(" ", "-")


def anchors(path):
    res, seen = set(), {}
    with open(path, encoding="utf-8") as f:
        text = f.read()
    for line in strip_code(text):
        m = re.match(r"#{1,6}\s+(.*?)\s*#*\s*$", line)
        if m:
            s = slug(m.group(1))
            n = seen.get(s, 0)
            seen[s] = n + 1
            res.add(s if n == 0 else f"{s}-{n}")
    return res


def main():
    bad, total = [], 0
    for f in FILES:
        with open(f, encoding="utf-8") as fh:
            lines = strip_code(fh.read())
        for i, line in enumerate(lines, 1):
            for m in LINK.finditer(line):
                t = m.group(1)
                if re.match(r"^(https?:|mailto:)", t):
                    continue
                total += 1
                target, _, anchor = t.partition("#")
                dest = f if target == "" else os.path.normpath(os.path.join(os.path.dirname(f), target))
                rel = os.path.relpath(f, ROOT)
                if not os.path.exists(dest):
                    bad.append(f"{rel}:{i}: missing target {t}")
                elif anchor and dest.endswith(".md") and anchor not in anchors(dest):
                    bad.append(f"{rel}:{i}: missing anchor {t}")
    for b in bad:
        print(b)
    print(f"checked {len(FILES)} files, {total} relative links, {len(bad)} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
