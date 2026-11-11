#!/usr/bin/env python3
"""The content digest `kjob lake build` records as `source_sha256` (MEASUREMENT ONLY).

  tree_digest.py [DIR]     prints the sha256 of the tree at DIR (default: the current directory)

Same method as kjob-session's lake_build: every file `git ls-files --cached --others --exclude-standard`
lists (sorted, without .git/ and .lake/), hashed as name NUL + ("symlink" NUL target | "file" NUL mode +
content | "missing" NUL).  lean_isolated.sh compares it with the build it runs on, so a case never reads
the oleans of a tree other than the one checked out now.
"""
import hashlib
import os
import subprocess
import sys


def digest(source):
    names = subprocess.check_output(["git", "-C", source, "ls-files", "-z", "--cached", "--others",
                                     "--exclude-standard"], text=True).split("\0")
    h = hashlib.sha256()
    for name in sorted(set(names) - {""}):
        rel = name.split("/")
        if os.path.isabs(name) or ".." in rel or rel[0] in (".git", ".lake"):
            continue
        item = os.path.join(source, name)
        h.update(name.encode() + b"\0")
        if os.path.islink(item):
            h.update(b"symlink\0" + os.readlink(item).encode())
        elif os.path.isfile(item):
            h.update(b"file\0" + str(os.stat(item).st_mode & 0o777).encode())
            with open(item, "rb") as f:
                for chunk in iter(lambda: f.read(1048576), b""):
                    h.update(chunk)
        else:
            h.update(b"missing\0")
    return h.hexdigest()


if __name__ == "__main__":
    print(digest(sys.argv[1] if len(sys.argv) > 1 else "."))
