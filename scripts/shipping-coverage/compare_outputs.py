#!/usr/bin/env python3
"""Compare the outputs two runs of pass 1 kept (WORKDIR/out).

    scripts/shipping-coverage/compare_outputs.py OLD_WORK/out NEW_WORK/out

Every file's text (the generated Verilog of each `#synthesizeVerilog` is in
it) is compared after dropping profile/timing lines.  A file is

  identical   byte for byte;
  renumbered  equal once the numeric suffixes of fresh `_tmp_*` wire names are
              renumbered in order of first appearance — or, for files holding
              several modules that reuse a name, once the suffixes are dropped
              (the compiler allocated a different number of fresh names,
              typically a sharing change, and emitted the same hardware);
  different   anything else.  Source positions in messages are ignored.

The dispatch arms are shared by the certified and the legacy front end, so
this is the check that a compiler change did not alter what legacy-route
designs compile to.  Exit status 1 when a file is `different`.
"""
import glob, os, re, sys


def text(path):
    return ''.join(
        l for l in open(path, errors='replace')
        if not l.startswith('[profile]') and not l.startswith('  Meta ')
        and not l.startswith('  handle') and ' calls / ' not in l
        and not l.rstrip().endswith(' ms)'))


def renumber(t):
    seen = {}

    def r(m):
        k = m.group(0)
        if k not in seen:
            seen[k] = '_tmp_' + m.group(1) + '#' + str(len(seen))
        return seen[k]
    return re.sub(r'_tmp_([A-Za-z0-9_]*?)_(\d+)\b', r, t)


def unnumber(t):
    return re.sub(r'_tmp_([A-Za-z0-9_]*?)_(\d+)\b', r'_tmp_\1_#', t)


def unposition(t):
    return re.sub(r'\.lean:\d+:\d+:', '.lean:', t)


old, new = sys.argv[1], sys.argv[2]
same = renum = diff = missing = 0
for f in sorted(glob.glob(old + '/*.txt')):
    g = os.path.join(new, os.path.basename(f))
    if not os.path.exists(g):
        missing += 1
        continue
    a, b = unposition(text(f)), unposition(text(g))
    if a == b:
        same += 1
    elif renumber(a) == renumber(b) or unnumber(a) == unnumber(b):
        renum += 1
        print('renumbered', os.path.basename(f))
    else:
        diff += 1
        print('DIFFERENT ', os.path.basename(f))
print(f'identical {same}, renumbered only {renum}, different {diff}, missing {missing}')
sys.exit(1 if diff else 0)
