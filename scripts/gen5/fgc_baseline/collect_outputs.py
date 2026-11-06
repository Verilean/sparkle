#!/usr/bin/env python3
"""S0 output baseline for #writeDesign / #writeVerilogDesign (these print no module text on stdout).

usage: collect_outputs.py RAW_DIR STORE_DIR [FILES_FILTER]   (run from the repo root, after the files
       were elaborated by capture.sh, so the written files exist at their relative paths)
Reads  scripts/gen5/fgc_baseline/inventory.tsv, RAW/out/<key>.txt (stdout of the elaboration), the source files
Writes STORE/<file-key>/<line>/<kind>-<basename>   a copy of every written file (outside the source tree)
       STORE/output_baseline.tsv  one row per (command, kind): file line command top kind declared_path path
                                  status sha256 bytes stored
Attribution is by path, never by order: the first string literal of the command in the source is the .sv path;
the stdout block that starts with `Written N modules to <that path>` and its two following lines
(`Written C simulation ... to <p>`, `Written JIT wrapper to <p>`) give the other paths.  A command whose
.sv path is not in stdout, or whose file is not on disk, gets status NOT-IN-STDOUT / MISSING; summarize.py
--outputs turns any such row into FAIL.  Kinds: sv; and for #writeDesign also cppsim and jit.
"""
import hashlib, os, re, shutil, sys

raw, store = sys.argv[1], sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))
lines = open(f'{here}/inventory.tsv').read().split('\n')
hdr = lines[0].split('\t')
inv = [dict(zip(hdr, l.split('\t'))) for l in lines[1:] if l]
key = lambda f: f.replace('/', '_')
cmds = [r for r in inv if r['command'] in ('#writeDesign', '#writeVerilogDesign')]
os.makedirs(store, exist_ok=True)
rows = []
for r in cmds:
    f, ln = r['file'], int(r['line'])
    src = open(f).read().split('\n')
    # the command's text: its line and the continuation lines (indented or blank-free) up to the next blank line
    text = src[ln - 1]
    i = ln
    while i < len(src) and src[i].strip() and (src[i].startswith((' ', '\t'))):
        text += ' ' + src[i]; i += 1
    lits = re.findall(r'"([^"]+)"', text)
    declared = lits[0] if lits else ''
    out = open(f'{raw}/out/{key(f)}.txt', errors='replace').read().split('\n') if os.path.exists(f'{raw}/out/{key(f)}.txt') else []
    paths = {}
    for j, o in enumerate(out):
        m = re.match(r'Written \d+ modules to (.+)$', o)
        if m and m.group(1) == declared:
            paths['sv'] = m.group(1)
            for o2 in out[j + 1:j + 3]:
                m2 = re.match(r'Written C simulation \(\d+ modules\) to (.+)$', o2)
                m3 = re.match(r'Written JIT wrapper to (.+)$', o2)
                if m2: paths['cppsim'] = m2.group(1)
                if m3: paths['jit'] = m3.group(1)
            break
    kinds = ['sv'] if r['command'] == '#writeVerilogDesign' else ['sv', 'cppsim', 'jit']
    for k in kinds:
        p = paths.get(k, '')
        row = dict(file=f, line=ln, command=r['command'], top=r['top'], kind=k, declared_path=declared if k == 'sv' else '',
                   path=p, status='', sha256='', bytes='', stored='')
        if not p: row['status'] = 'NOT-IN-STDOUT'
        elif not os.path.isfile(p): row['status'] = 'MISSING'
        else:
            data = open(p, 'rb').read()
            dst = f'{store}/{key(f)}/{ln}/{k}-{os.path.basename(p)}'
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(p, dst)
            row.update(status='OK' if data else 'EMPTY', sha256=hashlib.sha256(data).hexdigest(), bytes=len(data), stored=dst)
        rows.append(row)
cols = list(rows[0].keys())
with open(f'{store}/output_baseline.tsv', 'w') as fh:
    fh.write('\t'.join(cols) + '\n')
    for row in rows: fh.write('\t'.join(str(row[c]) for c in cols) + '\n')
bad = [r for r in rows if r['status'] != 'OK']
print(f'commands {len(cmds)}, rows {len(rows)}, not OK {len(bad)}')
for r in bad: print(f"  {r['status']}: {r['file']}:{r['line']} {r['kind']} {r['path'] or r['declared_path']}")
sys.exit(1 if bad else 0)
