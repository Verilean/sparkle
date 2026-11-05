#!/usr/bin/env python3
"""S0 static inventory of synthesis commands (the "IP list" population).

usage: extract_inventory.py REPO_ROOT OUT_DIR
Writes OUT_DIR/inventory.tsv (one row per synthesis command occurrence) and
OUT_DIR/files.tsv (one row per file of the shipping-coverage run.sh file set).

Population: the run.sh file set (plus files whose only command is
#synthesizeParameterizedVerilog/#synthesizeDesign, which run.sh's grep misses)
and every `#synthesizeVerilog|#synthesizeParameterizedVerilog|
#synthesizeVerilogDesign|#writeDesign|#writeVerilogDesign|#synthesize` command
at line start in *.lean under Tests IP Examples (the grep of
scripts/shipping-coverage/run.sh). It is NOT the 235-root measurement and NOT
the 1369-compile measurement. Static: success/failure comes from capture.sh.
"""
import os, re, sys, collections

root, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
CMD = re.compile(r'^#(synthesizeParameterizedVerilog|synthesizeVerilogDesign|synthesizeVerilog|writeVerilogDesign|writeDesign|synthesizeDesign|synthesize)\b\s*(.*)$')
FILE_GREP = re.compile(r'^#synthesizeVerilog|^#writeDesign|^#writeVerilogDesign|^#synthesizeVerilogDesign|^#synthesize |^#synthesizeParameterizedVerilog|^#synthesizeDesign|synthesizeCombinational|synthesizeHierarchical', re.M)

def mod_of(path):
    return path[:-5].replace('/', '.')

# files of run.sh
files = []
for d in ('Tests', 'IP', 'Examples'):
    for dp, _, fs in os.walk(os.path.join(root, d)):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.relpath(os.path.join(dp, f), root)
                if FILE_GREP.search(open(os.path.join(root, p), errors='replace').read()):
                    files.append(p)
files.sort()

# import closure of Tests.AllTests (lake build Tests.AllTests)
def imports(path):
    try:
        txt = open(os.path.join(root, path), errors='replace').read()
    except OSError:
        return []
    return re.findall(r'^import\s+([A-Za-z0-9_.]+)', txt, re.M)
seen, todo = set(), ['Tests.AllTests']
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m)
    p = m.replace('.', '/') + '.lean'
    if os.path.exists(os.path.join(root, p)):
        todo += imports(p)
def in_all(p): return mod_of(p) in seen

rows = []
frows = []
for p in files:
    lines = open(os.path.join(root, p), errors='replace').read().split('\n')
    ns = []
    pending_opts = []
    n_api = len(re.findall(r'synthesizeCombinational|synthesizeHierarchical', '\n'.join(lines)))
    n_cmd = 0
    for i, ln in enumerate(lines, 1):
        m = re.match(r'^(?:noncomputable\s+)?namespace\s+([A-Za-z0-9_.]+)', ln)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+([A-Za-z0-9_.]+)\s*$', ln)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        # `set_option X V in` on the same line or the line before a command
        so = re.findall(r'set_option\s+(\S+)\s+(\S+)\s+in', ln)
        if so and not ln.lstrip().startswith('--'):
            pending_opts = [f'{a}={b}' for a, b in so]
            rest = re.sub(r'^(?:\s*set_option\s+\S+\s+\S+\s+in\s*)+', '', ln)
            if not rest.strip(): continue
            ln = rest
        m = CMD.match(ln)
        if not m:
            if ln.strip() and not ln.lstrip().startswith(('--', '/-', '*')): pending_opts = []
            continue
        cmd, rest = m.group(1), m.group(2)
        n_cmd += 1
        toks = rest.split()
        top = toks[0] if toks else ''
        params = ''
        extra = ''
        if cmd == 'synthesizeParameterizedVerilog':
            pm = re.search(r'\[(.*)\]', rest)
            params = pm.group(1).strip() if pm else ''
        if cmd in ('writeDesign', 'writeVerilogDesign'):
            extra = ' '.join(toks[1:])[:120]
        opts = list(pending_opts)
        if cmd == 'synthesizeParameterizedVerilog': opts.append('symbolicMode=true')
        pending_opts = []
        rows.append(dict(file=p, line=i, command='#' + cmd, ns='.'.join(ns), top=top,
                         qualified=('.'.join(ns) + '.' + top) if ns and not top.startswith('_root_') else top,
                         params=params, options=';'.join(opts), args=extra,
                         in_alltests_closure='Y' if in_all(p) else 'N',
                         area=p.split('/')[0] + '/' + p.split('/')[1] if p.count('/') else p))
    frows.append((p, n_cmd, n_api, 'Y' if in_all(p) else 'N'))

cols = ['file','line','command','ns','top','qualified','params','options','args','in_alltests_closure','area']
with open(os.path.join(out, 'inventory.tsv'), 'w') as f:
    f.write('\t'.join(cols) + '\n')
    for r in rows: f.write('\t'.join(str(r[c]).replace('\t',' ') for c in cols) + '\n')
with open(os.path.join(out, 'files.tsv'), 'w') as f:
    f.write('file\tcommands\tapi_calls\tin_alltests_closure\n')
    for r in frows: f.write('\t'.join(map(str, r)) + '\n')

cnt = collections.Counter(r['command'] for r in rows)
print('files (run.sh set):', len(files), ' in AllTests closure:', sum(1 for r in frows if r[3]=='Y'))
print('command occurrences:', len(rows), dict(cnt))
print('distinct (file,top):', len({(r['file'], r['top']) for r in rows}))
print('distinct qualified top:', len({r['qualified'] for r in rows}))
print('with options:', sum(1 for r in rows if r['options']))
print('AllTests closure modules:', len(seen))
