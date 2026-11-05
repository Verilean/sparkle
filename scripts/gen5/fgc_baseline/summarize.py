#!/usr/bin/env python3
"""S0 summarize: raw capture (capture.sh) + inventory.tsv -> baseline tables.

usage: summarize.py OUT_DIR
Reads  OUT/inventory.tsv, OUT/status/*.txt, OUT/out/*.txt, OUT/prof/*.log, OUT/env.txt
Writes OUT/baseline_files.tsv    one row per captured file (exit, seconds, #modules, #errors)
       OUT/baseline_modules.tsv  one row per generated SV module (hash + interface facts)
       OUT/baseline_commands.tsv one row per inventory command (success/fail, route, module, hash)
       OUT/summary.txt           counts by population
The module hash is sha256 of the module text exactly as printed (IR->SV text of the
current printer); it is the "generated artifact" identity compared with a new path.
Attribution of a module to a command: module name == sanitized last component of the
top (method=name), else the k-th unattributed module of the file in command order
(method=order); unattributed commands in a file with an error at their line are FAIL.
"""
import collections, hashlib, os, re, sys

out = sys.argv[1]
env = dict(l.strip().split('=', 1) for l in open(f'{out}/env.txt') if '=' in l)
lines = open(f'{out}/inventory.tsv').read().split('\n')
hdr = lines[0].split('\t')
inv = [dict(zip(hdr, l.split('\t'))) for l in lines[1:] if l]
key = lambda f: f.replace('/', '_')

MOD = re.compile(r'^module\s+(\S+?)\s*(?:#\(.*?\)\s*)?\(', re.M | re.S)
def split_modules(txt):
    res = []
    for m in re.finditer(r'(?ms)^module\s+([A-Za-z0-9_$]+).*?^endmodule\s*$', txt):
        res.append((m.group(1), m.group(0)))
    return res

def facts(name, text):
    ports = []
    hm = re.search(r'(?s)^module\s+\S+.*?\);', text, re.M)
    head = hm.group(0) if hm else ''
    params = re.findall(r'parameter\s+integer\s+(\S+)\s*=\s*(\S+?)[,\s)]', head)
    for d, ty, nm in re.findall(r'\b(input|output)\s+((?:signed\s+)?(?:logic\s+|wire\s+)?(?:\[[^\]]+\]\s*)?)(\w+)', head):
        w = re.search(r'\[([^\]]+)\]', ty)
        ports.append(f"{d[0]}:{nm}:{w.group(1).replace(' ','') if w else '1'}{':s' if 'signed' in ty else ''}")
    regs = []
    for m in re.finditer(r'always_ff\s+@\(posedge\s+(\w+)(?:\s+or\s+posedge\s+(\w+))?\)\s*begin\s*\n\s*if\s*\((\w+)\)\s*\n\s*(\w+)\s*<=\s*([^;]+);', text):
        clk, arst, rst, reg, init = m.groups()
        regs.append((clk, 'async' if arst else 'sync', rst, reg, init.strip()))
    mems = []
    for m in re.finditer(r'logic\s+\[(\d+):0\]\s+(\w+)\s+\[0:(\d+)\];', text):
        w, nm, hi = m.groups()
        comb = bool(re.search(r'assign\s+\w+\s*=\s*' + re.escape(nm) + r'\[', text))
        wr = len(re.findall(re.escape(nm) + r'\[[^\]]*\]\s*<=', text))
        mems.append(f"{nm}:w{int(w)+1}xd{int(hi)+1}:{'comb-read' if comb else 'sync-read'}:wports{wr}")
    clocks = sorted({r[0] for r in regs} | set(re.findall(r'always_ff\s+@\(posedge\s+(\w+)', text)))
    return dict(
        params=','.join(f'{a}={b}' for a, b in params),
        ports=';'.join(ports),
        n_in=sum(p.startswith('i') for p in ports), n_out=sum(p.startswith('o') for p in ports),
        clocks=','.join(clocks),
        resets=','.join(sorted({f'{r[2]}({r[1]},active-high)' for r in regs})),
        n_regs=len(regs),
        reg_inits=';'.join(f'{r[3]}={r[4]}' for r in regs),
        n_signed=text.count('$signed'),
        mems=';'.join(mems),
        n_inst=len(re.findall(r'^\s+\w+\s+\w+\s+\(\.', text, re.M)),
    )

files, mods, cmds = [], [], []
status = {}
for fn in os.listdir(f'{out}/status'):
    f, rc, secs = open(f'{out}/status/{fn}').read().split()
    status[f] = (int(rc), int(secs))

byfile = collections.defaultdict(list)
for r in inv: byfile[r['file']].append(r)

for f in sorted(byfile):
    if f not in status:
        for r in byfile[f]:
            cmds.append(dict(file=f, line=r['line'], command=r['command'], top=r['top'], params=r['params'],
                options=r['options'], result='NOT-RUN', route='', module='', sha256='', method='', file_exit='', area=r['area'], in_alltests=r['in_alltests_closure']))
        continue
    rc, secs = status[f]
    txt = open(f'{out}/out/{key(f)}.txt', errors='replace').read()
    prof = open(f'{out}/prof/{key(f)}.log', errors='replace').read()
    errs = re.findall(r'^[^\s:]+:(\d+):\d+: error', txt, re.M)
    ms = split_modules(txt)
    files.append(dict(file=f, exit=rc, seconds=secs, modules=len(ms), errors=len(errs), commands=len(byfile[f])))
    routes = collections.defaultdict(list)
    for m in re.finditer(r'\[profile\] synthesizeCombinational (\S+) (.*)', prof):
        d, w = m.groups()
        r = ('certified' if w == 'certified front end' else 'mixed' if w == 'mixed certified front end'
             else 'machine' if w == 'machine certified front end' else 'memo' if w == 'MEMO HIT'
             else 'legacy' if w.startswith('starting') else None)
        if r: routes[d.split('.')[-1]].append(r)
    for name, text in ms:
        h = hashlib.sha256(text.encode()).hexdigest()
        mods.append(dict(file=f, module=name, sha256=h, bytes=len(text), **facts(name, text)))
    pool = [(n, hashlib.sha256(t.encode()).hexdigest()) for n, t in ms]
    used = set()
    err_lines = {int(x) for x in errs}
    for r in byfile[f]:
        short = r['top'].split('.')[-1]
        hit = next((i for i, (n, _) in enumerate(pool) if i not in used and (n == short or n.endswith(short) or short in n)), None)
        method = 'name'
        if hit is None and int(r['line']) not in err_lines:
            hit = next((i for i in range(len(pool)) if i not in used), None); method = 'order'
        rt = routes.get(short, [])
        route = '+'.join(sorted(set(x for x in rt if x != 'memo'))) or ('memo' if rt else '')
        if int(r['line']) in err_lines: res = 'FAIL'
        elif hit is not None: res = 'OK'
        elif r['command'] in ('#writeDesign', '#writeVerilogDesign'): res = 'OK-nostdout' if rc == 0 else 'FAIL'
        else: res = 'FAIL' if rc != 0 else 'UNATTRIBUTED'
        if hit is not None: used.add(hit)
        cmds.append(dict(file=f, line=r['line'], command=r['command'], top=r['top'], params=r['params'],
            options=r['options'], result=res, route=route, module=pool[hit][0] if hit is not None else '',
            sha256=pool[hit][1] if hit is not None else '', method=method if hit is not None else '', file_exit=rc,
            area=r['area'], in_alltests=r['in_alltests_closure']))

def dump(name, rows):
    if not rows: open(f'{out}/{name}', 'w').write(''); return
    cols = list(rows[0].keys())
    with open(f'{out}/{name}', 'w') as fh:
        fh.write('\t'.join(cols) + '\n')
        for r in rows: fh.write('\t'.join(str(r[c]).replace('\t', ' ').replace('\n', ' ') for c in cols) + '\n')
dump('baseline_files.tsv', files); dump('baseline_modules.tsv', mods); dump('baseline_commands.tsv', cmds)

c = collections.Counter(r['result'] for r in cmds)
ca = collections.Counter(r['result'] for r in cmds if r['in_alltests'] == 'Y')
with open(f'{out}/summary.txt', 'w') as s:
    s.write(f"sha={env.get('sha')} toolchain={env.get('toolchain')}\n")
    s.write(f"files captured {len(files)} (exit0 {sum(1 for x in files if x['exit']==0)}), inventory files {len(byfile)}\n")
    s.write(f"commands {len(cmds)}: {dict(c)}\n")
    s.write(f"commands in AllTests closure: {dict(ca)}\n")
    s.write(f"routes (OK commands): {dict(collections.Counter(r['route'] or 'none' for r in cmds if r['result']=='OK'))}\n")
    s.write(f"modules {len(mods)}\n")
print(open(f'{out}/summary.txt').read())
