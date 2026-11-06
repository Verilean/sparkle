#!/usr/bin/env python3
"""S0 summarize: raw capture (capture.sh) + inventory.tsv -> baseline tables.

usage: summarize.py RAW_DIR [DEST_DIR] [--outputs OUTPUT_BASELINE.tsv]
Reads  RAW/inventory.tsv, RAW/status/*.txt, RAW/out/*.txt, RAW/prof/*.log, RAW/env.txt
       (RAW is only read; DEST_DIR defaults to RAW, so a saved raw dir can be re-summarised elsewhere)
       --outputs: output_baseline.tsv from collect_outputs.py.  With it, a #writeDesign/#writeVerilogDesign
       command is OK only if its output files are all present and hashed (a missing one is FAIL);
       without it those commands stay OK-nostdout and the summary says the output baseline is not fixed.
Writes DEST/baseline_files.tsv    one row per captured file (exit, seconds, #modules, #errors)
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

args = sys.argv[1:]
outputs_tsv = None
if '--outputs' in args:
    i = args.index('--outputs'); outputs_tsv = args[i + 1]; del args[i:i + 2]
out = args[0]
dest = args[1] if len(args) > 1 else out
os.makedirs(dest, exist_ok=True)
env = dict(l.strip().split('=', 1) for l in open(f'{out}/env.txt') if '=' in l)
lines = open(f'{out}/inventory.tsv').read().split('\n')
hdr = lines[0].split('\t')
inv = [dict(zip(hdr, l.split('\t'))) for l in lines[1:] if l]
excl = {}
if os.path.exists(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'exclusions.tsv')):
    for n_, l in enumerate(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'exclusions.tsv')).read().split('\n')[1:], 2):
        if not l.strip() or l.lstrip().startswith('#'):
            continue
        cols = l.split('\t')
        if len(cols) != 4:
            sys.exit(f'exclusions.tsv line {n_}: expected 4 tab-separated columns (file, top, cause, fix_target), got {len(cols)}')
        excl[(cols[0], cols[1])] = (cols[2], cols[3])
outputs = collections.defaultdict(list)   # (file, line) -> rows of output_baseline.tsv
if outputs_tsv:
    ol = open(outputs_tsv).read().split('\n'); oh = ol[0].split('\t')
    for l in ol[1:]:
        if l:
            r_ = dict(zip(oh, l.split('\t'))); outputs[(r_['file'], r_['line'])].append(r_)
def tier(area, f):
    # A: shipped IP (IP/, Examples/, Tests/IP/ synthesis of IP); B: compiler feature / regression tests
    return 'A-ip' if area.startswith(('IP/', 'Examples/', 'Tests/IP')) else 'B-feature'
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
                options=r['options'], result='NOT-RUN', route='', module='', sha256='', out_sha256='', method='', file_exit='', area=r['area'], in_alltests=r['in_alltests_closure'], tier=tier(r['area'], f),
            excluded=excl.get((f, r['top']), ('', ''))[0][:60], fix_target=excl.get((f, r['top']), ('', ''))[1][:60]))
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
        if res == 'OK-nostdout' and outputs_tsv:
            orows = outputs.get((f, r['line']), [])
            if not orows or any(o['status'] != 'OK' for o in orows): res = 'FAIL'
        cmds.append(dict(file=f, line=r['line'], command=r['command'], top=r['top'], params=r['params'],
            options=r['options'], result=res, route=route, module=pool[hit][0] if hit is not None else '',
            sha256=pool[hit][1] if hit is not None else '',
            out_sha256=';'.join(f"{o['kind']}={o['sha256']}" for o in outputs.get((f, r['line']), [])), method=method if hit is not None else '', file_exit=rc,
            area=r['area'], in_alltests=r['in_alltests_closure'], tier=tier(r['area'], f),
            excluded=excl.get((f, r['top']), ('', ''))[0][:60], fix_target=excl.get((f, r['top']), ('', ''))[1][:60]))

def dump(name, rows):
    if not rows: open(f'{dest}/{name}', 'w').write(''); return
    cols = list(rows[0].keys())
    with open(f'{dest}/{name}', 'w') as fh:
        fh.write('\t'.join(cols) + '\n')
        for r in rows: fh.write('\t'.join(str(r[c]).replace('\t', ' ').replace('\n', ' ') for c in cols) + '\n')
dump('baseline_files.tsv', files); dump('baseline_modules.tsv', mods); dump('baseline_commands.tsv', cmds)

for r in cmds:
    if r['excluded'] and r['result'] in ('FAIL', 'UNATTRIBUTED', 'NOT-RUN'): r['result'] = 'KNOWN-' + r['result']
unexplained = [r for r in cmds if r['result'] in ('FAIL', 'UNATTRIBUTED', 'NOT-RUN') and not r['excluded']]
nostdout = [r for r in cmds if r['result'] == 'OK-nostdout']
c = collections.Counter(r['result'] for r in cmds)
ca = collections.Counter(r['result'] for r in cmds if r['in_alltests'] == 'Y')
with open(f'{dest}/summary.txt', 'w') as s:
    s.write(f"sha={env.get('sha')} toolchain={env.get('toolchain')}\n")
    s.write(f"files captured {len(files)} (exit0 {sum(1 for x in files if x['exit']==0)}), inventory files {len(byfile)}\n")
    s.write(f"commands {len(cmds)}: {dict(c)}\n")
    s.write(f"commands in AllTests closure: {dict(ca)}\n")
    s.write(f"routes (OK commands): {dict(collections.Counter(r['route'] or 'none' for r in cmds if r['result']=='OK'))}\n")
    s.write(f"modules {len(mods)}\n")
    for t in ('A-ip', 'B-feature'):
        s.write(f"tier {t}: {dict(collections.Counter(r['result'] for r in cmds if r['tier']==t))}\n")
    s.write(f"output baseline: {'fixed from ' + os.path.basename(outputs_tsv) if outputs_tsv else 'NOT FIXED'}; commands without stdout module: {len(nostdout)}\n")
    s.write(f"unexplained failures / incomplete (FAIL, UNATTRIBUTED, NOT-RUN; must be 0 before fixing the baseline): {len(unexplained)}\n")
    for r in unexplained: s.write(f"  {r['file']}:{r['line']} {r['top']} {r['result']} exit={r['file_exit']}\n")
print(open(f'{dest}/summary.txt').read())
