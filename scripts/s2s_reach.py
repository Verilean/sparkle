#!/usr/bin/env python3
"""Textual reachability: which declarations (of the import closure of MODULE) does DECL transitively mention?"""
import re,os,sys
sys.path.insert(0,os.path.dirname(__file__))
KW=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([A-Za-z_][\w\.\']*)")
def closure(m,seen):
    if m in seen: return
    p=m.replace('.','/')+'.lean'
    if not os.path.exists(p): seen[m]=None; return
    s=open(p).read(); seen[m]=s
    for i in re.findall(r'^import (\S+)',s,re.M): closure(i,seen)
def nocom(t):
    t=re.sub(r'/-.*?-/','',t,flags=re.S); return re.sub(r'--[^\n]*','',t)
seen={}; closure(sys.argv[1],seen)
idx={}  # short name -> list of (module,text)
for m,s in seen.items():
    if not s or m.startswith('Sparkle') or 'S2sAdm' in m or not m.startswith('Tools.Shipping'): continue
    L=s.split('\n'); st=[i for i,l in enumerate(L) if KW.match(l)]
    for k,i in enumerate(st):
        e=st[k+1] if k+1<len(st) else len(L)
        n=KW.match(L[i]).group(1); idx.setdefault(n.split('.')[-1],[]).append((m,n,nocom('\n'.join(L[i:e]))))
start=sys.argv[2]
todo=[start]; done={}
while todo:
    n=todo.pop(); 
    if n in done or n not in idx: continue
    done[n]=idx[n]
    for (_,_,t) in idx[n]:
        for tok in set(re.findall(r"[A-Za-z_][\w\.']*",t)):
            for part in {tok,tok.split('.')[-1]}:
                if part in idx and part not in done: todo.append(part)
by={}
for n,l in done.items():
    for (m,full,t) in l: by.setdefault(m,[]).append(n)
for m,l in sorted(by.items()): print(m,len(l)); 
if len(sys.argv)>3:
    for m,l in sorted(by.items()): print(m,l)
