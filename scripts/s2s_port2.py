#!/usr/bin/env python3
"""Selective port: python3 scripts/s2s_port2.py SRC.lean OUT.lean EXTRA_IMPORT... 
Keeps only declarations that mention the context-predicate bundles (or an already-ported name, or a
kept declaration); renames them with suffix X. Everything else is taken from the (imported) original."""
import re,sys,os
sys.path.insert(0,os.path.dirname(__file__))
import s2s_port as P
TRIG=re.compile(r'RefLawsAOps\b|RefLawsATele\b|AdmCtx\b|\bLaws\b|\bStart\b|\bL\.O\b|\bL\.T\b|\bJQC\b|RealChildA\b|CacheInvA\b|\bJQHX?\b')
KW=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|macro|syntax|macro_rules|opaque|example)\b")
STRUCT=re.compile(r'^(section|end|variable|open|namespace|universe|attribute|local|noncomputable section|set_option\s+\S+\s+\S+\s*$|import|-- )')
def main():
    src,out=sys.argv[1],sys.argv[2]; extra=sys.argv[3:]
    lines=open(src).read().split('\n')
    lines=[l for l in lines if not l.startswith('import ')]
    ren=P.names()
    ren.update({'Laws':'LawsX','Start':'StartX'})
    ren.update({k:v for k,v in [l.split('=') for l in os.environ.get('S2S_REN','').split(',') if '=' in l]})
    starts=[i for i,l in enumerate(lines) if KW.match(l)]
    bounds=[]
    for k,i in enumerate(starts):
        j=i
        floor=starts[k-1]+1 if k>0 else 0
        while j>floor:
            pl=lines[j-1]
            if re.match(r'^set_option .* in\s*$',pl) or pl.startswith('@['):
                j-=1; continue
            if pl.rstrip().endswith('-/'):
                m=j-1
                while m>floor and not lines[m].lstrip().startswith('/-'): m-=1
                if lines[m].lstrip().startswith('/-'): j=m; continue
            break
        bounds.append([j,starts[k+1] if k+1<len(starts) else len(lines)])
    # fix: next chunk's start trimmed
    for k in range(len(bounds)-1): bounds[k][1]=bounds[k+1][0]
    head=lines[:bounds[0][0]] if bounds else lines
    texts=['\n'.join(lines[a:b]) for a,b in bounds]
    names=[]
    for t in texts:
        m=P.DECL.search(t)
        mm=re.search(r'^(?:local\s+)?macro\s+"(\w+)\s*"',t,re.M)
        names.append(m.group(1) if m else (mm.group(1) if mm else None))
    def nocom(t):
        t=re.sub(r'/-.*?-/','',t,flags=re.S)
        return re.sub(r'--[^\n]*','',t)
    dirty=[bool(TRIG.search(nocom(t))) for t in texts]
    cur=dict(ren)
    ch=True
    while ch:
        ch=False
        for k,t in enumerate(texts):
            if dirty[k]:
                if names[k] and names[k] not in cur: cur[names[k]]=names[k]+'X'; ch=True
                continue
            for n in cur:
                if re.search(r'(?<![\w\'])'+re.escape(n)+r'(?![\w\'X])',nocom(t)):
                    dirty[k]=True; ch=True; break
    res=[]
    def struct_lines(t):
        out=[];keep=False
        for l in t.split('\n'):
            if re.match(r'^(section|end|variable|open|namespace|universe)\b',l): out.append(l); keep=True
            elif keep and re.match(r'^\s+\S',l): out.append(l)
            else: keep=False
        return '\n'.join(out)
    for k,t in enumerate(texts):
        if not dirty[k]:
            sl=struct_lines(t)
            if sl: res.append(sl)
            continue
        t=t.replace('RefLawsATele O.quiet mref cref','RefLawsATeleX O.quiet O.adm mref cref')
        t=re.sub(r'RefLawsATele (\w+)\.quiet mref cref',r'RefLawsATeleX \1.quiet \1.adm mref cref',t)
        t=re.sub(r'AdmCtx ([\w\.]+?)\.quiet',r'\1.adm',t)
        for n in sorted(cur,key=lambda x:-len(x)):
            t=re.sub(r'(?<![\w\'])'+re.escape(n)+r'(?![\w\'X])',cur[n],t)
        res.append(t)
    def rn(t):
        for n in sorted(cur,key=lambda x:-len(x)):
            t=re.sub(r'(?<![\w\'])'+re.escape(n)+r'(?![\w\'X])',cur[n],t)
        return t
    head=[rn(l) if re.match(r'^open .*\(',l) else l for l in head]
    hdr='\n'.join('import '+m for m in extra)+'\n'
    note='-- FG circuit pilot S2s4: SELECTIVE port of %s onto the context-predicate bundles (only the declarations that mention RefLawsAOps/AdmCtx/Laws/... or an already-ported name; the rest is taken from the imported original); rename-only script scripts/s2s_port2.py (suffix X, `AdmCtx O.quiet` -> `O.adm`). No sorry/axiom/native_decide/TRUSTED/law.\n'%os.path.basename(src)
    open(out,'w').write(hdr+note+'\n'.join(head)+'\n'+'\n\n'.join(res)+'\n')
    print(len(res),'of',len(texts),'declarations kept;', [names[k] for k in range(len(texts)) if dirty[k]])
main()
