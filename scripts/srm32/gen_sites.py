#!/usr/bin/env python3
# SRM32: list every anonymous-constructor pattern (obtain/rcases/intro/fun/match) with >= 15 top-level components
# in Tools/ and Tests/, with component count and last component. A MachineWired destructuring has 19 (now 20) components.
import re,sys,glob
def split_top(s):
    d=0;cur='';out=[]
    for ch in s:
        if ch in '⟨([{': d+=1
        if ch in '⟩)]}': d-=1
        if ch==',' and d==0: out.append(cur.strip());cur=''
        else: cur+=ch
    out.append(cur.strip());return out
for f in sorted(glob.glob('Tools/*.lean')+glob.glob('Tests/**/*.lean',recursive=True)):
    src=open(f,encoding='utf-8').read()
    # join into one string with line map
    for m in re.finditer(r'⟨',src):
        i=m.start();d=0;j=i
        while j<len(src):
            if src[j]=='⟨': d+=1
            elif src[j]=='⟩':
                d-=1
                if d==0: break
            j+=1
        body=src[i+1:j]
        parts=split_top(body)
        if len(parts)>=15 and '⟨' not in parts[-1][:0]:
            line=src.count('\n',0,i)+1
            ctx=src[j+1:j+60].split('\n')[0]
            print(f"{f}:{line}: n={len(parts)} last='{parts[-1][:30]}' after='{ctx.strip()[:40]}'")
