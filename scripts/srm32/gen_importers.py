#!/usr/bin/env python3
# transitive importers of a module over Tools/ Tests/ (+ any other .lean under repo dirs listed in lakefile roots by import lines)
import re,sys,glob,collections
root=sys.argv[1]
imp=collections.defaultdict(set)
for f in glob.glob('**/*.lean',recursive=True):
    if f.startswith('.lake') or f.startswith('.cluster'): continue
    mod=f[:-5].replace('/','.')
    for l in open(f,encoding='utf-8'):
        m=re.match(r'import\s+(\S+)',l)
        if m: imp[m.group(1)].add(mod)
seen=set();st=[root]
while st:
    x=st.pop()
    for y in imp[x]:
        if y not in seen: seen.add(y);st.append(y)
for s in sorted(seen): print(s)
