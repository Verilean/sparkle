#!/usr/bin/env python3
# SRM4 porting script: copies hnomem-bearing A-form theorems into memory-aware (hnomem-free, KidTA) versions.
import re,sys,json
SRM3_DONE={ # original name -> (new name); the SRM3 files already provide these (hfne after hins)
 'core_kids_facts_ranA':'core_kids_facts_ranAM','core_outsIn_ranA':'core_outsIn_ranAM',
 'core_calls_portsG_ranA':'core_calls_portsG_ranAM','core_inPorts_ranA':'core_inPorts_ranAM','deepChild_ifaceP':'deepChild_ifaceP_M'}
NS={}
def read(p): return open(p).read()
TOP=re.compile(r"^(set_option|/--|/-!|theorem|lemma|def|abbrev|instance|structure|end|namespace|section|open|variable|#print|@\[|private|noncomputable|omit|include|attribute|--)")
def find_chunk(lines,name):
    pat=re.compile(r"^(theorem|lemma) "+re.escape(name)+r"(\s|$)")
    idx=[i for i,l in enumerate(lines) if pat.match(l)]
    assert len(idx)==1,(name,idx)
    i=idx[0]; s=i
    j=i-1
    if j>=0 and lines[j].rstrip().endswith('-/'):
        while not lines[j].startswith('/--'): j-=1
        s=j; j-=1
    if j>=0 and lines[j].startswith('set_option'): s=j
    e=i+1
    while e<len(lines) and not TOP.match(lines[e]): e+=1
    return s,e
def sig_of(text):
    k=text.find(':= by')
    k2=text.find(':=\n')
    ks=[x for x in (k,k2) if x>=0]
    return text[:min(ks)] if ks else text
HNOMEM_BINDER=re.compile(r"\n[ ]*\(hnomem :[^\n]*(?:\n[ ]+\(Sparkle\.Compiler\.MachMemory\.memChild\? x\.1\)\.isNone = true\))?[^\n]*(?=\n)")
def transform(text,rename,lacks_hfne):
    # drop heartbeat raises
    text=re.sub(r"^set_option maxHeartbeats \d+ in\n","",text,flags=re.M)
    own_has_hfne='hfne' in sig_of(text)
    # remove hnomem binder (possibly two lines)
    text=re.sub(r"\n[ ]*\(hnomem : ∀ x ∈ d\.shape\.instTagged, x\.2\.child\?\.isNone = true ∧\s*\(Sparkle\.Compiler\.MachMemory\.memChild\? x\.1\)\.isNone = true\)","",text)
    # add hfne binder
    if not own_has_hfne:
        text=re.sub(r"(\n[ ]*\(hins : d\.shape\.insts ≠ \[\]\))",r"\1\n    (hfne : d.shape.instFields ≠ [])",text,count=1)
    # renames
    for old,new in rename.items():
        nsq=NS.get(old)
        text=re.sub(r"(?<![\w'.])"+re.escape(old)+r"(?![\w'])",new,text)
        if nsq:
            text=re.sub(r"(?<![\w'.])(?:[A-Za-z0-9_]+\.)+"+re.escape(old)+r"(?![\w'])",nsq+'.'+new,text)
        else:
            text=re.sub(r"(?<=[A-Za-z0-9_]\.)"+re.escape(old)+r"(?![\w'])",new,text)
    # hfne at call sites whose callee originally lacked it
    for old in lacks_hfne:
        new=rename[old]
        def fix(m):
            return m.group(0)
        out=[];pos=0
        for m in re.finditer(r"(?<![\w'])"+re.escape(new)+r"(?![\w'])",text):
            if m.start()<pos: continue
            seg=text[m.end():m.end()+700]
            mm=re.search(r"\bhins\b(?!\s*:)",seg)
            if mm and 'hfne' not in seg[:mm.end()+8]:
                ins=m.end()+mm.end()
                out.append((ins,' hfne'))
        for ins,s in sorted(out,reverse=True):
            text=text[:ins]+s+text[ins:]
    # call-arg hnomem
    text=re.sub(r"\s+hnomem\b","",text)
    # the refuted memory case becomes the kid of the origin
    def kidrep(m):
        hy='hk' if m.group(1)=="hor'" else 'hy'
        return m.group(2)+"have hre := kidTA_ofO "+m.group(3)+" hMC "+hy+" "+m.group(1)
    text=re.sub(r"( *)rcases (hor'?) with hmem \| hre\n *· rw \[Tools\.ShippingChildInv\.nomem_tag (\w+'?)\] at hmem\n *cases hmem",
        lambda m:m.group(1)+"have hre := kidTA_ofO "+m.group(3)+" hMC "+('hk' if m.group(2)=="hor'" else 'hy')+" "+m.group(2),text)
    def hmc(m):
        ind=m.group(1)
        return (m.group(0)+"\n"+ind+"have hMC : MemChildren d.shape children := by\n"+ind+"  rcases hcc with ⟨hf0, -⟩ | ⟨-, -, h⟩\n"+ind+"  · exact absurd hf0 hfne\n"+ind+"  · exact h")
    if "rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩" in text:
        text=text.replace("rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, -⟩","rcases hcc with ⟨hf0, -⟩ | ⟨-, hG, hMC⟩")
    else:
        text=re.sub(r"( *)obtain ⟨hlenC, (?:hallC|hall)⟩ := hreal",hmc,text)
    text=re.sub(r"KidFactsA O \(d\.shape\.insts\[([^\]]+)\]\)\.1",
                lambda m:"KidFactsTA O (Tools.ShippingInstTagged.originAt d.shape "+m.group(1)+") (d.shape.insts["+m.group(1)+"]).1",text)
    # KidTA for per-kid RealChildA
    text=re.sub(r"(Tools\.ShippingChildCacheA\.)?RealChildA O \(d\.shape\.insts\[([^\]]+)\]\)\.1",
                lambda m:"Tools.ShippingCallsMemA.KidTA O (Tools.ShippingInstTagged.originAt d.shape "+m.group(2)+") (d.shape.insts["+m.group(2)+"]).1",text)
    return text
def run(spec):
    # spec: {"out":path,"module":"Tools.X","namespace":"Tools.Y","extra_imports":[...],"extra_opens":[...],"sources":[{"file":..,"names":[..]}], "rename":{..}, "lacks":[..]}
    rename={}; lacks=[]
    NS.clear()
    for a in spec['all']:
        if a.get('ns'): NS[a['name']]=a['ns']
    for a in spec['all']:
        rename[a['name']]=a.get('new',a['name']+'M')
        if a.get('lacks'): lacks.append(a['name'])
        elif 'file' in a and not a.get('done'):
            lines=read(a['file']).split('\n'); s_,e_=find_chunk(lines,a['name'])
            if 'hfne' not in sig_of('\n'.join(lines[s_:e_])): lacks.append(a['name'])
    chunks=[]; header=None
    for src in spec['sources']:
        lines=read(src['file']).split('\n')
        if True:
            ns=[i for i,l in enumerate(lines) if l.startswith('namespace ')][0]
            first=min(find_chunk(lines,n)[0] for n in src['names'])
            hl=[l for l in lines[ns+1:first] if l.startswith('open ') or l.startswith('variable') or l.startswith('  {') or l.startswith('  (')]
            if header is None: header=[]
            for l in hl:
                if l.startswith('open ') and l in header: continue
                if l.startswith('open Lean Meta'): continue
                if (l.startswith('variable') or l.startswith('  {')) and any(x.startswith('variable') for x in header): continue
                header.append(l)
        for n in src['names']:
            s,e=find_chunk(lines,n)
            t='\n'.join(lines[s:e]).rstrip()+'\n'
            chunks.append(transform(t,rename,lacks))
    out=[]
    for imp in spec['imports']: out.append('import '+imp)
    out.append(spec['header'])
    out.append('namespace '+spec['namespace'])
    out.append('open Lean Meta')
    out.extend(header)
    for o in spec['extra_opens']: out.append(o)
    out.append('')
    if spec.get('prelude'): out.append(spec['prelude'])
    body='\n'.join(chunks)
    for old,new in spec.get('patches',[]):
        assert old in body,old
        body=body.replace(old,new)
    out.append(body)
    out.append('end '+spec['namespace'])
    open(spec['out'],'w').write('\n'.join(out)+'\n')
if __name__=='__main__':
    run(json.load(open(sys.argv[1])))
