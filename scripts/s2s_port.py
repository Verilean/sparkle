import re,sys,glob,os
root='Tools/'
DECL=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|macro|syntax|macro_rules|opaque|axiom)\s+([A-Za-z_][\w\.\']*)',re.M)
def decls(path):
    s=open(path).read()
    r=set(m.group(1) for m in DECL.finditer(s))
    r|=set(m.group(1) for m in re.finditer(r'^(?:local\s+)?macro\s+"(\w+)\s*"',s,re.M))
    return r
def src_of(p):
    b=os.path.basename(p)[:-5]
    if b.startswith('ShippingFGCircuitS2sAdm'):
        r=b[len('ShippingFGCircuitS2sAdm'):]
        if r.startswith('Child') or r=='KWalk': 
            return root+('ShippingFGCircuit'+r if os.path.exists(root+'ShippingFGCircuit'+r+'.lean') else 'Shipping'+r)+'.lean'
        return root+'ShippingFGCircuit'+r+'.lean'
def names():
    ren={}
    for p in glob.glob(root+'ShippingFGCircuitS2sAdm*.lean'):
        if 'Hist2' in p: continue
        src=src_of(p)
        if not src or not os.path.exists(src): continue
        d=decls(p); o=decls(src)
        for n in o:
            if n+'X' in d: ren[n]=n+'X'
    return ren
def port(src,out,extra_imports,ren):
    s=open(src).read()
    own=decls(src)
    for n in own: ren.setdefault(n,n+'X')
    body=s
    # strip imports
    lines=body.split('\n')
    heads=[l for l in lines if l.startswith('import ')]
    rest=[l for l in lines if not l.startswith('import ')]
    body='\n'.join(rest)
    body=body.replace('RefLawsATele O.quiet mref cref','RefLawsATeleX O.quiet O.adm mref cref')
    body=re.sub(r'RefLawsATele (\w+)\.quiet mref cref',r'RefLawsATeleX \1.quiet \1.adm mref cref',body)
    body=re.sub(r'AdmCtx ([\w\.]+?)\.quiet',r'\1.adm',body)
    for n in sorted(ren,key=lambda x:-len(x)):
        body=re.sub(r'(?<![\w\'])'+re.escape(n)+r'(?![\w\'X])',ren[n],body)
        # qualified use  Foo.n
    return heads,body
if __name__=='__main__':
    src,out=sys.argv[1],sys.argv[2]
    ren=names()
    heads,body=port(src,out,[],ren)
    open(out,'w').write('\n'.join(['import '+h[7:] for h in heads])+'\n'+body)
    print(len(ren))
