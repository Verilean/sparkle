#!/usr/bin/env python3
# Generates Tests/Compiler/Srm22ExpStmt.lean: EXPECTED full statements of the SRM22 definitions/theorems, derived ONLY from
#   SOURCE A: scripts/srm22/EXPECTED.txt (fixed and committed BEFORE any proof file): the five gap defs, the six generic direction lemmas, the two counterexamples;
#   SOURCE B: the SRM20 `topshareM_svBoundsH_underComposedG` and SRM21 `topshareQ_svBoundsH_underComposedG'` SOURCE statements with the committed deletion/insertion list of scripts/srm22/gen_pairs_test.py.
# Never reads the SRM22 theorems.  Also emits MUTATIONS that the audit must reject:
#   Exp_mut_hin_dir (direction reversed: hin_of_hinsFit's binders, hinsFit_of_hin's conclusion), Exp_mut_cor_noHpost (hpost dropped), Exp_mut_cor_noHfit (hfit residual deleted),
#   Exp_mut_cor_noHIW (hIW deleted), Exp_mut_hstX_noHreg (the gap premise hreg dropped), Exp_mut_cor_withHin (the SRM20 statement itself, hin kept).
import re,sys,subprocess
def groups(sig):
    out=[];i=0;n=len(sig)
    while i<n:
        c=sig[i]
        if c in '({[':
            d=0;j=i
            while True:
                if sig[j] in '({[': d+=1
                elif sig[j] in ')}]': d-=1
                if d==0: break
                j+=1
            out.append(sig[i:j+1]);i=j+1
        elif c==':' and sig[i+1]!='=': return out,sig[i+1:].strip()
        else: i+=1
    raise Exception('no colon')
def bname(g):
    m=re.match(r"[({\[]\s*([^\s:]+)",g); return m.group(1) if m else None
exp=open('scripts/srm22/EXPECTED.txt').read().split('\n')
blocks={}
i=0
while i<len(exp):
    m=re.match(r'^(?:\[[^\]]*\]\s+)?(def|theorem) (\S+)(.*)$',exp[i])
    if m and not exp[i].startswith('==='):
        kind,name,rest=m.groups()
        txt=rest
        j=i+1
        while j<len(exp) and exp[j][:1] in (' ','\t'):
            txt+='\n'+exp[j]; j+=1
        blocks[name]=(kind,txt)
        i=j
    else: i+=1
GAPS=['InputsAreWires','ShippedRegsFromSource','SourceRegsKept','ShippedRegWidthLe','ShippedRegsAreSlots']
def expand(s):
    s=re.sub(r'(?<![A-Za-z_.])cO(?![A-Za-z_])','Sparkle.IR.OptCheck.checkedOptimize',s)
    s=re.sub(r'(?<![A-Za-z_.])san(?![A-Za-z_])','Sparkle.Backend.Verilog.sanitizeName',s)
    s=re.sub(r'(?<![A-Za-z_.])Reg (?=[a-z])','Sparkle.IR.AST.Stmt.register ',s)
    s=re.sub(r'(?<![A-Za-z_.])dropZeroWidthModule','Sparkle.IR.ZeroWidth.dropZeroWidthModule',s)
    s=re.sub(r'(?<![A-Za-z_.])hierGate','Sparkle.IR.RefineCheck.hierGate',s)
    s=re.sub(r'(?<![A-Za-z_.])Module\b','Sparkle.IR.AST.Module',s)
    s=re.sub(r'(?<![A-Za-z_.])Expr\b','Sparkle.IR.AST.Expr',s)
    for g in GAPS: s=re.sub(r'(?<![A-Za-z_.])'+g+r'\b','Exp_'+g,s)
    return s
def split_thm(name):
    kind,txt=blocks[name]; assert kind=='theorem'
    gs,concl=groups(txt)
    return [expand(g) for g in gs],expand(concl)
def build(name,gs,concl):
    if gs: return f"def {name} : Prop :=\n  ∀ {' '.join(gs)},\n    {concl}\n"
    return f"def {name} : Prop :=\n  {concl}\n"
defs=[]
for g in GAPS:
    kind,txt=blocks[g]; assert kind=='def'
    defs.append('def Exp_'+g+expand(txt).replace('Exp_'+g,'Exp_'+g)+'\n')
out_thms=[]
T=['hin_of_hinsFit','hinsFit_of_hin','hstX_of_hst3','hstR_of_hst1_hst2','regsFit_of_hstR_hst1','regsAtInit_of_hinit','hin_not_hinsFit','hstX_hstR_not_hst3']
S={}
for t in T:
    S[t]=split_thm(t); out_thms.append(build('Exp_'+t,*S[t]))
# mutations from SOURCE A
g1,c1=S['hin_of_hinsFit']; g2,c2=S['hinsFit_of_hin']
out_thms.append(build('Exp_mut_hin_dir',g1,c2))
gx,cx=S['hstX_of_hst3']
out_thms.append(build('Exp_mut_hstX_noHreg',[g for g in gx if bname(g)!='hreg'],cx))
# corollaries from SOURCE B
def cor(which):
    t=subprocess.check_output(['python3','scripts/srm22/gen_pairs_test.py',which],text=True)
    t=re.sub(r'--[^\n]*','',t)
    m=re.match(r"theorem (\S+)(.*)$",t.strip(),re.S)
    gs,concl=groups(m.group(2))
    return gs,concl
gM,cM=cor('M'); gQ,cQ=cor('Q')
out_thms.append(build('Exp_corM',gM,cM)); out_thms.append(build('Exp_corQ',gQ,cQ))
HFIT=re.compile(r"\(∀ mn iname conns gc gcwe, Stmt\.inst mn iname conns ∈ \(checkedOptimize b\)\.body →\s*childMap D\.modules mn = some \(gc, gcwe\) → FitTree \(childMap D\.modules\) \d gc \(kids iname\)\) →")
assert HFIT.search(cM) and HFIT.search(cQ)
out_thms.append(build('Exp_mut_cor_noHfit',gM,HFIT.sub('',cM)))
out_thms.append(build('Exp_mut_cor_noHpost',[g for g in gM if bname(g)!='hpost'],cM))
out_thms.append(build('Exp_mut_cor_noHIW',[g for g in gM if bname(g)!='hIW'],cM))
# the SRM20 statement itself (hin kept): source text of SRM20 with only the rename
s20=open('Tests/Compiler/Srm20BridgeTest.lean').read()
i0=s20.index('theorem topshareM_svBoundsH_underComposedG\n'); j0=s20.index(':= by',i0)
g20,c20=groups(re.sub(r'--[^\n]*','',s20[i0+len('theorem topshareM_svBoundsH_underComposedG'):j0]))
out_thms.append(build('Exp_mut_cor_withHin',g20,c20))
hdr=[l for l in open('Tests/Compiler/Srm21LiftTest.lean').read().split('\n') if l.startswith('open ')]
hdr+=[l for l in open('Tests/Compiler/Srm20BridgeTest.lean').read().split('\n') if l.startswith('open ') and l not in hdr]
out=['import Tests.Compiler.Srm22PairsTest','-- GENERATED by scripts/srm22/gen_exp.py from scripts/srm22/EXPECTED.txt and the SRM20 / SRM21 source statements (deletion/insertion list of scripts/srm22/gen_pairs_test.py); do not edit by hand.',
     'set_option autoImplicit false','namespace Tests.Compiler.Srm22ExpStmt']+hdr+[
     'open Tools.ShippingSrm13Supply Sparkle.IR.HierCheck Sparkle.IR.OptCheck','open Tools.ShippingDesignSV (weS)','open Tools.ShippingLeafInputWidths (tyW)','open Tools.ShippingHierOpen (bodyInstOuts)','open Sparkle.IR.Machine (SlotField)','']
out+=defs
out+=[t for t in out_thms]
out.append('end Tests.Compiler.Srm22ExpStmt')
open('Tests/Compiler/Srm22ExpStmt.lean','w').write('\n'.join(out)+'\n')
print('ok',len(defs),'defs',len(out_thms),'statements')
