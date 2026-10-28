#!/usr/bin/env python3
# Writes scripts/srm19/PREMISE_TABLE.txt from scripts/srm19/PREMISES.txt (rows printed by the audit) + the fixed classification below.
import re
CLS={'T':'machine premise (SRM4 RefLawsATele)','hA':'machine premise (AdmCtx)','hR0':'machine premise (MachineDefines leafP)','hcl':'machine premise (MachineCloses leafP)',
 'entryL':'machine premise (MachineDefines)','entry₁':'machine premise (MachineDefines)','entry₂':'machine premise (MachineDefines)','entry':'machine premise (MachineDefines)',
 'hw':'machine premise (JQC O 0 w, history)','hcore':'compiler-run premise (RunsTo synthesizeCombinationalCore; same hcore as hO)','hpost':'compiler-run premise (b is post-processed raw)',
 'hrun':'EXPLICIT RESIDUAL: run proposition (SRM11/13); not derived','hin':'EXPLICIT RESIDUAL hin: inputs fit widths (SRM13)','hst₁':'EXPLICIT RESIDUAL RegsAtInit on st0 (SRM13)',
 'hst₂':'EXPLICIT RESIDUAL RegsFit (SRM13)','hst₃':'EXPLICIT RESIDUAL NonRegBounded on st0 (SRM13)',
 'hRK':'EXPLICIT RESIDUAL hRK : ResetNk n raw D kids, the Reset parameter of ComposedG/ComposedGW (SRM18; replaces SRM17 hsk); NOT derived, NOT hsk',
 'hfit':'EXPLICIT RESIDUAL FitTree (SRM13)'}
DATA={'mctx','mref','cctx','cref','O','w','w1','raw','b','D','ins',"T'",'st0','mems','kids','envs'}
out=['SRM19 PREMISE TABLE (rows from scripts/srm19/PREMISES.txt; classification fixed in scripts/srm19/gen_premise_table.py)','']
cur=None
for l in open('scripts/srm19/PREMISES.txt').read().split('\n'):
    if not l: continue
    p=l.split('|')
    if p[0]=='S19THM': out.append(f'== {p[1].split(".")[-1]} ({p[2]} binders) =='); continue
    tag,thm,i,bi,nm=p[:5]
    if tag=='S19DATA': c='data (instance witness; the SAME term is passed to every component)' if nm in DATA else 'data'
    else: c=CLS.get(nm,'UNCLASSIFIED')
    out.append(f'  {i:>2} {bi:8} {nm:7} {c}')
out+=['','PROVED-elsewhere-and-instantiated (binders DELETED from the final theorem, filled inside its proof, same proof terms as SRM14 `_computed`):',
 '  rk := rkOf gM 4 / rkOf gQ 3 (SRM7 Tools/ShippingSrm7Rank.lean rkOf), hrkmem := rkOf_mem, hrT/hrW/hrW3|hrP/hrQ/hrL := rkOf_decl + decided gM_*/gQ_* (Tests/Compiler/Srm7RankTest.lean)',
 'PROVED-elsewhere and used inside (not a binder): topshare{M,Q}_hO (SRM16), topshare{M,Q}_svBoundsH_viaResetO (SRM16), topshare{M,Q}_svBoundsH_viaStartNk (SRM18), kidInvN_of_resetNk (SRM13)',
 'NOT derived / OPEN: hRK, hin, RegsAtInit, RegsFit, NonRegBounded, FitTree (hfit), hrun, and that any concrete run satisfies them']
assert 'UNCLASSIFIED' not in '\n'.join(out)
open('scripts/srm19/PREMISE_TABLE.txt','w').write('\n'.join(out)+'\n')
