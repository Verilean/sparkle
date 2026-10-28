#!/usr/bin/env python3
# SRM22: generate the two corollary STATEMENTS of Tests/Compiler/Srm22PairsTest.lean FROM THE SOURCE STATEMENTS of
#   SRM20 `topshareM_svBoundsH_underComposedG` (Tests/Compiler/Srm20BridgeTest.lean) and SRM21 `topshareQ_svBoundsH_underComposedG'` (Tests/Compiler/Srm21LiftTest.lean)
# by the committed DELETION/INSERTION list:  (1) delete the `hin` conjunct line;  (2) replace the end of the outer binder list `(hBd : …) :` by `(hBd : …)` + (hnd) (hsI) (hIW) + ` :`;  (3) rename.
# usage (repo root):  python3 scripts/srm22/gen_pairs_test.py         -> prints the two theorem headers (ending before `:= by`)
import sys
HIN='        (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (checkedOptimize b) x) →\n'
BD='(hBd : kidsMaskedN D.modules b.body = true) :'
NEW=('(hBd : kidsMaskedN D.modules b.body = true)\n'
     '    (hnd : (b.wires.map (·.name)).Nodup)\n'
     '    (hsI : ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)\n'
     '    (hIW : ∀ p ∈ b.inputs, declWidth b p.name ≤ Tools.ShippingLeafInputWidths.tyW p.ty) :')
def stmt(path,name,newname):
    s=open(path).read()
    i=s.index('theorem '+name+'\n')
    j=s.index(':= by',i)
    t=s[i:j]
    assert t.count(HIN)==1 and t.count(BD)==1
    t=t.replace(HIN,'').replace(BD,NEW)
    return t.replace('theorem '+name+'\n','theorem '+newname+'\n',1)
M=stmt('Tests/Compiler/Srm20BridgeTest.lean','topshareM_svBoundsH_underComposedG','topshareM_svBoundsH_underComposedG_noHin')
Q=stmt('Tests/Compiler/Srm21LiftTest.lean',"topshareQ_svBoundsH_underComposedG'","topshareQ_svBoundsH_underComposedG'_noHin")
if len(sys.argv)>1 and sys.argv[1]=='M': print(M)
elif len(sys.argv)>1 and sys.argv[1]=='Q': print(Q)
else: print(M); print(Q)
