# topshare: how the pieces of `Tests/Compiler/TopShareComposedTest.lean` were obtained (unit SR12, reviewer item 2)

**Status (binding wording).** The pasted proof text in `TopShareComposedTest.lean` is valid by kernel check (Lean elaborates it when the file is built).
It was obtained by *instantiating the template of the depth-2 generator `Tools/ShippingSeqParentGenD2M.lean` for a SHARED leaf, using a scratch copy of the
generator's analysis `analyseM` with the same-leaf refusal removed*. This is **NOT a completed shared-leaf generator**: `#machine_seq_parent_endpoint topshare` still REFUSES
(the generator file is unchanged; the refusal is intentional until a review decides otherwise), and nothing here shows that the template is correct for any other shared-leaf parent.

## Procedure (exact; the scratch files are under `.cluster/scratch/`, git-ignored)

1. `hdr.lean` (imports of the old chain pieces) + `#machine_design_svNR Tests.Compiler.SeqDeepGenDiffTest.topshare 2` generates the OLD chain
   (`topshare.machine_composedNR2`, `wrap{,3}.machine_composedNR1`, ...) from which `analyseM` reads the partition of the call groups.
2. `p3.lean` (imports `Tests.Compiler.TopShareTraceTest`, `Tools.ShippingSeqParentGenD2M`): inside `namespace Tools.ShippingSeqParentGenD2M` it defines the **scratch copy `analyseM2`
   of `analyseM`** (diff below) and runs, after the old chain,
   `let p ← analyseM2 ``Tests.Compiler.SeqDeepGenDiffTest.topshare; let s := assembleM p; IO.FS.writeFile ".cluster/scratch/topshare_gen.lean" s`
   (`assembleM` is the generator's public text assembly, used UNCHANGED). Run: `./.cluster/qbuild.sh env lean .cluster/scratch/p3.lean` (SR11 run p3).
   The dumped file `topshare_gen.lean` (sha256 prefix `5595c26ed019f3e6`) is the template text for `P = topshare`, `Cs = [wrap, wrap3]`, `Gs = [acc, acc]`.
3. `xform.py` (verbatim below) splits that text into the head (per-callee blocks `ts0_*` for `wrap -> acc`, `ts1_*` for `wrap3 -> acc`) and the parent part,
   DELETES the parent's `epD2M_disj` and `epD2M_closesA`, and rewrites the start world from `JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA …)` to `JQC O 0 w`, with
   `machineRanA_start0` + SR10 `topshare_closes0` / `topshare_machineRun`. A last rename `topshare.epD2M…` → `Tests.Compiler.TopShareComposedTest.ts…` is applied (so no
   `epD2M_*` declaration exists for the refused `topshare`).
4. The result (`t2.lean` … `t4.lean`; SR11 runs: t1 exit 1 [only the `decide` of `epD2M_disj` was false], t2 and t3 exit 0) was pasted into the test file.

## Why `analyseM` refuses, and what the scratch copy removed

`analyseM` refuses when two callees call the SAME leaf: the closing lemma `machineClosesAtA_of_memKids'` needs `hdisjD` (module-name sets of different call classes disjoint),
false for a shared leaf. The generated text contains the parent closing built on that lemma (`epD2M_disj`, `epD2M_closesA`); these two declarations are the only ones that
cannot elaborate for a shared leaf, and they are replaced by SR10's START-world closing (`topshare_closes0`, derived).

## DIFF: scratch `analyseM2` (`.cluster/scratch/p3.lean`) versus `analyseM` of `Tools/ShippingSeqParentGenD2M.lean`

(Re-computed in SR12 from the surviving scratch file.)

```diff
--- analyseM (Tools/ShippingSeqParentGenD2M.lean)
+++ analyseM2 (scratch p3.lean, renamed back)
@@ -26,9 +26,6 @@
     Gs := Gs.push G
   -- the leaves must be pairwise different, and different from every callee and from the parent
   for G in Gs.toList do
-    if Gs.toList.count G > 1 then
-      let who := (Cs.zip Gs.toList).filter (·.2 == G) |>.map (·.1)
-      refuseM fn s!"the callees {who} call the SAME leaf {G}: the closing lemma `Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'` has the premise `hdisjD` (the module-name sets of two DIFFE [... truncated in this document: the rest of the line is the refusal text of analyseM]
     if Cs.contains G then refuseM fn s!"the leaf {G} is also a callee of the parent: `hdisjD` of `machineClosesAtA_of_memKids'` cannot hold (OPEN)"
     if G == fn then refuseM fn s!"the leaf {G} is the parent itself"
   let al ← liftTermElabM do readNatLists (← elabText s!"({fn}.machineData.shape.insts.map (·.2.1))")
```

That is the ONLY difference (3 lines: the `if Gs.toList.count G > 1 then …` block of the same-leaf refusal). Every other refusal of `analyseM` (`Cs.contains G`, `G == fn`,
depth 3, mixed parent, memory, several grandchildren, domain polymorphism, …) is kept in the scratch copy.

## `xform.py` (the transformation of step 3, verbatim)

```python
import re,sys
s=open('.cluster/scratch/topshare_gen.lean').read()
P='Tests.Compiler.SeqDeepGenDiffTest.topshare'
# split at parent level
marker='noncomputable def _root_.%s.epD2M_calleeAt (k : Nat)'%P
i=s.index(marker)
head,par=s[:i],s[i:]
# drop theorems by name
def drop(par,name):
    pat='theorem _root_.%s.%s'%(P,name)
    a=par.index(pat)
    m=re.search(r'\n\n(?=(theorem|def|noncomputable|instance|/--|set_option))',par[a:])
    b=a+m.start()+2
    return par[:a]+par[b:]
par=drop(par,'epD2M_disj')
par=drop(par,'epD2M_closesA')
par=par.replace('{D₀ : Nat} {w w1 : Void IO.RealWorld}','{w w1 : Void IO.RealWorld}')
par=par.replace('{D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))','(hw : JQC O 0 w)')
par=par.replace('(hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))','(hw : JQC O 0 w)')
par=par.replace(' hw hc',' hw')
par=par.replace('Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (%s.epD2M_closesA O T hA hM0 hR0 hM1 hR1) hw'%P,
  'Tools.ShippingTopShareRan.machineRanA_start0 O hA T hcore entry (Tests.Compiler.TopShareTraceTest.topshare_closes0 O T hA hM0 hM1 hR0) hw')
par=par.replace('(n := D₀ + 1) (htr_of_tele O hA T D₀)','(n := 0 + 1) (htr_of_tele O hA T 0)')
par=par.replace('(machineRunJQC_of_closesA O hA hcore entry (%s.epD2M_closesA O T hA hM0 hR0 hM1 hR1) hw)'%P,
  '(Tests.Compiler.TopShareTraceTest.topshare_machineRun O T hA entry hM0 hM1 hR0 hw hcore)')
par=par.replace('∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))','JQC O 0 w')
open('.cluster/scratch/part_head.lean','w').write(head)
open('.cluster/scratch/part_par.lean','w').write(par)
print(len(head),len(par))
for k in ['D₀','closesA','CacheInvA',' hc ']:
    print(k,[m.start() for m in re.finditer(re.escape(k),par)][:10])
```

## What is NOT shown here

* The byte-level diff between the `xform.py` output and the pasted text in the test file (the final rename and the surrounding `section`/`open` header) is not recorded as a patch;
  the file building is the validity evidence. Whether the template is right for other shared-leaf parents is OPEN.
* `topshare` stays REFUSED by the generator; lifting that refusal or adding a shared-leaf variant is a review decision.
