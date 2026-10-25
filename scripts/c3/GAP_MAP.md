# C3 GAP MAP — every binder of Tools.ShippingSrm33.machine_ships_hierC_noHstR (Tools/ShippingSrm33Core.lean:24, base 99dcc086) for C4
Status words: EXISTS-GENERIC (a generic theorem, file:line), INSTANCE-ONLY (proved only for topshareM/Q), MISSING (named Prop, to prove), CONTRACT (kept as premise by design).
Owners: W = a worker unit (to be briefed after review of this map), I = integrator. "dep" = what it needs first. Nothing below is claimed proved beyond the cited theorems.

| T1 binder / bridge | how C2 supplies it for M (Tests/Compiler/Srm33EndpointTest.lean:69-82) | C4 status | missing Prop (name) / generic source | dep | owner |
|---|---|---|---|---|---|
| hloc | KSn_local (Tools/ShippingHierStateG.lean:632) | EXISTS-GENERIC | — | — | — |
| Bnd | TmBnd (Tests/Compiler/Srm9ComposedTest.lean:66): O,T,hA,MachineDefines×3, TmH1, TmH2, TmGrp, JQC O 0 w | SPLIT | contract part = explicit C4 binders O,T,hA,entryL,entryW,entry,hw; TmH1/TmH2 ↦ G-HCALLS; TmGrp ↦ P.group (G-GRP) | — | I |
| C (closes) | fun _ _ _ _ => True | EXISTS-GENERIC (trivial) | — | — | — |
| Bd + hBd + Inv + hRI | Bd := kidsMaskedN D.modules b.body = true; hBd := KSn_boundedIn (Tools/ShippingMachineShipsDepth.lean:171); Inv := True; hRI := true_inv (Tools/ShippingMachineShipsHier.lean:106) | hBd/Inv/hRI EXISTS-GENERIC; Bd value is a conclusion ANTECEDENT in C2 | G-MASK: `∀ P hcore hpost …, kidsMaskedN D.modules b.body = true` from the run (instance: topshareM_kidsMasked, Tests/Compiler/Srm4ParentTest.lean ~:150, via kidsNC_*) | G-KID, G-RAN | W |
| soundL | topshareM_soundLA (Tests/Compiler/Srm4ParentTest.lean:201) ← topshareM_traceXA (:182) ← genTrace (Tools/ShippingQuadComposed.lean:156, GENERIC) + topshareM_machineRun_derived (Tests/Compiler/SharedLeafMemKidIfaceTest.lean:180, INSTANCE) | INSTANCE-ONLY wrapper over a generic core | G-RUN: `machineRun_of_class P …` (the generic replacement of topshareM_machineRun_derived) ⇒ `soundLA_of_class` | G-CLOSES | W |
| composed (joint ComposedNWRegs) | Tests/Compiler/Srm32InstTest.lean topshareM_composedNW_hWd = composedNWRegs_of_composedNW (Tools/ShippingSrm28Regs.lean:77, GENERIC) ∘ topshareM_composedNW (Tests/Compiler/Srm4ComposedTest.lean:231, INSTANCE: needs hcalls₁/hcalls₂ : HCallsOf … (Tools/ShippingSeqParentLemmas.lean:53) with memLeafPC (Tools/ShippingSrm4Callee.lean:54), hgrp : QuadGroupFacts) + hWd_of_wired (Tools/ShippingSrm32Width.lean:28, GENERIC) | INSTANCE-ONLY at topshareM_composedNW | G-COMPOSED: `composedNW_of_class P … : ComposedNW 2 P.decl P.d P.nDecl raw D …` — the real generality gap (ledger: "ComposedNW supply for an arbitrary memory-bearing parent" OPEN) | G-HCALLS, G-GRP, G-RAN | W |
| houtTy | topshareM_outTy (Tests/Compiler/Srm4ParentTest.lean:62, decide) | CLASS FIELD | P.outTy (decidable data check) | — | I |
| hinitW | `by decide` | CLASS-DERIVABLE | G-INITW: `hinitW_of_ok : d.ok = true → ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width` (d.ok contains the check, Tools/ShippingMachineAuto.lean:225) | — | W |
| facts (RunFacts) | topshareM_runFacts (Tests/Compiler/Srm4ParentTest.lean:104) = kidsNC_runFacts (Tools/ShippingSrm4Parent.lean:29, GENERIC) applied to parentData checks (= P fields), tmOuts/tmIns, hkid (topshareM_hkid ← wrapM_kidFactsNC, Tests/Compiler/Srm4KidTest.lean:55, INSTANCE), topshareM_cw, ranA (topshareM_ranA :91 = machineRanA_start0, Tools/ShippingTopShareRan.lean:24, GENERIC, needing topshareM_closes0_derived, Tests/Compiler/SharedLeafMemKidIfaceTest.lean:170, INSTANCE) | GENERIC core, INSTANCE inputs | G-KID: `kidFactsNC_of_wrapper P wd …` (generic wrapM_kidFactsNC); G-CLOSES: `closes0_of_class P …` (generic topshareM_closes0_derived); G-OUTS: tmOuts/tmIns/topshareM_cw as functions of P | G-CLOSES | W |
| hcore, hpost, entry | the run | CONTRACT (the one actual run) | — | — | — |
| hBnd antecedent of the conclusion | TmBnd | SPLIT (see Bnd row) | — | — | — |
| hstR (inner) | removed in C2 via hinit + 19th clause (sourceRegsAreSlots_of_wired_all, Tools/ShippingSrm28Regs.lean:24) + 20th clause (slotWidths_of_wired, Tools/ShippingSrm32Width.lean:19) + hinitW, in hstR_of_wired_slots (Tools/ShippingSrm31Core.lean:26) | EXISTS-GENERIC given G-INITW and G-COMPOSED | — (G3 NOT needed for this route; G3 status unchanged: NOT DECIDED) | G-INITW, G-COMPOSED | — |
| SourceInputs, regs pass, rst, clk, hinit, ResetNk 2, hinsFit, hstX (inner) | input conditions | CONTRACT (input conditions) | hinsFit clk/rst-aware (SRM29B); ResetNk 2 = start state of the instance tree | — | — |

## Named missing Props (C4 work list; none proved)
* G-HCALLS — `HCallsOf 1 wd.2 design m … (memLeafPC O P.leafDecl P.leafD design)` for every wrapper wd ∈ P.wrappers, from P.wrapLeaf/P.leafMem (today TmH1/TmH2 PREMISES inside TmBnd). dep: none. owner W.
* G-GRP — `QuadGroupFacts P.d P.nDecl` from a decidable group check (today TmGrp PREMISE; P.group is a Prop field until a Bool check + soundness lemma exists). dep: none. owner W.
* G-CLOSES — generic `closes0` for P's children (today topshareM_closes0_derived). dep: G-HCALLS. owner W.
* G-RUN — generic `machineRun_of_class` (today topshareM_machineRun_derived) ⇒ soundL via genTrace. dep: G-CLOSES. owner W.
* G-KID — generic `kidFactsNC_of_wrapper` (today wrapM_kidFactsNC / wrapM3_kidFactsNC). dep: none. owner W.
* G-OUTS — tmOuts/tmIns/topshareM_cw as functions of P (data). dep: none. owner W.
* G-COMPOSED — generic `composedNW_of_class` (today topshareM_composedNW). dep: G-HCALLS, G-GRP, G-RAN(=machineRanA_start0 + G-CLOSES). owner W. LARGEST GAP.
* G-MASK — generic kidsMaskedN from the run (today topshareM_kidsMasked). dep: G-KID, G-CLOSES. owner W.
* G-INITW — hinitW_of_ok. dep: none. owner W (small).
* C-DEF — the NEW structure MemSharedLeafParent + projections P.src/ext/extB/lsrc + member instances P_M, P_Q (decide). dep: none. owner I/W.
Proposed order: C-DEF, G-INITW, G-OUTS, G-KID, G-HCALLS, G-GRP → G-CLOSES → G-RUN, G-MASK → G-COMPOSED → C4 assembly.

## Not in C4's endpoint scope (stated so they are not silently dropped)
* SV-bounds side (SRM11–21: hseedB/hst/hkids, ranks/heights gM/gQ, HeightBridge, FitTree, C1 endToEnd hst2 replacement): not binders of the C4 endpoint; separate.
* G3 SourceRegsKept: not needed by this C4 route (hstR via hinit + 19th/20th clauses); status unchanged (NOT DECIDED; SRM36 conditional lemma only).
* Depth: C fixes n = 2 (wrappers over one leaf). Other depths / several leaves / non-wrapper callees are outside C.
