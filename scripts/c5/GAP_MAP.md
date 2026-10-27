# C5 GAP MAP — every binder of Tools.ShippingSrm33.machine_ships_hierC_noHstR (Tools/ShippingSrm33Core.lean:24) for the Q shape
Base: branch kjob/c5-spec = kjob/c4-int 692d78e3 (accepted C4). Class and statement: scripts/c5/Q_CLASS.md, scripts/c5/C5_STATEMENT.lean.txt (elaborated in Tests/Compiler/QDefTest.lean).
Status words as in scripts/c3/GAP_MAP.md: EXISTS-GENERIC (generic theorem), INSTANCE-ONLY (only for topshareQ), MISSING (named Prop to prove), CONTRACT (premise by design).
The "Q supply today" column is the instance endpoint Tests.Compiler.Srm33EndpointTest.topshareQ_hierC_noHstR (:85-131) with the bundle
TqBnd (Tests/Compiler/Srm9ComposedTest.lean:146-154). "C4 lemma" is the M-shape generic theorem to generalise (all in Tests/Compiler/C4*Test.lean).
Nothing here is claimed proved beyond the cited theorems. No target Prop is a class field (checked by the QDefTest audit).

## Differences Q vs M that every row below must respect (found by the inventory + this spec)
1. PLAIN leaf: `leafP` has no instances, no generated machineExt / machineExtB, hence NO `GenPkg` for it (AMENDMENT 2 of C4); its data are `LeafData` (Tests/Compiler/SharedLeafMemKidRunTest.lean:145),
   `LeafKidData` (Tests/Compiler/Srm4KidTest.lean:71) and the GENERATED `leafP.seq_child_runN` (= `leafP_run`, Tests/Compiler/Srm4MixedTest.lean:36, `generateSeqChildN`).
2. `MachineCloses` of the leaf (`hcl`, TqBnd component, Srm9ComposedTest.lean:151) is a premise today. It is DERIVABLE: `Tools.ShippingMachineClosesData.closes_of_data` (Tools/ShippingMachineClosesData.lean:226)
   needs `ok`, the body equation and `letsOk = true`; `letsOk` DECIDES for leafP (class field `leafLetsOk`, QDefTest `P_Q`, `P_Q_hcl` audit). So `hcl` is NOT a contract binder.
3. Per-wrapper arity: wrapP 3, wrapQ 5, top nDecl 4 (C4 had one `nDecl` for all: `wArityN`). The class has `QWrapData.arity`; every table below is per wrapper.
4. Mixed calls: wrapQ has two ordinary calls of leafP and ONE memory entry. wrapP only ordinary calls. The unified route for BOTH wrappers is the mixed one of Tools/ShippingSrm4Mixed.lean
   (`ordCallee_hcalls` :159, `callee_seqChildRunN2` :245, `genBsC/genOutsC/genSrcC/genPC` :111-117, `CallFactFO` :120), since `MemCalleeData` takes per-call tables and needs no memory call.
5. Gs = [] and per-wrapper `names` (csQ, SharedLeafMemKidEntryTest.lean:213-214: namesP / namesQ); C4's `tieCs` has Gs = the leaf's call names and one shared `lNames`.
6. NEW FINDING (not in the inventory): the C4 decoding hypothesis `wArgsIn` / `argInOk` (CDefTest.lean:60) says the wrapper passes its own input at the SAME position as the leaf port (`bpos j = p`). That is FALSE for wrapQ:
   `leafP x` takes `x` at leaf port 1 but `x` is wrapper position 3 (binders `dom we wa x y`). So the Q class carries a port map `QWrapData.argPos : call → leaf port → wrapper position` with `argInOkQ` (QDefTest) and
   `callOut` states agreement `bools' p = bools (argPos k p)`. C4's `decode_bool` / `decode_bits` (Tests/Compiler/C4HCallsTest.lean:158,179) must be generalised by the map (named item Q-DECODE below). It is the only place where a C4 proof does not transfer by renaming.

## Binder table
| T1 binder / bridge | how C2 supplies it for Q today (topshareQ_hierC_noHstR) | C5 status | C4 lemma to generalise | named missing Prop | dep |
|---|---|---|---|---|---|
| hloc | KSn_local (Tools/ShippingHierStateG.lean:632) | EXISTS-GENERIC | — | — | — |
| Bnd (premise bundle TqBnd) | O,T,hA, MachineDefines×4 (leafP, wrapP, wrapQ via entryL/entryW), `hcl`, TqHcallsP, TqFQ, TqGrp, JQC O 0 w | SPLIT: contract part = explicit binders `O T hA entryL entryW entry hw`; `hcl` DERIVED (`leafLetsOk`); TqHcallsP, TqFQ ↦ Q-HCALLS (derived); TqGrp ↦ class field `group` (STRUCTURAL CLASS ASSUMPTION) | C4 binder split (C4_STATEMENT) | — | — |
| C (closes) | `fun _ _ _ _ => True` | EXISTS-GENERIC (trivial) | — | — | — |
| Bd + hBd + Inv + hRI | Bd := kidsMaskedN D.modules b.body = true (conclusion antecedent); hBd := KSn_boundedIn (Tools/ShippingMachineShipsDepth.lean:171); Inv := True; hRI := true_inv | hBd/Inv/hRI EXISTS-GENERIC; Bd value = Q-MASK | `kidsMasked_of_class` (C4ShipsTest.lean:60) | **Q-MASK**: `kidsMasked_of_class` for `QSharedLeafParent` (instance: topshareQ_kidsMasked, Srm4ParentQTest.lean:116, via `kidsNC_maskedN` with tqOuts/tqIns, hkid, ranA) | Q-KID, Q-RAN |
| soundL | topshareQ_soundLA (Srm4ParentQTest.lean:182) ← topshareQ_traceXA (:162) ← genTrace (GENERIC, Tools/ShippingQuadComposed.lean:156) + topshareQ_machineRun_derived (SharedLeafMemKidIfaceTest.lean:278) | INSTANCE-ONLY wrapper over a generic core | `machineRun_of_class` / `soundLA_of_class` (C4ClosesTest.lean:115,127) | **Q-RUN**: `machineRun_of_class` for Q (`nm_machineRun` with `csQ_callees`/`csQ_iface` generic: CalleeNM data from `tags/agree/cne`, per-wrapper `names`, Gs = []) | Q-CLOSES |
| composed (ComposedNW 2 → ComposedNWRegs) | topshareQ_composedNW (Srm4ComposedQTest.lean:~210, INSTANCE, premises TqHcallsP, TqFQ, TqGrp, hR0, hcl) ∘ Tests/Compiler/Srm32InstTest.lean topshareQ_composedNW_hWd (generic composedNWRegs_of_composedNW, hWd_of_wired) | INSTANCE-ONLY at topshareQ_composedNW | `composedNW_of_class` / `hcomposed_of_class` (C4ComposedTest.lean:262,309) | **Q-COMPOSED**: `composedNW_of_class` for Q: per-call `tq_callRunP/Q` become ONE generic `callee_seqChildRunN2` per wrapper (arity per wrapper, `tieBsC/OutsC/SrcC` by `QWrapData.arity`); `leafCallee_*` not used | Q-HCALLS, Q-RUN, group |
| houtTy | topshareQ_outTy (decide) | CLASS FIELD (data check) | `P.outTy` | — | — |
| hinitW | `by decide` | CLASS-DERIVABLE | `hinitW_of_ok` (Tools/ShippingC4InitW.lean:24) | — (EXISTS) | — |
| facts (RunFacts) | topshareQ_runFacts (Srm4ParentQTest.lean:85) = kidsNC_runFacts with tqOuts/tqIns, topshareQ_hkid (:60 ← wrapP_kidFactsNC :30 from leafCallee_kidFactsA minus check, wrapQ_kidFactsNC Srm4KidTest.lean:85), topshareQ_cw, topshareQ_ranA (:74) | GENERIC core, INSTANCE inputs | `runFacts_of_class` (C4ShipsTest.lean:76), `c4_hkid` (C4KidTest.lean:53) | **Q-KID**: `∀ k hk, KidFactsNC O (top.insts[k]).1 (P.outsOf k) (P.insOf k)`: per wrapper `memCallee_kidFactsNC` (Tools/ShippingSrm4Kid.lean:60) with `mem`, `kidOuts/kidIns/kidMemT/kidOrdT/cw`; the ordinary kid is `leaf_kidFactsA` from `leafData/leafKidData` + entryL + DERIVED hcl; per-call kind dispatch on `(originAt ..).child?` | hcl-derived |
| Q-CLOSES | topshareQ_closes0_derived (SharedLeafMemKidIfaceTest.lean:267) = nm_closes0 with csQ_callees (needs wrapP_calleeNM / wrapQ_calleeNM: step of the PLAIN leaf `leafKid_step_nm` with leafP_leafOK) + wrapQ_closesA | INSTANCE-ONLY | `closes0_of_class`, `callees_of_class`, `wrapper_closesA_of_class`, `leaf_step_of_class` (C4ClosesTest.lean:45-96) | **Q-CLOSES**: `closes0_of_class` for Q: wrapper `MachineClosesAtA` by `memCallee_closesA` with `ordT`; leaf step by `leafKid_step_nm O hA (leafOK_of_data leafData entryL hcl)`; CalleeNM from `tags/agree/cne` (Gs = [], no `wNotin`) | hcl-derived |
| hcore, hpost, entry | the run | CONTRACT | — | — | — |
| hstR (inner) | removed in C2 (hinit + 19th/20th clauses + hinitW) | EXISTS-GENERIC given hinitW and Q-COMPOSED | — | — | Q-COMPOSED |
| SourceInputs, regs, rst, clk, hinit, ResetNk 2, hinsFit, hstX (inner) | input conditions | CONTRACT | — | — | — |

## Named missing Props (C5 work list; none proved; every one is derived from class fields, none is a field)
* **Q-DERIVE-HCL** (tiny): `hcl_of_class P : ∀ mc cc, MachineCloses mc mref cc cref P.leaf.decl P.leaf.d.shape` = `closes_of_data` applied to `leafData.ok/.body/leafLetsOk`. Already elaborated as `P_Q_hcl` for the member (QDefTest); generic form is one line.
* **Q-DECODE**: C4HCallsTest `decode_bool` / `decode_bits` / `lsrc_*_val` with the port map `argPos` and `argInOkQ`: `boolsOf L.d.bsIn (valsOf (letObsB ..) args) p = bools (argPos k p)` (likewise bits). dep: none. NEW (see difference 6).
* **Q-HCALLS**: for every wrapper `w ∈ P.wrappers`: `∀ m design, HCallsOf 1 w.d design m … w.dat.arity (genBsC L.decl L.d.bsIn) (genOutsC L.decl L.d.shape.layout.outs) (genSrcC L.decl L.d.bsIn L.src) (genPC (PCs design))`
  (exact shape of `wrapQ_hcalls`, Srm4MixedTest.lean:102; this REPLACES BOTH TqHcallsP (`leafCallee_hcalls`, Tools/ShippingQuadCalls.lean:346, needing CallFactF of wrapP) AND TqFQ (CallFactFO of wrapQ)).
  Route: `ordCallee_hcalls` (Tools/ShippingSrm4Mixed.lean:159) with `mem`, `ordKid`, `ordArgsN`, `widths/wid/ordW`, `memCalls` (hmem), `leafRun` (hrunPC), and `hF : CallFactFO` PROVED from `argsIn` + `callOut` + Q-DECODE
  (the CallFactFO of ordinary calls is exactly what `callOut` states, restricted to `child? = none`). dep: Q-DECODE.
* **Q-KID**, **Q-CLOSES**, **Q-RUN**, **Q-MASK**: rows above. dep chain: hcl-derived → Q-KID, Q-CLOSES → Q-RUN, Q-MASK.
* **Q-COMPOSED**: generic `composedNW_of_class` + `hcomposed_of_class` (HComposed) for Q: per wrapper `callee_seqChildRunN2` (Tools/ShippingSrm4Mixed.lean:245) with hB (served run of the leaf ⇒ `PCs`, as `wrapQ_hrunN`, SharedLeafMemKidIfaceTest/Srm4MixedTest.lean:~143) and `hcl` closesA; the parent `hcallsNW` as `topshareQ_hcallsNW` (Srm4ComposedQTest.lean:~160) but with `if k<2` replaced by `wOf k` and `tieIns/tieOuts/tieBsC/tieSrcC`. dep: Q-HCALLS, Q-RUN, `group`.
* **Q-RAN**: `ranA_of_class` for Q (`machineRanA_start0` + Q-CLOSES). dep: Q-CLOSES.
* **Q-SHIPS**: `qSharedLeaf_ships` = `memSharedLeaf_ships_of_composed` for Q (C4ShipsTest.lean:92). dep: all above.
* **Q-FINAL** (audit unit): `topshareQ_hierC_of_class : type_of% @Tests.Compiler.Srm33EndpointTest.topshareQ_hierC_noHstR` from `qSharedLeaf_ships (P_Q hgrp)`, FrozenC5 isDefEq audit, closure walk (no instance constants), axioms.

## Class assumption and optional items
* `group : QuadGroupFacts …` = TqGrp is a STRUCTURAL CLASS ASSUMPTION (as TmGrp for M); G-GRP-DERIVE stays optional.
* Not in scope: SV bounds side (SRM11-21), G3, depth other than 2, several leaves, wrappers over the memory leaf (that is the M class).
