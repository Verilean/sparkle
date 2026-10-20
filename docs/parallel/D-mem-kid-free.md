# D — the check-free design-level endpoint of a parent of a memory-machine child (round par/d-1)

Branch `par/d-1` from poc `91d0f907`. **WRITTEN, NOT BUILT.** No `lean`,
`lake` or `iverilog` was started; nothing below is proved-and-built. Marks:
[R] read (file:line at 91d0f907), [M] measured by the integrator earlier,
[P] PREDICTED, [?] not known.

**How far it got — short.**

| task | state |
|---|---|
| 1 the measurement of worker C's by-reading claim | written: `Tests/Compiler/MemKidCheckProbe.lean` (logs only) |
| 2 `GenKidT`, `memCounterH_factsT` | written: `Tools/ShippingGenKidT.lean`, `Tools/ShippingGenKidM.lean`, the instance in the test |
| 3 the hand endpoint `memParent_design_noPorts1_closed` | written, asserting, with the census re-check and `#print axioms`: `Tests/Compiler/MemParentFreeTest.lean` |
| 4 `memGrand` (depth 2) | written up to the EXACT OBSTACLE: every check antecedent discharged, the boundary reduced to `ChildBnd`; the closing of `memGrand` itself stays a premise (the `mixDeep` name collision, §6): `Tests/Compiler/MemGrandFreeTest.lean` |
| 5 the generator | NOT written (task order: only after 4 is complete; 4 ends in an obstacle that is not about memories) |

Two things the reading changed against the task text, both stated where they
matter:

* the hand endpoint is NOT made from `memParent.machine_design_svNR1` — its
  check antecedents sit under `∃ raw D` with no link to the core run and
  cannot be discharged from outside (§2.6). It is the head
  `machine_design_noPorts` at the arguments of `memParent.machine_ships_hierNR1`,
  as in every built generator, applied by the BUILT function `endpointTermX`;
* `hsep` of the built `kidsT_designCheck` is FALSE for `memGrand` (`cnt` is a
  callee and a callee of the callee `memParent`). A name-free replacement is
  written (`core_callSelf`, §3.2), so `GenKidT` has NO separation field.

## 1. Files

| file | what | made how |
|---|---|---|
| `Tests/Compiler/MemKidCheckProbe.lean` | `#memkid_check_log`: which of `t = true` / `t = false` the kernel decides, 14 lines | by hand (the command copied from `NoRepeatFamilyTest`) |
| `Tools/ShippingCallSelf.lean` | `core_callSelf`, `core_kidsPass_own`, `kidsT_designCheckO` | `scripts/gen_call_self.py` from built proofs + one hand proof |
| `Tools/ShippingGenKidT.lean` | `kids_designCheck_inT`, `GenKidT`, `GenKidT.core/outsIn/kidAR/ports/typedIn/masked/clk/check/factsT` | `scripts/gen_genkid_t.py` from the built `ShippingGenKid.lean` + two hand theorems |
| `Tools/ShippingGenKidM.lean` | `core_calls_portsGM`, `core_conn_refsGM`, `kids_run_kidM`, `kids_real_kidM`, `kidsM_designCheck_in`, `GenKidM`, `GenKidM.core/…/factsT` | `scripts/gen_genkid_m.py` from three built files + hand theorems |
| `Tools/ShippingBndOnly.lean` | meta tools: `#noports_open_as`, `bnd_only%`, `bnd_only_closing%`, `#assert_check_free`, `#log_check_free` | by hand |
| `Tests/Compiler/MemParentFreeTest.lean` | step 3 (asserting) | by hand, the terms of the built generators |
| `Tests/Compiler/MemGrandFreeTest.lean` | step 4 (asserting; last command logs) | by hand |

No built file is edited. Nothing under `Sparkle/`, `lakefile.lean`,
`Tests/AllTests.lean`. The three scripts fail unless every replacement
occurs the stated number of times and every segment starts and ends on the
expected built line; rerun: `python3 scripts/gen_call_self.py` etc. (they
read and write files only).

## 2. Step 0: what was read, and the statements used

### 2.1 Read in full

`docs/parallel/B-mem-depth.md`, `C-mem-depth-ships.md`, `C-mem-depth-free.md`
(all sections and build records); `Tools/ShippingGenKid.lean` 1–422;
`Tools/ShippingKidFacts.lean` 1–253; `Tools/ShippingKidFactsT.lean` 1–342;
`Tools/ShippingKid.lean` 1–118; `Tools/ShippingMemKidFacts.lean` 1–741;
`Tools/ShippingCoreFromM.lean` 1–278; `Tools/ShippingCallsPortsG.lean` 1–321;
`Tools/ShippingChecksCore.lean` 1–605; `Tools/ShippingNoPorts.lean` 1–174;
`Tools/ShippingNoPortsKidsCommand.lean` 1–704; `Tools/ShippingNoPortsDeepCommand.lean`
1–627; `Tests/Compiler/MemDepthProbeTest.lean`, `MemParentClosesTest.lean`,
`NoRepeatFamilyTest.lean`.

Read in part: `Tools/ShippingMachineDepthCommandR.lean` 1–330 and 505–1051
(`generateRunOfR`, `generateCoreNR` whole, `generateShipsNR`,
`generateDesignNR`, `preClose`; NOT 330–505: `proveGroup`, `entryProof`);
`Tools/ShippingMemKidPorts.lean` (the eight statements, not the proofs);
`Tools/ShippingMemKidCore.lean` (`core_linkedWFM` statement);
`Tools/ShippingKidsChildIfaceM.lean` 1–140, 228–262, 312–352;
`Tools/ShippingKidsSelf.lean` 76–140; `Tools/ShippingPortsMatchRaw.lean`
240–360; `Tools/ShippingMemOnly.lean` 108–230; `Tools/ShippingShipsDesignSVCommand.lean`
1–110; `Tools/ShippingShipsDesignSVAll.lean` 25–75; `Tools/ShippingFinalGoalCommand.lean`
20–60; `Tools/ShippingDesignCoverage.lean` 1–190; `Tools/ShippingCallsKidsD.lean`
30–140; `Tools/ShippingMachineShipsHier.lean` 196–222. `docs/parallel/C-loop-child-calls.md`
was NOT read (ship level; nothing of it is used here).

### 2.2 The interface statements used [R]

| statement | where |
|---|---|
| `KidFacts` (9 fields), `kids_runFacts`, `kids_outsCheck`, `kids_maskedN`, `kids_designCheck` | `ShippingKidFacts.lean` 72–99, 106, 138, 168, 199 |
| `KidFactsT`, `KidFacts.toT`, `core_kidsPass_top`, `kidsT_runFacts`, `kidsT_outsCheck`, `kidsT_maskedN`, `kidsT_designCheck` | `ShippingKidFactsT.lean` 57–83, 85, 108, 185, 217, 247, 279 |
| `GenKid`, `kids_designCheck_in`, `GenKid.core … facts`, `kidCheck_succ` | `ShippingGenKid.lean` 230–272, 109–224, 280–420, 95 |
| `Kid`, `kid_of`, `Kid.real`, `Kid.mem`, `real_of_kid` | `ShippingKid.lean` 33, 44, 63, 71, 103 |
| `KidFactsM`, `kidFacts_toM`, `memKid_facts`, `memOuts`, `memIns`, `hkidW_of_dataM`, `kidsM_runFacts`, `kidsM_outsCheck`, `kidsM_mixed`, `kidsM_designCheck` | `ShippingMemKidFacts.lean` 423–449, 453, 468, 185, 190, 530, 564, 594, 665, 694 |
| `leafKid_facts`, `LeafKid` | `ShippingLeafKidFacts.lean` 50; `ShippingPortsMatchRawLeaf.lean` 58–75 |
| `KidNamesP`, `namesOfP`, `memKidNamesP`, `kidsChild_of_realM` | `ShippingKidsChildIfaceM.lean` 52, 64, 71, 320–352 |
| `KidNames`, `namesOf`, `ChildIfaceD`, `ChildIfaceD.kid` | `ShippingKidsChildIface.lean` 84–88, 108, 90; `ShippingCallsKidsD.lean` 37–51 |
| `MemOnlyData` (the fields of the generated `f.noPortsMem_data`) | `ShippingMemOnly.lean` 115–133 |

### 2.3 The `M` core lemmas worker C knew by name — their statements [R]

All in namespace `Tools.ShippingMemKid`, all with `hfne : d.shape.instFields ≠ []`
in the place of `hnomem`, over `Kid` where a child is mentioned:

| lemma | where | argument order after `hins` | conclusion |
|---|---|---|---|
| `core_kids_factsM` | `ShippingChecksCore.lean` 449–471 | `outTy hfne hB hcore hpost entry closes` | `core_kids_facts`'s six conjuncts, the fifth over `Kid` |
| `core_closed_typedInM` | `ShippingMemKidPorts.lean` 53–73 | `outTy hfne hB hcore hpost entry closes hon hoty` | `TypedIn b` |
| `core_clkM` | 300–318 | `outTy hfne hsl hB hcore hpost entry closes` | `weS b "clk" = 1 ∧ weS b "rst" = 1` |
| `core_callConnsM` | 430–464 | `hfne outTy hB hcore hpost entry closes` | `core_callConns`'s conclusion over `Kid` |
| `core_callStmtM` | 627–651 | `hfne outTy hB …` | each instance is a `CallStmtG` of a kid's own module |
| `core_portsMatch_rawM` | 732–773 | `hfne outTy hkidW hkidT (hargs) hkidIn hkidClk hB hcore hpost entry closes hon hoty hclkB` | `portsMatchB (childMap D.modules) b = true` |
| `core_kids_selfM` | 841–858 | `hfne hB hcore entry closes` | `core_kids_self`'s conclusion over `Kid` |
| `core_kidsPass_deepM` | 909–936 | `hfne outTy n hkidK hB …` | `kidsPass … (checkedOptimize b).body` (the uniform check) |
| `core_designCheck_runM` | 978–1012 | — | `designCheck (childMap D.modules) n (checkedOptimize b)` |
| `core_linkedWFM` | `ShippingMemKidCore.lean` 98–115 | `outTy hfne hB hcore hpost entry closes` | `linkedWF (childMap D.modules) b.body = true` |
| `core_callPorts_fromM` | `ShippingCoreFromM.lean` 135–164 | (with `hnomem`!) | the OLD `core_callPorts` re-derived from `core_callPortsM` — a fact about instance CONNECTIONS, not `CallsPorts`; NOT what `outTys` / `inW` need |

Do `M` forms exist of the four others? By `grep` of `^theorem` over `Tools/`:

| built | `M` form | consequence |
|---|---|---|
| `kids_real_kid` / `kids_run_kid` (`ShippingChecksCore.lean` 360, 287) | NO | derived here: `kids_run_kidM`, `kids_real_kidM` |
| `core_conn_refsG` (`ShippingCallsPortsG.lean` 267) | NO | derived here from the built `core_callConnsM`: `core_conn_refsGM` |
| `outsMaskedN_of_callsG` (304) | not needed | it is PURE (no run, no closing, no `hnomem`): used as built |
| `core_calls_portsG` (61) | NO | derived here: `core_calls_portsGM`. Its proof reads `hnomem` in ONE place (the call of `core_kids_facts`, 90–91) |

### 2.4 The head [R `ShippingNoPorts.lean` 42–162]

`machine_design_noPorts (n) (Reset) (Bnd : CtxBnd) (C) (Bd) (Inv) (hBd) (hRI)
{declName} (d) {kD ι dom src ext extB lsrc srcL extL extBL} (soundL)
(composed) (houtTy) {mctx mref cctx cref w w' b design} (hr) (entry) (closes :
C mctx mref cctx cref) (hFacts) (hOuts) (hBdRun) (hDesign)` — parametric in
the closing predicate `C` and the boundary `Bnd`. The four run hypotheses
are functions of the CORE run:

    hFacts  : RunsTo (core) … (raw, D) w1 → hpost → Bnd … raw D → RunFacts (childMap D.modules) b
    hOuts   : … → hpost → hierGate b = true → Bnd … → outsCheck (childMap D.modules) n (checkedOptimize b) = true
    hBdRun  : … → hpost → Bnd … → Bd b D
    hDesign : … → hpost → Bnd … → designCheck (childMap D.modules) n (checkedOptimize b) = true

Conclusion: `∃ raw D, hpost ∧ (Bnd mctx mref cctx cref w raw D → ∃ ids, … DesignSV …)`.

### 2.5 What the generators emit [R]

`#machine_no_ports_kids f n` (`ShippingNoPortsKidsCommand.lean` 643–684):
`k.machine_leafKid` / `k.machine_oneOutKid` per callee; `f.machine_kidsK{n}`
(`KidFacts` of every entry, per-entry tables `fun k => List.getD […] k []`,
by `cases k`); `f.machine_runFactsK{n}`, `_outsGK{n}`, `_maskedGK{n}`,
`_designPK{n}` (`runTheorems`, 347–479: `kids_*` at `f`'s data, the data
conditions `by decide` in fixed positions, binders `hcore hpost entry closes
(hg) hB` and the reflections); then `endpointTerm` (507–571): the head at
arguments 3…24 of the VALUE of `f.machine_ships_hierNR{n}` (a
`machine_ships_hierC` application with 25 arguments) and its 11 binders; each
run hypothesis is `mkAppM thm #[hcore, hpost, entry, closes(, hg)]`, the
remaining premises found among the conjuncts of the boundary (`dischargeWith`,
484–501); `closedTerm` (577–616) replaces the closing binder by the premises
of `f.closes_deep` / `f.machine_closes_at`. `#machine_no_ports_deep`
(`ShippingNoPortsDeepCommand.lean`): the same with `k.machine_genKid{n-1}`
(240–358: the `GenKid` structure instance, every data field `by decide`,
`kid` / `self` / `kidsLo` / `kidsHi` / `closes` from named theorems) and
`endpointTermX` (474–545: extra `MachineDefines` binders for machines that
are not direct callees).

### 2.6 The statement shape of `memParent.machine_design_svNR1` [R]

`generateDesignNR` = `compose declName ships …` (`ShippingMachineDepthCommandR.lean`
998–1001; `ShippingShipsDesignSVCommand.lean` 48–72):
`ships_design_svN_all n reset bnd bd … (memParent.machine_ships_hierNR1 xs)`,
whose statement (`ShippingShipsDesignSVAll.lean` 30 ff.) is

    ∃ raw D, hpost ∧ (shipsHierCheck … → Bnd raw D → Bd b D → … designCheck … → …)

The antecedents are about the existential witnesses; the statement does not
say that `(raw, D)` is the core run's result (the remark at the end of the
header of `ShippingChecksCore.lean`, 32–37). They CANNOT be discharged from
`memParent.machine_design_svNR1`. Hence the head of §2.4, as the generators.

The boundary `Bnd` of `memParent.machine_ships_hierNR1` [R `generateCoreNR`
641–692, 916–918; `conj`, `ShippingMachineShipsHierCommand.lean` 16–20]:
`conj [ChildBnd, pT(cnt), pT(memCounterH)]` with `seqKids = [cnt,
memCounterH]`:

    ChildBnd mref cref w ∧ MachineDefines mctx mref cctx cref cnt … ∧
      (MachineDefines mctx mref cctx cref memCounterH … ∧
        ∀ mctx' cctx', ChildRanIn mref cref memCounterH mctx' cctx' →
          MachineClosesAt mctx' mref cctx' cref memCounterH … ∧
            ∀ wc raw D, ChildBnd mref cref wc → ChildBnd mref cref wc)

(`cnt` is a leaf with `cnt.machine_closes`: `free`, 687–689, its premise is
the reflection alone; `memCounterH` has no `machine_closes_at` / `closes_deep`:
`And defs0 pT`, 692, with `pT` the closing AND the kid's own boundary — which
for `memCounterH.machine_composedNR0` is `ChildBnd` alone.) NOT printed: if
the shape differs, the last theorem of the test fails at its `refine`, with
the real shape in the message.

## 3. What is written — statements

### 3.1 Task 1: `Tests/Compiler/MemKidCheckProbe.lean`

`#memkid_check_log "<tag>" <term>` elaborates `example : t = true := by first
| decide | decide +kernel`, then the same with `false`, each in a saved and
restored command state, and logs `MEMKIDCHECK <tag> = true (kernel decide) |
false (kernel decide) | true (by the built theorem leafCheck_memModule; …) |
UNDECIDED`. Never an error. Terms: `mem := (memModule true 4 8).1`; child
maps `CM := childMap (memModule true 4 8).2.modules` (the memory module's
own design) and `C0 := childMap []`; `instLike`: a module whose body is one
instance statement (the kid's own module is a compiler output, not a closed
term: its REASON is measured, not the module).

### 3.2 `Tools/ShippingCallSelf.lean` (no name premise)

    theorem core_callSelf {c} (d) (ok) (hbody) {nDecl} (hC) (hslots) (hdomB) (hins) (hfne) (outTy) (hnomem)
        (hB) (hcore) (hpost) (entry) (closes) :
        ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
          ∃ mc, moduleByName D.modules mn = some mc ∧
            ∃ (k) (hk : k < d.shape.insts.length) (y : Res),
              RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
              moduleByName D.modules y.1.name = some y.1 ∧
              ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2

    theorem core_kidsPass_own …   -- core_kidsPass_top's statement WITHOUT namesK / hname / hsep
    theorem kidsT_designCheckO …  -- kidsT_designCheck's statement WITHOUT namesK / hname / hsep

`core_callSelf` is `core_callConns`'s built proof, lines 283–356 of
`ShippingPortsMatchRaw.lean`, with three asserted edits: the local `hrealE`
keeps BOTH halves of `(closeInstsG_names hG).2.2.2 y …` (the built proof
takes `.1` and drops the second: that the design resolves the modules of the
child's design to themselves — the same fact `core_kids_self` reads off the
same list, `ShippingKidsSelf.lean` 111–117), and the conclusion is stated
from them. Why it matters: `core_kidsPass_top` needs `hsep` only because its
two inputs name two possibly different children.

### 3.3 `Tools/ShippingGenKidT.lean`

    theorem kids_designCheck_inT … (kids_designCheck_in's premises over KidFactsT) :
        designCheck (childMap ms) n b = true                               -- no name premise

    structure GenKidT (mref) (cref) (c : Name) (dk : MachineData) (nDecl : Nat)
        (namesK : Nat → List String) (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat) : Prop
      -- GenKid's fields (ok … closes, incl. nomem, kid : KidNames, self), WITHOUT kidsHi, and
      kidsLo : ∀ k hk, KidFactsT mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) n

    theorem GenKidT.check (K) (hy : RealChild mref cref c y) (ms) (hms : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
        designCheck (childMap ms) n y.1 = true
    theorem GenKidT.factsT (K : GenKidT mref cref c dk nDecl namesK kidOuts kidIns n) :
        KidFactsT mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1)

`core`, `outsIn`, `kidAR`, `ports`, `typedIn`, `masked`, `clk` are `GenKid`'s
(lines 277–368, `GenKid` → `GenKidT` seven times). `kidsHi` is not needed:
it served only the second conjunct of `KidFacts.check`.

### 3.4 `Tools/ShippingGenKidM.lean`

    theorem core_calls_portsGM …  -- core_calls_portsG without hnomem : CallsPorts c d kD b
    theorem core_conn_refsGM …    -- core_conn_refsG without hnomem
    theorem kids_run_kidM … (hfne) (nameK : Nat → String) (namesK) (hkid : Kid … → KidNamesP (nameK k) (namesK k) y.1 y.2)
        (hkidA hkidR over Kid) (hself : ofDecl c ∉ namesOfP d nameK namesK) (hw) (hr) (entry) (closes) : …  -- kids_run_kid's conclusion
    theorem kids_real_kidM …      -- the same from a RealChild witness
    theorem kidsM_designCheck_in … (hkid : ∀ k hk, KidFactsM … n) (hcw) (hargs) … (ms) (hms) :
        designCheck (childMap ms) n b = true

    structure GenKidM (mref) (cref) (c) (dk) (nDecl) (nameK : Nat → String) (namesK : Nat → List String)
        (kidOuts) (kidIns) (n) : Prop
      -- GenKid's data fields WITHOUT nomem, and
      kid    : ∀ k hk y, Kid mref cref (dk.shape.insts[k]).1 y → KidNamesP (nameK k) (namesK k) y.1 y.2
      self   : ofDecl c ∉ namesOfP dk nameK namesK
      kidsLo : ∀ k hk, KidFactsM mref cref (dk.shape.insts[k]).1 (kidOuts k) (kidIns k) n
      callW, callA, entry, closes                                        -- as GenKid

    theorem GenKidM.factsT (K : GenKidM mref cref c dk nDecl nameK namesK kidOuts kidIns n) :
        KidFactsT mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1)

**Per field of `KidFactsT`, for `memCounterH_factsT`** (the table of
`C-mem-depth-free.md` §4.1, now decided):

| field | what proves it | built `M` lemma, or derived here |
|---|---|---|
| the bridge (`GenKidM.core`) | `core_kids_factsM`, `synthesizeCombinational_designL`, `KidNamesP` / `namesOfP` | BUILT lemmas; the six lines are `GenKid.core`'s with the name membership of `kidsChild_ifaceM` |
| `outsIn` | `kidsChild_of_realM … .outsIn` | BUILT |
| `outTys` | `(core_calls_portsGM …).outs` | DERIVED HERE (script, from the built `core_calls_portsG`: one line changed) |
| `kidA`, `kidR` | `kids_real_kidM` | DERIVED HERE (script, from the built `kids_run_kid`: 9 asserted edits) |
| `masked` | `outsMaskedN_of_callsG` (built, pure) on `core_calls_portsGM`, `core_closed_typedInM`, `outsIn`, `core_conn_refsGM` | the conclusion lemma BUILT; `core_conn_refsGM` DERIVED HERE from the built `core_callConnsM` (the 12 lines of `core_conn_refsG`) |
| `portsIn` | `PortsIn.of_typedIn (core_closed_typedInM …)` | BUILT |
| `inW` | `(core_calls_portsGM …).inWidths (core_closed_typedInM …).wn` | DERIVED HERE (as `outTys`) |
| `clk` | `core_clkM` | BUILT |
| `check` (own module, `designCheck (childMap ms) 0 y.1`) | `kidsM_designCheck_in` | DERIVED HERE (script, from the built `kids_designCheck_in`: 11 asserted edits, each an old lemma → its built `M` lemma) |

`masked` (the field worker B / C left open): `outsMaskedN y.1 = true` is
DERIVED for the kid's own module — nothing in it is false of a module whose
memory is an instance; `noMem` comes from `TypedIn.kinds`.

### 3.5 `Tests/Compiler/MemParentFreeTest.lean`

    theorem cnt_leafKid (entryC : MachineDefines mctx mref cctx cref cnt cnt.machineData.shape) :
        LeafKid mctx mref cctx cref cnt cnt.machineData
    theorem memCounterH_genKidM (hR : ∀ mctx' cctx', MachineDefines mctx' mref cctx' cref memCounterH memCounterH.machineData.shape) :
        GenKidM mref cref memCounterH memCounterH.machineData 3
          (fun _ => ofMem true 4 8) (fun _ => [ofMem true 4 8]) (fun _ => memOuts 8) (fun _ => memIns 4 8) 0
    theorem memCounterH_factsT (hR : ∀ mctx' cctx', MachineDefines mctx' mref cctx' cref memCounterH …) :
        KidFactsT mref cref memCounterH memCounterH.machineData.shape.layout.outs
          (argWidths memCounterH.machineData 3) 1
    theorem memParent_kidsT (hRc) (hRm) : ∀ k hk,
        KidFactsT mref cref (memParent.machineData.shape.insts[k]).1 (kidOutsP k) (kidInsP k) 1
    theorem memParent_kidIface (hRc) (hRm) : ∀ k hk y, RealChild … → ChildIfaceD … (nkT k) (outsT k) (namesT k) y.1 y.2
    theorem memParent_runFacts1 / memParent_outsG1 / memParent_maskedG1 / memParent_designP1
        (hcore) (hpost) (entry) (closes) [(hg)] (hB : ChildBnd mref cref w) (hRc) (hRm) : …   -- the four run hypotheses
    #noports_open_as memParent_design_noPorts1 := memParent 1 memParent_runFacts1 memParent_outsG1
      memParent_maskedG1 memParent_designP1 [ ]
    theorem memParent_design_noPorts1_closed : bnd_only% memParent_design_noPorts1 [cnt, memCounterH]
    #assert_check_free memParent_design_noPorts1_closed
    #print axioms memCounterH_factsT
    #print axioms memParent_design_noPorts1_closed

The last statement, unfolded (what `bnd_only%` builds from the stored
statement of `memParent_design_noPorts1`; `Tools/ShippingBndOnly.lean`):

    ∀ {mctx mref cctx cref} {w w'} {b design},
      RunsTo (synthesizeCombinational memParent) mctx mref cctx cref w (b, design) w' →
      MachineDefines mctx mref cctx cref memParent memParent.machineData.shape →
      MachineDefines mctx mref cctx cref cnt cnt.machineData.shape →
      MachineDefines mctx mref cctx cref memCounterH memCounterH.machineData.shape →
      ∃ raw D, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
        (ChildBnd mref cref w → <the head's conclusion: ∃ ids, … DesignSV (childMap D.modules) 1 (checkedOptimize b) …>)

Its proof: `memParent_design_noPorts1 hr hP (memParent_closes hRc hRm)`, then
the boundary of §2.6 given component by component (`hB`, `hRc`, `hRm`,
`memCounterH.noPortsMem_closes`, the identity). The data conditions of
`memCounterH` are taken from the built `memCounterH.noPortsMem_data`
(`MemOnlyData`, the probe's step C5) with `decide` as the fallback.

`memParent_designP1` uses the BUILT `kidsT_designCheck` (with `namesT`,
`hname` from `memParent_kidIface`, `hsep` by `ofDecl_not_mem_allMem`), so
that step 3 does not depend on the new `Tools/ShippingCallSelf.lean`.

### 3.6 `Tests/Compiler/MemGrandFreeTest.lean`

    theorem memGrand_calls : memGrand.machineData.shape.insts.map (·.1) = [cnt, cnt, memParent]
    theorem memParent_self : ofDecl memParent ∉ namesOf memParent.machineData namesT
    theorem memParent_genKidT (hRp) (hRc) (hRm) :
        GenKidT mref cref memParent memParent.machineData 4 namesT kidOutsP kidInsP 1
    theorem memGrand_kidsT (hRc) (hRp) (hRm) : ∀ k hk,
        KidFactsT mref cref (memGrand.machineData.shape.insts[k]).1 (kidOutsGr k) (kidInsGr k) 2
    theorem memGrand_runFacts2 / _outsG2 / _maskedG2 / _designP2 …      -- _designP2 by kidsT_designCheckO
    #noports_open_as memGrand_design_noPorts2 := memGrand 2 … [memCounterH]
    theorem memGrand_design_noPorts2_bnd : bnd_only_closing% memGrand_design_noPorts2 [cnt, memParent, memCounterH]
    #log_check_free memGrand_design_noPorts2_bnd

`memGrand_design_noPorts2_bnd`: the run, `MachineDefines` of `memGrand`,
**`MachineClosesAt … memGrand …`**, `MachineDefines` of `cnt`, `memParent`,
`memCounterH`; under `∃ raw D`: `ChildBnd` only; `DesignSV … 2 …` conclusion.

## 4. Build order, `lean_lib` lines

1. `Tests.Compiler.MemKidCheckProbe` (imports the built probe,
   `Tools.ShippingKidFactsT`, `Tools.ShippingDesignSVMem`) — independent of
   everything else here; cheap.
2. `Tools.ShippingGenKidM` (imports built files only).
3. `Tools.ShippingBndOnly` (imports the built `Tools.ShippingNoPortsDeepCommand`,
   `Tools.ShippingDesignCoverage`).
4. `Tests.Compiler.MemParentFreeTest` (2, 3, the built `MemParentClosesTest`
   and built Tools files) — it does NOT depend on 5 and 6.
5. `Tools.ShippingCallSelf` (imports the built `Tools.ShippingKidFactsT`).
6. `Tools.ShippingGenKidT` (imports 5 and the built `Tools.ShippingGenKid`).
7. `Tests.Compiler.MemGrandFreeTest` (4, 5, 6).

    lean_lib «Tools.ShippingCallSelf» where
      roots := #[`Tools.ShippingCallSelf]

    lean_lib «Tools.ShippingGenKidT» where
      roots := #[`Tools.ShippingGenKidT]

    lean_lib «Tools.ShippingGenKidM» where
      roots := #[`Tools.ShippingGenKidM]

    lean_lib «Tools.ShippingBndOnly» where
      roots := #[`Tools.ShippingBndOnly]

Nothing for `Tests/AllTests.lean` (three target-only tests).

## 5. PREDICTED outcomes (all [P])

### 5.1 `MemKidCheckProbe`

| line | PREDICTED |
|---|---|
| S1, S2 | `true (kernel decide)`, `false (kernel decide)` |
| M1 `leafCheck mem`, M4 `kidCheck CM 0 mem` | `true` — most likely `true (by the built theorem leafCheck_memModule …)`: `leafCheck` evaluates `sanitizeName` on strings, which the built proof does by `simp` lemmas; `decide +kernel` may still do it [?] |
| M2, M3, M3', M5, M5', M6, M7 | `false (kernel decide)` — the first conjunct `body.all seqStmtOkI` reduces to `false` on the memory statement and `&&` does not look at the rest |
| K1, K2, K3 | `false (kernel decide)` (`seqStmtOkA (.inst …) = false`) |

M5 / K3 `false` is worker C's claim, measured. If M5 were `true`, `KidFactsT`
would be unnecessary; if K3 were `true`, depth index 0 would do.

### 5.2 Tools files

| file | PREDICTED | weakest points |
|---|---|---|
| `ShippingGenKidM` | builds | (i) `core_calls_portsGM`: 200 copied lines under the source file's own `open` set — a name that resolved through the source file's NAMESPACE (not its opens) would be unknown; I found none; (ii) `kids_run_kidM`: `rw [heq, full.name]` then `List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩` — the phrase of the built `kidsChild_ifaceM` 229–231, against a goal `nameK k ∈ namesOfP …` that must unfold; (iii) `GenKidM.outsIn`: the 23 arguments of `kidsChild_of_realM` in order |
| `ShippingCallSelf` | builds | `hyS.1`, `hyS.2` have the design written as the built proof's (the `rw [hyn, hfind] at hyfind` of the built text is kept on a copy); the final anonymous constructor's nesting |
| `ShippingGenKidT` | builds if `ShippingCallSelf` does | `rw [← e, e2]` on `kidCheck (childMap ms) n mc = true` |
| `ShippingBndOnly` | builds | Meta API only (`forallTelescope`, `withLocalDeclD`, `mkForallFVars`, `Expr.find?`); the `elab … : term` with `ident,*` between brackets; no new keyword is declared (separators `:=`, `[`, `]`) |

### 5.3 `MemParentFreeTest`, line by line

| item | PREDICTED | if not |
|---|---|---|
| `cnt_leafKid` | OK (the generator's term) | a `decide` position |
| `memCounterH_genKidM` | OK | a field of `memCounterH.noPortsMem_data` not of the expected type falls back to `decide` (each field is `first | exact … | decide`); `hkD … hNIn` are the six `decide`s of the built `memCounterH_iface` |
| `memCounterH_factsT` | OK (`0 + 1` against `1`: by reduction) | |
| `memParent_kidsT`, `memParent_kidIface` | OK (the generator's `cases k`; the second is the built block of `memParent_closes`) | the tables `kidOutsP` / `kidInsP` are `noncomputable def`s (the generator inlines the lambda): a unification that does not unfold them |
| `memParent_runFacts1` … `_designP1` | OK | `callWidthsOk` / `callArgsOk` by `decide`: FALSE would mean the tables are wrong (`declWidths cnt`, `argWidths memCounterH 3`) — the error is then at that `show … from by …` |
| `#noports_open_as … memParent_design_noPorts1` | OK: `NOPORTS OPEN …` | "asks … which is neither a conjunct of the endpoint's boundary … nor a grandchild's reflection": the boundary is not as §2.6 says |
| `memParent_design_noPorts1_closed` | OK | the `refine`: the message shows the real boundary |
| `#assert_check_free` | `CHECK-FREE OK …: proposition binders 4, antecedents under the existentials 1, NOT ALLOWED 0, checker / closing constants [], DesignSV mentioned: true` | an error naming what is left |
| `#print axioms` (two) | `[propext, Classical.choice, Quot.sound]` | |

### 5.4 `MemGrandFreeTest`

| item | PREDICTED |
|---|---|
| `memGrand_calls` | OK [P by the analogy with `memParent_calls`; if it fails the tables are wrong and nothing after it means anything] |
| `memParent_self`, `memParent_genKidT` | OK; weakest: the six split `decide`s (`hkD … hNIn`) for `memParent` at `nDecl = 4` — never decided before for it |
| `memGrand_kidsT`, the four run theorems | OK |
| `#noports_open_as … memGrand_design_noPorts2 … [memCounterH]` | OK |
| `memGrand_design_noPorts2_bnd` | OK; weakest: the nested boundary (the inner one is `memParent`'s, in the contexts `memParent` is synthesised in) |
| `#log_check_free` | `CHECK-FREE LOG …: DOES NOT PASS — proposition binders 6, antecedents 1, NOT ALLOWED 1, checker / closing constants [Tools.ShippingChildInv.MachineClosesAt], DesignSV mentioned: true` |

## 6. The obstacle for `memGrand` (exact)

Missing statement:

    theorem memGrand_closes (hRc : MachineDefines … cnt …) (hRp : MachineDefines … memParent …)
        (hRm : MachineDefines … memCounterH …) :
        MachineClosesAt mctx mref cctx cref memGrand memGrand.machineData.shape

The built `machineClosesAt_of_kidsD` [R `ShippingCallsKidsD.lean` 98–135] at
`memGrand`'s data asks, for the entries `k` (`cnt`) and `k'` (`memParent`),

    hdisjD : (insts[k]).1 ≠ (insts[k']).1 → ofDecl (insts[k]).1 ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k'

and `hkid` forces `namesK k'` to contain every module name of `memParent`'s
design (`ChildIfaceD.desNames`), among them `ofDecl cnt`: the first conjunct
is FALSE. No memory is involved: it is `mixDeep`'s collision (a callee that
is also a descendant of another callee). What `memGrand` shows beyond
`mixDeep`: the check side of that shape is NOT blocked (`core_callSelf`), only
the closing is. With `memGrand_closes`, the closed endpoint is three lines
(`memGrand_design_noPorts2_bnd hr hP (memGrand_closes …) …`).

A second `memGrand`-like declaration WITHOUT the collision (a parent of
`memParent` and of a leaf that `memParent` does not call) would close with
the built theorem; none is in the probe, and adding declarations to a built
test was not in scope.

## 7. Task 5 (the generator): not written

What it would emit is exactly the terms of the two tests: per memory-machine
kid `k.machine_genKidM0` (the `GenKidM` instance: data fields from
`k.noPortsMem_data`, `kid` by `memKidNamesP`, `kidsLo` by `memKid_facts`,
`closes` `k.noPortsMem_closes`); per general-closing kid without a memory
entry `k.machine_genKidT{n-1}`; the per-entry tables and `machine_kidsT{n}`;
the four run theorems with `kidsT_*` / `kidsT_designCheckO`; `endpointTermX`;
then the boundary step (`bndOnlyType` + the components), which the built
`closedTerm` does not do — the kid's closing sits INSIDE the boundary here
(`And closesAt bndHere`, `ShippingMachineDepthCommandR.lean` 682), because the
kid has no `machine_closes_at` / `closes_deep`. The alternative for the
integrator: register `memCounterH.noPortsMem_closes` and `memParent_closes`
under a name `closingThm?` finds BEFORE `#machine_design_svNR`, so that the
depth endpoint's boundary no longer carries the kid's closing (then the built
`closedTerm` suffices). Which name is safe was left open by worker C
(`C-mem-depth-ships.md` §7.1) and is not decided here.

## 8. Risks, in order

1. **The boundary's shape (§2.6)** is read off the generator, not printed.
   The closed theorem's `refine` is where a difference shows.
2. **`core_calls_portsGM` / `kids_run_kidM` / `kidsM_designCheck_in`**: long
   copies. Each edit is asserted; what is not asserted is that the copied
   text elaborates under my section's `open`s exactly as under the source
   file's namespace.
3. **`bnd_only%`**: a term elaborator used as a theorem's type; it reads the
   stored type of the open endpoint (`∃ raw D, P ∧ (Bnd → R)`) by
   pattern — `Bnd` is `headBeta`-normalised before `ChildBnd mref cref w` is
   looked for in it.
4. **Kernel reduction of reflected data** in `exact` (the entries' callees,
   the tables): the built generators rely on the same reductions for the same
   declarations' shapes, but with inline lambdas for the tables.
5. **`core_callSelf`** rests on reading that `closeInstsG_names … y hy` is
   stated over the same design expression the conclusion names (`D`); the
   built `core_kids_self` closes a goal over `D.modules` with it (116–117).
6. `MemKidCheckProbe`: the `true` lines may come out by the built theorem
   rather than by `decide`; the log says which.
7. `#noports_open_as` adds a theorem with `addTheorem` under the current
   namespace; a rerun in the same environment is an error ("exists already").

## 9. Not determined by reading

* Whether anything builds; every [P] of §5.
* The exact stored shape of the boundary (risk 1), and whether `cnt`'s
  premise in it is the reflection alone (`free`) — the proof tries both.
* `proveGroup` / `entryProof` (`ShippingMachineDepthCommandR.lean` 330–505):
  not read; they are behind the built `memParent.machine_composedNR1` [M].
* Whether a closing theorem tolerant of a shared descendant exists under
  another name (the "cache-coherence route" for `mixDeep`): not searched
  beyond `machineClosesAt_of_kidsD` / `…_kidsDM`.
* Whether the census (`#design_coverage`) should count a hand theorem: mine
  are named `…_design_noPorts…` in a test namespace, so `isDesign`
  (`machine_design_` prefix) does NOT pick them up — by intent ("no generator
  names"); coverage of `memParent` in the census needs the generator or a
  registration under `memParent.machine_design_…`.

## Integrator's build record (2026-10-13) — MEASURED

BUILT on poc 91d0f907 + these files, cgrun 3 GiB swap 0, runs `d1` (exit 0, peak 0.76 GB) and `d1ax`;
worker's files UNCHANGED, FIRST ATTEMPT, all seven targets (`MemKidCheckProbe`, `Tools.ShippingGenKidM`,
`Tools.ShippingBndOnly`, `MemParentFreeTest`, `Tools.ShippingCallSelf`, `Tools.ShippingGenKidT`,
`MemGrandFreeTest`). Every prediction confirmed.

* `MemKidCheckProbe` (kernel-decided): on the memory module — `body.all seqStmtOkI` false, `textCheckI`
  false (both child maps), `kidCheck … 0` true (by the built `leafCheck_memModule`), `kidCheck … 1` false,
  `kidCheck … 2` false, `designCheck … 0` false; on an instance-bearing module — `leafCheck` false,
  `kidCheck … 0` false. So worker C's claim is MEASURED: no depth index passes both the memory module and
  a module with an instance; `KidFacts` of a kid with a memory below it is false.
* `MemParentFreeTest` (asserting): `memParent_design_noPorts1_closed` —
  `CHECK-FREE OK: proposition binders 4, antecedents under the existentials 1, NOT ALLOWED 0, checker /
  closing constants [], DesignSV mentioned: true` (the census's own `recheck`); axioms
  `[propext, Classical.choice, Quot.sound]` (also printed by the integrator, with the statement: binders
  the run of `synthesizeCombinational memParent`, `MachineDefines` of `memParent`, `cnt`, `memCounterH`;
  `ChildBnd` under `∃ raw D`).
* `MemGrandFreeTest`: `memGrand_design_noPorts2_bnd` — `DOES NOT PASS: NOT ALLOWED 1, closing constants
  [MachineClosesAt]` (logged, as intended): every check antecedent discharged, the closing of `memGrand`
  itself still a premise.

Endpoint — premise — state: for `memParent` (a register parent of a memory-machine child and of `cnt`),
the check antecedents and the closings of the depth endpoint are GONE from
`memParent_design_noPorts1_closed`; premises the run, three reflections, `ChildBnd`. BY HAND, in a
target-only test, under a non-generator name: it is NOT in AllTests and NOT a census row.
SCOPE: one declaration (a probe declaration), depth 1, data conditions decided per declaration, runtime
boundary, `DesignSV` of the module list — not the SV string, not `#sim`.
`memGrand`: OPEN — its closing needs sibling separation, false because `cnt` is a callee and a callee of
the callee `memParent` (the `mixDeep` obstacle, not a memory fact); the check side is not blocked.
