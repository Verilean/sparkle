# General compiler theorem: target, induction, reuse boundary and roadmap (frozen plan, spec only)

Issue `sparkle-gen2-general-spec` (milestone `sparkle-gen2`).
- **Base:** `poc/roundtrip-proof` fea429dae6288095f8265e6c8916bc44bcc0c50e.
- **Branch:** `par/gen2-spec`.
- **Changes:** docs only. No Lean, no production edit, no build.
- **Inputs:**
  - the gap table docs/ShippingCompiler-Gaps-2026-10-28.md (G1-G8, N1);
  - the G8 census scripts/gaps/G8_CENSUS_RESULT.md;
  - the IP shape survey scripts/gen2/SURVEY_RESULT.md (`par/gen2-survey` 69dfa43e, diagnostic only).

**What this document is not:**
- It is NOT a proof, and completing it completes nothing of the general theorem.
- The survey and the census are measurements. They do not count as progress of the proof either.
- C4/C5 are class theorems and are NOT the general theorem. Adding further classes is not a route to it (§0).

Every file:line below is at fea429da.

## 0. Why the plan changes
- **What C4 and C5 are:** `memSharedLeaf_ships` (C4) and `qSharedLeaf_ships` (C5) are ∀-class theorems. Their classes fix
  the arrangement top → paired wrappers → one shared leaf, at depth `n = 2`.
- **What the measurements showed:**
  - The census found 20 T0 candidates, all test tops, and no IP top in the measured modules.
  - The survey found that the 12 H.264/RV32 IP tops are one-level machines whose every call entry is a memory instance.
    The YOLOv8 top is the same, but slotless.
- **The decision:** stop adding classes. Target one theorem over every successful compilation, built from a common
  one-level composition rule and an induction over the real child runs. The C4/C5 proofs are reused where they are
  generic in `n` (§4). The shared-leaf, depth-2 glue is not reused.

## 1. The final goal (FG) and the first theorem (T1), stated separately

### 1.1 FG: every successful compilation (target, not shrunk)
For the default command entry `Sparkle.Compiler.Elab.synthesizeCombinational declName`
(Sparkle/Compiler/Elab.lean:8920, with its two post-processing steps) and the parametric entry
`synthesizeCombinationalWithParameters` (:8940):

```
FG : ∀ declName mctx mref cctx cref w b D w',
  RuntimeLaws mref cref w            -- G5, exact Props below
  → RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w'   -- the compilation SUCCEEDED
  → Reflects declName                -- G3, per route, exact Props below
  → Ships declName b D               -- conclusion, §1.3
```

- **`RuntimeLaws mref cref w` (G5):** these are the binders C4/C5 carry today, named exactly:
  - `O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref`;
  - `T : RefLawsATele O.quiet mref cref`;
  - `hA : AdmCtx O.quiet mctx cctx`;
  - `hw : JQC O 0 w`.

  They are a uniform law about the runtime, the same for every declaration. Their joint satisfiability and their fit to
  Lean's real runtime are OPEN (gap table G5).
- **`Reflects declName` (G3):** a per-route reflection premise for every declaration that the run reaches (the top and
  every child it synthesises). These are per-declaration premises, not a uniform law. FG is therefore conditional on them
  until milestone M5 discharges them (§6).

  | route | exact premise |
  |---|---|
  | machine | `MachineDefines mctx mref cctx cref c d.shape` (Tools/ShippingMachineEntry.lean:2345) and `GenFacts d … src` (Tools/ShippingQuadComposed.lean:106) for the data `d` the reader yields |
  | mixed gate | `GateDefines …` (Tools/ShippingGateDefines.lean:72) |
  | certified gate | its certified-shape reflection (exact Prop fixed in M4) |
  | legacy | the `LegacyDom` contract of `legacy_translate_contract` (Tools/ShippingLegacySemContract.lean:327), including `ReachesUnfold` (G2) |
- **Success only:** runs that fail, hit the depth limit (`sparkleSynthDepthLimit = 1024`, Elab.lean:970, :5465) or throw
  are outside FG. They produce no design.

### 1.2 What the conclusion compares
- **The emitted side:** the IR run of the emitted top, `runModuleTG (KSn (childMap D.modules) n) … (checkedOptimize b).body
  …`, at the height `n` of its instance tree (§3.3).
- **The source side:** the denotation `src` of the reified data that the route read, which GenFacts ties to the
  declaration's body (`body_eq : d.shape.body = quote … d.packed`).
- **What this is not:** a statement about the printed SystemVerilog. The printer is G7, TRUSTED, and is audited in M5.
- **Initial conditions:** the C4 conjunction, unchanged:
  - `SourceInputs` for the declaration's inputs;
  - `rst`/`clk` at 0;
  - registers at their slot inits;
  - `ResetNk n raw D kids`;
  - in-range inputs.

### 1.3 `Ships c b D` (the predicate the induction carries)
`Ships c b D` holds when the module and design emitted for `c` satisfy both of these:
- **(a) The C4 conclusion form:** `∃ ids … regs …, ∀ i bools bits T ins st0 mems kids, conditions → ∃ envsO, runModuleTG …
  = some envsO ∧ outputs = src`, at some height `n`, with `src` the denotation of `c`'s reified data. This is exactly the
  conclusion of `machine_ships_hierC_noHstR` (Tools/ShippingSrm33Core.lean:24-110).
- **(b) The child interface:** `SeqChildRunN children D n b (bsC c) (outsC c) (S c)` (Tools/ShippingMachineDepth.lean:64),
  with `bsC`/`outsC`/`S` computed from `c`'s own data. This is what a parent consumes through
  `SeqFactsRN … PC`.
  - For a memory child, (b) is replaced by `MemFacts` (Tools/ShippingMachineCallsLinkedT.lean:31).
  - For a combinational one-output child, (b) is replaced by the closing interface used by `closeInsts`.

### 1.4 T1: the first theorem to prove (a fragment, explicitly NOT FG)
T1 is FG restricted to runs where the top and every descendant take the machine route or are memory instances, with
`Reflects` = `MachineDefines` + `GenFacts` for each of them.
- It is proved for every such tree: any depth, any mix of memory and ordinary children, shared and cached children.
- Slotless parents are included only after M2's unit (c).
- T1 is the deliverable of M3. Every other route is M4.

## 2. Dispatch coverage (every way a successful run is produced)
Source: `synthesizeFromConst` (Elab.lean:5288-5345), `synthesizeChild` (:8929).

| # | route (order of `synthesizeFromConst`) | condition | in FG | plan | evidence today |
|---|---|---|---|---|---|
| 1 | certified gate | `certifiedShape? … = some` (:5293) | yes | M4 | per-declaration gate theorems; no ∀-declaration theorem examined here |
| 2 | mixed gate | `mixedCertifiedShape? … = some` (:5300) | yes | M4 | `GateDefines` class; per-declaration existence-only / all-run (Tools/ShippingGateCoverage.lean:411 tally) |
| 3 | machine | `machineShape? … = some` and `synthesizeMachineCertified … = some` (:5310-5323); only `certifiedFrontEnd && !symbolicMode && parameters.isEmpty` | yes | **M2, M3 (T1)** | C4/C5 class theorems; generic consumers (§4) |
| 4 | machine shape read but synthesis refused (`closeLets` rejects, `MachineCloses` false, :2363) | falls through to 5/6 | yes (as 5/6) | M4 | `machineCloses_of_noLets` (:2371) for shapes without lets and calls |
| 5 | memo hit `sparkleSubModuleCache` (:5329-5335) | not symbolic, cached | yes | M3 (cache invariant, §3.2) for machine entries; M4 for legacy entries | G2 "memo-hit disjunct" OPEN |
| 6 | legacy | every other `defnInfo` (:5337-) | yes | M4 | `legacy_translate_contract` CONDITIONAL on `LegacyDom` (G2) |
| 7 | parametric / symbolic entry (:8940) | machine route disabled | yes | M4 | not examined |
| 8 | child served from `sparkleChildCache` (`synthesizeChild`, :8929) | any route | yes | M3 (`CacheShips`, §3.2) | `CacheInvA` / `RealChildA` (Tools/ShippingChildCacheA.lean:105, :115) |
| 9 | depth limit reached, non-`defnInfo`, exception | no design | **no** (not a success) | — | `core_tripleK0` closes the overflow branch |

## 3. Cases and the induction

### 3.1 Case table (machine route, T1)
| case | example | one-level supplier | status |
|---|---|---|---|
| ordinary leaf (`insts = []`) | the `leafP` shape | `seqChildRunN_of_flat` (Tools/ShippingMachineDepth.lean:83, any n), `genTrace` + `nm_machineRun` | generic pieces exist; leaf `Ships` packaging OPEN (M2-a) |
| memory leaf / memory-only parent, `slots ≠ []` | `leafM`; the 12 H.264/RV32 IP tops | `memCallee_composedNW` (Tools/ShippingSrm4Run.lean:75, any depth), `memCallee_closesA` (Tools/ShippingSrm3Callee.lean:91), `memCallee_kidFactsNC` (Tools/ShippingSrm4Kid.lean:60), `core_runFacts_ranAM` (Tools/ShippingSrm4Core2.lean:601) | used only as a CALLEE; as a top: Bd/Inv/hRI and the parent RunFacts wrapper are MISSING (§4.3) |
| slotless (`slots = []`) | YOLOv8 `activationDoubleBuffer` | none: `MemCalleeData.slotsNe` (Srm3Callee:52), `hsl` (Srm4Parent:37, Srm4Core2:610, SeqChildDeepRunA:51) all require slots | OPEN (M2-c) |
| ordinary children only | C4 wrappers → leaf | consumer 2 with `SeqFactsRN` + `PC` (§4.2) | generic in n; supplied at n = 2 by shared-leaf glue only |
| mixed memory + ordinary children | `wrapQ` | consumer 2 per entry (`MemFacts ∨ SeqFactsRN`) | consumer generic; Bd for mixed kids exists only at `flatKS` (`kidsMixed`, Tools/ShippingMachineShipsHier.lean:827) |
| one-output combinational children (`instFields = []`) | gate children | `ServedReal1A` (Tools/ShippingServedRealA.lean:60), `closeInsts` | consumer 2 needs `hfe : instFields ≠ []`: a separate branch, OPEN |
| arbitrary depth / unequal heights | `grand` (depth 3) | one `kids : String → KT n` for all children; lifts exist only for flat, memory and `ComposedNW n ⇒ SeqChildRunN (n+1)` (`seqChildRunN_of_composedCA`, SeqChildDeepRunA:32) | no `SeqChildRunN n → SeqChildRunN (n+1)` lift: **G-LIFT** OPEN |
| shared callee, repeated calls, cache hit | `topshare*` | per-instance `RealChildA` (ServedRealA) | handled per instance in consumers; the cache invariant must carry `Ships` (§3.2) |
| child on another route (gate/legacy) | gate-route children of machine parents | needs `Ships` from that route | M4 |

### 3.2 Induction: object, measure, and its tie to the real run
- **Object:** a run `RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, D) w'` with `JQC`-type world data at
  depth `dv w = Dp`.
  - Children are synthesised inside that run by `synthesizeChild`: either served from the cache, or by a nested run at
    depth `Dp + 1`.
- **Measure:** `sparkleSynthDepthLimit - dv w`.
  - This is the induction `childKeepsP_all_of_tele` (Tools/ShippingChildPinC.lean:357) already performs: `∀ k D,
    limit - D = k → …`, step `D → D + 1`.
  - It is a measure on the REAL run, not on an assumed graph. A design with sharing is not a tree, but every fresh child
    run is strictly deeper. That is the decreasing argument.
- **Cache hits:** the cached result is not a sub-run. The invariant `CacheShips w := ∀ c r, (cv w).get? c = some r →
  Ships' c r` is carried exactly like `CacheInvA` (ChildCacheA:115):
  - it holds at the empty cache (depth 0, Elab.lean:5541);
  - it is preserved by every insertion, because the inserted result came from a run covered by the IH.
- **The induction statement** (M3):
  ```
  ∀ k Dp, limit - Dp = k → ∀ c mctx cctx w b D w', Laws → JQC O Dp w → CacheShips w →
    RunsTo (synthesizeCombinational c) … w (b, D) w' → Reflects* c → (Ships c b D ∧ CacheShips w')
  ```
  - `Reflects* c` is `Reflects` for `c` and every declaration the run reaches.
  - This is the only global premise of that kind. It is G3, stated per declaration and never per design structure.
- **The step:** the one-level rule (§3.3) applied to the parent, with each child's `Ships` coming from:
  - the IH at `Dp + 1` for a fresh run;
  - `CacheShips` for a hit;
  - `MemFacts` for a memory entry.

### 3.3 The one-level composition rule (the common lemma of M2)
```
step : ∀ c d b D n, Reflects c (d) → MachineDefines … c d.shape → hcore / hpost of c's run →
  (∀ k, entry k is a memory instance ∧ MemFacts … k ∨ ∃ c' (mc, Dc), RealChildA O c' (mc, Dc) ∧ Ships' c' mc Dc at height ≤ n) →
  Ships c b D at height n + 1
```

**How the rule is built:**
- `Ships` (a) comes from consumer 1. Its `composed` comes from consumer 2, with:
  - `hcalls`: `MemFacts` for a memory entry; `SeqFactsRN` for an ordinary entry, with `PC c' mc := Ships' c' mc …` and
    the run part from (b) of the child's `Ships`;
  - `hrunN`: the IH, through `realChildA_inv`.
- `Ships` (b) at `n + 1` comes from `seqChildRunN_of_composedCA` (needs `slots ≠ []`).

**Height:** children at different heights `≤ n` need G-LIFT, so that they can share the one `kids : String → KT n`.

## 4. Reuse: every premise of the two generic consumers, and where it will come from
Legend:
- **G:** generic, with decidable or data premises.
- **IH:** a child's run, from §3.2.
- **C:** a contract (G3/G5, exact Prop).
- **NEW:** to be proved, and listed as a gap.
- **OLD-S:** the shared-leaf/depth-2 supplier in C4, NOT reused.

C4 suppliers are cited from Tests/Compiler/C4ShipsTest.lean, C4ComposedTest.lean and C4ClosesTest.lean.

### 4.1 Consumer 1 `machine_ships_hierC_noHstR` (Tools/ShippingSrm33Core.lean:24, `{n}` general)
| premise | C4 supplier | general supplier | class |
|---|---|---|---|
| `n` | 2 (C4ShipsTest:131) | the tree height from §3.2 | IH |
| `hloc` | `KSn_local _ 2` | `KSn_local _ n` (Tools/ShippingHierStateG.lean:632) | G |
| `Bnd` | `C4Bnd P` (C4ShipsTest:33): O, T, AdmCtx, MachineDefines of leaf and wrappers, JQC | AdmCtx ∧ JQC ∧ `CacheShips` ∧ the top's MachineDefines; no per-child MachineDefines list (children come from the IH) | C + IH |
| `C`, `closes` | `True` | `True` | G |
| `Bd`, `Inv`, `hBd`, `hRI` | `kidsMaskedN` / `True` / `KSn_boundedIn` / `true_inv` | **NEW (G-BD):** a bound true for memory, ordinary and mixed kids at `KSn n` with `ResetImpliesInv (ResetNk n)`. Today `kidsMaskedN` is false for memory children (Tools/ShippingMemKidFacts.lean:18-23); `kidsMem`/`kidsMixed` exist only at `flatKS` (ShipsHier:719, :827, `memKS_boundedIn` :748) | NEW |
| `soundL` | `soundLA_of_class` = `genTrace` + `nm_machineRun` with wrapper callees | `genTrace` (QuadComposed:156) + `machineRunJQC_of_closesA` (ServedRealA) + `machineRanA_main` (Tools/ShippingParentRanA.lean:64); callee closing from the IH | G + C (GenFacts) + IH |
| `composed` | `composedNWRegs_of_class` (C4ComposedTest:286) | `composedNWRegs_of_composedNW` (Srm28Regs:77) + `hWd_of_wired` (Srm32Width:28) + `core_hierGate_anyAM` (Srm4Core2:47) over consumer 2 | G |
| `houtTy`, `hinitW` | `P.outTy`, `hinitW_of_ok` (Tools/ShippingC4InitW.lean:24) | decidable from `d` / `hinitW_of_ok` | G |
| `hcore`, `hpost`, `entry` | statement binders | the run under induction; `entry` is `Reflects` | C |
| `facts` (RunFacts) | `kidsNC_runFacts` (needs no memory) + `c4_hkid` | **NEW (G-RUNFACTS):** a parent-level assembly over `core_runFacts_ranAM` (Srm4Core2:601), with memory kids from `memKidTNC_facts` (Tools/ShippingSrm4Core6.lean:98) and ordinary kids from the IH | NEW |
| antecedents `Bnd`, `Bd b D` | `kidsMasked_of_class` | from G-BD and G-RUNFACTS | NEW |

### 4.2 Consumer 2 `machine_linkedT_callsRNA` (Tools/ShippingMachineDepthRunRA.lean:142, `(n)` general)
| premise | C4 supplier | general supplier | class |
|---|---|---|---|
| `O` | contract | contract | C |
| `h` (MachineTraceLBX + ServedRealA) | `c_traceXA` = `genTrace` on the run | the same, on the parent's run | G + C |
| `hfe`, `kD`, `hkD`, `hI`, `hIlen`, `hSL`, `hSlen`, `hLlen`, `hNIn` | `P.pdata.*`, `c_parent_*` (C4ComposedTest:136-163) | decidable / `d.ok`; `hfe` excludes the one-output branch (§3.1) | G |
| `bsC`, `outsC`, `S` | `P.bsC`/`outsC`/`srcC` (tied to wrappers) | computed from each child's own data, inside its `Ships` | IH |
| `PC` | `cPC` = `MachineRunNCA` of the wrapper | `Ships'` of the child | IH |
| `hcalls` | always `SeqFactsRN`, through `P.group`, `k/2`, depth 2 (OLD-S) | per entry: `MemFacts` (memory) or `SeqFactsRN` from (b) of the child's `Ships` | G + IH; **NEW (G-MEMCALLS):** `MemFacts` for every memory entry derived from `d` (today `MemCalls`, Srm4Run:50, is a generated GEN-SHAPE fact) |
| `hrunN` | `c_runWrap` = `machineRunNCA_of_real_main` | the IH applied through `realChildA_inv` | IH |

### 4.3 Named gaps (each one gets its own unit; none is a class field)
- **G-BD:** the memory/mixed kid bound and its reset implication at `KSn n`.
- **G-RUNFACTS:** the parent-level `RunFacts` on the A-boundary with memory kids.
- **G-MEMCALLS:** `MemFacts` from the reader's data, generically.
- **G-LIFT:** `SeqChildRunN n → SeqChildRunN (n+1)`, or an equivalent common-height argument.
- **G-SLOTLESS:** slotless parents.
- **G-ONEOUT:** one-output combinational children (`instFields = []`).
- **G-CACHE:** `CacheShips` preservation.
- **G-TOPSTART:** `memCallee_composedNW` used at a top start world (`JQC O 0 w`, `D₀ = 0`). Its statement admits it, but
  it has never been used there.

## 5. Roadmap (milestones; the provisional order, corrected against the sources)
Each stage lists its deliverable, acceptance, residue, risk, the alternative if it fails, and its link to FG. Stages that
measure are marked [measure]; stages that prove, [proof].

### M1 Specification (this Issue) [spec]
- **Deliverable:** this document.
- **Accept:** reviewer approval; the milestone goal is revised (§7).
- **Residue:** none proved.
- **Link:** it fixes FG, T1, `Ships` and the gap list that every later milestone refers to.

### M2 Common one-level composition rule (milestone `sparkle-gen2`) [proof]
- **Units, in order:**
  - **(a) Memory-only parent with slots** (first unit, §8): G-BD for memory kids, G-RUNFACTS for memory kids,
    G-MEMCALLS, G-TOPSTART. It gives `Ships` for any machine-route declaration whose every entry is a memory instance,
    and the ordinary-leaf `Ships`.
  - **(b) The general step** (§3.3): mixed memory + ordinary children, with the child `Ships'` as a HYPOTHESIS. It
    extends G-BD and G-RUNFACTS to mixed kids, and proves G-LIFT.
  - **(c)** G-SLOTLESS.
  - **(d)** G-ONEOUT.
- **Accept, per unit:**
  - a theorem over all `MachineData`/declarations of the case, with no class field that restates the conclusion;
  - binders limited to G3/G5 contracts and child `Ships'` hypotheses;
  - an audit of binders and axioms;
  - an exact-head build.
- **Acceptance of the milestone:** `step` is proved with no per-design binder, and (a) is applied to at least one IP
  top. That top's `GenFacts` is supplied by its generator and labelled as the G3 per-declaration premise.
- **Residue:** G3/G5 contracts.
- **Risks:**
  - G-BD may need a different `Bd` shape than consumer 1 assumes. Alternative: generalise consumer 1's `Bd`/`Inv` binder
    to masked-or-memory, or prove at `n = 0` (`flatKS`, where `memKS_boundedIn` exists) and lift.
  - G-LIFT may be false for `KT` as defined. Alternative: state `Ships` at the exact height and add a
    height-heterogeneous kid state. This is a semantics change and a large cost, which needs a user decision.
  - G-MEMCALLS may not be derivable from `d` alone. Alternative: a decidable data check computed from `d`, never a
    semantic field.
- **Link:** M3 applies `step` at every node.

### M3 Hierarchy induction: T1 (milestone proposal `sparkle-gen3`) [proof]
- **Deliverable:** the §3.2 induction on `limit - dv w` with `CacheShips` (G-CACHE). The result is T1, for every
  machine-route tree.
- **Accept:** a theorem whose only premises are `RuntimeLaws` and `Reflects*`, with no per-design binder.
  - The C4/C5 endpoints and an IP top are recovered as corollaries. The corollaries are checks, not the result.
- **Residue:** other routes (M4) and G3/G5 (M5).
- **Risks:**
  - `Ships` must be context-independent, so that a cache entry produced in one context serves another. `RealChildA`
    already quantifies contexts. Alternative: index `CacheShips` by `AdmCtx`.
  - `dv` must increase on every nested synthesis. To be verified against Elab.lean:5465-5541 in the first M3 unit,
    before any proof.
- **Link:** FG restricted to route 3, with memory instances.

### M4 Route coverage (milestone proposal `sparkle-gen4`) [proof + measure]
- **Deliverable:** `Ships` for routes 1, 2, 5, 6 and 7 of §2, as IH providers for children and as top theorems:
  - gate routes: `GateDefines` and the certified-shape reflection;
  - legacy: the G2 contract, `ReachesUnfold` and the memo-hit disjunct;
  - route 4 (closeLets refusal → legacy);
  - the parametric entry.
- **Accept:** FG for every route, conditional only on `RuntimeLaws` and `Reflects*`. A re-run of the G8-style census
  then reports how many corpus tops FG covers. That census is [measure], and it is not the proof.
- **Risk:** the legacy route may stay CONTRACT-only (G2). If so, FG holds with an explicit legacy contract, reported as
  such, and the user is asked whether to accept that guarantee level. That is a guarantee change.
- **Link:** removes the route restriction of T1.

### M5 Boundary premises and final endpoint audit (milestone proposal `sparkle-gen5`) [proof + audit]
- **Deliverable:**
  - discharge `Reflects` per route from the reader proofs: `readTerm_sound` (Tools/ShippingReaderTerm.lean),
    `readTerm_quote` (Tools/ShippingReaderComplete.lean), `driveShape_complete`;
  - fix the G5 laws' status: a model, or explicitly TRUSTED;
  - G7 (IR → `DesignSV` objects) and N1 `hfresh`;
  - the final endpoint audit: statement text, binder table, axioms, no per-design binder.
- **Accept:** the final theorem's premises are exactly the uniform G5 laws, with G7 trusted.
- **Risk:** G3 is not dischargeable for the production reader (`machineShape?` is `partial`, gap table G3).
  - Alternative: switch to the fuel-total reader candidate (`driveShape_complete`). That is a production change and a
    user decision.
  - Otherwise FG stays conditional on per-declaration `Reflects`. It must be reported so, not as complete.
- **Link:** FG with only uniform premises.

**Dependency corrections to the provisional order:**
- M4's gate/legacy `Ships` are needed INSIDE M3 for machine parents with gate or legacy children. M3 therefore delivers
  T1 (machine-only trees), and M4 extends the same induction with the other routes as additional IH providers. It is
  not a separate later induction.
- G-LIFT moves into M2-(b). It is needed by the one-level rule itself, not only by the induction.

## 6. G3/G5 as exact Props (never "G3"/"G5" by name only)
| premise | exact Prop | kind |
|---|---|---|
| runtime ops | `RefLawsAOps MkRefd mref cref` (Tools/ShippingChildInvA.lean) | uniform law |
| runtime tele | `RefLawsATele O.quiet mref cref` | uniform law |
| admissible context | `AdmCtx O.quiet mctx cctx` | uniform condition on the start contexts |
| start world | `JQC O 0 w` (ChildCacheA:120) | uniform condition on the start world |
| machine reflection | `MachineDefines … c d.shape` and `GenFacts d … src` | per declaration reached |
| gate reflection | `GateDefines … c bs body` | per declaration reached |
| legacy | `LegacyDom …` (Tools/ShippingLegacySemEntry.lean:138) | per declaration reached |

**How the result is reported:**
- While per-declaration premises remain, FG is reported as "conditional on the reflection of every reached
  declaration".
- IR correctness under the runtime laws, and correctness of the printed RTL (G7), are reported separately.

## 7. Milestone goal revision (proposal; applied after approval)
- **`sparkle-gen2` (now):** "G8 class extension: shared-leaf tops with memory entries". Proposed goal:
  > A one-level composition rule `step` (spec GENERAL_SPEC.md §3.3) is proved for machine-route parents with memory,
  > ordinary and mixed children, slotless parents and one-output children (M2 units a-d). It has no per-design binder:
  > child behaviour is a `Ships'` hypothesis, and G3/G5 are exact contract Props. Reviewer-accepted, with at least one
  > IP top shown as an instance. The general theorem FG is not complete at this milestone.
- **New milestones:** `sparkle-gen3` (M3, T1 induction), `sparkle-gen4` (M4, routes), `sparkle-gen5` (M5, boundary +
  final audit), with the goals of §5.

## 8. The immediate implementation unit (Issue proposal `sparkle-gen2-step-mem`, M2-a)
Its own freeze comes first. This section fixes its scope.
- **Statement:**
  ```
  memParent_ships :
    ∀ declName d n O T mctx cctx w …, RuntimeLaws → GenFacts d … →
      d.shape.layout.slots ≠ [] → (∀ k < d.shape.insts.length, entry k is a memory instance) →
      hcore → hpost → MachineDefines … declName d.shape → <C4 conclusion at n>
  ```
  - "Memory instance" means `memChild?` is `some` and `origin.child?` is `some memModule`, a decidable check on `d`.
  - The only per-declaration premises are `GenFacts`/`MachineDefines` (G3). Everything else is a decidable data check.
- **Proof plan:**
  - consumer 2 with `hcalls := Or.inl` (MemFacts from G-MEMCALLS) and `hrunN` vacuous, following the pattern of
    `memCallee_composedNW` (Srm4Run:93-94);
  - consumer 1 with G-BD (memory) and G-RUNFACTS (memory);
  - `soundL` from `genTrace` + `machineRunJQC_of_closesA`;
  - `closes` from `memCallee_closesA`, with `hord` vacuous.
- **Also in this unit:** the ordinary-leaf `Ships` (`insts = []`), which is the base case of M3.
- **Checks:**
  - corollaries for one H.264 top (for example `quantModule`, 2 memory entries) and for `leafM`, with their generated
    `GenFacts`;
  - a binder audit (no class field restates the conclusion);
  - `#print axioms`;
  - an exact-head build.
- **Expected new files:** `Tools/ShippingGen2MemParent.lean` and `Tests/Gen2/MemParentTest.lean`. No compiler or
  production edit.
- **Not claimed:** FG, T1, mixed children, slotless.

## 9. Decisions that would go to the user (none is needed now)
These change the goal, the guarantee or the cost:
- a semantics change for G-LIFT (height-heterogeneous kid state);
- accepting a legacy-route contract in FG (M4);
- a production reader switch for G3 (M5).

Everything else is coder/reviewer work inside this plan.

## 10. Not claimed
- No theorem, no build, no production change.
- FG is the target and is unproved. T1 is unproved.
- The class theorems C4/C5, the census and the survey are not progress on FG beyond the reusable generic pieces listed in
  §4.
- The order of §5 is a plan corrected against the cited sources. It is not a feasibility result.
