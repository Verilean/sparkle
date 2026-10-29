# General compiler theorem: target, induction, reuse boundary and roadmap (frozen plan rev1, spec only)

Issue `sparkle-gen2-general-spec` (milestone `sparkle-gen2`).
- **Base:** `poc/roundtrip-proof` fea429dae6288095f8265e6c8916bc44bcc0c50e.
- **Branch:** `par/gen2-spec`.
- **Changes:** docs only. No Lean, no production edit, no build.
- **Companion file:** scripts/gen2/GEN2_DEFS.lean.txt holds the EXACT Lean text of every definition and statement named
  here. Unit U0 (§8.1) elaborates it verbatim.
- **Inputs:**
  - the gap table docs/ShippingCompiler-Gaps-2026-10-28.md;
  - the G8 census scripts/gaps/G8_CENSUS_RESULT.md;
  - the IP shape survey scripts/gen2/SURVEY_RESULT.md (`par/gen2-survey` 69dfa43e).

**What this document is not:**
- It is NOT a proof.
- Completing it does not complete the general theorem FG.

Every file:line below is at fea429da.

**Rev1** answers review R1-R4 of 407497f2:
- the ordinary-call decoding is a separate obligation (§4.2, G-CALLDEC);
- fresh, cached and transported children are separated, with an exact interface (§3.2, G-SERVED, G-TRANSPORT, G-EXC,
  G-MEMO);
- exact statement text (GEN2_DEFS.lean.txt) and an inventory of GenFacts (§6);
- an inventory of the data conditions with coverage obligations (§4.4);
- a type-connection unit U0 placed before M2 (§5, §8).

## 0. Where this plan stands relative to existing results
- **C4/C5 are general theorems over limited classes.** `memSharedLeaf_ships` and `qSharedLeaf_ships` are ∀-class
  theorems; their classes fix top → paired wrappers → one shared leaf, at `n = 2`.
- **The census and the survey are valid progress on coverage.** They measured that those classes contain no IP top
  among the measured modules. They also showed that the 12 H.264/RV32 IP tops are one-level machines whose call entries
  are all memory instances.
- **The change of plan:** the target is FG, every successful compilation. Further classes are not added as a
  substitute for FG.
  - The C4/C5 work is reused where it is generic in `n` (§4).
  - Its shared-leaf, depth-2 glue is not reused.
  - None of this denies the existing results. They are complete for their classes, and not FG.

## 1. Final goal (FG, schema) and the first theorems (exact text)

### 1.1 FG: every successful compilation (target schema, not shrunk)
```
FG : ∀ (L : Laws mref cref) declName (parameters : List (String × Nat)) mctx cctx w b D w',
  Start L mctx cctx w →                                   -- §1.2
  ( RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w'            -- default entry, Elab.lean:8920
  ∨ RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w' )  -- :8940
  → ReflectsAll L declName parameters →                   -- G3, per route, per reached declaration (§6)
  → ∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D   -- (b, raw) related by the entry's post-processing
```

**What is and is not fixed:**
- FG is a SCHEMA. Its route-specific parts are fixed in M4:
  - `ReflectsAll` for the gate, legacy and parametric routes;
  - the source package of a non-machine route;
  - the relation `b ↔ raw` of the default entry's two post-processing steps.
- The machine-route parts are exact text now (§1.3).
- **Success only.** Failed runs, the depth limit (`sparkleSynthDepthLimit = 1024`, Elab.lean:970, :5465) and
  exceptions are outside FG. They produce no design.

### 1.2 Runtime laws vs. start conditions (G5)
- **`Laws mref cref`** (GEN2_DEFS §2) is the uniform G5 law, the same for every declaration:
  `O : RefLawsAOps MkRefd mref cref` and `T : RefLawsATele O.quiet mref cref`.
- **`Start L mctx cctx w`** := `AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w` is a condition on the START of an outermost
  compilation, not a law.
- Inner runs carry `AdmCtx` and `JQC L.O (dv w) w` as induction data (§3.2).

### 1.3 The exact first statements (GEN2_DEFS.lean.txt §1-§5)
- **`SrcPkg ι dom`:** the source package. It is C4's `GenPkg` (CDefTest.lean:33) moved to Tools, plus `kD`. Derived
  from it: `SrcPkg.extS`/`extBS`/`lsrc`, `ports`, `S` (the child-interface source, as C4's `tieSrcC`,
  CDefTest.lean:111).
- **`Pkgs ι dom`** := `Name → Option (SrcPkg ι dom)`: a package assignment. Its correctness on the reached declarations
  is G3.
- **`TopShips p n declName b raw D`:** exactly the conclusion of `machine_ships_hierC_noHstR` (Srm33Core.lean:85-114),
  with `d := p.d`, `src := p.src`, `ext := p.extS`, `extB := p.extBS` and `kD := p.kD`.
- **`ChildShips q n mc Dc`:** the child interface at height `n`, `SeqChildRunN (childMap dsn.modules) dsn n mc (q.d.bsIn.take
  q.kD) q.d.shape.layout.outs (q.S i)`.
  - It holds for EVERY design `dsn` that contains `Dc`'s modules and `mc`.
  - The transport from the child's own design to the parent's is therefore part of what a producer proves
    (G-TRANSPORT), not something the parent assumes.
- **`CallDec p q k`** (G-CALLDEC) and **`MemDec p k c`** (G-MEMCALLS): facts of the PARENT's package (§4.2).
- **`ShipsRes L P c r`** := `RealChildA L.O c r ∧ ∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2`, and
  **`CacheShips L P m`** := every `sparkleChildCache` entry satisfies `ShipsRes`.
- **`ServedShipsStmt`** (G-SERVED), **`StepStmt`** (the one-level rule), **`MemParentStmt`** (first proof unit),
  **`LeafStmt`** (base case, a separate unit) and **`T1Stmt`** (M3): all are `def … : Prop`, with no proof.

### 1.4 T1 (M3 deliverable; explicitly NOT FG)
`T1Stmt L P Reach DataOk`: every successful outermost machine-route compilation of a reached declaration ships at some
height. It is conditional on four named premises:
- G3: the package of every reached declaration, with its `MachineDefines` in every admissible context;
- `DataOk` (§4.4);
- the decodings G-CALLDEC and G-MEMCALLS;
- closure of `Reach` under calls (G-REACH).

The last three are to be DERIVED: in M2 for the data and the decodings, and in M3 for G-REACH, from the run. Until then
they stay named premises, and T1 must be reported as conditional on them.

## 2. Dispatch coverage (every way a successful run is produced)
Source: `synthesizeFromConst` (Elab.lean:5288-5345), `synthesizeChild` (:8929).

| # | route | condition | in FG | plan | evidence today |
|---|---|---|---|---|---|
| 1 | certified gate | `certifiedShape? … = some` (:5293) | yes | M4 | per-declaration theorems; no ∀-declaration theorem examined |
| 2 | mixed gate | `mixedCertifiedShape? … = some` (:5300) | yes | M4 | `GateDefines` (Tools/ShippingGateDefines.lean:72); per-declaration tally (Tools/ShippingGateCoverage.lean:411) |
| 3 | machine | `machineShape? … = some` and `synthesizeMachineCertified … = some` (:5310-5323), only `certifiedFrontEnd && !symbolicMode && parameters.isEmpty` | yes | **U0, M2, M3 (T1)** | class theorems C4/C5; generic consumers (§4) |
| 4 | machine shape read, synthesis refused (`MachineCloses` false, Tools/ShippingMachineEntry.lean:2363) | falls to 5/6 | yes, as 5/6 | M4 | `machineCloses_of_noLets` (:2371) |
| 5 | memo hit `sparkleSubModuleCache` (:5329-5335) | not symbolic, cached | yes | M3 (G-MEMO) for machine entries, M4 for the rest | G2 memo-hit disjunct OPEN |
| 6 | legacy | other `defnInfo` | yes | M4 | `legacy_translate_contract` (Tools/ShippingLegacySemContract.lean:327) on `LegacyDom` (:264) |
| 7 | parametric / symbolic entry (:8940) | machine route disabled | yes | M4 | not examined |
| 8 | child served from `sparkleChildCache` (:8929) | any route | yes | M3 (`CacheShips`, G-SERVED) | `CacheInvA`/`RealChildA` (Tools/ShippingChildCacheA.lean:105, :115) |
| 9 | depth limit, non-`defnInfo`, exception | no design | no (not a success) | — | `core_tripleK0` closes the overflow branch |

## 3. Cases and the induction

### 3.1 Case table (machine route)
| case | example | one-level supplier | status |
|---|---|---|---|
| ordinary leaf (`insts = []`) | `leafP` | `seqChildRunN_of_flat` (Tools/ShippingMachineDepth.lean:83, any n), `genTrace` (Tools/ShippingQuadComposed.lean:156) | `LeafStmt`, a separate unit (M2-a') |
| memory-only parent, `slots ≠ []` | `leafM`; the 12 H.264/RV32 IP tops | `memCallee_composedNW` (Tools/ShippingSrm4Run.lean:75), `memCallee_closesA` (Tools/ShippingSrm3Callee.lean:91), `memCallee_kidFactsNC` (Tools/ShippingSrm4Kid.lean:60), `core_runFacts_ranAM` (Tools/ShippingSrm4Core2.lean:601) | `MemParentStmt` (M2-a). Needs G-BD, G-RUNFACTS, G-MEMCALLS, G-TOPSTART and the §4.4 data |
| slotless | YOLOv8 top | none: `slotsNe`/`hsl` everywhere | M2-c (G-SLOTLESS) |
| ordinary children | C4 wrappers | consumer 2 + `CallDec` + `ChildShips` | `StepStmt` (M2-b) |
| mixed memory + ordinary | `wrapQ` | consumer 2, per entry | `StepStmt` (M2-b); G-BD for mixed kids |
| one-output combinational children (`instFields = []`) | gate children | `ServedReal1A` (Tools/ShippingServedRealA.lean:60) | M2-d (G-ONEOUT); consumer 2 needs `hfe` |
| unequal child heights | `grand` | one `kids : String → KT n` | G-LIFT (M2-b) |
| shared callee, repeated calls, cache hit | `topshare*` | per instance, the served `(mc, Dc)` | G-SERVED (M3) |
| child on another route | gate/legacy children | the `ChildShips` of that route | M4 |

### 3.2 The induction and the served-child connection (no circular obligation)
**The run under induction:**
- It is a run `RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w'`, with
  `AdmCtx`, `JQC L.O Dp w` (`Dp = dv w`) and `CacheShips L P (cv w)`.
- **Measure:** `sparkleSynthDepthLimit - Dp`. Its use as a measure follows `childKeepsP_all_of_tele`
  (Tools/ShippingChildPinC.lean:357). That lemma proves the preservation of a pin invariant, not the semantic property;
  only its shape (`∀ k D, limit - D = k → …`, step `D → D + 1`) is reused.

**How a child's result reaches the parent.** There are three distinct paths:
1. **Fresh miss.** `synthesizeChild` runs `synthesizeCombinational c'` NESTED in the parent's run, from a world at
   depth `Dp + 1`.
   - The IH (the measure is smaller) gives `ShipsRes` for its result, and `CacheShips` after it.
   - That run's result is inserted in the cache, so `CacheShips` is kept.
2. **Cache hit.** The returned value is the cache entry. `CacheShips` at the time of the hit gives `ShipsRes`.
   - This needs `CacheShips` to hold at EVERY point of the parent's run, not only at its start. The translator and every
     step of the parent's run must keep it.
   - That is a keep-invariant argument of the `KeepsCP`/`JQP` kind (ChildPinC), with the child step discharged by
     path 1. It is gap **G-CACHE**.
3. **Into the parent's design.** The served `(mc, Dc)` becomes an instance of `raw` in `D`. `ChildShips` is stated for
   every `dsn ⊇ Dc ∪ {mc}`, so it applies at `D`, given `Dc ⊆ D`.
   - `Dc ⊆ D` is today `hcons` from `realChildA_inv` (ServedRealA.lean, used at DepthRunRA:189-190).
   - Proving `ChildShips` for every extending `dsn`, in the producer, is gap **G-TRANSPORT**. A candidate base is
     `ExtendsAway` / `StepExtendsAway` (Tools/ShippingHierMono.lean:123, :128).

**Why `realChildA_inv` alone is not enough:**
- `RealChildA.run` (ChildCacheA:105) records a past run at an arbitrary depth, and its cache premise gives `RealChildA`
  only.
- It says nothing about `ShipsRes`, and it does not say that the run was deeper than the current one.

The chosen option is to STRENGTHEN the served-child evidence:
- **G-SERVED:** `ServedShipsStmt` (GEN2_DEFS §4). In a machine-route run from a `CacheShips` world, whose nested fresh
  runs ship (that hypothesis is the IH), every non-memory instance is served by THE result `(mc, Dc)` with `ShipsRes`,
  and `CacheShips` holds at the end.
- **How it is proved:** by re-proving the `ServedRealA` chain (ServedRealA.lean:45-74 and its producers) with the cache
  invariant `CacheInvA` generalised from `RealChildA` to `ShipsRes`.
- **The rejected alternative:** a separate history induction over `RealChildA` derivations. It does not reach the
  nested fresh runs, which are not sub-derivations, so it would still need the depth measure.

**The remaining invariants and premises:**
- **G-EXC:** `CacheShips` must also be kept on the exception and refusal paths that the parent's run catches. One
  example is the machine route returning `none` and falling back. A partially run child must not leave a non-shipping
  entry; the earlier cache-rollback fix (b7971f83) is relevant. Whether `KeepsCP` covers caught exceptions is checked in
  U0.
- **G-MEMO:** `sparkleSubModuleCache` (the memo of route 5) is a different map. `CacheShips` does NOT cover it. It
  needs its own invariant, or a proof that machine-route parents never read it for their children.
- **`hrunN`** of consumer 2 quantifies over ARBITRARY runs of the child in any admissible context. In `StepStmt` it is
  not supplied from the IH. Instead, `PC c mc` is instantiated to the served-result fact itself, and consumer 2's use
  of `hrunN` (DepthRunRA:189-190) is replaced. Whether consumer 2 can be applied with `PC := fun c mc => ∃ q Dc, …
  ChildShips q n mc Dc` and an `hrunN` derived from G-SERVED, or needs a variant that takes the served fact directly, is
  decided in U0. If a variant is needed, it is a NEW consumer lemma with the same proof, which re-routes the final
  `exact hrunN …`.

### 3.3 The one-level rule
`StepStmt` (GEN2_DEFS §5) has these premises:
- the parent's package, `DataOk`, and the run and its post-processing;
- `MachineDefines`;
- per entry: `MemDec` or `CallDec` to a package `q`;
- per served non-memory instance: `ChildShips q n mc Dc` with `Dc ⊆ D`.

It concludes `TopShips p (n+1)` and `ChildShips p (n+1)`.

**How it is proved:**
- **(a) TopShips:** consumer 1, with `composed` from consumer 2. Consumer 2's `hcalls` is `MemDec` (left disjunct) or
  `SeqFactsRN`, assembled from `CallDec` and `ChildShips` (§4.2).
- **(b) ChildShips at `n+1`:** `seqChildRunN_of_composedCA` (Tools/ShippingSeqChildDeepRunA.lean:32), for every
  extending design (G-TRANSPORT).
- **Unequal child heights:** children at heights `≤ n` are lifted to `n` (G-LIFT).

## 4. Reuse: every premise of the two consumers
Legend: G = generic, with proved premises; IH = from §3.2; C = contract (exact Prop, §6); NEW = a named gap; DATA = a
data condition (§4.4); OLD-S = C4's shared-leaf / depth-2 supplier, not reused. The C4 suppliers are cited from
Tests/Compiler/C4ShipsTest.lean, C4ComposedTest.lean and C4ClosesTest.lean.

### 4.1 Consumer 1 `machine_ships_hierC_noHstR` (Tools/ShippingSrm33Core.lean:24, `{n}` general)
| premise | C4 supplier | general supplier | class |
|---|---|---|---|
| `n` | 2 | height from §3.2 | IH |
| `hloc` | `KSn_local _ 2` | `KSn_local _ n` (Tools/ShippingHierStateG.lean:632) | G |
| `Bnd` | `C4Bnd P` (C4ShipsTest:33) | `AdmCtx ∧ JQC ∧ CacheShips` ∧ the top's `MachineDefines`, with no per-child list | C + IH |
| `C`, `closes` | `True` | `True` | G |
| `Bd`, `Inv`, `hBd`, `hRI` | `kidsMaskedN` / `True` / `KSn_boundedIn` / `true_inv` | **G-BD**. `kidsMaskedN` is false for memory kids (Tools/ShippingMemKidFacts.lean:18-23); `kidsMem`/`kidsMixed` exist only at `flatKS` (Tools/ShippingMachineShipsHier.lean:719, :827, :748) | NEW |
| `soundL` | `soundLA_of_class` | `genTrace` + `machineRunJQC_of_closesA` (ServedRealA.lean:97) + `machineRanA_main` (Tools/ShippingParentRanA.lean:64) | G + C (GenFacts) + DATA (`MemCalleeData` for `memCallee_closesA`, §4.4) |
| `composed` | `composedNWRegs_of_class` | `composedNWRegs_of_composedNW` (Srm28Regs:77) + `hWd_of_wired` (Srm32Width:28) + `core_hierGate_anyAM` (Srm4Core2:47) over consumer 2 | G |
| `houtTy`, `hinitW` | `P.outTy`, `hinitW_of_ok` | `houtTy` is a DATA condition (§4.4); `hinitW` comes from `hinitW_of_ok` (Tools/ShippingC4InitW.lean:24) and `GenFacts.ok` | DATA / G |
| `hcore`, `hpost`, `entry` | binders | the run; `entry` is G3 | C |
| `facts` | `kidsNC_runFacts` (no memory) | **G-RUNFACTS** over `core_runFacts_ranAM` + `memKidTNC_facts` (Tools/ShippingSrm4Core6.lean:98) + IH | NEW |
| antecedents | `kidsMasked_of_class` | from G-BD and G-RUNFACTS | NEW |

### 4.2 Consumer 2 `machine_linkedT_callsRNA` (Tools/ShippingMachineDepthRunRA.lean:142, `(n)` general)
| premise | general supplier | class |
|---|---|---|
| `O`, `h` | contract; `genTrace` on the parent's run | C + G |
| `hfe`, `kD`, `hkD`, `hI`, `hIlen`, `hSL`, `hSlen`, `hLlen`, `hNIn` | the §4.4 inventory; `hfe` false means case G-ONEOUT | DATA |
| `bsC`, `outsC`, `S` | `fun c => (P c).map (·.d.bsIn.take ·.kD)`, `….d.shape.layout.outs` and `(P c).S i`, from the CHILD's package | IH (package) |
| `PC` | the served-result fact (§3.2 `hrunN` paragraph) | IH via G-SERVED |
| `hrunN` | from G-SERVED, or a consumer variant (decided in U0) | IH |
| `hcalls`, memory entry | `MemFacts`, from `MemDec` (G-MEMCALLS) | NEW |
| `hcalls`, ordinary entry | `SeqFactsRN` (Tools/ShippingMachineCallsLinkedTNR.lean:23), conjunct by conjunct below | see below |

**The `SeqFactsRN` conjuncts and their suppliers:**

| # | conjunct | supplier |
|---|---|---|
| 1 | `(origin k).child? = none` | `CallDec` conjunct 1 |
| 2 | `∃ args, insts[k].args = some args` | `CallDec` conjunct 2 |
| 3a | `∀ mc, PC c mc → SeqChildRunN children dsn n mc (bsC c) (outsC c) (S c)` | `ChildShips` at `dsn` (IH + G-TRANSPORT) |
| 3b | `∀ mc, PC c mc → (argPorts mc).length = args.length` | `SeqChildRunN`'s conjunct `(argPorts mc).length = ports.length` (MachineDepth.lean:71) + `CallDec`'s `args.length = q.ports.length` |
| 4 | `∀ q < args.length, args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g` | `CallDec` |
| 5 | `∀ τ, InRange (valsOf lsrc args τ) ports` | `CallDec` |
| 6 | output field `k'`, `o.name = instFields[k]`, `S c (valsOf lsrc args)[k']? = some f`, and `∀ τ, posEnc (extB, ext) (kD + k) … = f τ` | `CallDec` |

**G-CALLDEC is a NEW obligation of the parent's package, not of the child.** It is the general form of C4/C5's
`CallFactF` (Tools/ShippingQuadCalls.lean:223) and `CallFactFO` (Tools/ShippingSrm4Mixed.lean:120).
- In C4 those came from the generated `HPointAt` residues (`callFactF_of_hPointAt`, Tools/ShippingQuadHPoint.lean:41)
  plus `group`. They are per design and NOT derived.
- `GenFacts` does NOT give G-CALLDEC. Its fields relate `body` to the evaluation of the terms (`writes`/`result`) and
  `src` to `obsR` of the state loop (`source`). No field relates a call result `ext (kD + k)` to the callee's `src`.
- G-CALLDEC is therefore a **producer-export gap**. The generator, or a new generic lemma over the reader's call
  terms, must export it. That is the M2 unit G-CALLDEC (§5), placed EARLY because its size is unknown.
- It must never become a class field or a semantic premise of `StepStmt`'s users. In `T1Stmt` it is a named premise
  only until that unit derives it.

### 4.3 Named gaps
| gap | content | milestone |
|---|---|---|
| G-BD | memory/mixed kid bound at `KSn n` + `ResetImpliesInv (ResetNk n)` | M2-a/b |
| G-RUNFACTS | parent `RunFacts` with memory kids on the A-boundary | M2-a/b |
| G-MEMCALLS | `MemDec` from the package | M2-a |
| G-CALLDEC | `CallDec` from the package (producer export) | M2-early |
| G-TOPSTART | `memCallee_composedNW` at `JQC O 0 w` | M2-a |
| G-LIFT | `SeqChildRunN n → SeqChildRunN (n+1)` or an equivalent | M2-b |
| G-TRANSPORT | `ChildShips` for every extending design | M2-b |
| G-SLOTLESS | slotless parents | M2-c |
| G-ONEOUT | `instFields = []` children | M2-d |
| G-SERVED | `ServedShipsStmt` | M3 |
| G-CACHE | `CacheShips` kept by every step of a run | M3 |
| G-EXC | `CacheShips` on caught exception / refusal paths | M3 |
| G-MEMO | `sparkleSubModuleCache` invariant | M3 |
| G-REACH | the reached set, from the run | M3 |
| G-DATA | coverage: every successful machine-route run ⇒ each DATA check is true (§4.4) | M2 (per check) |
| G3-GEN, G3-DECL | the package exists, and is the declaration's (§6) | M5 |

### 4.4 Data conditions (R4): decidable is not the same as true on every successful run
`MemCalleeData` (Srm3Callee.lean:34-75), `d.ok` (Tools/ShippingMachineAuto.lean:217) and the consumers' data premises,
classified:
- **E:** already a field of the package (`GenFacts`, generated per declaration).
- **R?:** a candidate to DERIVE from a successful machine-route run. U0 checks which, by reading `synthesizeMachineCertified`
  and the reader. Each derivation is a G-DATA lemma.
- **CASE:** a case split of the plan, not a data obligation.
- **D:** decidable only. A DATA field of `DataOk`. It needs a G-DATA coverage lemma ("every successful run ⇒ check =
  true"), or a recorded counterexample that shrinks the case. A counterexample is a scope change and must be reported.

| condition | where | class |
|---|---|---|
| `d.ok`, `body = quote …` | GenFacts `ok`, `body_eq` | E |
| `init` (`initOk`) | GenFacts `init` | E |
| `letsAliasOk` (Tools/ShippingMachineClosesData.lean:157) | MemCalleeData `alias` | R? (does `closeLets` acceptance imply it?) |
| `callsOk n` (Tools/ShippingCallsShape.lean:106) | `callsOk` | R? |
| `ss.length = slots.length`, `domB`, `hkD`, `hIlen`, `hSL`, `hSlen`, `hLlen`, `hNIn` | MemCalleeData; consumer 2 | R? (reader shape invariants; partly in `d.ok`) |
| `insts_ne`, `fne`, `slotsNe` | MemCalleeData | CASE (leaf / G-ONEOUT / G-SLOTLESS) |
| `outTy` | MemCalleeData; consumer 1 `houtTy` | R? |
| `outHead` (no output name starts with `i`) | MemCalleeData | D. It is a naming condition that a real design can violate. Candidate: an N1-style name lemma, or a coverage counterexample |
| `argsN`, `fieldOut`, `fieldsNd`, `sepK`, `parent`, `parentD`, `disjD`, `nameIn` | MemCalleeData kid tables | R? from the served results (memory: `memT` from `memModule`) |
| `memT` | MemCalleeData | R? from `memModule` (MachMemory) |
| `cw`, `nomemKey`, `group` (C4 fields) | C4 class | OLD-S; not used |

**No DATA field may restate a semantic conclusion.** `DataOk` is a conjunction of Bool checks over `p.d`, fixed in U0.
The derived ones are removed from it once their G-DATA lemma exists.

## 5. Roadmap (milestones, with dependencies corrected against the sources)
[spec] / [proof] / [measure] mark what each unit does. Every unit below is preceded by its own freeze.

### M1 Specification (this Issue) [spec]
- **Deliverable:** this document and GEN2_DEFS.lean.txt.
- **Accept:** reviewer approval; the milestone goal is revised (§7).

### M2 Common one-level rule (milestone `sparkle-gen2`)
Units in dependency order:
1. **U0 Type connection [proof, small]** (§8.1). Elaborate GEN2_DEFS verbatim, then prove the connection lemmas below.
   - `seqFactsRN_of_callDec`: `CallDec p q k ∧ ChildShips q n mc Dc ∧ Dc ⊆ dsn ⇒ SeqFactsRN …` with `PC :=` the served
     fact. This proves the §4.2 conjunct table is complete.
   - `memFacts_of_memDec`: by definition.
   - Decide `hrunN`: whether consumer 2 applies with PC as stated, or a consumer variant is needed.
   - Check whether `KeepsCP` covers caught exceptions (G-EXC).
   - Classify every `R?` row of §4.4 by reading the sources, with no proof.
   - **Accept:** a build; `#print axioms`; the deviation list.
   - **If it fails:** a mismatch in the interface types changes GEN2_DEFS before any M2 proof. A missing `hrunN` route
     is planned as the consumer variant.
2. **G-CALLDEC probe [measure → proof]**, right after U0:
   - for one ordinary-call parent, derive `CallDec` from the generated declarations (`machineExt`, `machineSource`) and
     the reader's call terms;
   - report the route, size and missing pieces;
   - then a generic proof, or a generator export (a compiler-side `Tools` generator change, no production change).
   - **If it fails:** a generator certificate per declaration. That leaves G-CALLDEC as a per-declaration G3-style
     premise and is reported as such. Choosing it is a guarantee change, so it goes to the user.
3. **M2-a `MemParentStmt` [proof].** Gaps G-BD (memory), G-RUNFACTS (memory), G-MEMCALLS and G-TOPSTART, plus the
   G-DATA lemmas for the memory-relevant rows.
   - **Corollary checks:** `quantModule` (H.264, 2 memory entries) and `leafM`, with their generated packages.
   - **If G-BD does not fit consumer 1's `Bd` shape:** generalise consumer 1's `Bd`/`Inv` binder (a new consumer with the
     same proof), or work at `n = 0` (`flatKS`) and lift.
4. **M2-a' `LeafStmt` [proof]**, a separate unit: `seqChildRunN_of_flat` + `genTrace` + G-TRANSPORT for leaves.
5. **M2-b `StepStmt` [proof]:** G-LIFT, G-TRANSPORT, G-BD/G-RUNFACTS for mixed kids, and `seqFactsRN_of_callDec` from U0.
   - **If G-LIFT is false:** state `ChildShips` at the exact height and add a height-heterogeneous kid state. That is a
     semantics change, and a user decision.
6. **M2-c G-SLOTLESS and M2-d G-ONEOUT [proof].**

**Acceptance of M2:** `StepStmt` is proved. Its premises are G3/G5 Props, `DataOk` (only `D` rows remaining, each with
a coverage lemma or a reported counterexample), and the IH-type child facts. At least one IP top is shown as an instance
of `MemParentStmt`.

**Residue after M2:** G-CALLDEC (if it took the certificate route), G-SERVED/CACHE/EXC/MEMO/REACH, and G3/G5.

### M3 Hierarchy induction: T1 (proposal `sparkle-gen3`) [proof]
- **Deliverable:** G-SERVED (re-proving the served chain over `ShipsRes`), G-CACHE, G-EXC, G-MEMO and G-REACH, then
  T1 by the §3.2 induction.
- **Accept:** `T1Stmt` is proved with premises exactly G3 (`P` correct on the reached declarations), `Laws`, `Start`,
  and the decodings (unless M2 derived them).
  - The C4/C5 tops and an IP top are recovered as checks, not as the result.
- **Risks and alternatives:**
  - The served chain may not generalise to a predicate. Alternative: carry `ShipsRes` as a second map invariant next to
    `CacheInvA`.
  - `dv` must increase on each nested synthesis (Elab.lean:5465-5541). This is checked in M3's freeze, before any proof.
- **Link:** FG on route 3 plus memory instances.

### M4 Route coverage (proposal `sparkle-gen4`) [proof + measure]
- **Deliverable:** packages and `ChildShips`/`TopShips` for routes 1, 2, 4, 5, 6 and 7. They act as IH providers for
  children, inside the SAME induction as M3, which is extended rather than redone. Also the FG `b ↔ raw`
  post-processing relation, and the parametric quantification.
- **Accept:** FG proved for every route, conditional only on `Laws`, `Start` and `ReflectsAll`. Then a G8-style census
  [measure] of the corpus tops FG covers. The census is not the proof.
- **Risk:** the legacy route stays CONTRACT-only (G2). Then FG holds with an explicit legacy contract, reported so.
  Accepting that is a guarantee change, for the user.

### M5 Boundary discharge and final audit (proposal `sparkle-gen5`) [proof + audit]
- **G3-SHAPE:** `MachineDefines`/`GateDefines` from reader soundness: `readTerm_sound` (Tools/ShippingReaderTerm.lean:1129),
  `readTerm_quote` (Tools/ShippingReaderComplete.lean:548), `driveShape_complete` (Tools/ShippingReaderFuelDriverComplete.lean:203).
- **G3-GEN, a separate work item (§6):** a package exists for every accepted declaration. That means
  `writes`/`result`/`source`/`causal` from a GENERIC body/denotation, rather than the generated `X.machine_*` theorems.
  This is generator soundness, not reader soundness.
- **G3-DECL:** the package's `body` IS the declaration's meaning. That is a meta-level fact, generated per declaration
  today.
- **G5:** a model of `Laws`, or an explicit TRUSTED status.
- **G7 and N1:** IR → `DesignSV`, and `hfresh`.
- **The final audit:** statement text, binder table, axioms, no per-design binder.
- **Accept:** FG's premises are only uniform laws, plus whatever G3 items are recorded as irreducibly per declaration,
  stated as such.
- **Risk:** G3-SHAPE for the `partial` production reader may need the fuel-total reader in production. That is a user
  decision.

**Dependency corrections:**
- U0 and the G-CALLDEC probe come BEFORE M2-a. The source/child interface, the served result and the design extension
  are type-checked first, so that M2 is not built on an interface M3 cannot supply.
- G-LIFT and G-TRANSPORT belong to M2-b, the one-level rule.
- M4 extends M3's induction; it is not a separate induction.
- G3-GEN (generator soundness) is separate from G3-SHAPE (reader soundness).

## 6. G3/G5 as exact Props, and the GenFacts inventory
| premise | exact Prop | kind |
|---|---|---|
| runtime ops / tele | `Laws.O : RefLawsAOps MkRefd mref cref`, `Laws.T : RefLawsATele O.quiet mref cref` | uniform law (G5) |
| start | `Start L mctx cctx w = AdmCtx … ∧ JQC L.O 0 w` | start condition |
| machine shape | `MachineDefines mctx mref cctx cref c q.d.shape` in every admissible context | per declaration (G3-SHAPE) |
| package | `P c = some q ∧ q.decl = c` with `q.gen : GenFacts …` | per declaration (G3-GEN) |
| gate / legacy | `GateDefines …`; `LegacyDom …` | per declaration (M4) |

**The `GenFacts` fields** (QuadComposed.lean:106-152). Its header says they are "NOT derived generically".

| field | content | kind | discharge |
|---|---|---|---|
| `ok`, `init` | Bool checks on `d` | computed | `decide` per declaration; G-DATA for every run |
| `body_eq` | `d.shape.body = quote … d.packed` | shape ↔ terms | reader completeness (`readTerm_quote`), G3-SHAPE |
| `writes`, `result` | `body` (the generated Circuit) evaluated = the evaluation of `d.nexts`/`d.outs` | semantic, generated | G3-GEN: a generic denotation body, with these as theorems |
| `source` | `src` = `obsR` of the state loop | semantic, generated | G3-GEN |
| `causal` | `HCausalOf d dom ext extB` | semantic, generated | G3-GEN |
| (link) | `body` is `X.machineBody`, the declaration's own value | meta-level | G3-DECL (per declaration) |

**Reporting rule:** FG/T1 are reported as conditional on the G3 rows that remain, row by row. IR correctness under
`Laws` is reported apart from RTL correctness (G7).

## 7. Milestone goal revision (proposal; applied after approval)
- **`sparkle-gen2`:** "U0 type connection, the G-CALLDEC probe, and the one-level rule `StepStmt`
  (GEN2_DEFS.lean.txt) for machine-route parents with memory, ordinary and mixed children, slotless parents and
  one-output children (M2 units)".
  - Child behaviour is a `ChildShips` premise, G3/G5 are exact Props, and the remaining `DataOk` checks each carry a
    coverage lemma or a reported counterexample.
  - Reviewer-accepted, with an IP top as an instance of `MemParentStmt`.
  - FG is not complete at this milestone.
- **New milestones:** `sparkle-gen3` (M3, T1), `sparkle-gen4` (M4, routes), `sparkle-gen5` (M5, boundary + audit),
  with the §5 goals.

## 8. Immediate units (proposals; each with its own freeze)

### 8.1 U0 `sparkle-gen2-u0-types`
- **Files:** `Tools/ShippingGen2Defs.lean` (GEN2_DEFS verbatim) and `Tools/ShippingGen2Connect.lean`.
- **Theorems in `Tools/ShippingGen2Connect.lean`:**
  - `seqFactsRN_of_callDec`:
    ```
    CallDec p q k → (∀ mc, PC c mc → ∃ Dc, ChildShips q n mc Dc ∧ ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g)
      → moduleByName dsn.modules mc.name = some mc → SeqFactsRN (childMap dsn.modules) n p.d.shape dsn body (p.lsrc i bools bits)
        p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits) bsC outsC (S i) PC k c
    ```
    with `bsC`/`outsC`/`S` from `P` as in §4.2. The exact `PC` (which must contain `mc ∈ dsn`) is fixed in U0's freeze.
  - `memFacts_of_memDec`.
  - `hrunN`: either a proof that consumer 2 applies, or the variant's statement.
- **Report:** the classification of §4.4's R? rows, and the G-EXC finding.
- **Accept:**
  - an exact-head build of `Tools.ShippingGen2Connect`;
  - axioms standard;
  - no change to existing files.

### 8.2 The G-CALLDEC probe `sparkle-gen2-calldec`
- **Subject:** `CallDec` for one ordinary call of an existing generated parent (a C4 wrapper → leaf call), from
  `machineExt`/`machineSource` and the reader's call terms.
- **Deliverable:** a route/size report, then the generic unit or the certificate decision.

### 8.3 M2-a `sparkle-gen2-step-mem`
- **Subject:** `MemParentStmt` (GEN2_DEFS §5), with the corollaries for `quantModule` and `leafM`.
- **Prerequisites:** U0, and the memory rows of §4.4 classified.

### 8.4 M2-a' `sparkle-gen2-leaf`
- **Subject:** `LeafStmt`.

## 9. User decisions (none needed now)
These would change the goal, the guarantee or the cost:
- the certificate route for G-CALLDEC;
- a height-heterogeneous semantics for G-LIFT;
- a legacy contract in FG;
- the production reader switch for G3-SHAPE;
- any DATA counterexample that shrinks a case.

Everything else is coder/reviewer work inside this plan.

## 10. Not claimed
- No theorem, no build, no production change. FG and T1 are unproved.
- GEN2_DEFS.lean.txt is frozen text that has not been elaborated. U0 elaborates it and records the deviations.
- The order of §5 is a plan corrected against the cited sources. It is not a feasibility result.
