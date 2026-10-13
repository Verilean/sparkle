# E — `#machine_no_ports_memkid`: the generator for a parent of memory machines (round par/e-1)

Branch `par/e-1` from poc `930a2400`. **WRITTEN, NOT BUILT.** No `lean`,
`lake` or `iverilog` was started; nothing below is proved-and-built. Marks:
[R] read (file:line at 930a2400), [M] measured by the integrator earlier
(build records of the C / D documents), [P] PREDICTED, [?] not known.

**How far it got.**

| task | state |
|---|---|
| 1 `#machine_no_ports_memkid f`, the sweep, summary, expect | written: `Tools/ShippingMemKidTags.lean`, `Tools/ShippingNoPortsMemKidCommand.lean`, `Tools/ShippingNoPortsMemKidSweep.lean` |
| 2 the asserting test | written: `Tests/Compiler/NoPortsMemKidTest.lean` |
| 3 what the census shows | §6, by reading `recheck` and the marker rules |
| 4 this document | — |

No built file is edited. Nothing under `Sparkle/`, `lakefile.lean`,
`Tests/AllTests.lean`.

One thing the reading changed against the hand files, stated where it
matters (§3.2): the hand closing of `memParent` proves the sibling
separation by "only ONE entry has names below it" (`namesT_two`). A
generator that accepts two memory-machine callees cannot; the names below an
entry are described by a TAG per entry instead, in a new small file of
general lemmas. The statements the generator emits for `memParent`'s shape
are the hand statements; the proof of three name arguments differs.

## 1. Files

| file | what |
|---|---|
| `Tools/ShippingMemKidTags.lean` | `Tagged`, `tagged_nil`, `Tagged.allMem`, `tagged_namesOfP_const`, `tagged_disj` — 4 small lemmas over lists of strings; no compiler notion |
| `Tools/ShippingNoPortsMemKidCommand.lean` | the scope (`scopeShape`, `scopeArtifacts`), the tactic `memkid_boundary`, the generated theorems, `generate`, `#machine_no_ports_memkid` |
| `Tools/ShippingNoPortsMemKidSweep.lean` | `#machine_no_ports_memkid_sweep` (never an error), `#machine_no_ports_memkid_summary`, `#machine_no_ports_memkid_expect` |
| `Tests/Compiler/NoPortsMemKidTest.lean` | own declarations, the chains, the generator (asserting), the hand-statement comparison, the sweep with expect lines |

## 2. Reading notes

### 2.1 Read in full

`docs/parallel/D-mem-kid-free.md` (all sections and the build record);
`Tests/Compiler/MemDepthProbeTest.lean`, `MemParentClosesTest.lean`,
`MemParentFreeTest.lean`; `Tools/ShippingBndOnly.lean`,
`ShippingNoPortsDeepCommand.lean`, `ShippingNoPortsKidsCommand.lean`,
`ShippingChildIfaceGen.lean`, `ShippingDesignCoverage.lean`,
`ShippingLeafSweepCommand.lean`, `ShippingLeafSweepExpect.lean`,
`ShippingMemNamesP.lean`, `ShippingKidsChildIfaceM.lean`.

Read in part: `Tools/ShippingGenKidM.lean` 600–803 (`GenKidM`, its
projections, `factsT`); `ShippingKidFactsT.lean` 40–110, 180–342
(`KidFactsT`, `KidFacts.toT`, the four `kidsT_*` statements);
`ShippingCallsKidsD.lean` 54–62, 85–140 (`ChildIfaceG.toD`, the statement of
`machineClosesAt_of_kidsD`); `ShippingNoPortsMemCommand.lean` 125–470
(`memParamsOf`, `scope`, `emit`, `dataTheorems`, the start of
`closingTheorems`), 630–660, 782–800; `ShippingMemOnly.lean` 100–140
(`MemOnlyData`); `ShippingMachineDepthCommandR.lean` 108–134, 630–700,
900–925 (the boundary); `ShippingNoPortsCommand.lean` 105–135, 280–292
(`leafKidTheorem`, `forbidden`); `ShippingNoPorts.lean` 36–174 (the head);
`ShippingModuleName.lean` 1–150, 766–784; `ShippingSeqChildIface.lean`
234–254; `ShippingMachineClosesGen.lean` 60–126;
`ShippingFinalGoalCommand.lean` 46–90 (`allowed`, `isPropArrow`);
`ShippingReflectCtx.lean` 78–86; `ShippingShipsNoOutsCommand.lean` 33–38
(`andParts`); `Sparkle/Compiler/MachMemory.lean` 36–70;
`Tests/Compiler/ShippingMachineSeqTest.lean` 1–80,
`DepthLoopChildCompareTest.lean`, `LeafSweepClosesTest.lean` 1–60,
`DesignCoverageTest.lean`; the build records of
`docs/parallel/C-mem-depth-ships.md` (385–400, 668–690).

Also read: `docs/parallel/C-mem-depth-free.md` in full (with its build
record); of `docs/parallel/C-mem-depth-ships.md` the section list, §7.1 and
both build records; of `docs/parallel/C-loop-child-calls.md` the section
list and the build record.

NOT read: the other sections of `C-mem-depth-ships.md` and
`C-loop-child-calls.md` (ship level: how the built commands of the chain
work inside; they are used here as commands, in the measured order);
`Tools/ShippingCallSelf.lean`,
`ShippingGenKidT.lean` (not used: the hand file's `kidsT_designCheck` route
is followed, §3.3); `ShippingGenKidM.lean` 1–600 (the copied lemmas — built
and measured); the bodies of `#machine_ext_joint`, `#machine_composed_memNR`,
`#machine_seq_child_memNR`, `#machine_depth_core` (used as commands, in the
measured order).

### 2.2 The facts the generator rests on [R]

| fact | where |
|---|---|
| a single-placeholder memory machine has `k.noPortsMem_entry : ∀ k hk, (insts[k]).1 = memChildName cb aw dw` (the disjunction has one alternative) | `ShippingNoPortsMemCommand.lean` 345–358 |
| `k.noPortsMem_data : MemOnlyData k.machineData nDecl aw dw`, fields `calls slots domB … cw args outNames outScalar` | 381–395; `ShippingMemOnly.lean` 115–133 |
| `k.noPortsMem_closes : ∀ {mctx mref cctx cref}, MachineClosesAt … k …`, NO premise | 462–468 |
| `memParamsOf` (a public `def`): the parameters of a placeholder name | 144–149 |
| the boundary of `f.machine_ships_hierNR1`: `conj (ChildBnd :: pTypes)`; per sequential child `c`: `MachineDefines` alone when `closesTheorem? c` (a leaf with `c.machine_closes`), else `MachineDefines ∧ (∀ mctx' cctx', ChildRanIn … → MachineClosesAt … ∧ ∀ wc raw D, ChildBnd … wc → bnd_c)` when `c` has no `machine_closes_at` / `closes_deep` | `ShippingMachineDepthCommandR.lean` 641–692, 916–918; 108–111 |
| `endpointTermX f [] [] 1 facts outs masked design`: 11 binders (those of the ships theorem), each run theorem applied to `hcore hpost entry closes (hg)`, the rest found among the conjuncts of the boundary | `ShippingNoPortsDeepCommand.lean` 474–545 |
| `addOrCompare`: an existing constant must have an `isDefEq` statement; the rebuilt proof is kept as `…_regen` | `ShippingNoPortsKidsCommand.lean` 628–640 |
| `bndOnlyType c ks`: the first 10 binders of `c`, `MachineDefines` of `ks` (named `hK{i}`), the boundary replaced by `ChildBnd mref cref w` | `ShippingBndOnly.lean` 62–115 |
| `closesDeep` / `ifaceDeep` refuse a memory child | `ShippingChildIfaceGen.lean` 311–312 |
| `machineClosesAt_of_kidsD`: `hparentD`, `hselfD`, `hdisjD` over `namesK` | `ShippingCallsKidsD.lean` 98–135 |
| `ofMem_injective`, `ofDecl_ne_ofMem` | `ShippingModuleName.lean` 772–781 |
| `memParent`'s chain, measured order: C1 C2 C3 C5, J1, K1, K2; then `#machine_endpoint`, `#machine_depth_core`, `#machine_depth_ships`, `#machine_design_svNR` on the parent | `MemDepthProbeTest.lean` 149–158, 205, 238, 272–280; C build records [M] |

### 2.3 What is CALLED and what is COPIED from built generators

CALLED (unchanged, from another file):

* `Tools.ShippingNoPortsCommand.leafKidTheorem` — `k.machine_leafKid`;
* `Tools.ShippingNoPortsKidsCommand.Ctx` and `Ctx.binders`, `Ctx.hyps`,
  `Ctx.hR`, `Ctx.outsOf`, `Ctx.insOf` — the reflection binders `hR{j}` and
  the per-callee table entries (a memory machine is entered as
  `.oneOut .anonymous nD`, as `DeepScope.toK` enters a general callee: only
  the binder count is read, for `argWidths k.machineData nD`);
* `addOrCompare`, `regenName` (the compare path);
* `Tools.ShippingNoPortsDeepCommand.endpointTermX` — the open endpoint;
* `Tools.ShippingNoPortsMemCommand.memParamsOf`;
* `Tools.ShippingShipsFreeCommand.checkMade` (errors of a generated
  theorem, standard axioms);
* `Tools.ShippingMachineClosesGen.closedName`;
* `bnd_only%` (`Tools.ShippingBndOnly.bndOnlyType`) — the closed STATEMENT;
* `Tools.ShippingDesignCoverage.recheck` — the statement check.

COPIED (the built function cannot serve this class):

* `runTheorems` (`ShippingNoPortsKidsCommand.lean` 347–479) → `runTheoremsT`:
  the same four texts with `Tools.ShippingKidFactsT.kidsT_*` for
  `Tools.ShippingKidFacts.kids_*`, and for the design check the three extra
  arguments of `kidsT_designCheck` (`namesK`, `hname`, `hsep`). The built one
  states `KidFacts`, which is FALSE of a memory machine at every depth index
  [M `MemKidCheckProbe`];
* the `cases k` tactic of `kidsTheoremD` (`ShippingNoPortsDeepCommand.lean`
  444–453) → `Gen.casesTac`, used three times;
* the application of `machineClosesAt_of_kidsD` in `closesDeep`
  (`ShippingChildIfaceGen.lean` 288–304) → `closesTheorem`; `closesDeep`
  itself throws at the memory machine's own callee (311–312);
* `closedTerm` is NOT usable (the kid's closing is inside the boundary) — the
  closed form is new code: `closedCommand` + `memkid_boundary`.

The per-entry tables are ALWAYS `fun k => List.getD […] k d` here (the built
`Ctx.kidOuts` gives the constant function when there is one distinct
callee; one code path instead of two).

## 3. What is generated — names and statements

`f`: the parent; `k`: a memory-machine callee with declared binders `nD` and
memory module `(cb, aw, dw)`; `m := ofMem cb aw dw`; `hR{j}`: the reflection
of the `j`-th distinct callee at the theorem's contexts.

### 3.1 Per memory-machine callee

    k.machine_genKidM0 {mref cref} (hR : ∀ mctx' cctx', MachineDefines mctx' mref cctx' cref k k.machineData.shape) :
        GenKidM mref cref k k.machineData nD (fun _ => m) (fun _ => [m])
          (fun _ => memOuts dw) (fun _ => memIns aw dw) 0
    k.kid_factsT {mref cref} (hR : …the same…) :
        KidFactsT mref cref k k.machineData.shape.layout.outs (argWidths k.machineData nD) 1
    k.iface_deepM {mctx mref cctx cref} (hR : MachineDefines mctx mref cctx cref k k.machineData.shape)
        (y) (hy : RealChild mref cref k y) :
        ChildIfaceD k ((k.machineData.bsIn.take nD).filter (fun b => b.2 != .domain)).length
          (k.machineData.shape.layout.outs.map (·.name))
          (namesOfP k.machineData (fun _ => m) (fun _ => [m])) y.1 y.2

The terms of `memCounterH_genKidM` / `memCounterH_factsT`
(`MemParentFreeTest.lean` 123–183) and `memCounterH_iface`
(`MemParentClosesTest.lean` 72–91), with two inlinings: the hand
`memCounterH_entry` / `mem_isMem` are local `have`s (`hent` by
`first | exact k.noPortsMem_entry | decide`, `hmem` by `first | rfl | decide`),
and the hand definition `memNames` is its right-hand side, so
`memNames_allMem` is `namesOfP_const_allMem k.machineData cb aw dw` in place.

### 3.2 The parent's tables, interfaces and closing

Tables over the call ENTRIES, in the reader's order, entry `i` with callee `c`:

| table | leaf `c` | memory machine `c` |
|---|---|---|
| `nkF` | `((c.machineData.shape.binders.take (binders.length - slots.length - lets)).filter fun x => x.2 != .domain).length` | `((c.machineData.bsIn.take nD).filter …).length` |
| `outF` | `c.machineData.shape.layout.outs.map (·.name)` | the same |
| `nmF` | `([] : List String)` | `namesOfP c.machineData (fun _ => m) (fun _ => [m])` |
| `tgF` | `none` | `some (cb, aw, dw)` |
| `kidOuts` | `c.machineData.shape.layout.outs` | the same |
| `kidIns` | `declWidths c.machineData` | `argWidths c.machineData nD` |

    f.machine_kidIfaceM {mctx mref cctx cref} (hR0 …) (hR1 …) … :
        ∀ k hk y, RealChild mref cref (f.machineData.shape.insts[k]).1 y →
          ChildIfaceD (f.machineData.shape.insts[k]).1 (nkF k) (outF k) (nmF k) y.1 y.2
    f.machine_kidTagsM :
        ∀ k, k < f.machineData.shape.insts.length → Tagged (tgF k) (nmF k)
    f.machine_closes_at_memkid {mctx mref cctx cref} (hR0 …) (hR1 …) … :
        MachineClosesAt mctx mref cctx cref f f.machineData.shape

`f.machine_closes_at_memkid` is the hand `memParent_closes`' statement (the
reflections of the DISTINCT callees, in the order of their first entry), by
`machineClosesAt_of_kidsD` with the hand argument list. Differences in the
proof term:

* the tables are `List.getD` lists (the hand ones are pattern-matching
  `noncomputable def`s) — the form `closesDeep` uses;
* `hkid` is `f.machine_kidIfaceM hR0 hR1 …` (the hand file has the block
  twice: inline in `memParent_closes` and as `memParent_kidIface`);
* **the three name arguments.** Hand: `namesT_allMem` and `namesT_two` ("only
  entry 2 has names"). Generated (`Tools/ShippingMemKidTags.lean`):

      Tagged t L := ∀ x ∈ L, ∃ p, t = some p ∧ x = ofMem p.1 p.2.1 p.2.2
      Tagged.allMem : Tagged t L → AllMem L
      tagged_disj : Tagged t L → Tagged t' L' → (t = none ∨ t ≠ t') → ∀ x ∈ L, x ∉ L'

  `hparentD`, `hselfD` and the first half of `hdisjD` by the built
  `ofDecl_not_mem_allMem` on `Tagged.allMem (f.machine_kidTagsM k hk)`; the
  second half of `hdisjD` by `tagged_disj`, its third argument DECIDED per
  declaration:

      ∀ k hk k' hk', (insts[k]).1 ≠ (insts[k']).1 → (tgF k = none ∨ tgF k ≠ tgF k')

  This is FALSE exactly when two different memory-machine callees have the
  same memory module — and then `hdisjD` itself is false (the module is a
  shared descendant). The scope refuses that shape before anything is
  generated.

### 3.3 The run theorems, the endpoint, the closed form

    f.machine_kidsT1 {…} (hR0 …) … :
        ∀ k hk, KidFactsT mref cref (f.machineData.shape.insts[k]).1 (kidOuts k) (kidIns k) 1
    f.machine_runFactsT1 / _outsGT1 / _maskedGT1 / _designPT1
        {mctx mref cctx cref w w1 raw b D} (hcore) (hpost) (entry) (closes) [(hg)] (hB : ChildBnd mref cref w) (hR0 …) … :
        RunFacts (childMap D.modules) b
        / outsCheck (childMap D.modules) 1 (checkedOptimize b) = true
        / kidsMaskedN D.modules b.body = true
        / designCheck (childMap D.modules) 1 (checkedOptimize b) = true

— the hand `memParent_kidsT`, `memParent_runFacts1` … `memParent_designP1`.
`_designPT1` follows the hand file: the BUILT `kidsT_designCheck` with
`nmF`, `hname` from `f.machine_kidIfaceM` (`.name`, `.desNames`), `hsep` by
`ofDecl_not_mem_allMem` on the tags (the name-free `kidsT_designCheckO` of
`Tools/ShippingCallSelf.lean` is not used: nothing in this class needs it).

    f.machine_design_noPortsNR1          -- endpointTermX f [] [] 1 …; addOrCompare
    f.machine_design_noPortsNR1_closed : bnd_only% f.machine_design_noPortsNR1 [callees]

The closed statement, unfolded (for `mkParent`, callees `kcnt`, `mkH`):

    ∀ {mctx mref cctx cref} {w w'} {b design},
      RunsTo (synthesizeCombinational mkParent) mctx mref cctx cref w (b, design) w' →
      MachineDefines mctx mref cctx cref mkParent mkParent.machineData.shape →
      MachineDefines mctx mref cctx cref kcnt kcnt.machineData.shape →
      MachineDefines mctx mref cctx cref mkH mkH.machineData.shape →
      ∃ raw D, (b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)) ∧
        (ChildBnd mref cref w → <the head's conclusion: ∃ ids, … DesignSV (childMap D.modules) 1 (checkedOptimize b) …>)

**How "the same statement the built generators give" is ensured for
`f.machine_design_noPortsNR1`:** it is made by the very function the built
`#machine_no_ports_deep` and `#noports_open_as` call (`endpointTermX`), with
no extra machine and no gate (then its text equals `endpointTerm` of
`#machine_no_ports_kids`); the statement is the INFERRED type of the head's
application to the ships theorem's arguments, so it does not depend on the
run theorems. If the constant exists, `addOrCompare` requires `isDefEq` and
keeps the rebuilt proof as `…_regen`; the closed form is then stated from
the EXISTING constant.

The closed proof:

    intro mctx mref cctx cref w w' b design hr hP hK0 hK1 …
    obtain ⟨raw, D, hpost, h⟩ := f.machine_design_noPortsNR1 hr hP (f.machine_closes_at_memkid hK0 hK1 …)
    refine ⟨raw, D, hpost, fun hB => h ?_⟩
    memkid_boundary [callees]

`memkid_boundary` (a tactic of the generator file, `proveBnd`): the goal is
the boundary; a component is closed by (1) a local hypothesis whose type is
the component (reducible `isDefEq`), (2) `And.intro` of its two parts, (3)
introducing a binder (a proposition becomes a hypothesis), (4) for
`MachineClosesAt mc mref cc cref k _` the constant `k.noPortsMem_closes` at
the goal's four contexts (for `MachineCloses …`: `k.machine_closes`), `k`
among the listed callees, (5) a reflection at other contexts by
`MachineDefines.ctx`; the term is checked against the goal and, with the
theorem, by the kernel. The hand file's `refine ⟨raw, D, hpost, fun hB => h
⟨hB, ?_, hRm, fun _ _ _ => ⟨k.noPortsMem_closes, fun _ _ _ hb => hb⟩⟩⟩` is
one such search written out; the test proves the same statement that way
too (§5, item 3), so a boundary of another shape shows at BOTH.

### 3.4 The statement check, the audit, restoring

`generate` ends with: `recheck` on the closed constant must be `ok`; its
proposition binders must be `2 + (distinct callees)` and its antecedents
under the existentials 1; `collectAxioms` of every generated constant ⊆
`{propext, Classical.choice, Quot.sound}`. `#machine_no_ports_memkid` saves
the environment and the message log first and puts both back on ANY
exception, then throws `NOPORTS MEMKID f: NOT GENERATED …`. The sweep does
the same and logs.

### 3.5 Refusals (`scopeShape`, from the SOURCE by the compiler's reader; then `scopeArtifacts`)

| shape | reason line contains |
|---|---|
| the reader does not read `f` / a callee | `is not read by the machine reader` |
| no call | `no call` |
| a memory entry of `f` itself | `a memory entry of` |
| `f` without a register / under the one-output closing | `parent without a register` / `one-output closing` |
| an output of `f` starting with `i` | `starts with 'i'` |
| a callee that is also a descendant of another callee (`memGrand`, `mixDeep`) | `is also a descendant of the callee` |
| a gate callee | `is a GATE child` |
| a callee without a register | `has no register` |
| a callee with calls that are not memory placeholders | `has calls that are not memory placeholders` |
| a memory machine under the one-output closing | `is under the one-output closing` |
| a memory machine with several different placeholders | `several different placeholders` |
| two different memory machines with the same memory module | `have the SAME memory module` |
| a missing constant (`scopeArtifacts`) | `not a machine with an endpoint`, `has no … machine_closes`, `lacks …noPortsMem_…`, `no depth endpoint at depth 1` |

The shape is checked BEFORE the constants: a declaration of a refused shape
is refused without any command having run on it (`mkGrand` in the test).

## 4. Build order, `lean_lib` lines, the `AllTests` import

1. `Tools.ShippingMemKidTags` (imports the built `Tools.ShippingMemNamesP`,
   `Tools.ShippingModuleName`) — cheap.
2. `Tools.ShippingNoPortsMemKidCommand` (imports 1 and built files only).
3. `Tools.ShippingNoPortsMemKidSweep` (imports 2).
4. `Tests.Compiler.NoPortsMemKidTest` (imports 2, 3, the built
   `Tools.ShippingBndOnly` and the built command files of the probe).

    lean_lib «Tools.ShippingMemKidTags» where
      roots := #[`Tools.ShippingMemKidTags]

    lean_lib «Tools.ShippingNoPortsMemKidCommand» where
      roots := #[`Tools.ShippingNoPortsMemKidCommand]

    lean_lib «Tools.ShippingNoPortsMemKidSweep» where
      roots := #[`Tools.ShippingNoPortsMemKidSweep]

`Tests/AllTests.lean`, when the test is measured green:

    import Tests.Compiler.NoPortsMemKidTest

The test imports neither the probe nor `ShippingMachineSeqTest`; every
constant it generates is under `Sparkle.Tests.Compiler.NoPortsMemKidTest.*`
or `Tests.Compiler.NoPortsMemKidTest.*` (two hand theorems). It keeps no
`…by_the_generated_proof` constant (the environment is put back).

## 5. PREDICTED outcome per test line (all [P])

| # | line | PREDICTED | if not |
|---|---|---|---|
| 0 | the declarations | elaborate (copies of `cnt`, `memCounterH`, `memParent`, `memGrand`; `mkW` = `mkH` at address width 5; `mkParent2` adds `let z := mkW we wb wd` and `y + z`) | a DSL error names the line |
| 1 | the seven kid commands on `mkH` | OK, as C1 C2 C3 C5 J1 K1 K2 on `memCounterH` [M] (C4 `#machine_design_svR0` is left out: nothing here reads it [P]) | |
| 2 | the seven kid commands on `mkW` | OK (the same shape at `BitVec 5`) | a width-specific failure would be a finding about the built generators |
| 3 | `#machine_endpoint mkParent`, `#machine_depth_core … 1`, `#machine_depth_ships … 1`, `#machine_design_svNR … 1` | OK, as Q2.1, S2.a, S2.b, S2.c [M]. Difference to the probe: `kcnt`'s own artifacts are made on demand here (the probe imported `cnt`'s from `ShippingMachineSeqTest`, where `#machine_endpoint parent` made them the same way) | |
| 4 | `#machine_no_ports_memkid mkParent` | `NOPORTS MEMKID … GENERATED …machine_design_noPortsNR1; GENERATED …_closed; STATEMENT CHECK OK …: proposition binders 4, antecedents under the existentials 1, NOT ALLOWED 0, checker / closing constants [], DesignSV mentioned: true; AXIOMS: standard only …` | the message names the generated theorem that failed (`checkMade`), with its first two errors |
| 5 | `#noports_open_as mkParent_open_hand …` | `NOPORTS OPEN …` (the built tool on the generated run theorems) | |
| 6 | `mkParent_closed_hand` | OK (the hand `refine` of `MemParentFreeTest`) | the boundary is not as read: the message shows it |
| 7 | the `run_cmd` | `MEMKID COMPARE: … isDefEq … (the same term: true) …` | `the same term: false` with `isDefEq` true is not an error |
| 8 | `#assert_check_free`, three `#print axioms` | `CHECK-FREE OK …` as line 4; `[propext, Classical.choice, Quot.sound]` | |
| 9 | the four parent commands on `mkParent2` | OK [P, the weakest chain prediction: a parent with TWO loop children with memories was never run through `#machine_endpoint` / the grouped depth generator] | the file stops here with the built generator's message; everything above it is unaffected |
| 10 | sweep `mkParent2` | `GENERATED`; proposition binders 5, antecedents 1, NOT ALLOWED 0 | `FAILED` with the failing generated theorem |
| 11 | sweep `mkParent` | `REBUILT` (`REBUILT …NR1: statement isDefEq …_regen`, `REBUILT …_closed …_closed_regen`) | |
| 12 | sweep `mkH` | `REFUSED`, "a memory entry of" | |
| 13 | sweep `mkGrand` | `REFUSED`, "is also a descendant of the callee" (from the source; no command ran on `mkGrand`) | if the reader does not read `mkGrand` without its callees' artifacts: `REFUSED`, "is not read by the machine reader" — then the expect line's reason is to be corrected [?] |
| 14 | summary, four expect lines | no inconsistency; `MEMKIDSWEEP EXPECT …, as expected` ×4 | |
| 15 | `#assert_check_free mkParent2…_closed`, `#print axioms` | `CHECK-FREE OK`, binders 5; standard axioms | |
| 16 | `#leaf_sweep …kcnt` (built, never an error, LOG ONLY) | NOT predicted [?] | cannot fail the file |

## 6. What the census (`#design_coverage`) shows

By reading `Tools/ShippingDesignCoverage.lean` [R]:

* `collect` (123–133) takes every constant whose LAST component starts with
  `machine_design_` (`isDesign`, 112–113) and does not end with `_gap`,
  `_regen`, `_expected` (`isCompanion`, 107–108), under its prefix as the
  declaration. So for `f` = `mkParent` / `mkParent2`:
  `f.machine_design_svNR1`, `f.machine_design_noPortsNR1`,
  `f.machine_design_noPortsNR1_closed` are scanned;
  `…NR1_regen` and `…NR1_closed_regen` (the compare path) are NOT.
* `recheck` (164–187) is the function the generator's statement check calls
  on the same constant; the generator throws unless it returns `ok`. Hence
  `f.machine_design_noPortsNR1_closed` passes in the census: every
  proposition binder is `RunsTo` / `MachineDefines` (`allowed`,
  `ShippingFinalGoalCommand.lean` 49–54), the one antecedent under
  `∃ raw D` is `ChildBnd`, no constant of `checkerConsts` (96–99), `DesignSV`
  mentioned. NO census change is needed: no list of endpoint names decides
  coverage (45–47).
* The row [P]: `COVERAGE ROW …mkParent: COVERED — by
  [machine_design_noPortsNR1_closed]; notes on its design-level constants …:
  [machine_design_svNR1 (… NOT ALLOWED …), machine_design_noPortsNR1 (… NOT
  ALLOWED …; checker constants [MachineClosesAt, ChildRanIn] …)]`; in the
  totals the form `machine_design_noPortsNRN_closed` gains one per parent
  (`formOf`, 254–255).
* Other rows this test adds once it is in `Tests.AllTests` (the census file
  imports it): `mkH`, `mkW` — `COVERED` by `machine_design_noPortsR0_closed`
  (made by `#machine_no_ports_mem`, as for every memory-only parent [M for
  `memCounter`]); `kcnt` — it has `machineData` (as a child of `mkParent`):
  `OPEN register-leaf` unless it gets a design-level endpoint of its own.
  The test's LAST line is the built never-failing `#leaf_sweep …kcnt` (log
  only, nothing asserted, outcome NOT predicted [?]: whether a leaf made on
  demand as a child has what the leaf chain starts from,
  `kcnt.machine_ships_wired`, was not read): GENERATED → `kcnt` is
  `COVERED` by `machine_design_leaf0`; REFUSED / FAILED → one more OPEN row,
  with the reason in the log (the measured census at ef4d020a had 129
  declarations, 128 covered [M]); `mkGrand` —
  no artifact, no row; the two hand theorems `mkParent_open_hand`,
  `mkParent_closed_hand` — their last components do not start with
  `machine_design_`, not scanned.
* Before the test is in `Tests.AllTests`, the census of
  `Tests/Compiler/DesignCoverageTest.lean` does not see these declarations.

## 7. Risks, in order

1. **`memkid_boundary` / `closedCommand`** — new Meta code on the one step
   the built generators do not have. Points: the goal's form after
   `refine … h ?_` (handled: `headBeta` at every step, one `whnfR`
   fallback); hypothesis matching with reducible transparency (the
   components are built by the same `mkAppM` forms as the binders of
   `bnd_only%`; if a `MachineData.shape` projection is represented
   differently on the two sides the match fails and the message shows the
   component); the splice `intro … $hKs*` and the quotation of `bnd_only%`
   / `memkid_boundary` with `[$kidsI,*]`.
2. **`Tools/ShippingMemKidTags.lean`** — four short proofs, unbuilt:
   `tagged_disj` (`rcases` of two triples, `ofMem_injective`, `rw [hp, hp',
   a, b, c]`), `tagged_namesOfP_const` (the phrases of the built
   `namesOfP_allMem`).
3. **Tables as `List.getD` lists under `cases k`** in three generated
   theorems: `exact` must reduce `List.getD […] (0+1+1) d` and
   `(f.machineData.shape.insts[2]).1`. The built `kidsTheoremD` and
   `closesDeep` rely on the same reductions; new here: the table of
   `Option (Bool × Nat × Nat)` and `tagged_nil _` against a reduced `[]`.
4. **The decided tag condition** (`tgF k = none ∨ tgF k ≠ tgF k'` under four
   bounded binders): `decide` over `Option (Bool × Nat × Nat)`; the built
   generators decide statements of this binder shape over `Lean.Name`s.
5. **`hent` by `first | exact k.noPortsMem_entry | decide`**: if the built
   constant's statement is not syntactically the single equation, `decide`
   is the fallback (the hand file's own proof).
6. **Opening `Tools.ShippingNoPortsKidsCommand` whole** (needed for
   `Ctx.hR`, as the built deep generator notes): a name of that namespace
   could shadow one of mine — I found none.
7. **`mkParent2`'s chain** (test line 9) — built generators on an unmeasured
   shape; not this round's code.
8. **`mkGrand`'s refusal from the source** (line 13) — whether
   `readMachine` reads a declaration none of whose commands ran [?].
9. Build time: two memory-machine chains, two parents' depth generators,
   the generator twice on `mkParent` (the REBUILT sweep) — not estimated.
10. A rerun of `#machine_no_ports_memkid f` a THIRD time in one environment
    is an error (`…_regen` exists), as for the built generators.

## 8. Not determined by reading

* Whether anything builds; every [P] of §5 and §6.
* The call entries of `mkParent2` (`[kcnt, kcnt, mkH, mkW]` by analogy); the
  generator reads them, the test does not index them.
* Whether `kcnt` (generic in its domain, as `cnt`) gets `kcnt.machine_closes`
  and `kcnt.machine_leafKid` on demand exactly as `cnt` did: for `cnt` they
  were in the probe's environment when the hand files ran [M], made by the
  depth generator (`closesTheorem?`) and — the second — never (the hand file
  wrote `cnt_leafKid` itself; here the built `leafKidTheorem` makes it, the
  generator the hand term was copied from).
* The memory machine's own boundary inside the depth endpoint (`bnd_c`): read
  by worker D as `ChildBnd` alone and confirmed by the built hand proof for
  `memCounterH` [M]; `memkid_boundary` does not assume it, but only a
  component of one of its five kinds is proved.
* Whether a memory machine with a STRUCTURE result (then a parent could have
  it as its only callee under the general closing) passes: in scope by the
  code, no declaration tried.
* A synchronous-read memory machine (`cb = false`): in scope by the code
  (`memKid_facts` is for either read kind [R `ShippingMemOnly.lean` 135]),
  no declaration tried.

## 9. Scope sentence

Each generated `f.machine_design_noPortsNR1_closed` is about ONE declaration
as an entry at depth 1: data conditions decided per declaration (conditions,
not reductions), the run of the full entry, the reflections of `f` and of
its callees and the runtime boundary `ChildBnd` as premises, `DesignSV` of
the module LIST over the returned design's child map — not the SV string,
not `#sim`. Deeper shapes (`memGrand`), a callee shared between siblings
(`mixDeep`), memory entries beside machine callees, and two memory machines
over one memory module are REFUSED, not covered.

## Integrator's build record (2026-10-13) — MEASURED

BUILT on poc e4a8018b + these files, cgrun 3 GiB swap 0, runs `e1` (exit 0, peak 0.85 GB) and `e1-all`;
worker's files UNCHANGED, FIRST ATTEMPT (Tags, Command, Sweep, the test). Every prediction confirmed.

* `#machine_no_ports_memkid mkParent`: GENERATED `mkParent.machine_design_noPortsNR1` and
  `…NR1_closed`; statement check OK; `MEMKID COMPARE`: the generated statement isDefEq the hand statement
  (the same term: true) and the generated proof is accepted by the kernel AT the hand statement;
  `CHECK-FREE OK: proposition binders 4, antecedents 1, NOT ALLOWED 0, checker / closing constants [],
  DesignSV mentioned: true`.
* Sweep: `mkParent2` (two different memory-machine kids, memories 4x8 and 5x8, plus `kcnt`) GENERATED,
  proposition binders 5, NOT ALLOWED 0; `mkParent` REBUILT (statement isDefEq the existing one);
  `mkH` REFUSED (a memory entry of itself); `mkGrand` REFUSED (the callee `kcnt` is also a descendant of
  another callee). All four expect lines "as expected". Axioms of `mkH.kid_factsT`,
  `mkParent.machine_closes_at_memkid`, both `…_closed`: standard. `#leaf_sweep kcnt`: GENERATED.
* `Tests.AllTests` with `NoPortsMemKidTest` imported: 1342 jobs, exit 0. Census after it: 134
  declarations, COVERED 133, OPEN 1 (`mixDeep`). New rows: `kcnt` (leaf0), `mkH`, `mkW`
  (noPortsR0_closed), `mkParent`, `mkParent2` (noPortsNR1_closed). Log: `~/sparkle-work/coverage-census-3.log`.

Endpoint — premise — state: `mkParent.machine_design_noPortsNR1_closed` and
`mkParent2.machine_design_noPortsNR1_closed` (register parents of memory-machine children and a leaf):
premises the run, `MachineDefines` of the parent and of each callee, `ChildBnd` under the existential;
no check antecedent, no closing premise.
SCOPE of each: one declaration, depth 1, callees leaf register machines or memory machines with one
placeholder and distinct memory modules, no shared descendant, data conditions decided per declaration,
runtime boundary, `DesignSV` of the module list — not the SV string, not `#sim`.
