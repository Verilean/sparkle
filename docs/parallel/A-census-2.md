# A / G1: second census — every declaration a design-/ship-level generator is invoked on (round par/a-22)

Branch `par/a-22`, base poc `13688cd9`. NOTHING here was built or run. The
census is a READING of the sources at that commit and of the verification
records `docs/parallel/verification-*.md` (BUILT, with logs). Marks used in
the tables:

* **[V]** read from a verification record (a built log line or its
  "Established" paragraph);
* **[T]** read from the generator's template / the head theorem's statement
  (the statement was not printed by a build that I read);
* **[R]** read from the source of the declaration or of a test;
* **[I]** inferred from a neighbouring fact, not read.

WRITTEN, NOT BUILT in this round: four test files (§5). No `Tools/` file, no
edit of an existing file. Nothing counts as removed until the integrator's
build.

## 0. The commands (from the `elab` declarations, then their uses)

`grep` of `elab "#machine_…` / `"#gate_…` over `Tools/`, `Sparkle/`, `Tests/`:
all are in `Tools/Shipping*.lean`; none in `Sparkle/`. Uses
(`^\s*#(machine|gate)_`): ALL under `Tests/Compiler/` — none in `Tools/`,
`Examples/`, `IP/`, `Sparkle/`. Programmatic uses (a generator function
called from a `run_cmd` or a script) are listed in §3.

| level | commands (file) | what they add |
|---|---|---|
| entry (ship level of ONE module) | `#machine_endpoint` (`ShippingMachineCommand` 2705) | `f.machineData`, `f.machine_sound`; for a machine WITHOUT calls also `f.machine_ships`, and `f.machine_ships_wired` (a slot) or `f.machine_ships_comb` (no slot); `f.machine_closes` and the `_closed` forms where `letsOk` decides |
| child function | `#machine_child` (`…LinkedCommand` 90), `#gate_child` (`…GateChildCommand` 256) | `c.machine_child` / `c.gate_child`: `ChildFn b …` of the full-entry module |
| composition (IR) | `#machine_linked`, `#machine_composed`, `#machine_composedT`, `…TS`, `…TSR`, `#machine_composedN` | the linked IR run shows the source; not shipped, not text |
| shipped module (IR run of `checkedOptimize b`) | `#machine_ships_hier`, `…hierH`, `…hierN` | with `shipsHierCheck` / `shipsHierHCheck` and `Bd`; NOT `DesignSV` |
| design level, WITH checks | `#machine_design_sv0`, `…svN`, `…svH` (old instance boundary); `#machine_design_svR0`, `…svNR`, `…svHR` (`ChildBnd` boundary, closing `MachineClosesAt`) | `DesignSV …` under the four check premises (§0 of `A-remaining.md`) |
| closing | `#machine_closes`, `#machine_closes_at`, `#machine_closes_deep`, `#machine_closes_shared` | `MachineCloses(At)` and the `_closed` forms |
| design level, check-free | `#machine_design_svH_free`, `…svH_full`, `#machine_oneout(_any)(_try)`; `#machine_no_ships`, `…_masked`, `#machine_no_outs`, `#machine_no_design`, `#machine_no_kids`, `#machine_no_ports`, `…_kids`, `…_deep`, `…_seq` (+ `_try`) | `f.machine_design_svH_full(_closed)`, `f.machine_design_noPortsNR{n}(_closed)` |
| boundary / audit | `#machine_boundary_close(_try)`, `#machine_goal_gap`, `#machine_goal_gap_of(_try)` | `…_closedB`, `…_gap` |

## 1. The 29 (design-level endpoint free of check premises and of NOT-ALLOWED premises) — for reference

One line each; "premises" = every proposition binder and every antecedent
under the existentials that is not the run. All [V].

| declaration (definition) | kind | strongest BUILT endpoint | remaining premises (all ALLOWED) | record |
|---|---|---|---|---|
| `caller` (`ShippingMachineInstTest` 38), `callerTwice` (50), `callerNested` (67), `callerD` (86) | machine with calls; one-output gate child `pick` / `pickD` | `f.machine_design_svH_full_closed` | `MachineDefines f`, `EntryDefines` of the gate child, `ChildBnd` | `verification-oneout-a11`, `-family` |
| `callerRep` (`ShippingCallsCloseTest` 57), `callerABA` (83), `callerMix` (`ShippingPremiseEvalTest` 21) | the same; two entries / two callees | the same | the same, one `EntryDefines` per callee | `-family`, `-a11` |
| `callerL` (`ShippingMachineLinkedTest` 31), `callerLN` (48), `hftByte` (`ShippingMachineTeleTest` 65) | one-output calls of a SLOTLESS MACHINE child (`pickByteH`, `httpGetByte`) | the same | `MachineDefines f`, `MachineDefines` of the child, `ChildBnd` | `-machine-leaf` |
| `midH` (`ShippingMachineDepthHTest` 26), `callerInner` (`ShippingMachineInstTest` 106) | one-output gate child (`rcH`; `pick`, one call in a flattened sub-machine) | the same | as `caller` | `-a12`, `-a13` |
| `parent` (`ShippingMachineSeqTest` 28), `chained` (40), `two` (`ShippingChildBoundaryTest` 42), `mid` (`ShippingMachineSeqTest` 52) | register parent of leaf register machines, depth 1 | `f.machine_design_noPortsNR1_closed` | `MachineDefines f`, `MachineDefines` per child, `ChildBnd ∧ MachineDefines child` | `a1aad854`, `-a12`, `-a13` |
| `grandH` (`ShippingMachineDepthHTest` 35), `mixD1` (`ShippingDesignSVTest` 43) | child with a one-output gate call (`midH`), depth 1 | `f.machine_design_noPortsNR1_closedB` | reflections of `f`, `midH`, (`cnt`), `EntryDefines rcH`; `ChildBnd` | `-a14`, `-a14b` |
| `grand` (`ShippingMachineSeqTest` 62), `topD2` (`ShippingDesignSVTest` 34) | child under the general closing (`mid`; `mid2 → midH`), depth 2 (`topD2` also 3) | `f.machine_design_noPortsNR2_closedB` (`topD2`: also `…NR3_closedB`) | reflections of every descendant; `ChildBnd` | `-a15`, `-a16` |
| `seqMem` (`ShippingChildBoundaryTest` 52) | register parent, leaf child `cnt` + one memory | `seqMem.machine_design_noPortsR0_closed` | `MachineDefines seqMem`, `MachineDefines cnt`, `ChildBnd ∧ MachineDefines cnt` | `-b13`, `-a18` |
| `memCounter` (`ShippingMachineMemLinkedTest` 17), `twoMems` (27), `mixedMems` (38), `memWide` (`ShippingDesignSVMemTest` 23), `syncNarrow` (33) | `Signal.loop` parent, memory children only | `f.machine_design_noPortsR0_closed` (a NEW statement, base `…sv0`) | `MachineDefines f`, `ChildBnd` | `-b14`, `-b15`, `-a19` |
| `engineOnce` (`MultiInstanceTest` 58), `twinCalls` (65), `mesh2x2` (46) | parent WITHOUT a register, leaf register child `pe` | `f.machine_design_noPortsNR1_closed` | `MachineDefines f`, `MachineDefines pe`, `ChildBnd` | `-a20`, `-a21` |

## 2. Every OTHER declaration a design-/ship-level generator is invoked on

### 2.1 Declarations with calls

| declaration (definition) | kind | generators invoked (file:line) | strongest BUILT endpoint | its non-run, non-reflection premises | why not in the 29 |
|---|---|---|---|---|---|
| `mixDeep` (`ShippingChildBoundaryTest` 278) | register parent; callees `mid2`, `midH`, `cnt`; depth 2 | `#machine_endpoint` (288), `#machine_design_svNR … 2` (297), `#machine_closes_shared` (`CallsKidsSharedMixDeepTest` 91), `_try` probes | `mixDeep.machine_design_noPortsNR2` (OPEN form) [V `-a16`] | `MachineClosesAt mixDeep` (NOT ALLOWED) and the unreduced boundary's two ∀-contexts conjuncts [V `-a14` 25, `-a16` 83–90] | **user decision** (shared descendant: `midH` is a call entry of `mixDeep` AND of its callee `mid2`; `A-shared-descendant.md`). Not worked on |
| `loopParent` (`ShippingMachineSeqLoopTest` 27) | register parent; child `toggleL` (`Signal.loop`, `Bool` result); depth 1 | `#machine_endpoint` (37), `#machine_composedTS` (39), `#machine_ships_hier` (40); probe: `#machine_design_svNR … 1`, `#machine_closes_at`, `#machine_no_ports_try` (`RemainingProbeTest` 149–156) | NONE design-level. `loopParent.machine_ships_hier` (shipped IR run) [R] | `shipsHierCheck`, `Bd` = `kidsMixed` [T `machine_ships_hier`], the old instance boundary `BoundaryOf` [I] | **base endpoint missing**: `#machine_design_svNR 1` FAILED — "seq child …toggleL: …toggleL.machine_sound is not built from Tools.ShippingMachineAuto.machine_trace_of_data" [V `-a12` 72]. Source of the line: `soundArgs` (`ShippingMachineLinkedCommand` 49) called by `generateSeqChildN` (`ShippingMachineDepthCommand` 43). §4.1 — category (a), test WRITTEN |
| `withMemory` (`ShippingMachineFuseTest` 42) | `Signal.loop` parent with a fused inner loop (`innerCnt`, flattened) and two combinational-read memories (one dead) | `generate … (checkCloses := false)` (`ShippingMachineFuseTest` 60, programmatic), `#machine_composedT` (`ShippingMachineMemLinkedTest` 56), `#machine_composedTS` (`ShippingMachineSeqLoopTest` 43), `#machine_ships_hier` (44) | NONE design-level. `withMemory.machine_ships_hier` [R] | `shipsHierCheck`, `Bd` = `kidsMem` [T], all-worlds `MachineCloses withMemory` [T] | **never run** at design level (`#machine_design_sv0 withMemory` is a composition, [T] `ShippingShipsDesignSVCommand` 96–98 — it would add an endpoint WITH the four checks). The check-free generator **refuses**: `generateM0 (atForm := true)` — `"{f}: a transported endpoint — not handled here"` (`Tests/Compiler/NoPortsMemOnlyCounterTest.lean` 276). §4.2 — category (b) |
| `mid2` (`ShippingDesignSVTest` 26) AS AN ENTRY | register parent (polymorphic, structure result); child `midH`; depth 1 | `#machine_endpoint` (53) only; as `topD2`'s child everywhere else | NONE as an entry. As a child: `mid2.closes_deep`, `mid2.iface_deep`, `mid2_kid` [V `-a15`] | — | **never run** as an entry. Same shape as `grandH` (BUILT). Category (a), test WRITTEN (§5) |
| `callerBad` (`ShippingCallsCloseTest` 284) | register parent, one-output gate child `pick` | `#machine_endpoint` (304), `closesAtTheorem` (369, programmatic) | `callerBad.machine_sound`, `callerBad.machine_closes_at` [R] | `machine_sound`: `MachineCloses callerBad` (all worlds) [T] | **never run** beyond the closing (it is the fixture of the "failed generation leaves nothing" test). Same shape as `caller`. Category (a), test WRITTEN (§5) |
| `innerPick` (`ShippingMachineInstTest` 99) AS AN ENTRY — `callerInner`'s flattened callee | register machine, one gate call (not `let`-bound) | NONE (not a call entry: flattened into `callerInner`) | NONE | — | **never run**. Same closing as `callerInner` (BUILT). Category (a), test WRITTEN (§5) |
| `callerK` (`ShippingCallsCloseTest` 242), `callerNoEndpoint` (295) | zero-argument caller (legacy route, "not a machine shape" asserted at 269); fixture without data | none / none by design | none | — | **different axis** (legacy route: G2) / deliberately without an endpoint |

### 2.2 Leaf machines (no call) AS ENTRIES — `#machine_endpoint` only

Their strongest endpoint is ship-level of ONE module, [T]
(`Tools/ShippingMachineShipsW.lean` 41–74, `ShippingMachineShipsComb.lean`
202–235, `ShippingMachineShipping.lean` 62–98, 259–290). There is NO
design-level (`DesignSV`) endpoint for a declaration without calls: every
design head takes `f.machine_ships_hier*`, whose generators refuse — `"{declName}: no call"`
(`ShippingMachineSeqCommandR` 31, `ShippingMachineDepthCommandR` 187,
`ShippingMachineSeqCommand` 152), and the check-free ones:
`"{f}: no call (nothing to match: no instance statement)"`
(`ShippingNoPortsCommand` 86; BUILT logs: `cnt` at `-a16` 123, `pe` at `-a21` 108).

| declaration (definition) | kind | endpoint | its non-run, non-reflection premises | in the 29? why not |
|---|---|---|---|---|
| `pe` (`MultiInstanceTest` 34), `cnt` (`ShippingMachineSeqTest` 20), `acc` (`ShippingChildBoundaryTest` 34), `toggleL` (`ShippingMachineSeqLoopTest` 22) | leaf REGISTER machine (`circuit do`; `toggleL`: `Signal.loop`) | `f.machine_ships_wired` and, where `f.machine_closes` is derived, `f.machine_ships_wired_closed` [T; `cnt`, `acc` are generated by their parents' `#machine_endpoint`, `generateCore` 2450–2454 — [I] that the wired form was made] | under `∃ raw`, for every `wof`: `simpleBody b = false`, `seqCheck wof (weOf wof) (checkedOptimize b).body = true`, `(seqNames …).all (declWidth (checkedOptimize b) · == weOf wof ·) = true` — THREE check premises; the open form also `MachineCloses f`. Conclusion `MachineShips` (IR run of `checkedOptimize b` + `runModuleSV` of its emitted statements, ONE module), not `DesignSV` | NO. **base endpoint missing** (no design head for a module without instances) and the three checks are not derived for the ENTRY's `checkedOptimize b`. AS CHILDREN they are covered (`LeafKid`, `leafKid_facts`). Category (b), §4.3 |
| `pickByteH` (`ShippingMachineLinkedTest` 21), `httpGetByte` (`IP/Net/HTTP.lean` 86) | leaf SLOTLESS machine (combinational, machine route) | `c.machine_child` (`#machine_child`, `ShippingMachineLinkedTest` 58, `ShippingMachineTeleTest` 86); `c.machine_ships_comb` [T] | `machine_child`: `MachineCloses c`, antecedent `dropZeroWidthModule raw = raw` → `ChildFn b …` (IR function, no text). `machine_ships_comb`: `simpleBody b = true`, `seqCheck …`, the width agreement, `MachineCloses c` | NO. As children covered (`callerL`, `callerLN`, `hftByte`). As entries: as the row above. Category (b), §4.3 |
| `pick` (`ShippingMachineInstTest` 29), `pickD` (78), `rcH` (`ShippingMachineDepthHTest` 20) | GATE-route leaf (the certified unified gate compiles it; `readMachine` without `allowGate` refuses it) | `c.gate_child` (`#gate_child pick`, `pickD`: `ShippingMachineInstTest` 170–171; `rcH`: by `generateComposed midH` [I]); plus `c.gate_full`, `gate_ports`, `gate_kidK`, `gate_width` (their facts as CHILDREN, BUILT) | `gate_child`: run + `EntryDefines c c.gateValue` → `ChildFn b InRange F` [T `ShippingGateChild` 252–269]. NO check premise. Conclusion: the IR function of the full-entry module `b` — not `checkedOptimize b`, not the emitted text, not `DesignSV` | NO: **different axis**. The gate route's own text-level statements are the S-series (not `#machine_*`; not surveyed here). No `#machine_*` design-level head takes a gate-route entry |
| `divInLoop`, `chain2`, `chain3` (`ShippingMachineTeleTest` 72…) | telescope machines (sub-machines flattened; no `@[hardware_module]` in `IP/Control/DividerQ.lean`: no instance [R]) | `f.machine_sound`; `f.machine_ships(_wired)` [T, the `_of_tele_ext` branch 2614] | as the first row | NO, as the first row. `divInLoop` is in `HierBindsCensusTest.candidates` (81) but has no call entry by reading |
| the other `#machine_endpoint`-only declarations (no `hardware_module` appears in their files, `grep`): `ApplicativeSemanticsTest` 80–92 (13), `ShippingMachineClosesTest` 59–63 (5), `ShippingMachineCombTest` 46–48 (`pickByte`, `ipv4HeaderByte`, `ipv4HeaderChecksumSig`), `ShippingMachineCommandTest` 51–63 (13, incl. `LINHW.checksumHW`, `EcdsaSignDemo.wMulN` / `wTx`, `P256SignDemo.wMul` / `wMulN`, `Fido2Demo.wTx`), `ShippingMachineLoopTest` 78–109 (8, incl. `bottleneckController`, `dividerSignal`), `ShippingMachineNestTest` 117–121 (5), `ShippingMachineNormTest` 130–136 (7), `ShippingMachineRawTest` 15–88 (16), `ShippingSignOpsTest` 30–35 (6) | leaf machines (register or combinational) | `f.machine_sound`, `f.machine_ships`, `…_wired` / `…_comb` [T] | as the first two rows; `f.machine_ships` (the unwired form) additionally asks `seqGate raw`, `seqGate b`, `refineCheck raw raw`, `refineCheck b b`, `"rst" ∈ raw.inputs`, the output-port clause, `dropZeroWidthModule raw = raw` | NO, as the first row. Kind not read one by one |

### 2.3 Keccak and the corpus

| what | read where | state |
|---|---|---|
| Keccak: `keccak256SpongeHW` (`IP/Crypto/Keccak256Sponge.lean` 94), `wKeccakF` (82, a `@[hardware_module]` wrapper whose value is the call `keccakF1600HW …`, a `circuit do` FSM at `IP/Crypto/Keccak256HW.lean` 174), `keccakRcHW` (`Keccak256HW.lean` 42, gate ROM, called at 252) | [R] | NO `#machine_*` / `#gate_*` command is run on any of them anywhere in the repository (`grep`). By shape `sponge → wKeccakF → keccakRcHW` is `grandH → midH → rcH` (said by `ShippingMachineDepthHTest`'s header), with: a wrapper entry (value = an application, not a `circuit do`), 26 output fields, 25 × 64-bit slots, 34 + 2 inputs. **Base endpoints missing; never run.** Whether `#machine_endpoint` accepts them and what the kernel checks cost is NOT known |
| the corpus sweep `scripts/shipping-coverage/endpoints.sh` + `endpoint_tail.lean.in` (NOT run) | [R] lines 36, 68, 76, 112, 123, 134–138, 172, 188–213 | for every machine-route declaration: `generate n (checkCloses := false)` → `f.machine_sound` (+ `machine_ships`, `_wired` / `_comb`): the rows of §2.2, WITH their check premises. For declarations with calls: `generateChild`, `generateLinked`, `generateGateChild`, `generateComposed`, `generateAny` (composedT / TS), `generateCoreN`, and the design heads `ShippingShipsDesignSVCommand.generateH / generate0 / generate n dn` → `f.machine_design_svH`, `…sv0`, `…svN{dn}`: the OLD-boundary endpoints WITH the four check premises, which `ShippingPremiseEval.measure` EVALUATES per declaration (`MOD:PREM`) and whose run boundary is MEASURED by a trace (`TRACE:MATCHED`), not discharged. NO check-free generator (`svHR` / `svNR` / `oneout` / `no_ports*` / `closes_at`) is swept. So: the corpus has no declaration in the 29's class, by construction of the sweep, not by a refusal |

## 3. Programmatic generator uses (not a `#` line)

| where | what | on |
|---|---|---|
| `Tests/Compiler/NoPortsSweepTest.lean` 30 | `Tools.ShippingNoPortsCommand.sweep 1` (logs `NOPORTS SWEEP`) | the 30 names of `HierBindsCensusTest.candidates` (53–83): all are rows of §1 / §2 |
| `Tests/Compiler/ShippingChildBoundaryTest.lean` 335 | `ShippingMachineDepthCommand.generateDesignNR … 1` (a refusal test) | `mixDeep` |
| `Tests/Compiler/ShippingMachineFuseTest.lean` 60 | `ShippingMachineCommand.generate` | `outer`, `siblings`, `withMemory` (fused loops; `outer`, `siblings`: leaf machines, §2.2 class) |
| `Tests/Compiler/NoPortsMemOnly*Test.lean` | `generateM0` (`atForm` false / true) | the five memory-only parents |
| `Tests/Compiler/ShippingCallsCloseTest.lean` 343–369 | `closesAtTheorem` | `callerBad`, `callerNoEndpoint` (failure test) |
| generators recursing into children | `generateCore c` (endpoint), `generateGateChild`, `leafKidTheorem`, `oneOutKidTheorem` | `cnt`, `acc`, `pe`, `rcH`, …: the children of §1's parents |

## 4. What remains, ranked

### (a) Same pattern — a BUILT generator covers the declaration if run

1. **`mid2` as an entry** — `#machine_design_svNR 1`, `#machine_no_ports_kids 1`
   (closing: the existing `mid2.closes_deep`), `#machine_boundary_close`.
   WRITTEN: `Tests/Compiler/NoPortsKidsMid2Test.lean`.
2. **`callerBad`** — `#machine_design_svHR`, `#machine_closes_at`, `#machine_oneout`.
   WRITTEN: `Tests/Compiler/OneOutCallerBadTest.lean`.
3. **`innerPick` as an entry** — `#machine_endpoint`, then as 2.
   WRITTEN: `Tests/Compiler/OneOutInnerPickTest.lean`.
4. **`loopParent`** (§4.1) — one generator branch is missing, supplied in the
   test with the generator's own ten lines; then `#machine_design_svNR 1`,
   `#machine_closes_at`, `#machine_no_ports 1`.
   WRITTEN: `Tests/Compiler/NoPortsLoopParentTest.lean`.
5. NOT written — **the check-free generators over the corpus's callers**: a
   second tail for `endpoints.sh` running `#machine_design_svHR` /
   `#machine_closes_at` / `#machine_oneout_any` (one-output parents) and
   `#machine_design_svNR` / `#machine_no_ports*` (others), logging the
   outcome class per declaration. Not written because the list of corpus
   callers exists only as the OUTPUT of a sweep (`machine_decls.txt`), which
   I must not run, and a script is not a per-declaration test.
6. NOT written — **Keccak** (§2.3): by shape `grandH`'s chain, but every
   base endpoint is missing and the kernel cost (25 × 64-bit slots, `decide`
   over the data) is unmeasured; a first step would be a log-only, time-limited
   probe of `#machine_endpoint` on the three declarations. Whether it is
   category (a) at all is NOT known before that probe.

### 4.1 `loopParent`: the exact missing piece

`toggleL.machine_sound` is made by `#machine_endpoint toggleL`
(`ShippingMachineSeqLoopTest` 35) through `loopProof`
(`Tools/ShippingMachineCommand.lean` 2111–2192: a root `Signal.loop` without
`runs`), i.e. its proof term is an application of
`Tools.ShippingMachineLoop.machine_trace_of_loop` (line 2150–2151).

The depth generators (`generateCoreN`, `ShippingMachineDepthCommand` 139;
`ShippingMachineDepthCommandR` 206) call, for a leaf child,

    def generateSeqChildN (c : Name) : MetaM Name := do          -- ShippingMachineDepthCommand 40–51
      …
      let args ← soundArgs c ``Tools.ShippingMachineAuto.machine_trace_of_data   -- throws for any other head
      let soundL := mkAppN (mkConst ``Tools.ShippingMachineCausal.machine_traceL_of_data) args
      let mut p ← mkAppOptM ``Tools.ShippingMachineDepthRun.seqChildRunN_full #[none, …, soundL]

The theorem `seqChildRunN_full` (`ShippingMachineDepthRun` 276–303) takes ANY
`sound : … → MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc`.
The depth-0 generator has the head table already
(`generateSeqChild`, `ShippingMachineSeqCommand` 53–59:
`_of_data → machine_traceL_of_data`, `_of_loop → machine_traceL_of_loop`,
`_of_regs → machine_traceL_of_regs`) and is BUILT on `toggleL`
(`#machine_composedTS loopParent`).

**Missing: that head table in `generateSeqChildN`** (one `if / else if`
replacing the `soundArgs` line). No theorem is missing by reading. The file
is an existing `Tools/` file, so the test supplies `toggleL.seq_child_runN`
itself (`generateSeqChildN` returns an existing constant, line 42) with the
same code. After the build the proper repair is the three-line change in
`Tools/ShippingMachineDepthCommand.lean` — an integrator / user step.

NOT known: everything after that point in `#machine_design_svNR loopParent 1`
(never reached), and `toggleL.machine_leafKid`'s decided conditions.

### (b) New proof units — the exact missing statements

**(b1) A leaf machine as an ENTRY (§2.2: `pe`, `cnt`, `acc`, `toggleL`, and
every `#machine_endpoint`-only register machine).** Two statements; neither
exists (searched: `Tools/ShippingLeafTyped.lean`, `ShippingChecksRun*.lean`,
`ShippingChecksMaskedLeaf.lean`, `ShippingDesignSVLeaf.lean`,
`ShippingLeafKidFacts.lean`).

    -- (b1.1) the three antecedents of machine_ships_wired, at the emitter's own width map
    theorem leaf_entry_textChecks (K : LeafKid mctx mref cctx cref c dk)
        (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w') :
        simpleBody b = false ∧
        seqCheck (wofOf (checkedOptimize b)) (weS (checkedOptimize b)) (checkedOptimize b).body = true ∧
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == weS (checkedOptimize b) n) = true
    -- what exists: leaf_real_kidK (ShippingLeafTyped 639) gives kidCheck C n y.1 — hence leafCheck y.1 —
    -- for the module the child cache SERVES (y.1 = dropZeroWidthModule raw ∨ mergeChecked …), i.e. for b.
    -- NOT for checkedOptimize b: the parents' theorem for the optimized module is core_designCheck_rest
    -- (ShippingChecksDesign 134), stated over RunFacts C b of a module WITH instances. Whether its
    -- optimizer part applies to an instance-free b was NOT read.

    -- (b1.2) the head: DesignSV at depth 0 of a module without instances is its own text run
    theorem designSV0_of_leaf {C} {o : Module} (hs : o.body.all seqStmtOk = true)
        (h : TextRun o seed T st mems envs) :
        DesignSV C 0 o seed T ⟨st, mems, kids⟩ envs
    -- needs: oracle C o.body E seed = seed for an instance-free body; Resolved, PortsMatch by
    -- portsMatchB_seq / linkedWF_seq (ShippingLeafTyped 120–173, BUILT); the instance clause is vacuous.

With (b1.1) and (b1.2): `f.machine_ships_wired_closed` gives a design-level
endpoint of a leaf register entry with premises run + `MachineDefines f`.
For the SLOTLESS leaves (`pickByteH`, `httpGetByte`, `pickByte`, …) the
analogue over `machine_ships_comb` (`simpleBody b = true`) and, for
`machine_child`, the antecedent `dropZeroWidthModule raw = raw`.

**(b2) `withMemory`: the at-form generator on a TRANSPORTED endpoint.**
`generateM0 (atForm := true)` throws at `back?.isSome`. Missing (generator,
not theorem, by reading): (i) the `RA` twin of the endpoint's head applied to
the FUSED source, transported to the declaration's source by the endpoint's
own equation (`endpointParts`' third component; `generateWith`,
`ShippingMachineShipsHierCommand` 48–54, does this for the cleanup facts);
(ii) `withMemory.machine_composedT`'s proof term is expected to be
`machine_linkedT_mem` on 21 arguments under 11 binders
(`NoPortsMemOnlyCounterTest` 288–298) — for a transported parent it is
wrapped in the transport ([I] from `ShippingMachineMemCommand` 61–96), so
the data arguments must be read under it. Then the data theorem
`MemOnlyData withMemory.machineData 2 4 8` (decided; `nDecl = 2`, widths
4 / 8 by reading the source — NOT measured), and `machineClosesAt_memOnly`
(`halias`, `hargsNd`, `hsep`, `hparent` decided — NOT measured for a parent
with a fused inner loop). Also never run: `#machine_design_sv0 withMemory`
(the base the audit compares with).

**(b3) The leaf-as-entry axis for GATE-route declarations** (`pick`, `pickD`,
`rcH`, `keccakRcHW`): no `#machine_*` head. Statement not designed here
(the S-series owns the gate route's text level).

**(b4) Not needed for any listed declaration, kept from `A-remaining.md`:**
a child that is a `Signal.loop` machine WITH calls under a depth parent
(`generateRunOfR` on a loop child) — no declaration in the tests.

### (c) Items needing a user decision

1. **Shared-descendant closing** (`mixDeep`): `A-shared-descendant.md`,
   `verification-a16.md` 83–90. Blocks `mixDeep.machine_design_noPortsNR2_closed`.
2. **`designCheck`'s statement for a memory child at depth ≥ 1**
   (`verification-a19.md` scope line; `designCheck C 0` tests a child by
   `leafCheck`, `designCheck C (n+1)` by `designCheck C n` — a memory module
   under a depth-≥1 parent meets the second). No test declaration has a
   memory below depth 0 today; `seqMem` is at depth 0.
3. **The head for slotless parents of COMBINATIONAL children only**
   (`A-remaining.md` U5 (5b): the head's reset premise and `hierCheck`'s
   `rst` conjunct). No test declaration.
4. **De-duplication restructuring** of the `core_*` / `M` copies
   (`B-unify-core.md`): 10 re-derived, 7 duplicated; an import cycle.
5. NEW, small: the three-line head table in `generateSeqChildN` (§4.1) — an
   edit of an existing `Tools/` file; and `generateM0`'s place (it lives in
   a TEST file, `NoPortsMemOnlyCounterTest`, and is the only generator of
   the memory-only endpoints).

### (d) General-theorem gaps that no per-declaration work closes

* **Reader**: every endpoint is about ONE declaration's reflected data
  (`f.machineData`, decided conditions). The reader generalisation (R1 / R5 /
  P5 of `G3-reader.md`, `B-readerinv.md`) and the partial-reader replacement
  are what would turn "for this declaration" into "for every accepted
  declaration".
* **All successful inputs**: the 29 + this round's four are instances; no
  theorem quantifies over the compiler's accepted inputs.
* **SV-string level**: every conclusion is `DesignSV` of the module LIST
  (emitted statements run by `runModuleSV`), not the printed string.
* **`#sim`**: not connected.
* **Runtime model**: `RunsTo`, `MachineDefines` / `EntryDefines`, `ChildBnd`
  stay premises of every endpoint.
* **Decided data conditions** per declaration (`callsOk`, `callWidthsOk`,
  name separation, …) are conditions, not reductions.

## 5. WRITTEN this round — not built

| file | endpoint | premise (of the base endpoint generated in the same file) | predicted state |
|---|---|---|---|
| `Tests/Compiler/NoPortsKidsMid2Test.lean` | `mid2.machine_design_noPortsNR1(_closed)`, `…_closedB(_gap)` | `shipsHierCheck`, `kidsMaskedN`, `designCheck 1`, `outsCheck 1` of `mid2.machine_design_svNR1`; `MachineClosesAt mid2`; the boundary's ∀-contexts conjunct | predicted absent, pending build |
| `Tests/Compiler/OneOutCallerBadTest.lean` | `callerBad.machine_design_svH_full(_closed)`, `…_closed_gap` | A₁–A₄ of `callerBad.machine_design_svHR`; `MachineClosesAt callerBad` | predicted absent, pending build |
| `Tests/Compiler/OneOutInnerPickTest.lean` | `innerPick.machine_design_svH_full(_closed)`, `…_closed_gap` | A₁–A₄ of `innerPick.machine_design_svHR`; `MachineClosesAt innerPick` | predicted absent, pending build |
| `Tests/Compiler/NoPortsLoopParentTest.lean` | `loopParent.machine_design_noPortsNR1(_closed)`, `…_closed_gap`; `toggleL.seq_child_runN` (prerequisite) | `shipsHierCheck`, `kidsMaskedN`, `designCheck 1`, `outsCheck 1` of `loopParent.machine_design_svNR1`; `MachineClosesAt loopParent` | predicted absent, pending build |

In each: the run, the reflections and `ChildBnd` STAY premises; the base
endpoint is generated in the same file, so "absent" is a comparison inside
one build. Each file's first command LOGS the reader's data, then asserts it.

### Integrator lines

No `lakefile.lean` entry (no new `Tools/` file; `Tests` is one library).
`Tests/AllTests.lean`, after line 208:

    import Tests.Compiler.OneOutCallerBadTest
    import Tests.Compiler.OneOutInnerPickTest
    import Tests.Compiler.NoPortsKidsMid2Test
    import Tests.Compiler.NoPortsLoopParentTest

Name clashes (none inside `AllTests` by `grep`): `NoPortsKidsMid2Test` adds
`midH.machine_oneOutKid` (also added by the target-only
`NoPortsKidsFamilyTest`, `NoPortsDeepFamilyTest`); `NoPortsLoopParentTest`
adds `loopParent.machine_closes_at` (also added by the target-only
`RemainingProbeTest`).

### Build order

1. `Tests.Compiler.OneOutCallerBadTest` (no unknown but the data conditions);
2. `Tests.Compiler.OneOutInnerPickTest`;
3. `Tests.Compiler.NoPortsKidsMid2Test`;
4. `Tests.Compiler.NoPortsLoopParentTest`;
5. `Tests.AllTests` with the four imports.

### UNVERIFIED, in risk order (highest first)

1. `NoPortsLoopParentTest`: everything after `toggleL.seq_child_runN` in
   `#machine_design_svNR loopParent 1` was never reached by any build; a
   `Bool` result of a `Signal.loop` child through the depth composition, and
   `toggleL.machine_leafKid`'s decided conditions.
2. `NoPortsLoopParentTest`: `seqChildRunNOfLoop` — the eight `mkDecideProof`
   steps (seven are the depth-0 generator's, built; `instFields = []` is
   new), and that `machine_traceL_of_loop` takes the endpoint's argument
   list unchanged (the depth-0 generator relies on the same).
3. `NoPortsKidsMid2Test`: `#machine_no_ports_kids` on a domain-polymorphic
   entry with a structure result (`closedTerm`'s binder order; the decided
   conditions of `mid2.machine_kidsK1` …); the asserted count of 4
   proposition binders (LOGGED before the assertion).
4. `OneOutInnerPickTest`: `#machine_endpoint` on a root whose only call is
   not `let`-bound.
5. `OneOutCallerBadTest`: `#machine_closes_at` on a declaration whose
   closing theorem already exists (the compare path of `closesAtTheorem`).
6. The census itself: rows marked [T] / [I] are readings of templates, not
   of built statements; the per-file "no `hardware_module`" `grep` of §2.2
   is not a reading of each declaration.

## Build record (integrator, 2026-10-13)

Built on poc 13688cd9 + `OneOutCallerBadTest`, `OneOutInnerPickTest`, `NoPortsKidsMid2Test` (worker files
unchanged; all three in AllTests). Established, by the BUILT generators run on declarations they had never
been run on (no new Tools file):
- `callerBad` and `innerPick` (one-output closing): the four check premises of `f.machine_design_svHR`
  (`shipsHierHCheck`, `kidsComb`, `designCheck`, `outsCheck`) are absent from `f.machine_design_svH_full`;
  closed form "other" NONE, goal gap none NOT ALLOWED.
- `mid2` as an entry (`#machine_no_ports_kids`): the four check premises of `mid2.machine_design_svNR1`
  (generated in the same file) are absent from `mid2.machine_design_noPortsNR1(_closed)`; `_closedB`
  boundary `ChildBnd`, 0 NOT ALLOWED.
NOT built: `NoPortsLoopParentTest` — line 212 names `Tools.ShippingMachineDepthRun.SeqChildRunN`, which
does not exist (the definition is in `Tools/ShippingMachineDepth.lean`); everything after it failed in
consequence. Left out of the tree; nothing claimed for `loopParent`.

```
20261013-073709-a22-tests: lake build Tests.Compiler.OneOutCallerBadTest Tests.Compiler.OneOutInnerPickTest Tests.Compiler.NoPortsKidsMid2Test Tests.Compiler.NoPortsLoopParentTest 
result=exit-code
exit=1
memory_peak_file=572055552
error: build failed
20261013-073724-a22-alltests: lake build Tests.AllTests 
result=success
exit=0
memory_peak_file=440225792
Build completed successfully (1240 jobs).
an:127:0: ONEOUT FAMILY callerBad: callerBad.machine_design_svH_full (13 lines; other: the closing premise only) and callerBad.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of callerBad.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap callerBad.machine_design_svH_full_closed_gap: 4 lines, none NOT ALLOWED. SCOPE of this statement: (1) data conditions decided per declaration by the kernel for callerBad (callerBad.oneout_callsOk, _slotLen, _domB, _insts, _instFields
an:130:0: ONEOUT FAMILY Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick: Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick.machine_design_svH_full (13 lines; other: the closing premise only) and Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick.machine_design_svH_full_closed (13 lines; other: NONE) — none of the four check premises of Sparkle.Tests.Compiler.ShippingMachineInstTest.innerPick.machine_design_svHR (shipsHierHCheck, kidsComb, designCheck, outsCheck), no residual; goal gap Sparkle.Tests.Compiler.ShippingMachineInstTes
an:168:0: NOPORTS MID2: Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2 AS AN ENTRY — GENERATED by the built #machine_no_ports_kids: Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_design_noPortsNR1 and Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_design_noPortsNR1_closed (closing: Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.closes_deep) on standard axioms, no statement mentions portsMatchB, kidsPass, designCheck, shipsHierCheck, outsCheck or kidsMaskedN, while Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machine_design_
8687:error: Tests/Compiler/NoPortsLoopParentTest.lean:212:34: Unknown constant `Tools.ShippingMachineDepthRun.SeqChildRunN`
8688:error: Tests/Compiler/NoPortsLoopParentTest.lean:219:0: seq child Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL: Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL.machine_sound is not built from Tools.ShippingMachineAuto.machine_trace_
8690:error: Tests/Compiler/NoPortsLoopParentTest.lean:225:0: Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent: no depth endpoint at depth 1 (Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_ships_hierNR1 is not there: run #machi
8691:error: Tests/Compiler/NoPortsLoopParentTest.lean:229:2: Unknown constant `Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_design_noPortsNR1_closed`
8692:error: Tests/Compiler/NoPortsLoopParentTest.lean:240:0: Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.loopParent.machine_runFacts: not generated
```
