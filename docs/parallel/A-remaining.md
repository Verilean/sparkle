# A / G1: what still carries a compiler-check premise — census by reading, and the next units (round par/a-12)

Branch `par/a-12`, base poc `fdd69046`. NOTHING here was built or run:
the census is a READING of the generator invocations, the generators'
scope tests and the heads' statements. "Read" = the line was read in the
file named; "inferred" = concluded from a neighbouring fact, not read.
WRITTEN, NOT BUILT in this round (§3): three test files, no `Tools/` file.
No premise of any endpoint counts as removed until the integrator's build.

## 0. The check premises, per head (where they were read)

| endpoint family | generator | check premises under `∃ raw D, … ∧ (…)` | read where |
|---|---|---|---|
| `f.machine_design_svHR` | `#machine_design_svHR` (`Tools/ShippingMachineComposeRCommand.lean`) | A₁ `shipsHierHCheck D.modules b` (= `hierCheck && kidsLocal && hierTyped`), A₂ `kidsComb D.modules (checkedOptimize b).body`, A₃ `designCheck (childMap D.modules) 0 (checkedOptimize b)` (incl. `kidsPass`, `portsMatchB`), A₄ `outsCheck … 0 …` | read: `ships_design_svH_all` (`Tools/ShippingShipsDesignSVAll.lean` 135–148), `Tools/ShippingHierPremises.lean` 18–20, the inventory assertion of `Tests/Compiler/OneOutLeafAudit.lean` (BUILT) |
| `f.machine_design_svR0` | `#machine_design_svR0` (`Tools/ShippingMachineSeqCommandR.lean`) | `shipsHierCheck (childMap D.modules) b` (= `hierCheck && instOutWidthsOk`), `Bd b D` = `kidsMixed`, `designCheck … 0 …`, `outsCheck … 0 …`; plus the closing `MachineClosesAt f` | read: `machine_ships_hierC` (`Tools/ShippingMachineShipsHier.lean` 216–230), `ships_design_svN_all`, `ShippingChildBoundaryTest` 96–123 (the four are evaluated there). `kidsMixed` as the instance of `Bd`: inferred from that evaluation, the generator's `Bd` argument was not read |
| `f.machine_design_svNR{n}` | `#machine_design_svNR` (`Tools/ShippingMachineDepthCommandR.lean`) | `shipsHierCheck`, `Bd` = `kidsMaskedN D.modules b.body`, `designCheck … n …`, `outsCheck … n …`; plus `MachineClosesAt f` | read: `generateShipsNR` 597 (`kidsMaskedN`), `ShippingChildBoundaryTest` 246–265, `Tools/ShippingNoPortsCommand.lean` `forbidden` |
| `f.machine_design_sv0`, `…_svN{n}`, `…_svH` | `Tools/ShippingShipsDesignSVCommand.lean` | as `svR0` / `svNR` / `svHR`, AND the old run boundary about the parent's instances (`BoundaryOf` / `BoundaryOfN` / `GateRun` / `MachineRun`) | the checks: read (same head `ships_design_svN_all`); the boundary: inferred from the `R` generators' headers ("No `BoundaryOf` premise") |
| `f.machine_ships_hier`, `…_hierH`, `…_hierN{n}` | — | `shipsHierCheck` / `shipsHierHCheck`, `Bd` | read (`machine_ships_hierC`). NOT design-level: the conclusion is the IR run of the shipped module, not `DesignSV` |

Check-free today (BUILT at `fdd69046`): `f.machine_design_svH_full(_closed)`
for `caller`, `callerTwice`, `callerD`, `callerNested`, `callerRep`,
`callerMix`, `callerABA`, `callerL`, `callerLN`, `hftByte`;
`f.machine_design_noPortsNR1(_closed)` for `parent`, `chained`.

## 1. Census: every declaration with a design-level endpoint that still carries a check premise

Sources: every `#machine_design_sv*` / `#machine_ships_hier*` /
`#machine_composed*` invocation in the repository (all are under
`Tests/Compiler/`; `grep` over `*.lean`: none in `Sparkle/`, `IP/`,
`Examples/`), and the programmatic uses (`sweep` over
`HierBindsCensusTest.candidates`, `generateDesignNR` in
`ShippingChildBoundaryTest` 335).

"reg" = `shape.layout.slots ≠ []` BY READING THE SOURCE (a `Signal.reg` in a
`circuit do`); for `Signal.loop` parents whether the loop's registers are
slots was NOT read (marked `loop`). "out/call" = outputs per call entry
(1 ⇒ `instFields = []`, the one-output closing; >1 or `Bool` ⇒ the general
closing, `Sparkle/Compiler/Elab.lean` per `A-comb-kids.md` §0).

| # | declaration (file) | deepest design-level endpoint | check premises left | reg | children (kind) | out/call | depth | refused by which BUILT generator, at which scan |
|---|---|---|---|---|---|---|---|---|
| 1 | `midH` (`ShippingMachineDepthHTest`) | `midH.machine_design_svHR` | A₁–A₄ | yes | `rcH` (gate) | 1 | 0 | NONE by reading: in the scope of `#machine_oneout` / `#machine_oneout_any`; never run on it (absent from `A-oneout.md` §10's table). §3 |
| 2 | `two` (`ShippingChildBoundaryTest`) | `two.machine_design_svR0` | `shipsHierCheck`, `kidsMixed`, `designCheck 0`, `outsCheck 0`, `MachineClosesAt two` | yes | `cnt`, `acc` (leaf register machines) | 2, 2 | 1 | NONE by reading: in the scope of `#machine_no_ports`; missing prerequisites only — `"{f}: no depth endpoint at depth {n} ({ships} is not there: run #machine_design_svNR {f} {n} first)"`; not in the sweep's candidate list. §3 |
| 3 | `grandH` (`ShippingMachineDepthHTest`) | `grandH.machine_design_svNR1`, `…NR2` (and `…svN1`, old boundary) | `shipsHierCheck`, `kidsMaskedN`, `designCheck n`, `outsCheck n` | yes | `midH` (machine with a register AND a call) | 2 | 1 (`midH → rcH`) | `#machine_no_ports`, `scopeP`: `"{f}: the callee {k} is not a leaf register machine: it has calls of its own (LeafKid.leaf asks shape.insts = []; depth 1 only)"`. Same reason in `ShippingShipsFreeCommand.scope`: `"{f}: the child {k} has calls of its own (not generated)"` |
| 4 | `mixD1` (`ShippingDesignSVTest`) | `mixD1.machine_design_svNR1`, `…NR2` | the same four | yes | `midH` (register + call), `cnt` (leaf register machine) | 2, 2 | 1 | as 3 (callee `midH`) |
| 5 | `topD2` (`ShippingDesignSVTest`) | `topD2.machine_design_svNR2`, `…NR3` (and `…svN2`) | the same four | yes | `mid2` (register + a call of `midH`: a child whose child has a call) | 2 | 2 | as 3 (callee `mid2`) |
| 6 | `mixDeep` (`ShippingChildBoundaryTest`) | `mixDeep.machine_design_svNR2` | the same four | yes | `mid2` (register + a call of `midH`), `midH` (register + a gate call), `cnt` (leaf register machine) | 2 each | 2 | as 3 (callee `mid2`) |
| 7 | `grand` (`ShippingMachineSeqTest`) | `grand.machine_design_svNR2` (`ShippingCallsCloseDeepTest` 25) | the same four | yes | `mid` (register + a call of `cnt`, general closing) | 2 | 1 | as 3 (callee `mid`) |
| 8 | `seqMem` (`ShippingChildBoundaryTest`) | `seqMem.machine_design_svR0` | `shipsHierCheck`, `kidsMixed`, `designCheck 0`, `outsCheck 0`, `MachineClosesAt seqMem` | yes | `cnt` (leaf register machine), a combinational-read MEMORY | 2; memory | 1 | `scopeP`: `"{f}: the callee {k} is not a leaf register machine: it is a memory child (LeafKid is about a machine declaration's data)"`; `#machine_closes_at` (`closesAtCoreG`): `"{c}: a memory child (not derived here)"` |
| 9–13 | `memCounter`, `twoMems`, `mixedMems` (`ShippingMachineMemLinkedTest`), `memWide`, `syncNarrow` (`ShippingDesignSVMemTest`) | `f.machine_design_sv0` | `shipsHierCheck`, `Bd` (inferred `kidsMixed`), `designCheck 0`, `outsCheck 0`; AND the old instance boundary (no `R` endpoint: `#machine_design_svR0` was not run on them) | loop | memory children only (comb read; sync read; both) | memory | 0 (memory leaves) | `scopeP`: the memory-child line, or `"{f}: parent without a register (…)"` first if a loop register is not a slot — not read; measured by `RemainingProbeTest` (B) |
| 14 | `withMemory` (`ShippingMachineFuseTest`) | NONE design-level (`withMemory.machine_ships_hier` only) | `shipsHierCheck`, `Bd` | loop | two memories, `innerCnt` (flattened or a call: not read) | — | — | no design-level endpoint to compare with |
| 15–17 | `engineOnce`, `twinCalls`, `mesh2x2` (`MultiInstance`) | NONE design-level (`f.machine_ships_hier` only) | `shipsHierCheck`, `Bd` | NO (no `Signal.reg`; `clk` / `rst` come from the child) | `pe` (leaf register machine, two registers) | 2 | 1 | `scopeP`: `"{f}: parent without a register (core_portsMatch_raw_leaf asks d.shape.layout.slots ≠ []: the parent's clk and rst ports, which the connections of a sequential child are matched against, are derived from the parent's own register by core_clk)"`; `ShippingShipsFreeCommand.scope`: `"{f}: no register (core_runFacts asks one of the parent)"` |
| 18 | `loopParent` (`ShippingMachineSeqLoopTest`) | NONE design-level (`loopParent.machine_ships_hier` only) | `shipsHierCheck`, `Bd` | yes (`r0`) | `toggleL` (a `Signal.loop` register; `Bool` result) | 1 (`Bool` ⇒ general closing) | 1 | by reading none of `scopeP`'s lines IF `toggleL`'s loop register is a slot; then `"… no depth endpoint at depth 1 …"`. Not read to the end: probe §3 |
| 19 | `mid` (`ShippingMachineSeqTest`) | NONE as an entry (it is `grand`'s child) | — | yes | `cnt` (leaf register machine) | 2 | 1 | in `scopeP`'s scope by shape; `"… no depth endpoint at depth 1 …"`. Probe §3 |
| 20 | `mid2` (`ShippingDesignSVTest`) | NONE as an entry | — | yes | `midH` | 2 | 1 | as 3; `#machine_closes_at mid2` refused `"calls of its own"` (asserted BUILT, `ShippingCallsCloseTest` 634) |
| 21 | `callerInner` (`ShippingMachineInstTest`) | NONE (`#machine_endpoint` only) | — | yes | `pick` ×2 (gate), one call inside the flattened sub-machine `innerPick` | 1 | 0 | `#machine_oneout(_any)`, first scan: `"no {ships}: run #machine_design_svHR {f} first"` (BUILT log, `verification-oneout-a11.md` 92). Whether `#machine_design_svHR callerInner` itself goes through: not read; probe §3 |
| 22 | `divInLoop` (`ShippingMachineTeleTest`; in the census candidates) | not found among the invocations | — | not read | not read | — | — | no design-level endpoint |
| — | Keccak (`IP/Crypto/Keccak256Sponge`: `keccak256SpongeHW`, `wKeccakF`, `keccakRcHW`) | NONE: no `#machine_*` command is run on any Keccak declaration (they appear only in `RtlStructureTest`'s text census). `midH → rcH` is the stand-in for `wKeccakF → keccakRcHW` (`ShippingMachineDepthHTest` header), `grandH` for the sponge | — | — | — | — | — | nothing to refuse: the base endpoints do not exist (`refine-check-shipping` notes "Keccak sponge (seq child with comb kids)" as open) |

`parent`, `chained`: `…_svR0`, `…_svNR1` carry the checks, but the SAME
declaration has `…_noPortsNR1_closed` — not counted. The ten `…_svHR`
parents other than `midH` have `…_svH_full_closed` — not counted.

## 2. The next units (at most five), ranked

Ranking key: (a) declarations with a design-level endpoint that would
become check-free, (b) how much BUILT proof is reused. By (a) alone the
memory unit (U4, seven declarations) would be second; it is ranked after
U2 / U3 because nothing of the check-free chain applies to it as it is
(every `core_*` theorem asks `hnomem`), and U3 needs U2.

### U1 — BUILT generators on the declarations in their scope that were never run (WRITTEN this round, §3)

* (a) `midH` (asserted), `two` (asserted); `mid`, `loopParent`,
  `callerInner` (logs only). (b) reuse: everything; NO new theorem.
* Missing theorem: none by reading. What can fail is a per-declaration data
  condition (a failed kernel `decide`, reported by name) or a
  never-elaborated branch of a generator (`two`: the several-callee
  branches).
* Out of scope: `midH` AS A CHILD (U2).

### U2 — a sequential child WITH one-output combinational calls, under a depth parent: `grandH`, `mixD1` (child `midH`)

* (a) 2 declarations (4 endpoints: `NR1`, `NR2` each); prerequisite of U3.
  (b) reuse: the parent side (`core_runFacts`, `core_outsCheck_all_gate`,
  `core_kidsMaskedN`, `core_portsMatch_shipped_leaf`'s proof, the head
  `machine_design_noPorts`) and, for the child's own module, the one-output
  lemmas of `Tools/ShippingOneOutFacts.lean` / `ShippingOneOutConns.lean`.
* The parent-side theorems take the child's facts as hypotheses over the
  module the child cache serves, `RealChild mref cref c y`. For a LEAF child
  they are discharged by `leaf_real_*` (each asks `dk.shape.insts = []`, by
  `rfl`). MISSING, for a child `c` with data `dk`, `dk.shape.insts ≠ []`,
  `dk.shape.instFields = []`, `dk.shape.layout.slots ≠ []`, gate
  grandchildren (statement SKETCHES; hypothesis names are the consumers'):

      -- (2.1) the bridge: the served module is the shipped module of the child's own run
      theorem oneout_real_run (dk : MachineData) (ok …) (hbody …) …
          (entry : MachineDefines mctx mref cctx cref c dk.shape)
          (closes : ∀ mctx' cctx', MachineClosesAt mctx' mref cctx' cref c dk.shape)   -- or c.machine_closes_at at the child's contexts
          {y : Res} (hy : RealChild mref cref c y) :
          ∃ mctx' cctx' w0 w1 raw, ChildBnd mref cref w0 ∧
            RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w0 (raw, y.2) w1 ∧
            (y.1 = dropZeroWidthModule raw ∨ y.1 = mergeChecked (dropZeroWidthModule raw)) ∧
            MachineDefines mctx' mref cctx' cref c dk.shape ∧ (grandchildren's EntryDefines at mctx' cctx')
      -- extends: leaf_run_* → leaf_real_* (Tools/ShippingLeafTyped.lean, ShippingChecksRun2.lean),
      --          kidsChild_of_real (Tools/ShippingKidsChildIface.lean 357, B3) — whether its proof
      --          already exposes this run was NOT read
      -- (2.2) hkidP / hkidW of core_runFacts
      theorem oneout_real_outs … (hy : RealChild mref cref c y) :
          (∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst") ∧
          (∀ p ∈ y.1.outputs, ∃ o ∈ dk.shape.layout.outs, p.name = o.name ∧ p.ty = o.ty)
      -- extends: seqChild_of_real(…).outsIn, leaf_real_outTys (both ask insts = [])
      -- (2.3) hkidA / hkidR of core_outsCheck_all_gate
      theorem oneout_real_kidA … : outsAssigned y.1 = true ∧ ∀ g ∈ y.2.modules, outsAssigned g = true
      -- extends: leaf_real_kidA / leaf_real_kidR; the second conjunct is about the GRANDCHILD
      --          modules (gate children: gate_kidA, BUILT)
      -- (2.4) hkidM of core_kidsMaskedN
      theorem oneout_real_kidM … : outsMaskedN y.1 = true          -- extends leaf_real_kidM
      -- (2.5) the children's check: the leaf statement `∀ C n, kidCheck C n y.1 = true` is FALSE
      --       for a module with instances (it needs C to hold the grandchild, and n ≥ 1). A new
      --       parent-side theorem beside core_kidsPass_leaf:
      theorem core_kidsPass_at … (hkidK : ∀ k hk y, RealChild mref cref (d.shape.insts[k]).1 y →
            ∀ C, (∀ g ∈ y.2.modules, C g.name = some (g, declWidth g)) → kidCheck C n y.1 = true) … :
          kidsPass (childMap D.modules) (kidCheck (childMap D.modules) n) (checkedOptimize b).body = true
      --       and its child-side instance from core_designCheckH at the child's run (2.1)
      -- (2.6) the ports: LeafKid (Tools/ShippingPortsMatchRawLeaf.lean 58) has the field
      --       `leaf : dk.shape.insts = []`; core_portsMatch_raw_leaf restated over an interface
      --       (PortsIn y.1, output types, input widths in both tables, clk / rst inputs) as
      --       GateChildPorts / SlotlessLeaf.inWidths did for the one-output parents.

* OPEN and not resolvable by reading: the grandchild's reflection is needed
  at the CHILD's run contexts (`mctx'`, `cctx'`); the depth endpoints state
  it there today (`ShippingChildBoundaryTest` 255, "the grandchild
  reflection fact"), so the boundary has it — whether in the form (2.1)
  returns is not read (memory note: "reflection context transfer" open).
* Out of scope: depth ≥ 2, a child under the general closing, memory.

### U3 — depth 2 and children under the general closing: `topD2`, `mixDeep` (child `mid2 → midH`), `grand` (child `mid → cnt`)

* (a) 3 declarations. (b) reuse: U2's interface, made recursive.
* MISSING: (3.1) the child-side facts of U2 for a child whose calls are
  SEQUENTIAL (`mid`, `mid2`: `instFields ≠ []`) — from `core_runFacts`,
  `core_outsCheck_all_gate`, `core_kidsMaskedN`, `core_designCheck*` at the
  CHILD's run, i.e. the `#machine_no_ports` chain's lemmas used as a child's
  facts; (3.2) `kidCheck C n` by induction on the depth (the child's own
  `kidsPass` at `n - 1`), with `closes_deep` (BUILT, B3) supplying the
  child's closing; (3.3) the generator: `scopeP` without "calls of its own",
  a per-callee kind as in `#machine_oneout_any`.
* Out of scope: memory, slotless parents.

### U4 — memory children: `seqMem`, `memCounter`, `twoMems`, `mixedMems`, `memWide`, `syncNarrow` (+ `withMemory`, no design endpoint)

* (a) 6 declarations with a design-level endpoint (7 with `withMemory`).
  (b) reuse: `leafCheck_memModule`, `outsLeaf_memModule`
  (`Tools/ShippingDesignSVMem.lean`: the built memory module is a checked
  leaf) and `kidsMem` / `mixInv`; of the check-free chain: none as is.
* MISSING: (4.1) every `core_*` theorem asks `hnomem : ∀ c ∈ d.shape.insts,
  memChild? c.1 = none` — the wiring of a memory instance by `closeInstsGM`
  is not described (`core_raw_facts`, `core_callConns`); (4.2) the closing:
  `closesAtCoreG` refuses a memory child; (4.3) for the five loop parents
  the derived-boundary endpoint (`…_svR0`) does not exist — only `seqMem`
  has it; (4.4) `Bd` is `kidsMixed`, not `kidsMaskedN`: `core_kidsMaskedN`
  has no memory case.
* Out of scope: `Signal.loop` parents' slots if they are not `layout.slots`
  (not read).

### U5 — parents WITHOUT a register

* (5a) of a sequential child: `engineOnce`, `twinCalls`, `mesh2x2` (3
  declarations; today NO design-level endpoint — `#machine_design_svR0` /
  `…NR 1` was never run on them; whether it goes through is not read).
  MISSING: `core_runFacts`, `core_portsMatch_raw_leaf`, `core_raw_facts` ask
  `hsl : d.shape.layout.slots ≠ []` to derive the parent's `clk` / `rst`
  inputs (`core_clk`); for these parents the ports come from the child
  (`withClockFor`): a second derivation of the same two facts, no statement
  change (the module HAS `rst`).
* (5b) of one-output combinational children: NO declaration in the tests
  (`A-oneout.md` §13.6). NEEDS A STATEMENT CHANGE (the head's reset premise
  `∀ t st, seedIn b ins t st "rst" = 0` is false without an `rst` input;
  `hierCheck`'s last conjunct asks `rst`) and a USER DECISION if the
  conjunct in `Sparkle/IR/HierCheck.lean` is touched. No compiler change is
  designed here.
* Also here if its probe fails: `callerInner` (a call inside a flattened
  sub-machine: the base endpoint `…_svHR` is missing, not a check).

## 3. WRITTEN this round (U1) — not built

    Tests/Compiler/OneOutMidHTest.lean       #machine_oneout_try midH "GENERATED" + the audit of OneOutFamilyTest
    Tests/Compiler/NoPortsTwoTest.lean       #machine_design_svNR two 1, #machine_closes_at two, #machine_no_ports two 1 + audit
    Tests/Compiler/RemainingProbeTest.lean   logs only: mid, loopParent, callerInner; the refusal lines of rows 3–8, 9, 15

| declaration | endpoint | premise (of which endpoint) | predicted state |
|---|---|---|---|
| `midH` | `midH.machine_design_svH_full` (+ `_closed`) | A₁ `shipsHierHCheck` (of `midH.machine_design_svHR`) | WRITTEN — predicted absent, pending build |
| | | A₂ `kidsComb` | predicted absent, pending build |
| | | A₃ `designCheck 0` | predicted absent, pending build |
| | | A₄ `outsCheck 0` | predicted absent, pending build |
| | | `hr`, `MachineDefines midH`, `EntryDefines rcH`, `ChildBnd` | stay premises |
| `two` | `two.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck` (of `two.machine_design_svNR1`, generated in the same file) | WRITTEN — predicted absent, pending build |
| | | `kidsMaskedN` | predicted absent, pending build |
| | | `designCheck 1` | predicted absent, pending build |
| | | `outsCheck 1` | predicted absent, pending build |
| | | `MachineClosesAt two` | predicted absent in `_closed`, pending build |
| | | `hr`, `MachineDefines two`, `MachineDefines cnt`, `MachineDefines acc`, `ChildBnd` | stay premises |
| `mid`, `loopParent`, `callerInner` | — | — | NO prediction: probes, logs only |

Predicted log lines: in the headers of the three files.

SCOPE (binding): one declaration each; data conditions decided per
declaration (conditions, not reductions); the run, the reflections and
`ChildBnd` remain premises; compiler guards with fallback; the conclusion
is `DesignSV` of the module list, not the SV string, not `#sim`. `midH`'s
endpoint is about `midH` as an ENTRY and removes nothing from `grandH`,
`mixD1`, `topD2`, `mixDeep`.

### UNVERIFIED, in risk order

1. `two`: the several-callee branches, never elaborated — `closesAtCoreG`
   with two reflection binders and `sepB` on `cnt` / `acc` / `two` (a name
   premise would be NOT ALLOWED: the test throws); `kidOuts` / `kid` as
   `List.getD […] k _` under `decide` (`callWidthsOk`, `callArgsOk`) and
   under the per-entry `cases k` (`exact … hy` must see
   `(List.getD [cnt.machineData, acc.machineData] 1 _)` as `acc.machineData`
   by reduction); `acc.machine_leafKid`'s decides; `acc.machineData` /
   `acc.machine_closes` exist only if the generators that built
   `two.machine_design_svR0` left them.
2. `two`: `#machine_design_svNR two 1` (two different LEAF children at
   depth 1; `mixD1` — `midH` + `cnt` — is the nearest built case).
3. `midH`: `midH.oneout_callArgs`, `_entries` (the argument is the
   register's read; `rcH.gateBinders` with a domain binder), `_outChars`,
   `_outScalar` on a `Bool` output; a PARENT with two outputs through
   `core_outsCheck_all_gate` / `core_hierTyped₁` (read: no hypothesis asks
   one output; never elaborated with two).
4. `RemainingProbeTest`: the command wrapper `#probe_log … in cmd`
   (`elabCommand` on a nested command, the error scan copied from
   `checkMade`), `Tools.ShippingFinalGoalCommand.gapOf` called from `MetaM`
   inside a `try`; an endpoint generated by a probe stays in the
   environment of the importers.
5. The census itself: rows marked "inferred" / "not read"; `instFields` of
   `loopParent`; whether loop registers are `layout.slots`.

### Build queue

1. `Tests.Compiler.OneOutMidHTest` (imports `Tests.Compiler.OneOutFamilyTest`)
2. `Tests.Compiler.NoPortsTwoTest` (imports `Tests.Compiler.NoPortsTest`)
3. `Tests.Compiler.RemainingProbeTest` (imports 2, `OneOutFamilyTest`, `ShippingMachineSeqLoopTest`)

1 and 2 are independent. No `lakefile.lean` line (no `Tools/` file).
`Tests/AllTests.lean` (integrator):

    import Tests.Compiler.OneOutMidHTest
    import Tests.Compiler.NoPortsTwoTest

`Tests.Compiler.RemainingProbeTest` is TARGET-BUILT ONLY, not for
`AllTests`: a probe that succeeds leaves constants under the declarations'
usual names in that module (see its header). Its log is the measurement
that replaces the "not read" cells of §1.

Same-name hazard checked by `grep` for 1 and 2: no other module runs a
generator on `midH` that adds `midH.oneout_*` / `midH.machine_factsH` /
`rcH.gate_full`, nor on `two` beyond `…_svR0` / `…_composedTS` /
`…_ships_hier` (upstream); `two` is not in the sweep's candidates.
`acc.machine_closes` is asked by the BUILT `two.machine_design_svR0`
generator (`ShippingMachineSeqCommandR` 278), so it is expected upstream.

---

# Round par/a-13 (base poc `e260bf3f`): proper tests for `mid` / `callerInner`; unit U2 written for `grandH`

NOTHING in this section was built or run. Every line is "WRITTEN, NOT
BUILT"; no premise of any endpoint counts as removed until the
integrator's build.

## 4. Task 1 — the two declarations of the probe, as proper tests

| declaration | endpoint | premise (of which endpoint) | predicted state |
|---|---|---|---|
| `mid` | `mid.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck`, `kidsMaskedN`, `designCheck 1`, `outsCheck 1` (of `mid.machine_design_svNR1`, generated in the same file) | WRITTEN (`Tests/Compiler/NoPortsMidTest.lean`; the probe logged OK for the same commands) — predicted absent, pending build |
| | | `MachineClosesAt mid` | predicted absent in `_closed`, pending build |
| | | `hr`, `MachineDefines mid`, `MachineDefines cnt`, `ChildBnd` | stay premises |
| `callerInner` | `callerInner.machine_design_svH_full` (+ `_closed`) | A₁ `shipsHierHCheck`, A₂ `kidsComb`, A₃ `designCheck 0`, A₄ `outsCheck 0` (of `callerInner.machine_design_svHR`, generated in the same file) | WRITTEN (`Tests/Compiler/OneOutCallerInnerTest.lean`) — predicted absent, pending build |
| | | `MachineClosesAt callerInner` | predicted absent in `_closed`, pending build |
| | | `hr`, `MachineDefines callerInner`, `EntryDefines pick`, `ChildBnd` | stay premises |

`mid` AS AN ENTRY gives NOTHING for `grand` (`grand → mid → cnt`):
`grand.machine_design_svNR2` keeps its four check premises; the test
asserts that and that no check-free constant exists under `grand`'s names.

NAME CLASH: `Tests/Compiler/RemainingProbeTest.lean` creates the same
constants. The new tests do not import it; it must not import them. Drop
its sections (A1) and (A3), or keep it target-built only.

## 5. Task 2 — unit U2, as written

### 5.1 Corrections to §2 (U2) by reading

* "OPEN and not resolvable by reading: the grandchild's reflection at the
  child's run contexts" — RESOLVED by reading: `MachineDefines.ctx` and
  `EntryDefines.ctx` (`Tools/ShippingReflectCtx.lean`, BUILT) move a
  reflection to any contexts; `RealChild.inv` gives the child's full-entry
  run from an `InvW` world.
* (2.3) existed: `Tools.ShippingChecksCore.kids_real_kid` (BUILT) is
  `hkidA` / `hkidR` for a child with calls.
* (2.4) as sketched (`hkidM` of `core_kidsMaskedN`) is NOT derivable: that
  hypothesis also asks `outsMaskedN` of the modules of the child's design —
  a GATE grandchild's output is not known to be assigned by a constant or
  a slice. Replaced by a parent theorem that asks the child's own module
  only (`core_kidsMaskedN_top`).
* (2.5) the correct form of the children's check (`core_kidsPass_deep`)
  needs module IDENTITY between the parent's design and the child's, which
  `core_kids_facts` does not state (names only) and `RealChild` does not
  give (two real children of one declaration need not be equal). Both
  closings CHECK it ("found by its name in the merged design as itself"):
  `core_kids_self` reads it off a successful closing.
* The child's module in the parent's design is UNOPTIMISED
  (`checkedOptimize` is applied to the top module only), so the child's
  `…machine_designFullH` (about `checkedOptimize b`) is NOT what the parent
  asks: `designCheck C 0 b` of the raw module is derived
  (`core_designCheck_in₁`) from the raw facts (`core_runFactsH`,
  `core_linkedWF`, `TypedIn`, `…machine_portsRawH`).
* `declWidths dk` is wrong for a child with calls (`declN` counts the call
  binders): the argument widths are `argWidths dk kD` over `dk.bsIn.take kD`.
* The input-width clause of `MachineWired` is under `insts = []`; for a
  machine with one-output calls it is derived (`core_calls_ports₁`, `argW`).

### 5.2 New files and their main statements

    Tools/ShippingChildMapCongr.lean    AgreeOn; linkedWF_congr, noSelfRead_congr, portsMatchB_congr,
                                        kidsPass_congr; outMaskedB_perm_insts; outsMaskedN_of_typed   (pure)
    Tools/ShippingKidsSelf.lean         core_kids_self, core_kidsPass_deep, core_kidsMaskedN_top
    Tools/ShippingCallsChildPorts.lean  argWidths, CallsPorts, CallsPorts.inWidths, core_calls_ports₁,
                                        core_conn_wires₁, outsMaskedN_of_calls
    Tools/ShippingKidFacts.lean         KidFacts; kids_runFacts, kids_outsCheck, kids_maskedN, kids_designCheck
    Tools/ShippingOneOutKid.lean        core_designCheck_in₁; OneOutKid; OneOutKid.core (the bridge),
                                        .outsIn, .kidAR, .ports, .typedIn, .masked, .clk, .check, .facts
    Tests/Compiler/NoPortsGrandHTest.lean   grandH by hand

    theorem core_kids_self … (hB) (hcore : RunsTo (synthesizeCombinationalCore c [] false) … (M, D) w1)
        (entry) (closes) :
        ∀ g ∈ D.modules, ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
          RealChild mref cref (d.shape.insts[k]).1 y ∧ (g = y.1 ∨ g ∈ y.2.modules) ∧
          moduleByName D.modules y.1.name = some y.1 ∧
          ∀ g2 ∈ y.2.modules, moduleByName D.modules g2.name = some g2

    theorem core_kidsPass_deep … (hfne : d.shape.instFields ≠ []) … (n : Nat)
        (hkidK : ∀ k hk (y : Res), RealChild mref cref (d.shape.insts[k]).1 y →
          ∀ ms : List Module, moduleByName ms y.1.name = some y.1 →
            (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
            kidCheck (childMap ms) n y.1 = true ∧ ∀ g ∈ y.2.modules, kidCheck (childMap ms) n g = true) … :
        kidsPass (childMap D.modules) (kidCheck (childMap D.modules) n) (checkedOptimize b).body = true

    theorem OneOutKid.core (K : OneOutKid mref cref c dk nDecl namesK) {y : Res}
        (hy : RealChild mref cref c y) :
        ∃ mctx' cctx' w w1 M D, ChildBnd mref cref w ∧
          RunsTo (synthesizeCombinationalCore c [] false) mctx' mref cctx' cref w (M, D) w1 ∧
          (y.1 = dropZeroWidthModule M ∨ y.1 = mergeChecked (dropZeroWidthModule M)) ∧
          y.2.modules = D.modules

    theorem OneOutKid.check (K : …) {y : Res} (hy : RealChild mref cref c y) (ms : List Module)
        (hms : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
        designCheck (childMap ms) 0 y.1 = true ∧ ∀ g ∈ y.2.modules, ∀ C n, kidCheck C n g = true

    theorem OneOutKid.facts (K : OneOutKid mref cref c dk nDecl namesK) :
        KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl) 1

    theorem kids_designCheck … (hkid : ∀ k hk, KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
        (hcw : callWidthsOk d nDecl kidOuts = true) (hargs : callArgsOk d nDecl kidIns = true) … (hon) (hoty) :
        designCheck (childMap D.modules) n (checkedOptimize b) = true

`OneOutKid` (the `LeafKid`-like interface WITHOUT `leaf`): the callee's data
conditions (`ok`, `body`, `callsOk nDecl`, slot lengths, no late domain
binder, `insts ≠ []`, `instFields = []`, `slots ≠ []`, output width / name /
scalar, no memory callee, the argument split at `nDecl`), the
grandchildren's `KidNames` / `kidA` / `kidR` / leaf-form `kidK`, the name
separation `self`, `portsRaw` (the callee's `…machine_portsRawH` over every
core run), its reflection and closing in every context.

### 5.3 The declaration

| declaration | endpoint | premise (of `grandH.machine_design_svNR1`) | predicted state |
|---|---|---|---|
| `grandH` | `grandH.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN (hand lemmas over the new Tools theorems; none built) — predicted absent, pending build |
| | | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | | `designCheck (childMap D.modules) 1 (checkedOptimize b)` | predicted absent, pending build |
| | | `outsCheck (childMap D.modules) 1 (checkedOptimize b)` | predicted absent, pending build |
| | | `MachineClosesAt grandH` | predicted absent in `_closed` (BUILT `grandH.closes_deep`), pending build |
| | | the boundary (`ChildBnd`, `MachineDefines midH`, `midH`'s own boundary in the contexts it is synthesised in) | STAYS unchanged — its ∀-contexts conjunct is not in the goal-gap classifier's allowed classes; inherited from the base endpoint, not removed |
| | | — | ADDED to the OPEN form: `EntryDefines mctx mref cctx cref rcH rcH.gateValue` (the grandchild's reflection at the run's contexts; already a binder of the BUILT `grandH.machine_design_svNR1_closed`) |
| `mixD1` | — | — | NOT written: needs `KidFacts` of the leaf `cnt` too (`LeafKid → KidFacts n`: each field a BUILT `leaf_real_*`) and `kidOuts` / `kidIns` by entry |
| `topD2`, `mixDeep`, `grand` | — | — | NOT written (U3): `KidFacts … n` for a callee under the general closing = the `kids_*` theorems at the CHILD's run + the ports of a `closeInstsG` module (`withClockFor`'s inputs: not read) |

### 5.4 Not done / open

* No generator: `scopeP` still refuses `grandH`; the hand file copies
  `Tools.ShippingNoPortsCommand.generate` with one change (the extra
  reflection binder).
* The extra reflection binder could be derived from the boundary
  (`ChildRanIn.of_run` + the child's boundary conjunct); not done — the
  shape of the generated child boundary was not read.
* `LeafKid → KidFacts` (for `mixD1`): not written.
* No goal-gap theorem for `grandH` (the inherited boundary is not in the
  classifier's allowed classes).

### 5.5 Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingChildMapCongr» where
      roots := #[`Tools.ShippingChildMapCongr]

    lean_lib «Tools.ShippingKidsSelf» where
      roots := #[`Tools.ShippingKidsSelf]

    lean_lib «Tools.ShippingCallsChildPorts» where
      roots := #[`Tools.ShippingCallsChildPorts]

    lean_lib «Tools.ShippingKidFacts» where
      roots := #[`Tools.ShippingKidFacts]

    lean_lib «Tools.ShippingOneOutKid» where
      roots := #[`Tools.ShippingOneOutKid]

`Tests/AllTests.lean`:

    import Tests.Compiler.NoPortsMidTest
    import Tests.Compiler.OneOutCallerInnerTest
    import Tests.Compiler.NoPortsGrandHTest

Order: (1) `Tests.Compiler.NoPortsMidTest`; (2)
`Tests.Compiler.OneOutCallerInnerTest` (imports 1); independently (3)
`Tools.ShippingChildMapCongr`, (4) `Tools.ShippingKidsSelf`, (5)
`Tools.ShippingCallsChildPorts` (imports 3), (6) `Tools.ShippingKidFacts`
(imports 4), (7) `Tools.ShippingOneOutKid` (imports 5, 6), (8)
`Tests.Compiler.NoPortsGrandHTest` (imports 7, `OneOutMidHTest`,
`NoPortsTwoTest`, `ShippingCallsCloseDeepTest`).

### 5.6 UNVERIFIED, in risk order

1. `core_calls_ports₁` (`Tools/ShippingCallsChildPorts.lean`): the copied
   run prelude with the 18-part pattern of `MachineWired`, `calls_ports`
   before the pattern, `closeInsts_inputs` / `closeMachine_inputs`, the
   `match` on `p.ty` of `weOf_of_port` after `rw [hty]`, `rw [hweb]` on an
   applied `weOf b`, the frame of `closeMachine_typed`.
2. `Tools/ShippingChildMapCongr.lean`: the `simp only [f, …]` unfoldings of
   `linkedWF` / `linkedWrites` on each constructor (catch-all alternatives),
   `simp only [e]` reducing the `match` of `noSelfRead` / `portsMatchB` /
   `kidsPass` on `.inst`, `Perm.count_eq`, `writesOf_insts`.
3. `NoPortsGrandHTest`: `generateH` / `closeDeep` (MetaM; the premises of
   `grandH.closes_deep` are ASSUMED to be the reflections of `midH` and
   `rcH`, of `midH.closes_deep` the reflection of `rcH` only — read off the
   BUILT "DEEP CLOSINGS … (2, 2, 3, 3)" line, not off the statements);
   `MachineDefines midH` found among the boundary's conjuncts; the six
   `decide`s of `midH_kid`'s argument split; `grandH_callArgs` against
   `argWidths`; the audit's binder count (4) and its `bad.size ≤ 1`.
4. `core_kids_self`: `closeInsts_names` / `closeInsts_acyclic` /
   `closeInstsG_names` on `hcc`'s two cases; `rw [← hDeq]`.
5. `core_designCheck_in₁`: `simp only [childMap, h1, h2]`, `textCheckI_of`'s
   argument order, `kidCheck … 0` after `simp only [hc]`.
6. `OneOutKid.core`: `synthesizeCombinational_designL (M' := y.1) (D' := y.2)`
   against a run returning `y` (pair eta); `OneOutKid.facts`: `kidCheck C 1`
   as `kidCheck C (0 + 1)`.
7. Task 1: `OneOutCallerInnerTest` imports `NoPortsMidTest` (to reproduce
   the probe's environment); a failure of the latter blocks the former.
