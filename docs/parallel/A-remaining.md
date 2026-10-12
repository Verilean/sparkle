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

---

# Round par/a-14 (base poc `099dacf0`): `grandH`'s boundary, `mixD1`, the generator for two kinds of callees

NOTHING in this section was built or run. Every line is "WRITTEN, NOT
BUILT"; no premise of any endpoint counts as removed until the
integrator's build.

## 6. Task 1 — the ∀-contexts conjunct of the boundary

### 6.1 `grandH.machine_design_noPortsNR1_closed`: YES, it follows from the binders

READ (real log, `verification-a13.md` 88–105): binders `entry :
MachineDefines … grandH`, `hR_…midH : MachineDefines mctx mref cctx cref
midH midH.machineData.shape`, `hRr : EntryDefines mctx mref cctx cref rcH
rcH.gateValue`; ONE antecedent under the existentials,

    ChildBnd mref cref w ∧ MachineDefines mctx mref cctx cref midH … ∧ True ∧
      ∀ mctx' cctx', ChildRanIn mref cref midH mctx' cctx' →
        ∀ wc raw D, ChildBnd mref cref wc →
          ChildBnd mref cref wc ∧ EntryDefines mctx' mref cctx' cref rcH rcH.gateValue

READ (generator, `Tools/ShippingMachineDepthCommandR.lean` 302–336): the
shape is `MachineDefines c ∧ (conj names ∧ ∀ mc' cc', ChildRanIn … c mc'
cc' → ∀ wc raw D, ChildBnd wc → Bnd_c mc' cc' wc raw D)`; `conj [] = True`
(`ShippingMachineShipsHierCommand.conj`).

The last conjunct is `fun _ _ _ _ _ _ hb => ⟨hb,
Tools.ShippingReflectCtx.EntryDefines.ctx hRr⟩`: `EntryDefines` has no world
argument and does not depend on the contexts (BUILT). `ChildRanIn` is not
used. Conjunct 2 is a binder. So under the binders the antecedent is
equivalent to `ChildBnd mref cref w`.

WRITTEN: `Tools/ShippingBoundaryClose.lean` (`#machine_boundary_close thm`
→ `thmB`; general, MetaM, no new statement about the compiler: each
NOT-ALLOWED antecedent is replaced by the conjunction of its conjuncts that
do NOT follow from the binders by {a binder, `True`, `∧`, `∀ … →` with its
own hypotheses, `MachineDefines.ctx`, `EntryDefines.ctx`}; `thmB` is `thm`
applied to the reassembled antecedent; a conjunct that is not derived is
KEPT and logged; nothing derived ⇒ error) and
`Tests/Compiler/NoPortsGrandHBTest.lean`:

| endpoint | premise (of `grandH.machine_design_noPortsNR1_closed`) | predicted state |
|---|---|---|
| `grandH.machine_design_noPortsNR1_closedB` | antecedent conjuncts `MachineDefines midH`, `True`, the ∀-contexts conjunct | WRITTEN — predicted absent from the antecedent, pending build |
| | `ChildBnd mref cref w` | stays (the one antecedent) |
| | binders (run, `MachineDefines grandH`, `MachineDefines midH`, `EntryDefines rcH`) | stay; none added |
| `…_closedB_gap` (`#machine_goal_gap_of`) | — | predicted: no `gap_…` hypothesis; premise listing 0 NOT ALLOWED |

### 6.2 The base family (same command; probe `Tests/Compiler/BoundaryCloseBaseProbe.lean`, logs only)

* `grandH.machine_design_svNR1_closed` (and `…NR2_closed`): READ — its
  boundary is the antecedent quoted above (the audit of `NoPortsGrandHTest`
  compares it with an antecedent of the OPEN base form; the closed base
  form has the reflections of `midH` and `rcH` as binders: "DEEP CLOSINGS
  … (2, …)"). The same derivation applies: the boundary reduces to
  `ChildBnd`. The four check antecedents are untouched (they are
  equations; the command keeps them). At depth 2 the same child `midH` has
  the same boundary (INFERRED: `bndOf` is per child).
* `mixD1.machine_design_svNR1_closed` (and `…NR2_closed`): INFERRED from
  the generator — boundary `ChildBnd ∧ (MachineDefines midH ∧ names ∧
  ∀-contexts conjunct about rcH) ∧ MachineDefines cnt` (`cnt` is `free`:
  `cnt.machine_closes` exists, so only its `MachineDefines` is asked);
  binders: reflections of `midH`, `rcH`, `cnt` (3, BUILT log). Reduces to
  `ChildBnd` IF `names` is `True` as in `grandH` (same child, same
  generator; not read off the statement).
* `topD2.machine_design_svNR2_closed` (and `…NR3_closed`): INFERRED —
  `mid2`'s conjunct is `MachineDefines mid2 ∧ names ∧ ∀ ctx', ChildRanIn
  mid2 ctx' → ∀ wc raw D, ChildBnd wc → Bnd_mid2 ctx' wc raw D` with
  `Bnd_mid2 = ChildBnd wc ∧ (MachineDefines ctx' midH ∧ names ∧ ∀ ctx'',
  ChildRanIn midH ctx'' → … EntryDefines ctx'' rcH)`. With the binders
  `MachineDefines mid2 / midH`, `EntryDefines rcH` (3, BUILT log) every
  part is a reflection moved by `.ctx`, a local `ChildBnd`, or `True`: the
  same lemma, one level deeper (the solver recurses through `∀`). NOT READ:
  whether `mid2`'s conjunct also carries `MachineClosesAt mid2` at the
  child's contexts (the generator's `namesOf.get? c = none` branch, line
  326: `closesAt ∧ bndHere`) — a closing does NOT transfer between contexts
  (`ShippingReflectCtx` header), so that conjunct would be KEPT, NOT
  ALLOWED. MISSING in that case: `∀ mctx' cctx', ChildRanIn mref cref mid2
  mctx' cctx' → MachineClosesAt mctx' mref cctx' cref mid2
  mid2.machineData.shape` from the reflections (a `mid2.closes_deep` in
  every context; whether one exists was not read). Also not read: whether
  `Bnd_mid2` is a `….machineBoundN…` constant (the solver unfolds those).
* `mixDeep.machine_design_svNR2`: NO closed form exists (`#machine_closes_deep
  mixDeep` was never run; READ `ShippingCallsCloseDeepTest`). The open
  form's only reflection binder is `MachineDefines mixDeep`; the
  reflections of `mid2`, `midH`, `cnt` are boundary conjuncts and `rcH`'s is
  only under the ∀-contexts conjuncts. `.ctx` does NOT give the reduction:
  it moves a reflection between contexts but needs ONE instance of it, and
  the conjunct `∀ ctx', ChildRanIn midH ctx' → … EntryDefines ctx' rcH`
  yields an instance only from a `ChildRanIn midH ctx'` witness, which
  exists only after the run (a child's real run), not at the level of the
  statement's binders. MISSING: either the binder `EntryDefines mctx mref
  cctx cref rcH rcH.gateValue` (i.e. the closed form: run
  `#machine_closes_deep mixDeep`, then the same command), or a statement
  "a run of `mixDeep`'s core entry from a `ChildBnd` world gives `∃ mctx'
  cctx', ChildRanIn mref cref midH mctx' cctx'`" — not available today.

## 7. Task 2 — `mixD1` by hand

    Tools/ShippingLeafKidFacts.lean            leafKid_facts
    Tests/Compiler/NoPortsMixD1Test.lean       mixD1_tables, mixD1_runFacts/_outsG1/_maskedG/_designP1, the endpoint, the audit
    Tests/Compiler/NoPortsMixD1BTest.lean      #machine_boundary_close + #machine_goal_gap_of + audit

    theorem leafKid_facts (K : LeafKid mctx mref cctx cref c dk) (n : Nat) :
        KidFacts mref cref c dk.shape.layout.outs (Tools.ShippingPortWidthsPure.declWidths dk) n

    theorem mixD1_tables (hRm : MachineDefines mctx mref cctx cref ``midH midH.machineData.shape)
        (hRr : EntryDefines mctx mref cctx cref ``rcH rcH.gateValue)
        (hRc : MachineDefines mctx mref cctx cref ``cnt cnt.machineData.shape) :
        ∃ (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat),
          (∀ k (hk : k < mixD1.machineData.shape.insts.length),
            KidFacts mref cref (mixD1.machineData.shape.insts[k]).1 (kidOuts k) (kidIns k) 1) ∧
          callWidthsOk mixD1.machineData 1 kidOuts = true ∧
          callArgsOk mixD1.machineData 1 kidIns = true

READ vs INFERRED about `mixD1`'s data: header of `NoPortsMixD1Test.lean`
(READ: the source, the callees, the projected fields; INFERRED and asserted
on the reader's data first: `nDecl = 1`, two entries, one per callee; the
entry ORDER is not assumed — `mixD1_tables` tries both).

| declaration | endpoint | premise (of `mixD1.machine_design_svNR1`) | predicted state |
|---|---|---|---|
| `mixD1` | `mixD1.machine_design_noPortsNR1` (+ `_closed`) | `shipsHierCheck`, `kidsMaskedN`, `designCheck 1`, `outsCheck 1` | WRITTEN — predicted absent, pending build |
| | | `MachineClosesAt mixD1` | predicted absent in `_closed` (`mixD1.closes_deep`, BUILT), pending build |
| | | the boundary | stays in `_closed`; reduced to `ChildBnd` in `_closedB` (predicted, pending build) |
| | | — | ADDED to the open form: `EntryDefines rcH` at the run's contexts |

## 8. Task 3 — the generator

`Tools/ShippingNoPortsKidsCommand.lean`: `#machine_no_ports_kids f n`
(`_try`: refusal logged). Callees: leaf register machines
(`leafKid_facts`) or register machines with one-output calls of ONE gate
child (`k.machine_oneOutKid`, generated as the hand `midH_kid`; depth 1).
Compare path: an existing endpoint name ⇒ the statement is rebuilt, added
as `…_regen`, and must be `isDefEq` the existing one (error otherwise).
Refused with a reason: memory callee, callee without a machine endpoint,
callee without a register, leaf callee without `machine_closes`, callee
with calls under the general closing, several distinct grandchildren, a
machine grandchild, missing `oneout_*` / `machine_portsRawH` /
`closes_deep` / `gate_full` / `gate_kidK`, depth ≠ 1 with a one-output
callee, parent without a register, parent under the one-output closing.
`Tests/Compiler/NoPortsKidsFamilyTest.lean`: `grandH` (compare), `mixD1`
(generated; then `_closedB` and its gap), refusals `topD2`, `mixDeep`,
`grand`, and `parent` (leaf-only, log only).

## 9. Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingBoundaryClose» where
      roots := #[`Tools.ShippingBoundaryClose]

    lean_lib «Tools.ShippingLeafKidFacts» where
      roots := #[`Tools.ShippingLeafKidFacts]

    lean_lib «Tools.ShippingNoPortsKidsCommand» where
      roots := #[`Tools.ShippingNoPortsKidsCommand]

`Tests/AllTests.lean` (ONE of the two alternatives — the hand `mixD1` files
and the family test define the same `mixD1.*` constants):

    import Tests.Compiler.NoPortsGrandHBTest
    import Tests.Compiler.NoPortsKidsFamilyTest          -- (A) generator in AllTests; NoPortsMixD1Test / NoPortsMixD1BTest target-built only
    -- or (B): import Tests.Compiler.NoPortsMixD1BTest   -- hand files in AllTests; NoPortsKidsFamilyTest target-built only

`Tests.Compiler.BoundaryCloseBaseProbe`: target-built only (leaves `…B`
constants under the base endpoints' names).

Order: (1) `Tools.ShippingBoundaryClose`; (2)
`Tests.Compiler.NoPortsGrandHBTest`; (3) `Tools.ShippingLeafKidFacts`; (4)
`Tests.Compiler.NoPortsMixD1Test`; (5) `Tests.Compiler.NoPortsMixD1BTest`;
(6) `Tests.Compiler.BoundaryCloseBaseProbe`; (7)
`Tools.ShippingNoPortsKidsCommand`; (8)
`Tests.Compiler.NoPortsKidsFamilyTest`. (4)/(5) and (8) must be SEPARATE
lake targets (never one import closure).

## 10. UNVERIFIED, in risk order

1. `Tools/ShippingNoPortsKidsCommand.lean`: ~500 lines of quoted syntax
   never elaborated — the term-mode `have hent … ; { … }` before a structure
   instance, the `rw [hent k hk] at hy ⊢` with a local hypothesis, the
   `(fun _ => …) k` tables under `rw` / `exact`, `closedTerm`'s binder
   arithmetic, the compare path (`isDefEq` of the rebuilt and the hand
   statements of `grandH`), `Ctx.binders` hygiene across quotations (as
   `portsTheorem` does).
2. `mixD1_tables`: `first | (refine …; intro …; cases …) | …` with nested
   `by first | decide | decide +kernel` (a wrong-order `decide` must fail,
   not time out); the unifier seeing `(mixD1.machineData.shape.insts[0]).1`
   as the callee's name and `List.getD […] 0 []` as its head under `exact`
   (the BUILT generator relies on the same for `two`); the entry order and
   count of `mixD1` (asserted first, never measured).
3. `Tools/ShippingBoundaryClose.lean`: `transfer?` (`forallMetaTelescope`
   on the `.ctx` lemmas, `withoutModifyingState`), the hand-built
   `And.left/right/intro` and `Exists.elim/intro` terms, `solve` through
   the `∀` (proposition binders as hypotheses), that `names` is literally
   `True` in `mixD1`'s boundary.
4. `leafKid_facts`: argument orders of nine `leaf_real_*` lemmas (read off
   their signatures); `check` at `childMap ms`.
5. `closeDeep` on `mixD1.closes_deep`: its three premises ASSUMED to be
   the reflections of `midH`, `cnt`, `rcH` with the contexts as its first
   four binders (the audits' binder count 5 throws otherwise).
6. The audits' `ppExpr`-string comparison of binders (`auditB`), the
   `parent` compare (`machine_closes_at`'s binder order not read; `_try`).

## 11. Repair after the first build of par/a-14 (WRITTEN, NOT BUILT)

BUILT by the integrator: `Tools.ShippingBoundaryClose`,
`Tools.ShippingLeafKidFacts`, `NoPortsGrandHBTest` (closedB: 0 NOT ALLOWED,
gap theorem generated), `BoundaryCloseBaseProbe`. FAILED:
`NoPortsMixD1Test`, `Tools.ShippingNoPortsKidsCommand`.

MEASURED (build log): `mixD1`'s call entries are `[midH, midH, cnt, cnt]`
(one entry per projected field; FOUR entries) — the "two entries, either
order" of §7 was wrong.

Changes: `NoPortsMixD1Test` — the abbreviations `dM` / `dC` are gone (the
constants are written out; the compiler rejected the abbreviations);
`outsT` / `insT` are `noncomputable def`s `if k < 2 then (midH's) else
(cnt's)`; ONE decided statement `mixD1_entry : ∀ k hk, (insts[k]).1 = if k
< 2 then midH else cnt`; `mixD1_tables` is `rw [mixD1_entry k hk]` and a
case split on `k < 2` (no `first` over orders); the data assertion asks
exactly `[midH, midH, cnt, cnt]`. `Tools.ShippingNoPortsKidsCommand` —
`let env ← getEnv` before the pure `let cl?`; the per-entry tables and the
nested `cases` already run over the reader's ENTRIES (4 for `mixD1`), the
single-callee case over a decided ∀ (2 entries for `grandH`).

---

# Round par/a-15 (base poc `c46b309c`): unit U3 — a callee under the GENERAL closing (`grand → mid → cnt`, `topD2 → mid2 → midH → rcH`)

NOTHING in this section was built or run. Every line is "WRITTEN, NOT
BUILT"; no premise of any endpoint counts as removed until the
integrator's build.

## 12. What was read (task 1)

* `grand` (`Tests/Compiler/ShippingMachineSeqTest.lean` 62–69, READ):
  callee `mid`; `mid`'s callee `cnt` (leaf register machine). MEASURED for
  `mid`: `nDecl = 2`, entries `[cnt, cnt]`, `instFields ≠ []`
  (`verification-a13.md`). `grand`'s `nDecl` / entries: NOT measured —
  asserted by the first `run_cmd` of `NoPortsGrandTest` (logged before the
  checks), `grand_entry` is one decided ∀-statement.
* `grand.machine_design_svNR2` (`ShippingCallsCloseDeepTest` 25): MEASURED
  to carry `shipsHierCheck`, `designCheck … 2`, `outsCheck … 2`,
  `kidsMaskedN` (`verification-a14.md` 146–150); the statement text itself
  was not printed anywhere and was not read.
* Why `LeafKid` / `OneOutKid` do not apply to `mid`: `LeafKid.leaf` asks
  `insts = []`; `OneOutKid.oneOut` asks `instFields = []`, used by
  `core_calls_ports₁` / `core_conn_wires₁` / `core_runFactsH` /
  `core_designCheck_in₁`. READ of what the general closing changes
  (`Sparkle/IR/MachineInstG.lean` 73–78, `Tools/ShippingMachineInstG.lean`
  451–490): `closeInstsG` closes `withClockFor children m₀`, whose inputs
  are `m₀`'s, or `m₀`'s with `clk`, `rst` appended; outputs, wires, name,
  body are `m₀`'s (`withClockFor_same`). Everything else `core_calls_ports₁`
  uses (`MachineWired`, `calls_ports`, `CloseCalls.some`) does not read the
  closing. `RealChild mid y` gives (`RealChild.inv`) a run of `mid`'s FULL
  entry from an `InvW` world in some contexts — the bridge of
  `OneOutKid.core` uses only `core_kids_facts` (either closing) and goes
  through unchanged.
* The depth: `KidFacts c … m` `.check` asks `kidCheck C m` of the child's
  module AND of every module of its design (what `core_kidsPass_deep`
  consumes). For a callee under the general closing at `m = n + 1` this
  needs its callees' `KidFacts` at `n` (its own `designCheck C n`) AND at
  `n + 1` (the modules of its design): `GenKid.kidsLo` / `kidsHi`. No
  depth-2 form of `kids_*` / `core_kidsPass_deep` is needed: they are
  already stated for every `n`.

## 13. New files and main statements

    Tools/ShippingCallsPortsG.lean      core_calls_portsG, core_conn_refsG, outsMaskedN_of_callsG
    Tools/ShippingGenKid.lean           kids_designCheck_in, GenKid, .core, .outsIn, .kidAR, .ports,
                                        .typedIn, .masked, .clk, .check, .facts
    Tools/ShippingOneOutKidDepth.lean   core_designCheck_inN₁, checkN, factsN
    Tests/Compiler/NoPortsGrandTest.lean / NoPortsGrandBTest.lean
    Tests/Compiler/NoPortsTopD2Test.lean / NoPortsTopD2BTest.lean

    theorem core_calls_portsG … (hfne : d.shape.instFields ≠ []) … (hsl) (kD) (hkD) (hIlen) (hSL) (hSlen)
        (hLlen) (hNIn) (hB) (hcore) (hpost) (entry) (closes) : CallsPorts c d kD b

    theorem kids_designCheck_in … (hsl) (hfne) … (kidOuts) (kidIns) (n : Nat)
        (hkid : ∀ k hk, KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
        (hcw : callWidthsOk d nDecl kidOuts = true) (hargs : callArgsOk d nDecl kidIns = true)
        (hB) (hcore) (hpost) (entry) (closes) (hon) (hoty)
        (ms : List Module) (hms : ∀ g ∈ D.modules, moduleByName ms g.name = some g) :
        designCheck (childMap ms) n b = true

    structure GenKid (mref) (cref) (c : Name) (dk : MachineData) (nDecl : Nat)
        (namesK : Nat → List String) (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat)
        (n : Nat) : Prop      -- data conditions, `general : instFields ≠ []`, the argument split,
                              -- kid (KidNames), self, kidsLo (KidFacts … n), kidsHi (KidFacts … (n + 1)),
                              -- callW, callA, entry / closes in every context

    theorem GenKid.check (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) {y : Res}
        (hy : RealChild mref cref c y) (ms : List Module)
        (hms : ∀ g ∈ y.2.modules, moduleByName ms g.name = some g) :
        designCheck (childMap ms) n y.1 = true ∧
          ∀ g ∈ y.2.modules, kidCheck (childMap ms) (n + 1) g = true

    theorem GenKid.facts (K : GenKid mref cref c dk nDecl namesK kidOuts kidIns n) :
        KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1)

    theorem Tools.ShippingOneOutKidDepth.factsN (K : OneOutKid mref cref c dk nDecl namesK) (n : Nat) :
        KidFacts mref cref c dk.shape.layout.outs (argWidths dk nDecl) (n + 1)

## 14. The declarations

| declaration | endpoint | premise (of the base endpoint `…machine_design_svNR2`) | predicted state |
|---|---|---|---|
| `grand` | `grand.machine_design_noPortsNR2` (+ `_closed`) | `shipsHierCheck (childMap D.modules) b` | WRITTEN — predicted absent, pending build |
| | | `kidsMaskedN D.modules b.body` | predicted absent, pending build |
| | | `designCheck (childMap D.modules) 2 (checkedOptimize b)` | predicted absent, pending build |
| | | `outsCheck (childMap D.modules) 2 (checkedOptimize b)` | predicted absent, pending build |
| | | `MachineClosesAt grand` | predicted absent in `_closed` (BUILT `grand.closes_deep`), pending build |
| | | — | ADDED to the OPEN form: `MachineDefines cnt` at the run's contexts (a binder of the base CLOSED endpoint already) |
| | `grand.machine_design_noPortsNR2_closedB` (+ `_gap`) | the boundary's conjuncts other than `ChildBnd` | predicted DERIVED from the binders (measured on the base closed endpoint), 0 NOT ALLOWED, no gap hypothesis; pending build |
| `topD2` | `topD2.machine_design_noPortsNR2` (+ `_closed`) | the same four, at depth 2 | WRITTEN — predicted absent, pending build |
| | | `MachineClosesAt topD2` | predicted absent in `_closed` (BUILT `topD2.closes_deep`), pending build |
| | | — | ADDED to the OPEN form: `MachineDefines midH`, `EntryDefines rcH` at the run's contexts (the second may be a conjunct of the boundary already — `names(mid2)`, inferred; then it is a redundant binder of the open form) |
| | `topD2.machine_design_noPortsNR2_closedB` (+ `_gap`) | the boundary's conjuncts other than `ChildBnd` | predicted DERIVED (measured on the base closed endpoint), pending build |
| `topD2` at depth 3 | `topD2.machine_design_svNR3` | the four checks | NOT written: `GenKid mid2` at `n = 2` (`kidsLo` = `factsN … 1`, `kidsHi` = `factsN … 2`) and `kids_*` at 3 — the same theorems, not instantiated |
| `mixDeep` | `mixDeep.machine_design_svNR2` | the four checks | NOT written. It lacks (i) a closed base form — `#machine_closes_deep mixDeep` was never run, so there is no `mixDeep.closes_deep` and no `…_svNR2_closed`; (ii) with it, the hand chain is `mixD1`'s pattern with three kinds of entries: `GenKid.facts` of `mid2` (this round), `factsN (midH_kid …) 1` of `midH` at depth 2, `leafKid_facts … 2` of `cnt`; (iii) the open form would need the reflections of `midH`, `rcH` (and possibly `cnt`) at the run's contexts as binders, as §6.2 states |

## 15. Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingCallsPortsG» where
      roots := #[`Tools.ShippingCallsPortsG]

    lean_lib «Tools.ShippingGenKid» where
      roots := #[`Tools.ShippingGenKid]

    lean_lib «Tools.ShippingOneOutKidDepth» where
      roots := #[`Tools.ShippingOneOutKidDepth]

`Tests/AllTests.lean`:

    import Tests.Compiler.NoPortsGrandBTest
    import Tests.Compiler.NoPortsTopD2BTest

Order: (1) `Tools.ShippingCallsPortsG`; (2) `Tools.ShippingGenKid` (imports
1); (3) `Tests.Compiler.NoPortsGrandTest`; (4)
`Tests.Compiler.NoPortsGrandBTest`; independently (5)
`Tools.ShippingOneOutKidDepth`; (6) `Tests.Compiler.NoPortsTopD2Test`
(imports 2, 5); (7) `Tests.Compiler.NoPortsTopD2BTest`. 3–4 and 6–7 are
independent of each other (a failure of `topD2` does not block `grand`).

Name clashes checked by `grep`: no module defines
`grand.machine_design_noPortsNR2*` or `topD2.machine_design_noPortsNR2*`
(`NoPortsKidsFamilyTest` and `RemainingProbeTest` only run the REFUSING
`_try` commands on them; `BoundaryCloseBaseProbe` creates
`…_svNR2_closedB`, other names).

## 16. UNVERIFIED, in risk order

1. `NoPortsTopD2Test`: nothing about `mid2` / `topD2` was measured (`nDecl`,
   entries — asserted first); `midH_names` (`kidsChild_of_real` over the
   fields of `midH_kid`, `rw [h] at h0`); `mid2_kid.self` (a kernel
   `decide` of the name separation of `mid2` from `midH`, `rcH` through
   nested `declsOf`); the premise order of `mid2.closes_deep` (`first` over
   both); `generateX` / `closeDeepX` (MetaM, `withLocalDeclsD`); the audit's
   binder count 5.
2. `core_calls_portsG`: the copied run prelude; `rcases hcc with ⟨hfe, -⟩ |
   ⟨-, hG, -⟩`; `withClockFor` named unqualified under `open
   Sparkle.IR.Machine`; `rw [e] at hpw` on `(withClockFor …).inputs`;
   `absurd (congrArg Port.name h) hp3.1` (a projection of a structure
   literal against `"clk"`).
3. `kids_designCheck_in`: `simp only [hc]` on the `kidsPass` match at depth
   `n`; `core_kids_self`'s argument order; `(hkid k hk).check` after
   `obtain` of the dependent `hk`.
4. `NoPortsGrandTest`: `grand`'s data (`nDecl = 1`, every entry `mid`) and
   its decided conditions (`callWidthsOk` / `callArgsOk` against `mid`; the
   lifted `nz` binding is new against `grandH`); `mid_kid`'s decides at
   `nDecl = 2`; `mid.closes_deep` with exactly one premise (the reflection
   of `cnt`); `KidFacts … (1 + 1)` accepted as `… 2`; `generateM`.
5. `GenKid.masked` (`(K.outsIn hy p hp).2` as `p.name ≠ "clk" ∧ p.name ≠
   "rst"`); `GenKid.facts`' `check` field.
6. `Tools.ShippingOneOutKidDepth`: `K.facts.outsIn` as field projections of
   a theorem application; `core_designCheck_inN₁` is a copy with `n` for `0`.
7. The B tests: that every conjunct of the two boundaries is derived
   (measured on the BASE closed endpoints only).

## 17. Round par/a-16 (WRITTEN, NOT BUILT; base fcabc921)

New files only:

    Tests/Compiler/NoPortsTopD2N3Test.lean / NoPortsTopD2N3BTest.lean     topD2 at depth 3
    Tests/Compiler/NoPortsMixDeepTest.lean / NoPortsMixDeepBTest.lean     mixDeep at depth 2 (+ its closing)
    Tools/ShippingNoPortsDeepCommand.lean                                 #machine_no_ports_deep f n (n ≥ 2)
    Tests/Compiler/NoPortsDeepFamilyTest.lean                             TARGET-BUILT ONLY

### 17.1 What was read

* `topD2.machine_design_svNR3`: generated by `#machine_design_svNR topD2 3`
  (`ShippingChildBoundaryTest` 297); MEASURED on its closed form: keeps the
  four checks, boundary reduces to `ChildBnd` (`verification-a14.md`
  134–138). `topD2.machine_ships_hierNR3`: INFERRED (asserted first).
* `topD2_runFacts`, `topD2_maskedG` (BUILT): their statements have no depth,
  so the depth-3 file reuses them; `kids_outsCheck`, `kids_designCheck` are
  instantiated at 3. `mid2_kid2` takes every depth-free field of the BUILT
  `mid2_kid`, `kidsLo := (mid2_kid …).kidsHi`, `kidsHi := factsN … 2`.
* `mixDeep` (`ShippingChildBoundaryTest` 278–286, READ): callees `mid2`,
  `midH`, `cnt`; the projected fields are `a.hit`, `b.n`, `c.n`. Its call
  ENTRIES are not measured, so the tables are indexed by the callee's NAME
  (`calleeOf k`, `outsOf`, `insOf`), with two decided ∀-statements.
* `#machine_closes_deep` (`Tools/ShippingChildIfaceGen.lean`, READ in full):
  its refusals are: a gate child directly under the general closing, a
  memory child, a child that is neither a gate child nor a machine with an
  endpoint, a leaf child without `machine_closes`, a slotless child with
  calls, a failing generated proof. None applies to `mixDeep` BY READING;
  the kernel-decided name separation over three children with descendants
  is not in any log.

### 17.2 The declarations

| declaration | endpoint | premise (of the base endpoint) | predicted state |
|---|---|---|---|
| `topD2` (depth 3) | `topD2.machine_design_noPortsNR3` (+ `_closed`) | `shipsHierCheck`, `kidsMaskedN`, `designCheck … 3`, `outsCheck … 3` of `…svNR3` | WRITTEN — predicted absent, pending build |
| | | `MachineClosesAt topD2` | predicted absent in `_closed` (BUILT `topD2.closes_deep`) |
| | | — | ADDED to the open form: `MachineDefines midH`, `EntryDefines rcH` |
| | `…NR3_closedB` (+ `_gap`) | boundary conjuncts other than `ChildBnd` | predicted DERIVED (measured on the base closed endpoint), 0 NOT ALLOWED, no gap hypothesis |
| `mixDeep` | `mixDeep.closes_deep` | — | generated in the test by the BUILT command; predicted premises: reflections of `mid2`, `midH`, `rcH`, `cnt` |
| | `mixDeep.machine_design_noPortsNR2` (+ `_closed`) | the four checks of `…svNR2` | WRITTEN — predicted absent, pending build |
| | | `MachineClosesAt mixDeep` | predicted absent in `_closed` |
| | | — | ADDED to the open form: `EntryDefines rcH` |
| | `…NR2_closedB` (+ `_gap`) | boundary conjuncts other than `ChildBnd` | predicted DERIVED — INFERRED (the open base form KEEPS two ∀-contexts conjuncts: it has no `midH` / `rcH` binder) |
| `grand`, `topD2` (depth 2) | `…noPortsNR2`, `_closed` | — | generator compare path: REBUILT, `isDefEq`, kept as `_regen`; nothing new removed |

### 17.3 Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingNoPortsDeepCommand» where
      roots := #[`Tools.ShippingNoPortsDeepCommand]

`Tests/AllTests.lean` (NOT `NoPortsDeepFamilyTest`: it creates the names of
the two hand tests):

    import Tests.Compiler.NoPortsTopD2N3BTest
    import Tests.Compiler.NoPortsMixDeepBTest

Order: (1) `Tests.Compiler.NoPortsTopD2N3Test`; (2) `…NoPortsTopD2N3BTest`;
independently (3) `Tests.Compiler.NoPortsMixDeepTest`; (4)
`…NoPortsMixDeepBTest`; independently (5)
`Tools.ShippingNoPortsDeepCommand`; (6) `Tests.Compiler.NoPortsDeepFamilyTest`
as a target of its own.

### 17.4 UNVERIFIED, in risk order

1. `#machine_closes_deep mixDeep`: the decided conditions of
   `machineClosesAt_of_kidsD` on three different children with descendants
   (kernel name separation: time and memory); the premise list.
2. `Tools/ShippingNoPortsDeepCommand.lean`: nothing of it was elaborated —
   `genKidTheorem` (the `kid` tactic for a one-output callee: `K.*` fields
   into `kidsChild_of_real`, `rw [hnm] at h0`; the `self` rewrite by
   `namesOf_map` on a spliced `fun`), `closesPremises` (argument 4 of
   `MachineDefines` / `EntryDefines` against `toExpr`), `DeepScope.toK`
   (the BUILT `runTheorems` driven with a general callee entered as
   `.oneOut .anonymous nD`), `kidsTheoremD`'s `cases k` with `GenKid.facts`
   at `(n - 1) + 1` against the literal `n`, `open` of the whole
   `Tools.ShippingNoPortsKidsCommand`.
3. `NoPortsMixDeepTest`: the name-indexed tables — `if_pos rfl` /
   `if_neg … |>.trans` through the unfolding of `outsOf`; `decide` of
   `mixDeep_callee`, `mixDeep_three`, `callWidthsOk` / `callArgsOk` through
   `Name` equality tests in the tables; that the reflections of `mid2`,
   `midH`, `cnt` are top-level conjuncts of the boundary (`generateX`
   throws with the asked statement otherwise); the audit's counts 6 / 5.
4. `NoPortsTopD2N3Test`: `topD2.machine_ships_hierNR3`'s shape;
   `kidsLo := K.kidsHi` (`1 + 1` against `2`); `(mid2_kid2 …).facts` as
   `KidFacts … 3`; the audit's depth read off `DesignSV`'s second argument.
5. The two B tests: every conjunct derived (measured for `topD2` at depth 3
   on the base closed form; inferred for `mixDeep`).

## 18. Repair after the first build of par/a-16 (WRITTEN, NOT BUILT)

BUILT (integrator, 3b70e5eb): `NoPortsTopD2N3Test`, `NoPortsTopD2N3BTest`.

* `mixDeep`: NO closed form, and §17.2's rows for `mixDeep.closes_deep`,
  `…noPortsNR2_closed`, `…closedB` are WITHDRAWN. MEASURED:
  `mixDeep.closes_deep` came out with three name premises. READ
  (`Tools/ShippingChildIfaceGen.lean` 181–232): the generator decides the
  three name hypotheses only when `namesSep` holds, else it makes all three
  premises (a branch, not a caught failure); `namesSep` fails because
  `midH` is a direct callee of `mixDeep` AND a descendant of its callee
  `mid2` (`sepB midH midH` is false). The third premise, `hdD` of
  `machineClosesAt_of_kidsD` (`Tools/ShippingCallsKidsD.lean` 131–133), is
  FALSE BY READING for `mixDeep` (not proved false): `midH`'s printed name
  is among the names of `mid2`'s descendants. MISSING: a closing theorem
  for callees that SHARE a descendant declaration (`hdD` weakened to "a
  printed name met under two callees is of the same declaration").
  `NoPortsMixDeepTest` now generates the OPEN endpoint only (it asks
  `MachineClosesAt mixDeep`; boundary unreduced), does not run
  `#machine_closes_deep mixDeep`, and its audit throws if a closed form
  exists. `NoPortsMixDeepBTest.lean` is removed.
* `Tools/ShippingNoPortsDeepCommand.lean`: the `match` of `factOf` has a
  typed scrutinee; every constructor pattern in the file is fully qualified.
* `Tests/AllTests.lean`: `import Tests.Compiler.NoPortsTopD2N3BTest` only;
  `NoPortsMixDeepTest` may be imported too (it owns
  `mixDeep.machine_design_noPortsNR2`; the family test stays target-only).
