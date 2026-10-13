# B — parents WITHOUT a register: what is covered at the design level, what is not (round par/b-36)

**WRITTEN, NOT BUILT**; nothing was run. Marks: [R] read (file:line at
0a0a4f71), [M] measured by the integrator earlier, [P] predicted. The
probe file of this round turns the [P] lines of §2 into measurements.

## 1. `hftByte` is not a slotless parent

`hftByte` (`Tests/Compiler/ShippingMachineTeleTest.lean` 65) is
`(hftStrategy inByte inValid).outByte`: a parent WITH registers (the
strategy's), calling the `@[hardware_module]` byte table. It is COVERED by
`machine_design_svH_full_closed` [R: `OneOutHftByteTest.lean` 624–631,
`#machine_closes_at` in `ShippingCallsCloseTest.lean` 104] — the
ONE-OUTPUT route, whose data conditions include `f.oneout_slots` "(the
parent has a register)" [R: `OneOutAnyFamilyTest.lean` 95]. All of
`caller`, `callerTwice`, `callerNested`, `callerD`, `callerL`, `callerLN`
have registers too [R: their definitions]. So no slotless parent of
combinational children is among the 128 COVERED declarations.

## 2. The classes of a parent without a register

| parent's calls | route [R] | design-level endpoint today |
|---|---|---|
| (a) leaf REGISTER machines (structure-result children: `engineOnce`, `twinCalls`, `mesh2x2`, `regsParent`) | machine route: the reader keeps a slotless body whose calls are structure / Bool / sequential (`Sparkle/Compiler/Elab.lean` 5131–5136: `n = 0 && !st.insts.isEmpty && !st.instStruct → none`, i.e. `instStruct` is the exception) ; endpoint `combCallsProof` | a closed form EXISTS: `#machine_no_ports_seq` → `machine_design_noPortsNR{n}_closed` (`Tools/ShippingNoPortsSlotlessCommand.lean` 4–24: the parent's `clk`/`rst` come from `SeqKid`) |
| (b) MEMORY children | machine route | the memory forms need `slots ≠ []` (`ShippingNoPortsMemCommand.lean` 208 "parent without a register") — NOT covered; no example in built files found by `grep` |
| (c) ONE-OUTPUT COMBINATIONAL children only (gate children, slotless machine children) | NOT the machine route: the reader refuses (5134–5135). The MIXED GATE takes it with the instance predicate: `unifiedInstanceRoot` (the body is one call on binders), `hierInstRoot` (calls of calls), `hierGateRoot` (a cone over call results) — `Elab.lean` 2725, 2734, 2843, 2880–2890 | **NONE.** Not even a row in the census: these declarations have neither `machineData` nor `gateValue` [P; the probe measures it] |
| (d) mixed: combinational + sequential children | machine route if one call is structure-result (`regsParent`: `DepthRegsChildTest.lean` 60–86) | by `#machine_no_ports_seq` only when EVERY callee is a leaf register machine (its scope, 62–72): a combinational callee is refused |

`Tools/ShippingNoPortsSlotlessCommand.lean` 64–68 says it in its own scope
list: "a parent WITHOUT a register whose callees are ALL combinational …
NOT COVERED — nothing gives the parent's `clk` / `rst`, and the head's reset
premise (`RunFacts.rst`) has to change". That is the machine-route view;
by the reader such a parent is not on the machine route at all.

### Class (c): the smallest uncovered examples EXIST in built files

`Tests/Compiler/ShippingHierarchySoundnessTest.lean` (in `Tests.AllTests`,
line 119): `parentUse a b := childAdd a b` (32), `wrapAdd` (146, concrete
domain), `parentMix := childAdd a b + a` (74), `parentTwoCalls`,
`parentRepeat`, `parentCmp` (Bool result), `parentNested := childAdd
(childAdd a b) b`. New in this round: `wrapPick sel x := pick sel x`
(`Tests/Compiler/SlotlessParentProbeTest.lean`) — the smallest parent of a
child that HAS a design-level endpoint (`pick.gate_design0`).

What exists for them (S6, hand-written per declaration) [R]:

* `parentUse_instance_entry` (251): `InstancePreserves` for the CORE entry
  (`synthesizeCombinationalCore`), premises `EnvDefines`, the tag of the
  child, `hscalar`.
* `parentMix_entry_observes` (854): ONE linked evaluation
  `evalAssignsH (moduleWidths m) (childrenOf childModule.name) mems m.body
  initial = some result ∧ result "out" = ((parentMix aS bS).val t).toNat`,
  with the child PINNED to a hand-written `childModule`
  (`SubSynthDefinesAll`, `HardwareTagged`, `dc.modules = []`).
* `parentMix_shipping_opt` (1125): to the optimized module's emitted text
  for ONE cycle (`runModuleSV … 1 …`), under 15 further hypotheses that are
  CHECKS of the run's modules (`optCheck (openFlat m …) (openFlat o …)`,
  `instsKept`, `connAgreeOk`, `seqCheck`, the two width `all`s, `semFragCheck`,
  `bodyImage`, `bodyReorderCheck`, `instOutWidthsOk`, `linkedWF`,
  `combStmtI` ×2, `houtName`) — every one NOT ALLOWED by the goal's
  classifier.

So for class (c): no generator, the core entry not the full entry, one
cycle not a run, the child a hand-written module not the returned design's,
no `DesignSV`, and the checks are premises.

## 3. What is missing for class (c), in dependency order

| # | missing piece | exists already | status |
|---|---|---|---|
| 1 | a linked RUN from linked evaluations (`runModuleH` for `T` cycles from `evalAssignsH` at each seeded environment) | `regNexts_comb`, `memNexts_okI` (`ShippingHierSVSoundness.lean` 45, 417) | **WRITTEN this round**: `Tools/ShippingHierRunTotal.lean` (`stepModuleH_comb`, `runModuleH_comb_total`) — pure, connected to nothing |
| 2 | the per-cycle linked evaluation of the run's module GENERICALLY: an `InstancePreserves` / cone statement with the child read from the RETURNED design (`childMap design.modules`), not a pinned hand module; for the full entry (the cleanup and `mergeChecked` on a body with instances) | `instance_entry_of_env`, `hierCone_entry_of_env` (core entry, pinned child); `Tools.ShippingCallsGate.childFull_of_real`, `gate_real_kidK` (a gate child of a MACHINE parent is the child's full-entry run) | missing: the gate-route parent's analogue of `childFull_of_real` |
| 3 | the text side as THEOREMS about the run, not checks: `hierTyped`, `kidsLocal`, `linkedWF`, `seqCheck`, width agreement, `bodyInstOuts ⊆ openIns` for a gate-route parent's module (what `linked_sv_of_runH`, `ShippingHierSVRunH.lean` 193, asks) and the optimizer on a body with instances (`checkedOptimize` keeps or validates it) | for MACHINE parents: `core_shipsHier_rest`, `kids_designCheck`, the one-output closing (`ShippingOneOutFullCommand`); for gate LEAVES: `checked_forwardCheck` | missing for the mixed gate's instance bodies |
| 4 | `DesignSV … 1 …` from the linked text run and the child's own closed run (`Supplies`, `SVBounds` at depth 0 for the child) | the machine parents' bridge (`machine_design_svH…`), the child's `gate_design0` / `machine_design_comb0` | missing: the composition for a parent without `MachineData` |
| 5 | a generator: the reflected data of a gate-route parent (its hierarchical term; `#gate_child`'s `unq` reads no call — PREDICTED refusal "the body is not read as a term") | `Tools.ShippingHierTermSoundness` (hand-written terms `parentMixTerm`) | missing |

An alternative to 2–5 that I could NOT evaluate by reading: make the
one-output MACHINE route apply — it would need the reader to take a
slotless one-output-call body (a COMPILER change, out of a worker's scope,
and it changes the route of every such corpus wrapper: the eight `synth_*`
wrappers of the coverage notes are, by their description there — concrete-domain
wrappers around tagged IP modules —, of this class [not re-measured]).

The honest statement: **class (c) has no design-level endpoint and no
single small bridge closes it**; pieces 2 and 3 are proof units of the size
of the machine parents' (`ShippingChecksRaw`, `ShippingCallsGate`). Piece 1
is the only one small enough to write blind; it is written and unused.

## 4. The probe (`Tests/Compiler/SlotlessParentProbeTest.lean`, target-only)

`#slotless_parent_probe f` — never an error, asserts nothing — logs per
declaration: the machine reader's verdict; `certifiedShape?`,
`mixedCertifiedShape?` without / with the instance predicate, and which
instance root accepts; `generateGateChild f` in a `try` (environment put
back); which of `machineData`, `gateValue`, `machine_sound`, `gate_child`,
`gate_design0`, `gate_design0S`, `machine_design_comb0` exist; the real
compile (number of instance statements, the design's module names).

PREDICTED for all eight: reader REFUSES; gate accepts only WITH the
instance predicate (`parentUse`, `wrapAdd`, `wrapPick`: `unifiedInstanceRoot`;
`parentNested`: `hierInstRoot`; `parentMix`, `parentTwoCalls`,
`parentRepeat`, `parentCmp`: `hierGateRoot`); `#gate_child` REFUSED;
constants present: none; compile: 1 instance statement (2 for
`parentTwoCalls` and `parentNested`; 1 for `parentRepeat` — identical calls
are one instance), the design holding the child.

Consequence for the census [P]: these eight are INVISIBLE to
`#design_coverage` (no `machineData`, no `gateValue`): "129 declarations,
128 COVERED" is over declarations that have generated data, not over
hardware declarations. If the probe confirms it, the census needs a class
for them (e.g. every local definition the instance-predicate gate accepts).

## 5. Not determined by reading

* Whether a slotless parent with a MEMORY child (class b) exists anywhere
  in built files, and which route it takes.
* Whether `mergeChecked` / `checkedOptimize` change a gate-route parent's
  module at all (piece 3 depends on which branch `checkedOptimize` takes on
  a body with an `inst`).
* The roots per declaration (§4) — the probe measures them.

## 6. Integrator

    lean_lib «Tools.ShippingHierRunTotal» where
      roots := #[`Tools.ShippingHierRunTotal]

and a target for `Tests.Compiler.SlotlessParentProbeTest` (imports
`ShippingHierarchySoundnessTest`, `GateDesignSweepTest`). Not for AllTests
(a probe).
