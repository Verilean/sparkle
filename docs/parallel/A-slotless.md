# A / G1, unit U5a: a parent WITHOUT a register, of a sequential child (round par/a-20, base poc `8554bddb`)

Status of everything below: **WRITTEN, NOT BUILT**. Nothing was run (no
`lean`, no `lake`); no premise counts as removed until the integrator
builds. "READ" means read in the source at the cited line; "INFERRED" means
concluded from what was read, not measured.

## 1. The declarations (READ)

| declaration | source | what it is |
|---|---|---|
| `pe` | `Tests/Compiler/MultiInstanceTest.lean:35` | `@[hardware_module]`, `{dom}`, three `BitVec 32` inputs, `circuit do` with two `Signal.reg` (`aReg`, `pReg`), two `let` aliases, structure result `PeOut` (`aOut`, `pOut`); no call |
| `engineOnce` | `MultiInstanceTest.lean:58` | plain `def`, `{dom}`, `let e := pe x y w; e.aOut + e.pOut` — no `Signal.reg`, one call, two projections |
| `twinCalls` | `MultiInstanceTest.lean:65` | two `let`-bound calls with identical arguments, `e1.aOut + e2.pOut` |
| `mesh2x2` | `MultiInstanceTest.lean:46` | four calls chained through their fields, a dead `let _ := pe11.aOut`, result `pe11.pOut` |

Endpoints that exist today (READ, `Tests/Compiler/ShippingMachineSeqLinkedTest.lean`):
`#machine_endpoint` (:25–35), `#machine_composedTS` (:29, :33, :37),
`#machine_ships_hier` (:48–50) — `f.machine_ships_hier`, premises
`shipsHierCheck`, `Bd` (`kidsMixed`). No design-level endpoint.

Reader data (`nDecl`, slots, `lets`, call entries, argument lets,
`instFields`, outputs) is NOT known by reading: it is LOGGED by the first
`run_cmd` of `Tests/Compiler/NoPortsSlotlessEngineOnceTest.lean`
(`NOPORTS SLOTLESS DATA` lines, for `pe` and all three parents) before any
assertion. EXPECTED for `engineOnce` (INFERRED from `readMachine`,
`Tools/ShippingMachineCommand.lean:437`, and from `mid`'s measured
`nDecl = 2` for `{dom} (en)`): `nDecl = 4`, slots `0`, two call entries
both `pe`, `instFields = ["aOut", "pOut"]`, one output. The hand theorems
are written for `nDecl = 4`; the test throws on any other value.

The endpoint head of a slotless parent with `instFields ≠ []` is
`combCallsProof` (`Tools/ShippingMachineCommand.lean:2519`), i.e.
`machine_trace_of_comb_calls`; its wired twins `…L`, `…R`, `…RA` exist
(`Tools/ShippingMachineSeqLinked.lean:154`,
`Tools/ShippingMachineSeqLinkedR.lean:117`, `:329`). The endpoint is not a
transported one (`back? = none`): the transport is made only for sign
operations or loop fusion (`ShippingMachineCommand.lean:2494`, `:2505`,
`:2560`).

## 2. Why there is no design-level endpoint (task 2) — READ

No generator REFUSES these three at the base. Every `throwError` on the
path was read:

* `#machine_design_svNR f n` (`Tools/ShippingMachineDepthCommandR.lean:678`;
  `generateCoreNR` :182, `generateShipsNR` :566, `generateDesignNR` :634):
  refusals — "no call" (:187), "one-output combinational calls" (:189,
  `instFields = []`), "the child has children; depth 0 is too shallow"
  (:208), "a transported endpoint (not yet at depth)" (:497, :571), and
  shape assertions on binder counts. None is about the slots; none applies
  (INFERRED from §1: calls, `instFields ≠ []`, leaf child, not transported).
* `#machine_design_svR0 f` (`Tools/ShippingMachineSeqCommandR.lean:341`):
  "no call" (:31) only.
* `#machine_design_sv0 f` (`Tools/ShippingShipsDesignSVCommand.lean:120`):
  `compose` (:48) on the existing `f.machine_ships_hier`; no scope test.
* The general theorems under them: `machine_linkedT_callsRN`
  (`Tools/ShippingMachineCallsLinkedTNR.lean:203`) and the head
  `machine_ships_hierC` (`Tools/ShippingMachineShipsHier.lean:166`) have no
  hypothesis on the slots. The head takes `"rst" ∈ b.inputs` from
  `shipsHierCheck_sound` (:264), not from the parent's register.

So the reason is: **the commands were never run on them** (the census,
`A-remaining.md` row 15–17, said "whether it goes through is not read").
The only refusals that name them are in the CHECK-FREE generators:
`Tools.ShippingNoPortsCommand.scopeP` (`Tools/ShippingNoPortsCommand.lean:87`,
"parent without a register …") and `Tools.ShippingShipsFreeCommand.scope`
(`Tools/ShippingShipsFreeCommand.lean:58`, "no register (core_runFacts asks
one of the parent)").

Whether the base commands actually go through on `engineOnce` is
UNVERIFIED: step 2 of the test runs them (as errors), step 7 logs them for
`twinCalls` / `mesh2x2` (nothing kept).

## 3. Every use of `hsl : d.shape.layout.slots ≠ []` on the path (task 1)

The path of a parent of leaf register machines to a check-free depth
endpoint is: the head `machine_design_noPorts` with four run hypotheses
(`facts`, `outs`, `masked`, `design`), discharged by `kids_runFacts`,
`kids_outsCheck`, `kids_maskedN`, `kids_designCheck`
(`Tools/ShippingKidFacts.lean`) or by the generators' equivalents.

### 3.1 The PARENT's `hsl` (three roots, the rest pass it on)

| theorem | file:line | what `hsl` is used for | slotless parent WITH a sequential child |
|---|---|---|---|
| `core_raw_facts` | `Tools/ShippingChecksRaw.lean:131` (`hsl` :139, used :222) | picks `[clk, rst]` in the wiring's input clause to show `"rst" ∈ b.inputs`. The two other conjuncts (instance names, self-read) do not use it | **follows from the closing** — `core_seqKid_inputs` (new); the other two conjuncts unchanged |
| `core_clk` | `Tools/ShippingCoreClk.lean:57` (`hsl` :67, used :167) | `weS b "clk" = 1 ∧ weS b "rst" = 1`: the input list is `allocated ++ [clk, rst] ++ extra` | **follows**: the list is `allocated ++ [] ++ [clk, rst]` once `extra = [clk, rst]` is known, which follows from `"rst"` being an input (`core_slotless_seq`, new) |
| `calls_ports` | `Tools/ShippingMachineDepthChild.lean:41` (`hsl` :45, used :80, :84) | forces `extra = []` | NOT on this path: it serves the parent AS A CHILD (`kidsChild_iface` `Tools/ShippingKidsChildIface.lean:129`/:137, `parent_run_outsCheck0` `Tools/ShippingChecksRun.lean:186`, `seqChildRunN_of_composedC` `Tools/ShippingMachineDepthRun.lean:150`, `…DepthRunR.lean:135`, `core_calls_ports₁` / `core_calls_portsG`). Not generalised here; the same argument would give it (`extra = [clk, rst]` and the same normal form of the inputs), NOT WRITTEN |
| `core_runFacts` | `Tools/ShippingChecksRunFacts.lean:42` (:50, :72) | passes to `core_raw_facts` | `core_runFactsS` (new) |
| `core_shipsHier_rest` / `rest4` / `rest3` / `rest3F` | `ShippingChecksRaw.lean:244`, `ShippingChecksOuts.lean:264`, `ShippingChecksWidths.lean:330`, `:429` | pass to `core_raw_facts` | not on the check-free path (they PRODUCE `shipsHierCheck`); not generalised |
| `core_designCheck_run` | `Tools/ShippingTextShipped.lean:131` (:139, :168) | passes to `core_runFacts` | `core_designCheck_runS` (new) |
| `kids_runFacts` | `Tools/ShippingKidFacts.lean:106` (:114, :130) | passes to `core_runFacts` | `kids_runFactsS` (new) |
| `kids_designCheck` | `Tools/ShippingKidFacts.lean:199` (:207, :236, :248) | `core_clk`, `core_designCheck_run` | `kids_designCheckS` (new) |
| `core_portsMatch_raw_leaf` / `…LeafAny` / `core_portsMatch_shipped_leaf` | `Tools/ShippingPortsMatchRawLeaf.lean:84` (:96, :156), `…RawLeafAny.lean:209` (:221), `…ShippedLeaf.lean:51` (:63) | `core_clk` | not used by the hand route (`kids_designCheckS` applies `core_portsMatch_raw` directly, which takes `hclkB` as a hypothesis and has NO `hsl`); the generator `#machine_no_ports` uses them — not generalised |
| `GenKid` / `kids_designCheck_in` | `Tools/ShippingGenKid.lean:117` | the parent as a child with a register | not this axis |

Theorems on the path WITHOUT `hsl` (READ: no such hypothesis):
`core_kids_facts` (`ShippingChecksCore.lean:71`), `core_hierGate`,
`core_instOutWidthsOk` (`ShippingChecksWidths`), `core_linkedWF`
(`ShippingLinkedFresh`), `core_outsExtracted` (`ShippingChecksOuts`),
`core_closed_typedIn` (`ShippingClosedTyped`, header :13 "no `hsl`"),
`core_portsMatch_raw`, `core_callConns` (`ShippingPortsMatchRaw`),
`core_outsCheck_all_gate`, `core_kidsMaskedN_top`, `core_kidsPass_deep`,
`kids_outsCheck`, `kids_maskedN`, `machineClosesAt_of_seqKids`
(`Tools/ShippingCallsSeqKids.lean:52`: `hslots` is the length equation
only).

### 3.2 The CHILD's `hsl` (true of `pe`: not an obstacle)

`LeafKid.slots` (`ShippingPortsMatchRawLeaf.lean:66`), `leaf_real_outTys`
(`ShippingChildIfaceTy.lean:182`), `leaf_run_masked` / `leaf_real_kidM`
(`ShippingChecksMaskedLeaf.lean:68`, :200, :222), `leaf_real_outsAssigned`
/ `leaf_real_kidA` (`ShippingChecksRun.lean:65`, :168;
`ShippingChecksRun2.lean:195`), `seqChildRun_full`
(`ShippingMachineSeqInst.lean:363`), `seqStream_of_trace`
(`ShippingMachineSeqChild.lean:97`, :279), `ShippingMachineShipsW.lean:55`:
all about a machine WITHOUT calls and WITH slots — the child. `pe` has two
registers.

### 3.3 The heads and the reset premise

* `machine_ships_hierC` (`ShippingMachineShipsHier.lean:166`),
  `machine_ships_hierC_at_free` (`ShippingShipsFree.lean:72`),
  `machine_design_noPorts` (`ShippingNoPorts.lean:42`): NO `hsl`. They turn
  the conclusion's premise `∀ t, ins t "rst" = 0` into
  `∀ t st, seedIn b ins t st "rst" = 0` (`ComposedG`,
  `ShippingMachineShipsHier.lean:137`) by `hrstIn : "rst" ∈ b.inputs`
  (:264, :286–289; `ShippingShipsFree.lean:165`, :183–186) — a component of
  `shipsHierCheck_sound`, resp. of the `facts` hypothesis (`RunFacts.rst`).
* The argument of `A-oneout.md` §13.6(b) — for a slotless parent of
  COMBINATIONAL children the reset premise is FALSE, because `rst` is not
  an input and `seedIn` then reads the state — **does NOT apply here**:
  `rst` IS an input (`withClockFor`,
  `Sparkle/IR/MachineInstG.lean:73–78`, appends `clk`, `rst` when a child
  has a `clk` or `rst` input and the module has not both). The premise is
  derived exactly as for a parent with a register, from `RunFacts.rst`.
  That concerned `ComposedH` (`ShippingMachineShipsHierH.lean:33`, :52) and
  `core_rst_any` / `core_runFactsH` / `core_designCheckH`
  (`ShippingOneOutFacts.lean:440`, :555, :640): the one-output
  (combinational-children) route, which is NOT this path (`instFields ≠ []`
  here).
* `hierCheck`'s `rst` conjunct holds for the same reason; it is no longer
  asked on the check-free route anyway.

### 3.4 What genuinely fails

**Nothing on this path** (INFERRED; to be confirmed by the build). The
census sentence "a second derivation of clk/rst, no statement change" is
confirmed by reading: the two facts are the only place the parent's
register enters, and both follow from the closing. What `MachineWired`
does not say (`Tools/ShippingChecksRaw.lean:36–38`,
`Tools/ShippingCoreClk.lean:33–35`: "the input clause does not say which
disjunct of `extra` holds") is recovered WITHOUT changing `MachineWired`:
the closing gives `"rst" ∈ M.inputs`, and with `extra = []` every input
would be an allocated name.

## 4. The second derivation (READ: the pieces; WRITTEN: the composition)

1. `synthesizeMachineCertified_runs` (`Tools/ShippingChildRun.lean:528`)
   gives, for a shape with calls, `children`, `CloseCalls …` and
   `ChildrenReal mref cref shape children`
   (`Tools/ShippingChildInv.lean:492`: entry `k`'s child is a `RealChild`
   of the callee, or the memory module).
2. `CloseCalls` with `instFields ≠ []` is
   `closeInstsG … children (closeMachine …, d₀) = some (M, D)`
   (`Tools/ShippingMachineEntry.lean:928`).
3. `closeInstsG_inputs` (`Tools/ShippingMachineInstG.lean:451`):
   `M.inputs = (withClockFor children m₀).inputs.filter (!outWs.contains ·.name)`,
   `outWs` the call ports `portNames[nIn + k]`.
4. `withClockFor_clk` (`Tools/ShippingCallsAssemblyG.lean:69`): a child
   `c ∈ children` with `isSeqChild c.1` gives a port named `clk` and one
   named `rst` among `(withClockFor children m).inputs` — whether appended
   or already there.
5. The call ports are transition inputs, hence wires, hence allocated names
   (`transitionPortTys_of_run`, `Tools/ShippingTransitionPortTys.lean:141`);
   `clk`, `rst` are not allocated: the filter keeps them.
6. A leaf register machine's real child is sequential:
   `LeafPorts.seq_iff` (`Tools/ShippingLeafPorts.lean:107`) with
   `leaf_real_ports` (:292).

## 5. New statements (verbatim; the common hypotheses `d ok hbody hC hslots hdomB hins hfne outTy hnomem hB hcore hpost entry closes` are those of `core_raw_facts`)

`Tools/ShippingSlotlessClk.lean`:

```lean
abbrev SeqKid (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (d : MachineData) : Prop :=
  ∃ (k : Nat) (hk : k < d.shape.insts.length), ∀ y : Res,
    RealChild mref cref (d.shape.insts[k]).1 y → isSeqChild y.1 = true

theorem seqKid_of_leafAt {d : MachineData} (k : Nat) (hk : k < d.shape.insts.length)
    {dk : MachineData} (K : LeafKid mctx mref cctx cref (d.shape.insts[k]).1 dk) :
    SeqKid mref cref d

theorem core_seqKid_inputs … (hins) (hfne) (hnomem) (hseq : SeqKid mref cref d) … (hB) (hcore) (entry) (closes) :
    "clk" ∈ M.inputs.map (·.name) ∧ "rst" ∈ M.inputs.map (·.name)

theorem core_slotless_seq … (hsl0 : d.shape.layout.slots = []) (hseq : SeqKid mref cref d) … :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true ∧
    Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1

theorem core_raw_factsS … (hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d) … :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true

theorem core_clkS … (hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d) … :
    Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1
```

plus the pure `inputs_tail_shape`, `weS_clk_rst_tail` (the `extra`
counterparts of `inputs_clk_shape`, `weS_clk_rst_filtered`).

`Tools/ShippingSlotlessKidFacts.lean`: `core_runFactsS`,
`core_designCheck_runS`, `kids_runFactsS`, `kids_designCheckS` — the
statements of `core_runFacts`, `core_designCheck_run`, `kids_runFacts`,
`kids_designCheck` with `(hsl : d.shape.layout.slots ≠ [])` replaced by
`(hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d)`, nothing else
changed; `kids_runFacts_again`, `kids_designCheck_again` (the old
statements from the new, `Or.inl hsl`).

What kind of generalisation this is: `core_raw_factsS` / `core_clkS`
case-split on `slots = []`; with a slot they APPLY the built
`core_raw_facts` / `core_clk` (the built facts are the first disjunct, not
re-proved); without one they apply `core_slotless_seq`. The `_again`
theorems therefore show the statements generalise, not an independent
proof. `core_slotless_seq`'s prelude is `core_clk`'s, copied (the chain's
practice: no prelude lemma exposes `MachineWired` of a core run).

## 6. The declaration: endpoint — premise — predicted state

`Tests/Compiler/NoPortsSlotlessEngineOnceTest.lean` (steps in its header).

| endpoint | premise | predicted state |
|---|---|---|
| `engineOnce.machine_design_svNR1` (NEW base, built command, first run on a slotless parent) | `shipsHierCheck`, `kidsMaskedN`, `designCheck 1`, `outsCheck 1`, `MachineClosesAt engineOnce`, boundary `ChildBnd ∧ MachineDefines pe` | all present (the inventory the audit asserts) |
| `engineOnce.machine_design_noPortsNR1` | the four checks | ABSENT; `MachineClosesAt engineOnce` still a binder |
| `engineOnce.machine_design_noPortsNR1_closed` | `MachineClosesAt engineOnce` | ABSENT (by `engineOnce.machine_closes_at`, built generator). Left: the run, `MachineDefines engineOnce`, `MachineDefines pe`, `ChildBnd ∧ MachineDefines pe` under the existentials — all ALLOWED; gap theorem with no gap hypothesis |
| `engineOnce.machine_ships_hier` (existing) | `shipsHierCheck`, `Bd` | unchanged |
| `twinCalls`, `mesh2x2` | — | analysis only; step 7 LOGS whether the two base commands go through, nothing kept |

Relative to what: `engineOnce` had no design-level endpoint, so the closed
form is a NEW statement; against the base endpoint generated in the same
file the four checks and the closing premise are gone and nothing is
added. The name-separation premises of `machine_closes_at` (`hnames`,
`hparent`, `hfresh`) are expected to be decided (`sepB`, output name not
starting with `i`); if one is not, it becomes a binder of the closed form
and the audit THROWS (NOT ALLOWED).

## 7. Not done / decisions

* No decision for the user is needed for this unit: no compiler file, no
  `HierCheck.lean`, no head, no `MachineWired` statement changes.
* NOT WRITTEN: a generator (the check-free generators refuse by `scopeP` /
  `scope` and hard-code `hsl`; a slotless variant needs new generator
  files); `twinCalls`, `mesh2x2` by hand (same four theorems at their
  data, if their base commands go through); `calls_ports` /
  `kidsChild_iface` for a slotless parent AS A CHILD (needed only when a
  slotless machine with a sequential child is itself called — no such
  declaration in the tests); `core_portsMatch_raw_leaf`-family and
  `core_shipsHier_rest*` with `hck`.
* Still open and unrelated to this unit: a slotless parent of
  COMBINATIONAL children (`A-oneout.md` §13.6: statement change of the
  head, and a user decision if `hierCheck`'s `rst` conjunct is touched).

## 8. UNVERIFIED, in risk order

1. **The base commands on a slotless parent** (step 2): by reading nothing
   refuses, but `#machine_design_svNR` / `#machine_closes_at` were never
   run on `combCallsProof` endpoints. Possible failures: a `decide` of
   `machine_linkedT_callsRN`'s data conditions, the per-call tactic of
   `generateCoreNR` (written for `machine_trace_of_data_causal` parents),
   `pe.machine_closes` not derivable (`letsAliasOk`), a data condition of
   `machineClosesAt_of_seqKids` (`hfieldsNd`, `letsAliasOk` of the
   parent). If this fails the unit is "first the base endpoint" and the
   new lemmas stay unexercised.
2. **Data**: `nDecl = 4` for `engineOnce`; `callWidthsOk` / `callArgsOk`
   / `callsOk 4` deciding `true` for a plain-`let` parent whose call
   arguments are declared binders.
3. `core_slotless_seq`: the component positions of `MachineWired`
   (2, 14, 17 of 18) were counted by reading; `if_pos hs` unifying with the
   wiring's `if`; the `extra = []` contradiction (`rw [hMin, h] at hp`,
   then the `first | rw [if_pos hs] … | simp …`).
4. `core_seqKid_inputs`: `mapM_some` / `List.getElem_range` step (copied
   from `Tools/ShippingMachineEntry.lean` ≈ :1990 and
   `ShippingChecksOuts.lean` ≈ :246), `rw [hzx] at hz`.
5. `inputs_tail_shape`: the `rw [hI, List.append_nil, List.filter_append, e1]` chain after two `subst`.
6. `Tools.ShippingNoPortsCommand.generate` reused on hand theorems whose
   extra binders are `hB`, `hRp` (the boundary's conjuncts must be exactly
   `ChildBnd` and `MachineDefines pe`).
7. Name clashes: this file creates `engineOnce.machine_ships_hierNR1`,
   `…machine_design_svNR1`, `…machine_closes_at`,
   `…machine_design_noPortsNR1(_closed)(_gap)`, `pe.machine_closes`,
   `pe.seq_child_runN`, `pe.machine_leafKid`. No other test module was
   found creating them (the sweeps and `RemainingProbeTest` restore the
   environment on the refusal).

## 9. Build queue (integrator)

`lakefile.lean`:

```
lean_lib «Tools.ShippingSlotlessClk» where
  roots := #[`Tools.ShippingSlotlessClk]

lean_lib «Tools.ShippingSlotlessKidFacts» where
  roots := #[`Tools.ShippingSlotlessKidFacts]
```

`Tests/AllTests.lean`:

```
import Tests.Compiler.NoPortsSlotlessEngineOnceTest
```

Order: `Tools.ShippingSlotlessClk` → `Tools.ShippingSlotlessKidFacts` →
`Tests.Compiler.NoPortsSlotlessEngineOnceTest` → `Tests.AllTests`.
