# Nonzero slot inits through the TBW head (round par/init, phase 1)

Base 87874a82. Status: phase 2 PARTIAL (written, not built): L1, L3, L4 and the TBS head are written; L5, L6 and the instance test are open (§4).
Probe: `Tests/Compiler/NonzeroInitProbe.lean` (written, not built, not in AllTests).

## 1. The obstacle

`sat_of_designClosedBW` (Tools/ShippingSatAssembly.lean:59; data condition `hinit` at :156,
used at :281; (11) discharged by `Nat.two_pow_pos` at :295) instantiates the start state of
the head `machine_design_noPortsTBW` (Tools/ShippingNoPortsTypedBW.lean:39) with `fun _ => 0`.
The head uses ONE start state `st0` for two different modules:

* the SOURCE side: `b` (the full entry's module, `dropZeroWidth raw`; with instances
  `mergeChecked` is the identity, TBW :191-194) runs from `st0`. Hypothesis (5)
  (TBW :149-150, `st0 r = f.init` for each slot register) is NOT the head's own: it is passed
  verbatim to the producer `ComposedGW` (Tools/ShippingComposedGW.lean:115) at TBW :209-210,
  where it fixes the source machine's start (the Signal-level reset values).
* the TARGET side: `checkedOptimize b` (the emitted module) runs from the SAME `st0`
  (TBW :255-263 via `hierRefineCheck_linked`, which hard-wires `stO := s.st`,
  Tools/ShippingHierOptRun.lean:643 and :652), and the emitted-text layer needs
  hypothesis (11) `Bounded (weS (checkedOptimize b)) st0` over ALL names (TBW :158; used at
  :257 via `boundOffI_of_bounded`, :280 `svBounds_of_checks`, :286 `design_sv_all`).

`weS o n = (moduleWof o n).getD 0` (Tools/ShippingDesignSVLeaf.lean:22,
Tools/SVParser/RoundtripProof.lean:3313): the declared width in `o.wires ++ o.inputs ++
o.outputs`, `0` if `o` declares no such name. If the optimizer drops a register `r` (and its
wire: `deinlineRaw` keeps only `m.wires` that the optimizer's output still declares,
Sparkle/IR/HierCheck.lean:136-139), then `weS (checkedOptimize b) r = 0` and (11) demands
`st0 r < 1`, contradicting (5) when `f.init ≠ 0`. So (5) and (11) are jointly unsatisfiable
for a removed nonzero-init register: no instantiation of the CURRENT head can cover it.
"Every source register keeps its width" is false (dead registers are dropped), so the fix
must decouple the two start states.

Optimizer side, what is already proved (the good news): the flat check already uses TWO
states. `refineCheck_run_sound` / `refineCheck_transfer`
(Tools/ShippingRefineSoundness.lean:934 / :1039) take `stM`, `stO` with only
`∀ r ∈ seqRegs o, stO r.1 = stM r.1` — the removed registers of `m` are unconstrained in
`stO`. And `open_linked_run` (Tools/ShippingHierOptRun.lean:314) takes a separate `stO`
with `∀ n, n ∉ drivesOf m.body → n ∉ drivesOf o.body → sM.st n = stO n` and concludes the
run of `o` from `⟨stO, sM.mems, sM.kids⟩`. Only `hierRefineCheck_linked` (:532)
specialises both to `s.st`. Also `refineCheck` (Sparkle/IR/RefineCheck.lean:161-168) forces
every register of `o` to be a register of `m` with the same name, same reset, and
`declWidth o r = declWidth m r > 0` — a KEPT register keeps its width.

Second, smaller gap (source side, instance parents): `MachineWired`
(Tools/ShippingMachineEntry.lean:654) gives the slot register's WIDTH
(`weOf m r = f.width`, :689-691) and "every register statement is a slot's" (:693-697) only
under `shape.insts = []`. With calls it gives only the register statement with the slot's
reset value (:750-754). A nonzero init needs `f.init < 2 ^ declWidth b r` for (9) (TBW :156)
and for the BoundOff fact; the width with calls is not exported by any run lemma today.
(The producer already has it in hand: `SlotOk` Tools/ShippingMachineClose.lean:137, the
slot-register conjunct's proof Tools/ShippingMachineEntry.lean:2014ff.)

## 2. Candidates

### A (recommended): two start states in the head, source `st0` and target `stO`

New head `machine_design_noPortsTBS` (new file, proof copied from TBW): quantify `stO`
beside `st0`; replace (11) by three premises and run the conclusion from `stO`:

    (11')  Bounded (weS (checkedOptimize b)) stO
    (13)   ∀ n, (n ∉ drivesOf b.body ∨ n ∈ drivesOf (checkedOptimize b).body) → stO n = st0 n
    (14)   BoundOff (declWidth b) (b.outputs.map (·.name) ++ b.inputs.map (·.name)) st0
    conclusion: DesignSV … (checkedOptimize b) (seedIn b ins) T ⟨stO, mems, kids⟩ …  (both parts)

(13) says: the target state is the source state except at names the source drives and the
target no longer drives (the removed registers / assignments), where it is free. TBW is the
instance `stO := st0` (then (13) is `rfl`, (11') is (11), (14) is what TBW derives at :257
from (11)); so TBS is a strict generalisation, not a wrapper. Changes in the proof:
* :257 `boundOffI_of_bounded hstW …` → premise (14);
* :260-262 `hierRefineCheck_linked` → L1 below with `stO` (premise from (13));
* :268-269 and :270-273 (rejected / not binding: `checkedOptimize b = b`): (13) gives
  `stO = st0` by `funext` (a name driven by `b` is driven by `checkedOptimize b = b`), then
  the existing proof;
* :276-286: `svBounds_of_checks` / `design_sv_all` with `stO` and (11').

Lemmas needed:
* L1 `hierRefineCheck_linkedS` (new file next to Tools/ShippingHierOptRun.lean): as
  `hierRefineCheck_linked` (:532) with an extra `stO` and premise
  `∀ n, (n ∉ drivesOf m.body ∨ n ∈ drivesOf o.body) → stO n = s.st n`; conclusion run from
  `⟨stO, s.mems, s.kids⟩`. Proof copied; at :643 pass `(stO := stO)` with `hcpl` from the
  premise (a register of `openFlat o …` is in `drivesOf o.body`: `openBody` is a filter), at
  :652 pass the premise for undriven names. Everything else unchanged
  (`refineCheck_transfer` and `open_linked_run` already take two states).
* L3 `seqCheck_drives`: `seqCheck wof we body = true → memFree body → n ∈ drivesOf body →
  wof n = some (we n)` (Tools/SVParser/EmitSem.lean:4331: assign and register targets are
  checked `wof l == some (we l)`); with `textCheckI_sound` (Tools/ShippingDesignSV.lean:243)
  from the head's `hDesign`.
* L4 `weS_eq_of_sub`: the equality version of `weS_le_of_sub`
  (Tools/ShippingNoPortsTypedI.lean:180): `wofOf o x ≠ none`, `x` not a port, `o.wires ⊆
  b.wires` (`checkedOptimize_ports_wires`, :214) → `weS o x = declWidth b x`.
* L5 (run lemma, new file, like `wireNames_runMT`): for the core run, `regs[k]? = some r →
  slots[k]? = some f → declWidth raw r = f.width` also WITH calls, and `r` is not an output
  name (outputs are layout names, regs are `Allocated`). Source: the producer's
  `SlotOk`/closeMachine registers (Tools/ShippingMachineEntry.lean:2014ff).
* L6 the sat lemma `sat_of_designClosedBS` (new file): `hinit` replaced by the data condition
  `hinitW : ∀ f ∈ slots, f.init < 2 ^ f.width`; extra run facts `hDesign`-like
  (`designCheck … (checkedOptimize b)`) and L5. Choose
  `st0 n := ((regs.zip slots).lookup n).map (·.init) |>.getD 0` and
  `stO n := if n ∈ drivesOf b.body ∧ n ∉ drivesOf (checkedOptimize b).body then 0 else st0 n`.
  (5): `regs.Nodup`. (8): an `openIns` name is undriven, slot registers are driven
  (MachineWired :750-754) → 0. (9)/(14): slot register → `f.init < 2^f.width = 2^declWidth b r`
  (L5, `hinitW`), else 0. (13): by definition. (11'): cleared → 0; else a slot register still
  driven by the target → L3 + L4 + L5 give `weS opt r = f.width`; anything else 0.

The `<p>_sat` conclusions then state the emitted text runs from `stO`: the slot registers at
their reset values, the registers the optimizer removed at 0 (they are not declared in the
emitted text, so their value is not observable there).

### B: weaken (11) to the target's registers only, keep one state
Replace `Bounded (weS opt) st0` by a bound on `seqRegs opt` only. Rejected: the emitted-text
layer needs the whole cycle-0 environment bounded (`runModuleTG_envBound`,
Tools/ShippingDesignSVBounds.lean:310, `seedIn` passes every non-input name through from
the state), so `svBounds_of_checks` (:369), `ParentBounds`, `design_sv_all` would all have to
be reworked with a "names the text declares" restriction — far larger than A.

### C: masked target state (variant of A)
Fix `stO := fun n => st0 n % 2 ^ weS opt n` inside the head instead of quantifying it.
(11') becomes free, (13) becomes the obligation `st0 n < 2^weS opt n` on driven names — the
same L3/L4/L5. Less general (fixes the junk value), same cost; A with the explicit `stO` of
L6 is clearer.

(Not a candidate: a compiler change keeping dead nonzero-init registers — edits Sparkle/,
changes the emitted text. Not a candidate: a decidable data check per parent — `checkedOptimize
b` is computed from the existential `raw`, not from `MachineData`.)

## 3. Recommendation
A: L1 (copy of `hierRefineCheck_linked` with `stO`), TBS head (copy of TBW, three premises),
L3, L4 (small, pure), L5 (run lemma; the only producer-side work), L6 (sat). No change to
`RefLaws`, no new trust. Open until the probe is run: whether the four collision parents
actually lose a register (if none of their nonzero-init registers is dead, A is still needed
for generality, but not for those four).

## 4. Probe results and phase-2 status

Probe runs (integrator): nz1 exit 1 (ambiguous `Module` at :95/:102, fixed by qualifying it as
`Sparkle.IR.AST.Module`); nz2 printed nothing (`saved.restore` dropped the logs; replaced by
`pure ()`); nz3 exit 0. The output is in `docs/parallel/nonzero-init-probe-nz3.txt`.
* keep5: register kept at width 8, bound true.
* dead7 (leaf route, `opt != b`): `_gen_loop0_r1` (init 7) has `weS opt = 0` and is not driven
  in `opt`; the bound is FALSE. **The obstacle is confirmed.**
* dup5: not merged; both registers kept at width 8.
* instDead7, instKeep5 (`hierGate` true, the TBW case): `hierBinds` false, so `opt == b`; every
  register is kept at width 8, the bound holds, `designCheck` is true. On these instance parents
  the dead register is not removed. The general hierarchical route (`hierRefineCheck` accepted)
  can still remove one, so the head must not rely on `opt == b`.

Phase 2 (written, NOT BUILT):
* L1 `Tools/ShippingHierOptRunS.lean`: `seqRegs_openFlat_drives`, `hierRefineCheck_linkedS`.
* L3/L4 `Tools/ShippingNonzeroInitWidths.lean`: `seqCheck_mem`, `drives_cases`,
  `seqCheck_drives`, `weS_eq_of_sub`, `weS_driven_checkedOptimize`.
* Head `Tools/ShippingNoPortsTypedBS.lean`: `stO_eq_of_same`, `machine_design_noPortsTBS`.

OPEN:
* L5 (run lemma, new file): from the core run (premises of `wireNames_runMT`), every register
  statement of `M` comes from a slot, `∃ f ∈ slots, init = Int.ofNat f.init ∧ weOf M r =
  f.width`. Planned proof, independent of `ids`/`regs`:
  * `machine_run_of_core`, then `synthesizeMachineCertified_runs` and `CloseCalls.some`:
    `M.wires = (closeMachine lay t').wires`, and `M.body` is a permutation of
    `closeMachine body ++ L` with `L.all isInst`;
  * `closedTransition_of_run`: `t'.body = B ++ [assign out core]`, `TypedStmts` (only
    assignments), `slotsc : Zip₂ SlotOk`;
  * the closeMachine body splits into `dropLast` (assignments), `nextAssigns`, `registers`
    (`registers_mem` gives `k`, `p`, `f`) and `outAssigns`;
  * `weOf_wires_append` and `weOf_congr_wires` give `weOf M p.name = f.width`.

  No producer change is needed: `MachineWired`'s unconditional conjunct
  (ShippingMachineEntry.lean:750-754) already gives `regs[k]`'s register statement with
  `f.init`.
* L6 `sat_of_designClosedBS`:
  * premises: the run facts of `sat_of_designClosedBW`, plus `hDesign` (designCheck), L5, the
    data condition `hinitW : ∀ f ∈ slots, f.init < 2 ^ f.width` and `houtTy`;
  * the source start state `st0 n` is the init of the slot whose register is `n` (via
    `regs.zip slots`), and `0` off the slot registers;
  * the target start state `stO` is `st0` with the names cleared that `b` drives and
    `checkedOptimize b` no longer drives;
  * (11'): from `weS_driven_checkedOptimize` and L5;
  * (13): holds by the definition of `stO`;
  * (9)/(14): from L5 and `hinitW`.
* Instance test: a `hierGate` parent with a nonzero init that applies `sat_of_designClosedBS`.
  It needs the four parents' generator chain (`<p>_sat` in MemNameCollisionSatTest), which
  depends on L6.

## 5. Phase 3 (written, NOT BUILT; base: merge of poc 853b1608)

Integrator build of phase 2 (bs1/bs2): HierOptRunS and NoPortsTypedBS built as written;
NonzeroInitWidths needed two parse fixes (`(by cases he)` inside a tuple, explicit `memory`
pattern), bs2 exit 0.

* L5 `Tools/ShippingSlotRegsRun.lean`:
  * `closeMachine_regs`: every register of `closeMachine lay t` is a slot's register, at the
    slot's reset value and the transition's slot width.
  * `slotRegs_runMT`: from the core run, every register statement of `M` (with or without
    calls) has `∃ f ∈ slots, init = Int.ofNat f.init ∧ weOf M r = f.width`.
  * No producer change, no `ids`/`regs` in the statement.
* L6 `Tools/ShippingSatAssemblyS.lean`:
  * definitions and helpers: `slotInit`, `stOf`, `slotInit_at`, `slotInit_cases`, `reg_drives`,
    `wired_more`;
  * `sat_of_designClosedBS`: TBS-shaped `H`, the run facts of BW plus `hDesign` and `hRegs`
    (L5), and the data conditions of BW (without `hinit`) plus `hinitW`, `houtTy`, `hon`
    (`outNameOk` of the outputs);
  * the conclusion exports `regs` with its `MachineWired`, and the runs start from
    `⟨stOf b regs slots, mems, kids⟩`.
* TBS change: hypothesis (14) is now stated with `BoundOff` unfolded (`∀ n, n ∉ outputs ++
  inputs → st0 n < 2 ^ declWidth b n`), because `generateW` refuses statements that mention
  `BoundOff`.
* Instance `Tests/Compiler/MemNameCollisionSatSTest.lean` (not registered):
  * `<p>_designClosedBS` comes from `generateTopW` with `head := machine_design_noPortsTBS`;
  * `<p>_satS` applies `sat_of_designClosedBS` to the four collision parents (inits 0: this
    type-checks the route only);
  * an audit checks the axioms and that no premise of `<p>_satS` mentions InvN / Reset1 /
    seedIn.
* A nonzero-init instance parent needs only its own copy of the existing per-parent chain:
  `#machine_*` endpoints, the gate-certificate run-fact lemmas, `_names`/`_gate`/`_oi`/
  `_inputWires`/`_kidsSat`, `_designP0`, `_closesR`. No new general lemma is needed.
