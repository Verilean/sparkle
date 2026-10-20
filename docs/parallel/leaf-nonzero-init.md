# Nonzero inits of REMOVED registers on the leaf route (round par/leafnz)

Base aa35e8a6. Status: BUILT (lf2/lf4 exit 0, ax5 standard); the plan sections below are now implemented as far as stated in the commit; no leaf sat layer, design-level leaf heads and generator not ported. Proved = theorem in a file written here
(kernel check pending the integrator's build); premise = hypothesis of a theorem; open = not done.

## 1. Where the leaf route ties the target start state to the source's

Leaf route = register machine, no instances (`d.shape.insts = []`, `hierGate b = false`).

* `MachineShips` (Tools/ShippingMachineShipping.lean:63-97) — the ship-level statement every
  leaf endpoint concludes (`f.machine_ships_wired`, `f.machine_ships_leafC`, the leaf design
  heads in Tools/ShippingLeafDesign.lean:240ff). ONE start state `st0` is used for the core
  module `raw`, the entry module `b`, the optimized module `o = checkedOptimize b` and its
  emitted Verilog (conclusion: `runModule (declWidth o) o.body (seedIn raw ins) T st0 mems`,
  `runModuleSV … T st0 mems`).
* Hypotheses fixing `st0`: the slot inits `st0 r = f.init` (:83-84), width fits on `raw`/`b`
  registers (:85-86), and `Bounded (weOf wof) st0` (:87) — over ALL names
  (`Bounded we env := ∀ n, env n < 2 ^ we n`, Sparkle/IR/Semantics.lean:503).
* `machine_ships` (ShippingMachineShipping.lean:105) is where the hard-wiring happens:
  both `refineCheck_transfer` calls use `(stO := st0) (fun _ _ => rfl)` (merge step :140,
  optimizer step :159). The optimizer step is the analogue of `hierRefineCheck_linked`'s
  `stO := s.st`.
* `machine_ships_wired` (Tools/ShippingMachineShipsW.lean:41) only derives the gates and
  calls `machine_ships` (:110); the generator builds it inline
  (Tools/ShippingMachineCommand.lean:2641-2681, `soundL := mkAppN headL args`, no named
  `soundL` constant).

## 2. Vacuity for a removed nonzero-init register (as for TBW)

At the emitter's width map (`wof = wofOf (checkedOptimize b)`, as `f.machine_ships_leafC`
states it), `weOf wof r = 0` for a register `r` the optimizer removed (probe nz3:
`dead7 reg _gen_loop0_r1: init 7; weS opt = 0; driven in opt: false`). Then `Bounded (weOf
wof) st0` demands `st0 r < 1`, while the init hypothesis demands `st0 r = 7`: the
hypotheses of `MachineShips` are jointly unsatisfiable, so every existing leaf endpoint is
VACUOUS for `dead7`. (Same mechanism as TBW, docs/parallel/nonzero-init.md §1.)

## 3. What already has two states

`refineCheck_run_sound` / `refineCheck_transfer` (Tools/ShippingRefineSoundness.lean:934 /
:1039) take `stM`, `stO` with only `∀ r ∈ seqRegs o, stO r.1 = stM r.1` and a width fit of
`stM` on `seqRegs m`. Inside `refineCheck_step_sound` (:687; extraction at :709-725) the
check gives, for every kept register `ro ∈ seqRegs o`, a namesake `rm ∈ seqRegs m` with
`declWidth m rm.1 = declWidth o ro.1` — not exported as a lemma.

## 4. Plan (this round)

New file Tools/ShippingMachineShipsS.lean:
* `tgtSt b o st0 n := if refineCheck b o ∧ n ∉ (seqRegs o).map (·.1) then 0 else st0 n`
  — the TARGET start state: the source state cleared on every name the accepted optimized
  module does not keep as a register (in particular every removed register).
* `refineCheck_regWidth` (copy of the :709-725 extraction): kept registers keep their width.
* `tgtSt_agree`: `∀ r ∈ seqRegs o, tgtSt b o st0 r.1 = st0 r.1` (the correspondence).
* `tgtSt_bounded`: when `refineCheck b o`, `Bounded (weOf wof) (tgtSt b o st0)` from the
  width fit of `st0` on `seqRegs b` and the width agreement `hwag` (registers are in
  `seqNames`) — NO bound on `st0` outside the kept registers.
* `MachineShipsS` = `MachineShips` with the target run (module and emitted Verilog) from
  `tgtSt b o st0`, and `Bounded (weOf wof) st0` asked ONLY when the optimizer's output was
  rejected (`refineCheck b o = false`, then `o = b` and nothing is removed).
* `machine_shipsS` (proof of `machine_ships` with the optimizer step's `stO := tgtSt …`),
  `machine_ships_wiredS` (proof of `machine_ships_wired` ending in `machine_shipsS`).

Test Tests/Compiler/LeafDeadInitTest.lean: `dead7` copied into namespace
`LeafDeadInitTest`, `#machine_endpoint`; run_cmd ASSERTS on the compiled module: a register
of `b` with init 7 is not a register of `checkedOptimize b`, `refineCheck b (checkedOptimize
b) = true`, and `weOf (wofOf opt)` of it is 0; a meta command rebuilds
`machine_ships_wiredS data soundL` from the value of `dead7.machine_ships_wired`
(`machine_ships_wired data soundL`) and adds it as `dead7.machine_ships_wiredS`
(kernel-checked); a theorem showing the source hypotheses are satisfiable at the removed
register is left as stated in §5.

## 5. Open (after this round)

* A leaf "sat" lemma (analogue of `sat_of_designClosedBS`): the leaf route has no sat layer
  today; the full discharge of the source hypotheses at `st0 = slot inits` is not written.
* The design-level leaf heads (Tools/ShippingLeafDesign.lean:240-606, `Bounded (weS
  (checkedOptimize b)) st0`) and `f.machine_ships_leafC` still use one state; porting them to
  `MachineShipsS` is the next step.
* Generator: `#machine_endpoint` does not emit `machine_ships_wiredS`.

## 6. Round par/leafnz-sat (written, not built; base 9df7578c)

* Tools/ShippingLeafSat.lean — `tgtSt2 raw b o st0` (cleared off `seqRegs o` when the MERGE or
  the optimizer was accepted by `refineCheck`; `st0` when both were the identity) and
  `leaf_sat`: from the wired endpoint (`soundL`, the four structural facts), data `hlen`,
  `hinitW` and the run, for every wof passing the text checks (+ `hwofIn`: emitted widths cover
  the input widths), every typed stream and every `T`, the stream's seeding (`leafIns`) carries
  the source inputs and the optimized module + emitted Verilog from
  `tgtSt2 … (slotInit regs slots)` show the source. Every run hypothesis (inputs, register
  pass-through, reset, slot inits, width fits, the bound) is PROVED from `MachineWired` under
  `insts = []`. Why not `MachineShipsS`: when the checked MERGE drops a slot register and the
  optimizer is rejected, `MachineShipsS`'s rejected-branch bound on `st0` is unsatisfiable
  (same mechanism as §2), so `leaf_sat` re-proves the chain with `tgtSt2`.
* Tools/ShippingLeafSatDesign.lean — `leaf_sat_design`: the same at `wofOf (checkedOptimize b)`,
  as `DesignSV C 0` over every child map and children's state, with uniqueness; antecedent `hs`
  (statement kinds of the shipped module) as in `leaf_design_of_ships`.
* Tests/Compiler/LeafDeadInitSatTest.lean — `dead7.machine_sat` (kernel), premises only
  `hr`, `MachineDefines`, `MachineCloses`; audit: standard axioms, no premise mentions
  `seedIn`/`Bounded`/`slotInit`/`SlotField.init`/`streamEnv`/`leafIns`.
* Open: the text-check antecedents (`seqCheck`, width agreement, `hwofIn`, `hs`) are not
  discharged for dead7 by theorem; the generator does not emit `machine_sat`.
