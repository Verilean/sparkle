# S2 stop-report: no real declaration is a slotless `Pkg` (FOR REVIEW)

- **Issue:** `sparkle-gen2-step`.
- **Branch:** `par/gen2-spec` at bb31bb0b.

## Evidence (two failed diagnostics, recorded)
- **`g2st-s2i-bf7d963e` (bf7d963e).** The corpus' slotless machine-route child `pickByteH` (Tests/Compiler/ShippingMachineLinkedTest.lean:21, a plain `let` expression) has `machineData`, `machineInits`, `machine_ok`, `machine_body`, `machine_closes` and `machine_combKid`. It has NO `machineBody`, `machineResult`, `machine_writes` or `machine_source` (`Unknown constant`, log 6750-6755). It DOES have `machineSource`: the comb endpoint (`combProof`, MachineCommand.lean:2008-2024) defines it, with `machine_next`/`machine_result` (correction after review; the later `decide`/`rfl` failures are cascades of the missing `pbh_gen`). So no `GenFacts`, and no `.gen` package.
- **`g2st-s2i-bb31bb0b` (bb31bb0b).** A self-declared `circuit do` with no register is refused by the front end: "circuit do: at least one `let r ← Signal.reg …` is required", followed by "not a machine shape". So `.gen` and `.loop` packages, the data/loop routes that produce `GenFacts`/`LoopFacts`, always have `slots ≠ []`, as far as these two observations show.
- **How slotless machine-route declarations are covered today:** a DIFFERENT fact family, `SlotlessLeaf … f f.machineData` (Tools/ShippingLeafOneOut.lean; used in Tests/Compiler/OneOutCallerLTest.lean:120), plus `machine_combKid`/`machine_combPos` (Tools/ShippingCombLeafClosedCommand.lean). Their source meaning is through the one-output closing route (`childFn_of_trace` style), not `stateLoop`.

## Consequence
- **What holds:** `slotlessLeaf_ships : SlotlessLeafStmt L` (built, standard axioms) is a true theorem.
- **What is not shown:** that it applies to any real declaration. Every real `Pkg` seen so far has `slots ≠ []`. This is not proved as a lemma; it is observed from the front end's refusal and the generator's output families.
- **So G-SLOTLESS is not discharged by S2 as it stands.** A real slotless declaration needs a package kind that carries its actual generated facts.

## Options (for review; no change applied)
1. **(recommended) A third `Pkg` constructor `.comb`** over the slotless fact family.
   - **Fields:** `d : MachineData`, `ok`, `body_eq`, and a source function `src`, defined as the closed one-output (or multi-output) combinational meaning of the reader's data.
   - **The theorem:** `Pkg.trace` for `.comb` comes from the existing slotless machine trace (`machine_traceL_of_*` for `closeLets`, MachineCommand.lean:2670-2680), on the A boundary as `Pkg.trace` does for `.gen`.
   - **Then:** S2's lemmas (stated over `MachineTraceLB`) apply unchanged. The non-vacuity instance becomes `pickByteH`.
   - **Cost:** the `Pkg` accessors and their by-cases theorems (`trace`, `ok`, `body_eq`, `lsrc_hl`), and a PkgCompat-style check.
2. **Keep `Pkg`, and state G-SLOTLESS over the existing `SlotlessLeaf` facts directly.** This sits outside `ShipsRes`/`ChildShips`, which need `P c = some q`. So the induction could not use it without (1).
3. **Rule out slotless machine children.** Not acceptable: they exist in the corpus (`pickByteH`, the 26 `machine_combKid` declarations), and FG must cover them.

## Next steps
- Ask for review of option 1's design: a freeze with the exact fields and `Pkg.trace .comb`.
- Meanwhile S4 (one-output parents) is unaffected: its children come from the parent's closing.
- The one-output `CallDec` probe (`sparkle-gen4-oneout-probe`) continues.
