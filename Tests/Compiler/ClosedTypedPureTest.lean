import Tools.ShippingNamesClk
import Tools.ShippingTextTyped
import Tools.ShippingCloseMachineTyped
import Tools.ShippingCoreWidth

/-! # Audit of the PURE steps of the closed machine's typedness (G1, round optfb-5)

The steps with no run: the `clk` / `rst` names, the bridge from the wire
table to the emitter's tables (`Tools/ShippingTextTyped.lean`), the closed
machine's typedness (`closeMachine_typed`), the remaining wire's width
(`spine_width`, `packLets_width`). Standard axioms only, an error otherwise.

A file of its own: these do not depend on the run-level files, so a failure
there does not hide them. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingNamesClk.sanitizeName_clk,
      ``Tools.ShippingNamesClk.sanitizeName_rst,
      ``Tools.ShippingTextTyped.scalarTy_spec,
      ``Tools.ShippingTextTyped.pos_wire,
      ``Tools.ShippingTextTyped.moduleWof_output,
      ``Tools.ShippingTextTyped.mem_seqNames,
      ``Tools.ShippingTextTyped.TypedIn.text,
      ``Tools.ShippingTextTyped.TypedIn.seqCheck,
      ``Tools.ShippingTextTyped.designCheck_same_of_typedIn,
      ``Tools.ShippingCloseMachineTyped.fieldRhs_typed,
      ``Tools.ShippingCloseMachineTyped.nextAssigns_zip,
      ``Tools.ShippingCloseMachineTyped.closeMachine_typed,
      ``Tools.ShippingCoreWidth.packLets_width,
      ``Tools.ShippingCoreWidth.spine_width,
      ``Tools.ShippingCoreWidth.weOf_wire_bw] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"CLOSEDTYPED PURE AUDIT: sanitizeName_clk, sanitizeName_rst, scalarTy_spec, pos_wire, moduleWof_output, mem_seqNames, TypedIn.text, TypedIn.seqCheck, designCheck_same_of_typedIn, fieldRhs_typed, nextAssigns_zip, closeMachine_typed, packLets_width, spine_width, weOf_wire_bw — standard axioms only"
