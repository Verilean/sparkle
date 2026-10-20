import Tools.ShippingCallWidthsDeclared

/-! # The shape decomposition, R5 / `nDecl`, and the declared one-Signal conjunct — axiom audit

Throws on a non-standard axiom. `Tools/ShippingShapeDecomp.lean`,
`Tools/ShippingCallWidthsDeclared.lean`; see `docs/parallel/B-readerinv.md`
§7. Nothing here is connected to an endpoint.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.ShapeDecompTest
open Tools.ShippingShapeDecomp Tools.ShippingCallWidthsDeclared

open Lean Elab Command in
run_cmd liftTermElabM do
  let names := [``machineShape?_decomp, ``instBinders_length, ``machSlotFields_length,
    ``ShapeDecomp.slots_length, ``ShapeDecomp.r5_of_lengths, ``ShapeDecomp.nDecl,
    ``ShapeDecomp.callBinder_bs, ``ShapeDecomp.callBinder, ``ShapeDecomp.single_out,
    ``callWidthsStrict_eq_all, ``callWidthsStrict_of_entries, ``kindTy_eq_machHWType,
    ``entryStrict_of_single, ``r1_of_kind, ``entryStrict_declared]
  for n in names do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"SHAPE DECOMP: {names.length} theorems (machineShape?_decomp; ShapeDecomp.nDecl / callBinder under the explicit hypothesis R5; entryStrict_declared under the explicit hypotheses R5 and R1) — standard axioms only; not connected to an endpoint"

end Tests.Compiler.ShapeDecompTest
