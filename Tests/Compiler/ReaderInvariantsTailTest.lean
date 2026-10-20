import Tools.ShippingMachineShapeTail

/-! # The second half of P4 and its compositions — axiom audit (throws on a non-standard axiom)

`Tools/ShippingMachineShapeTail.lean`: `machineShape?_some`,
`machineShape?_callBinder`, `machineShape?_single_out`, `callee_single_out`.
See `docs/parallel/B-readerinv.md`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.ReaderInvariantsTailTest
open Tools.ShippingMachineShapeUnfold

open Lean Elab Command in
run_cmd liftTermElabM do
  let names := [``machineShape?_some, ``machineShape?_callBinder,
    ``machineShape?_single_out, ``callee_single_out]
  for n in names do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"READER INVARIANTS TAIL: {names.length} theorems (P4 machineShape?_some, machineShape?_callBinder; compositions machineShape?_single_out, callee_single_out) — standard axioms only"

end Tests.Compiler.ReaderInvariantsTailTest
