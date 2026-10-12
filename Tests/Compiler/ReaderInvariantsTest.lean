import Tools.ShippingMachineShapeUnfold

/-! # Reader invariants P1, P2 and the PREFIX of P4 — axiom audit (throws on a non-standard axiom)

The theorems of `Tools/ShippingInstSignature.lean` (P1),
`Tools/ShippingReaderResultKind.lean` (P2) and
`Tools/ShippingMachineShapeUnfold.lean` (the prefix of `machineShape?`, the
one-step inversions, the list facts). The second half of P4 and the
compositions are audited in `Tests/Compiler/ReaderInvariantsTailTest.lean`.
See `docs/parallel/B-readerinv.md`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.ReaderInvariantsTest
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature
open Tools.ShippingMachineShapeUnfold

open Lean Elab Command in
run_cmd liftTermElabM do
  let names := [``instSignature?_some, ``instSignatureS?_some, ``structEnv_inst,
    ``structEnv_instS, ``kind_inv, ``machOuts?_signal, ``outs_of_kind,
    ``machResultKind?_inv, ``machOuts?_of_resultKind, ``machResultKind?_ne_domain,
    ``machOutFields_single, ``ite_none_inv, ``ite_else_none_inv, ``bind_inv,
    ``machineShape?_prefix, ``declOuts?_of_resultKind, ``instBinders_kinds, ``getElem?_mid]
  for n in names do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"READER INVARIANTS: {names.length} theorems (P1 instSignature?_some / instSignatureS?_some; P2 machOuts?_of_resultKind, declOuts?_of_resultKind; P4 prefix machineShape?_prefix) — standard axioms only"

end Tests.Compiler.ReaderInvariantsTest
