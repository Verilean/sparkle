import Tools.ShippingReaderLenOkReserve

/-! # The length invariant of the reader state, pure part — axiom audit

Throws on a non-standard axiom. `Tools/ShippingReaderLenOk.lean` (the
invariant, the initial state, every update site),
`Tools/ShippingReaderLenOkReserve.lean` (`machReserve`, the list lengths).
See `docs/parallel/B-readerinv.md` §8. NOT covered by any theorem: that the
state the `partial` readers return satisfies the invariant
(`ReadersKeepLenOk` is a definition, used by nothing). Nothing here is
connected to an endpoint.

UNVERIFIED: written, not built. -/
namespace Tests.Compiler.ReaderLenOkTest
open Tools.ShippingReaderLenOk

open Lean Elab Command in
run_cmd liftTermElabM do
  let names := [``lenOk_iff, ``lenOk_init, ``lenOk_frame, ``lenOk_append,
    ``lenOk_bareRegister, ``lenOk_loopRoot, ``lenOk_reserved,
    ``lenOk_ws, ``lenOk_instStruct, ``lenOk_lets, ``lenOk_inInner, ``lenOk_nestedClose,
    ``lenOk_dom, ``lenOk_instPush, ``lenOk_instS, ``lenOk_loopClose,
    ``mapM_option_length, ``loopRoot_inits_length, ``machInits_length,
    ``machSlotNames_length, ``machReserve_eq_spec, ``machReserve_some,
    ``machReserve_lenOk, ``machReserve_lenOk_init]
  for n in names do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"READER LENOK: {names.length} theorems (initial state; 3 slot-writing update sites, each writes all three arrays; 20 other update sites; machReserve preserves) — standard axioms only; the reachable state is NOT covered (partial readers: opaque constants)"

end Tests.Compiler.ReaderLenOkTest
