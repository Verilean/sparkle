import Tools.ShippingHeapProvenance
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! # Regression: the model counterexamples stay (round par/tr-mm-ca)

BUILT by the integrator: hr1 exit 1 (missing `import Lean.Elab.Command`), hr2 exit 0. Integrator-written. The pure heap model (`Tools/ShippingHeapModel.lean`,
`Tools/ShippingHeapProvenance.lean`) keeps two NEGATIVE results; this file
re-derives each as a kernel-checked `theorem` here, so removing or weakening
them breaks the suite:

* `historyElsewhere_not_fresh`: an allocation HISTORY in another world (the
  shape of `MkRefd`, `Tools/ShippingChildFresh.lean`) does NOT give
  non-alias in the use world — the returned ref equals (by id) a ref already
  valid there. So `MkRefd` is not `FreshIn`, and non-alias in the real run is
  NOT established by it;
* `frame_all_false` (a frame law over ALL actions is false in the model).

And it checks that the POSITIVE model results used by the ledger
(`prov_set_frame`, `prov_modify_frame`, `allocIn_ne_valid`) exist with
standard axioms. All of this is about the PURE MODEL; the fit of the model to
the real `ST` runtime is OPEN. -/

namespace Tests.Compiler.HeapProvenanceRegressTest
open Tools.ShippingHeapModel Tools.ShippingHeapProvenance

theorem historyElsewhere_not_fresh {σ : Sig} (h : Heap σ) (v : σ.O) :
    (∃ h0 h1, AllocIn h0 (@Ref.other σ 0) h1) ∧
    ¬ (∀ (β : Type) (r' : Ref σ β), Valid r' { h with next := 1 } →
        (@Ref.other σ 0).id ≠ r'.id) :=
  ⟨⟨_, _, (history_elsewhere_aliases h v).1⟩,
   fun hall => hall _ _ (history_elsewhere_aliases h v).2 rfl⟩

end Tests.Compiler.HeapProvenanceRegressTest

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tests.Compiler.HeapProvenanceRegressTest.historyElsewhere_not_fresh,
      ``Tools.ShippingHeapModel.frame_all_false,
      ``Tools.ShippingHeapProvenance.prov_set_frame,
      ``Tools.ShippingHeapProvenance.prov_modify_frame,
      ``Tools.ShippingHeapProvenance.allocIn_ne_valid] do
    unless (← getEnv).contains n do throwError "HEAPREGRESS: {n} absent"
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "HEAPREGRESS: {n} uses {ax}"
  logInfo "HEAPREGRESS OK: model counterexamples (history elsewhere ≠ freshness; frame over all actions false) and positive model frames present, standard axioms (model only; runtime fit OPEN)"
