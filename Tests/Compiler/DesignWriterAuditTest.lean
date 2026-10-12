import Tools.ShippingDesignWriterRun

/-! # The design writer prints the endpoints' artifact: axiom audit

Throws if a theorem of `Tools/ShippingDesignWriter*.lean` depends on an
axiom beyond `propext`, `Classical.choice`, `Quot.sound`. -/

open Lean Elab Command in
run_cmd liftTermElabM do
  let names : List Name := [
    ``Tools.ShippingDesignWriter.toVerilogDesignChecked_eq,
    ``Tools.ShippingDesignWriter.hier_artifact,
    ``Tools.ShippingDesignWriter.toVerilogDesignChecked_hier,
    ``Tools.ShippingDesignWriterRun.writer_prints_endpoint_artifact]
  for e in names do
    let axs ← Lean.collectAxioms e
    if axs.any fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
      throwError "{e} depends on a non-standard axiom: {axs}"
  logInfo m!"DESIGNWRITER AUDIT: {names} — standard axioms only"
