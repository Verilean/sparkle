import Tools.ShippingNamesNext

/-! # Audit of the next-value wire names (branch `fix/opt-fallback`)

`Tools/ShippingNamesNext.lean` (`clean_nextName`, `sanitizeName_nextName`):
standard axioms only, an error otherwise. A file of its own: the proof of
`clean_nextName` evaluates the characters of a string literal and is the
most likely of round optfb-4 to need a repair. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Tools.ShippingNamesNext.clean_nextName,
      ``Tools.ShippingNamesNext.sanitizeName_nextName] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"NAMESNEXT AUDIT: clean_nextName, sanitizeName_nextName — standard axioms only"
