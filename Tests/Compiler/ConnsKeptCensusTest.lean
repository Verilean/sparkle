import Tests.Compiler.HierBindsCensusTest
import Tools.ShippingPortsMatchShipped

/-! # Does the connected-width guard (G5, `connsKept`) ever fire? (round par/a-2)

Compiled evidence, LOGS ONLY (prefix `CONNSKEPT`). Over the candidates of
`HierBindsCensusTest`: for the full entry's module `b` and the raw candidate
`c = deinlineRaw b (optimizeModule b)`:

* `fires`: `c` passes G2, G4 and `printOk` and fails `connsKept b c` — G5
  alone replaces the candidate by `b`;
* `connsKept b c`, `connsKept b (checkedOptimize b)`.

Expected: fires on 0 (the optimizer keeps the declaration of every wire an
instance connects).

Then an axiom audit of the guard's lemmas and of `portsMatchB_shipped` /
`core_portsMatch_shipped` (an error otherwise).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.ConnsKeptCensusTest
open Sparkle.IR.HierCheck

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let mut total := 0
  let mut fired : List Name := []
  let mut badC := 0
  let mut badO := 0
  for n in Tests.Compiler.HierBindsCensusTest.candidates do
    if env.contains n then
      try
        let (b, _) ← Sparkle.Compiler.Elab.synthesizeCombinational n
        let c := deinlineRaw b (Sparkle.IR.Optimize.optimizeModule b)
        let o := Sparkle.IR.OptCheck.checkedOptimize b
        total := total + 1
        let others := decide (instNamesOf c.body).Nodup &&
          linkedWFX ((openIns b).map (·.name)) c.body && Sparkle.IR.PrintGuard.printOk c
        let kc := connsKept b c
        let ko := connsKept b o
        if others && !kc then fired := fired ++ [n]
        unless kc do badC := badC + 1
        unless ko do badO := badO + 1
        logInfo m!"CONNSKEPT {n}: connsKept candidate={kc} shipped={ko}; G2&G4&printOk on the candidate={others}"
      catch e =>
        logInfo m!"CONNSKEPT {n}: COMPILE FAILED: {e.toMessageData}"
  logInfo m!"CONNSKEPT CENSUS: {total} declarations; G5 alone fires on {fired.length} {fired}; connsKept false on the raw candidate: {badC}, on the shipped module: {badO}"

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Sparkle.IR.HierCheck.connsKept_sound, ``Sparkle.IR.HierCheck.keepGuarded_conns,
      ``Sparkle.IR.HierCheck.deinline_conns, ``Sparkle.IR.HierCheck.keepGuarded_cases,
      ``Sparkle.IR.HierCheck.keepGuarded_print,
      ``Tools.ShippingPortsMatchShipped.checkedOptimize_conns,
      ``Tools.ShippingPortsMatchShipped.portsMatchB_shipped,
      ``Tools.ShippingPortsMatchShipped.core_portsMatch_shipped] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  Lean.logInfo m!"CONNSKEPT AUDIT: connsKept_sound, keepGuarded_conns, deinline_conns, keepGuarded_cases, keepGuarded_print, checkedOptimize_conns, portsMatchB_shipped, core_portsMatch_shipped — standard axioms only"

end Tests.Compiler.ConnsKeptCensusTest
