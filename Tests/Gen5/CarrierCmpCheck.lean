import Lean
import Tools.ShippingGen5CarrierU
import Tools.ShippingGen5CarrierP
import Tools.ShippingGen5CarrierI
set_option autoImplicit false
/-! # Check for the carrier-extension prototypes (issue sparkle-ledger-dd4-final, Q-A (ii); draft: §Compare)

Axiom census of every theorem of the three prototype files (`CarrierU`, `CarrierP`, `CarrierI`): only `propext` / `Classical.choice` / `Quot.sound` may occur (never `sorryAx`, never a user axiom).
Control: the detector reports `Classical.choice` for `Classical.em`, and the three new rules exist (`CVPB.thm`, `CVIB.iota`, universe-polymorphic `CVU`). -/
open Lean Elab Command

def okAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#carrier_axiom_census" : command => do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array String := #[]
  let mut perFile : Array String := #[]
  for ns in [`Tools.ShippingGen5CarrierU, `Tools.ShippingGen5CarrierP, `Tools.ShippingGen5CarrierI] do
    let mut cnt : Nat := 0
    for (c, ci) in env.constants.map₁.toList do
      if ns.isPrefixOf c && (ci.isTheorem || ci.isDefinition) && !c.isInternal then
        let ax ← liftCoreM (Lean.collectAxioms c)
        cnt := cnt + 1
        for a in ax do
          unless okAxioms.contains a do bad := bad.push s!"{c}: {a}"
    perFile := perFile.push s!"{ns}: {cnt} declarations"
    n := n + cnt
  logInfo m!"axiom census: {n} declarations in the 3 prototype files; {perFile.toList}; non-standard axioms: {bad.toList}"
  unless bad.isEmpty do throwError "non-standard axioms: {bad}"

elab "#carrier_axiom_control" : command => do
  let env ← getEnv
  let ax ← liftCoreM (Lean.collectAxioms ``Classical.em)
  unless ax.contains ``Classical.choice do throwError "detector control failed: Classical.em should depend on Classical.choice"
  logInfo m!"detector control ok: Classical.em uses {ax.toList}"
  -- the new rules exist with the stated shapes
  let has (n : Name) : CommandElabM Unit := unless env.contains n do throwError "missing {n}"
  has ``Tools.ShippingGen5CarrierP.CVPB.thm
  has ``Tools.ShippingGen5CarrierI.CVIB.iota
  has ``Tools.ShippingGen5CarrierU.cvu_fun
  has ``Tools.ShippingGen5CarrierP.cvp_fun
  has ``Tools.ShippingGen5CarrierI.cvi_fun
  logInfo m!"rules and functionality theorems present"

#carrier_axiom_control
#carrier_axiom_census
