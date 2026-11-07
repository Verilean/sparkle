import Tools.ShippingFGCircuitS2zEnvCheck
import Tools.ShippingFGCircuitS1kStmt
import Sparkle.Compiler.PilotEnvTables
set_option autoImplicit false
-- FG circuit pilot S2z step 2: the generated rows in `Sparkle/Compiler/PilotEnvTables.lean` ARE the rows of `hftObCDT_of_tablesT.Delta/Gamma` (`decide +kernel`: `pin_defs` / `pin_ctors`), hence
-- the entry's check `startEnvOk hftRoot env = true` gives `EnvDefs ∧ EnvCtors ∧ RecFact` at the same `env`. docs/FG-CIRCUIT-PILOT.md §49. No sorry/axiom/native_decide/TRUSTED/law.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS2zPin
open Lean Tools.ShippingFGCircuitS2zEnvCheck Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1wTbl
open Sparkle.Compiler.PilotEnvTables

local instance : DecidableEq Expr := fun a b => Sparkle.Compiler.ExprDecEq.exprDecEq a b

theorem pin_defs : hftDefRows = defTuples hftDeltaL := by decide +kernel
theorem pin_ctors : hftCtorRows = ctorTuples hftGammaL := by decide +kernel
theorem pin_root : hftRootName = Tools.ShippingFGCircuitS1kStmt.hftRoot := rfl

theorem tablesOkB_eq (env : Environment) : tablesOkB env = hftEnvCheckB env := by
  unfold tablesOkB hftEnvCheckB
  rw [pin_defs, pin_ctors]

/-- **the check of the entry is sound for the pilot root**: `startEnvOk hftRoot env = true` gives the three conditions of v4 at the same `env` -/
theorem startEnvOk_sound {env : Environment} (h : startEnvOk Tools.ShippingFGCircuitS1kStmt.hftRoot env = true) :
    EnvDefs env Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Delta ∧ EnvCtors env Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Gamma ∧ RecFact env := by
  unfold startEnvOk at h
  rw [← pin_root] at h
  simp only [beq_self_eq_true, if_true] at h
  rw [tablesOkB_eq] at h
  exact hftEnvCheckB_sound h

end Tools.ShippingFGCircuitS2zPin

#print axioms Tools.ShippingFGCircuitS2zPin.startEnvOk_sound
