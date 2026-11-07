import Tools.ShippingFGCircuitS2tHftOb
import Sparkle.Compiler.EnvTableCheck
set_option autoImplicit false
-- FG circuit pilot S2z step 1: a decidable check over `Environment` for the tables `Delta`/`Gamma` of `hftObCDT_of_tablesT` and `List.rec`, and its soundness
-- `hftEnvCheckB env = true → EnvDefs env Delta ∧ EnvCtors env Gamma ∧ RecFact env` (same `env`, rows exactly as `EnvDefs`/`EnvCtors`/`RecFact` state them). docs/FG-CIRCUIT-PILOT.md §49.
-- No sorry/axiom/native_decide/TRUSTED/law.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS2zEnvCheck
open Lean Elab Command Sparkle.Compiler.EnvTableCheck
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bRun

-- the row lists of the generated tables (the arguments of `mkDelta` / `mkGamma` in the generated definitions, copied as terms)
run_cmd do
  let env ← getEnv
  for (src, dst, isD) in [(``Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Delta, `Tools.ShippingFGCircuitS2zEnvCheck.hftDeltaL, true),
                          (``Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Gamma, `Tools.ShippingFGCircuitS2zEnvCheck.hftGammaL, false)] do
    let some (.defnInfo d) := env.find? src | throwError "missing {src}"
    unless d.value.getAppFn.isConstOf (if isD then ``mkDelta else ``mkGamma) && d.value.getAppNumArgs == 1 do throwError "unexpected shape of {src}"
    let l := d.value.appArg!
    let ty ← liftTermElabM (Meta.inferType l)
    liftCoreM <| addAndCompile (.defnDecl { name := dst, levelParams := [], type := ty, value := l, hints := .abbrev, safety := .safe })

theorem hftDelta_eq : Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Delta = mkDelta hftDeltaL := rfl
theorem hftGamma_eq : Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Gamma = mkGamma hftGammaL := rfl

def defTuples (l : List (Name × DefRow)) : List (Name × List Name × Expr) := l.map fun p => (p.1, p.2.lps, p.2.value)
def ctorTuples (l : List (Name × CtorRow)) : List (Name × Name × Nat × Nat) := l.map fun p => (p.1, p.2.induct, p.2.numParams, p.2.numFields)

theorem envDefs_mkDelta {env : Environment} {l : List (Name × DefRow)} (h : defsOkB env (defTuples l) = true) : EnvDefs env (mkDelta l) := by
  intro c r hr
  unfold mkDelta at hr
  cases hf : l.find? (fun p => p.1 == c) with
  | none => rw [hf] at hr; cases hr
  | some p =>
    rw [hf] at hr
    have hpr : p.2 = r := Option.some.inj hr
    have hmem : p ∈ l := List.mem_of_find?_eq_some hf
    have hpc : p.1 = c := by simpa using List.find?_some hf
    obtain ⟨d, hd, h1, h2⟩ := defsOkB_sound h (p.1, p.2.lps, p.2.value) (List.mem_map.2 ⟨p, hmem, rfl⟩)
    subst hpc; subst hpr
    exact ⟨d, hd, h1, h2⟩

theorem envCtors_mkGamma {env : Environment} {l : List (Name × CtorRow)} (h : ctorsOkB env (ctorTuples l) = true) : EnvCtors env (mkGamma l) := by
  intro c r hr
  unfold mkGamma at hr
  cases hf : l.find? (fun p => p.1 == c) with
  | none => rw [hf] at hr; cases hr
  | some p =>
    rw [hf] at hr
    have hpr : p.2 = r := Option.some.inj hr
    have hmem : p ∈ l := List.mem_of_find?_eq_some hf
    have hpc : p.1 = c := by simpa using List.find?_some hf
    obtain ⟨cv, hc, h1, h2, h3⟩ := ctorsOkB_sound h (p.1, p.2.induct, p.2.numParams, p.2.numFields) (List.mem_map.2 ⟨p, hmem, rfl⟩)
    subst hpc; subst hpr
    exact ⟨cv, hc, h1, h2, h3⟩

/-- the check of the pilot's tables against an environment -/
def hftEnvCheckB (env : Environment) : Bool :=
  defsOkB env (defTuples hftDeltaL) && ctorsOkB env (ctorTuples hftGammaL) && recOkB env

/-- soundness: a passing check gives the three conditions of v4 at the SAME environment -/
theorem hftEnvCheckB_sound {env : Environment} (h : hftEnvCheckB env = true) :
    EnvDefs env Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Delta ∧ EnvCtors env Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT.Gamma ∧ RecFact env := by
  unfold hftEnvCheckB at h
  simp only [Bool.and_eq_true] at h
  rw [hftDelta_eq, hftGamma_eq]
  exact ⟨envDefs_mkDelta h.1.1, envCtors_mkGamma h.1.2, recOkB_sound h.2⟩

end Tools.ShippingFGCircuitS2zEnvCheck

#print axioms Tools.ShippingFGCircuitS2zEnvCheck.hftEnvCheckB_sound
