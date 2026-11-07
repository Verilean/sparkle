import Tools.ShippingFGCircuitS3aGenKids
import Tools.ShippingFGCircuitS2zPin
import Sparkle.Compiler.PilotKidTables
set_option autoImplicit false
-- FG circuit pilot S3a step 1c: the generated callee terms in `Sparkle/Compiler/PilotKidTables.lean` ARE `httpType`/`httpValue`/`httpInlValue`/`tlp…` (`decide +kernel`),
-- hence the entry's check `startKidsOk hftRoot env (userInliner env) (instancePredicate env) gatePeeledBody = true` gives `HftKidsGateFacts env` at the same `env`.
-- docs/FG-CIRCUIT-PILOT.md §50. No sorry/axiom/native_decide/TRUSTED/law.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3aKids
open Lean Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS1kStmt Sparkle.Compiler.PilotKidTables

local instance : DecidableEq Expr := fun a b => Sparkle.Compiler.ExprDecEq.exprDecEq a b

theorem pin_httpT : httpT = httpType := by decide +kernel
theorem pin_httpV : httpV = httpValue := by decide +kernel
theorem pin_httpVi : httpVi = httpInlValue := by decide +kernel
theorem pin_tlpT : tlpT = tlpType := by decide +kernel
theorem pin_tlpV : tlpV = tlpValue := by decide +kernel
theorem pin_tlpVi : tlpVi = tlpInlValue := by decide +kernel
theorem pin_http : hftHttpName = hftHttp := rfl
theorem pin_tlp : hftTlpName = hftTlp := rfl

/-- `peeled` (the statement of the facts) is the compiler's `gatePeeledBody` -/
theorem peeled_eq (e : Lean.Expr) : peeled e = Sparkle.Compiler.Elab.gatePeeledBody e := rfl

/-- **the callee check of the entry is sound for the pilot root**: `startKidsOk hftRoot env (userInliner env) (instancePredicate env) gatePeeledBody = true` gives `HftKidsGateFacts env` at the same `env` -/
theorem startKidsOk_sound {env : Environment}
    (h : startKidsOk hftRoot env (Sparkle.Compiler.Elab.userInliner env) (Sparkle.Compiler.Elab.instancePredicate env) Sparkle.Compiler.Elab.gatePeeledBody = true) :
    HftKidsGateFacts env := by
  unfold startKidsOk at h
  rw [← Tools.ShippingFGCircuitS2zPin.pin_root] at h
  simp only [beq_self_eq_true, if_true] at h
  unfold kidsOkB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨⟨d1, e1, l1, t1, v1⟩, u1, u2, i1, i2⟩ := Sparkle.Compiler.KidFactsCheck.kidRowOkB_sound h1
  obtain ⟨⟨d2, e2, l2, t2, v2⟩, w1, w2, j1, j2⟩ := Sparkle.Compiler.KidFactsCheck.kidRowOkB_sound h2
  rw [pin_http, pin_httpT, pin_httpV, pin_httpVi] at *
  rw [pin_tlp, pin_tlpT, pin_tlpV, pin_tlpVi] at *
  exact ⟨⟨⟨d1, e1, l1, t1, v1⟩, u1, u2, i1, i2⟩, ⟨⟨d2, e2, l2, t2, v2⟩, w1, w2, j1, j2⟩⟩

end Tools.ShippingFGCircuitS3aKids

#print axioms Tools.ShippingFGCircuitS3aKids.startKidsOk_sound
