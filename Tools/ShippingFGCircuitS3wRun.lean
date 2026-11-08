import Tools.ShippingFGCircuitS3wComb
import Tools.ShippingFGCircuitS3tCombRun
set_option autoImplicit false
-- FG circuit pilot S3w, step 2 (run): `checkCombN` (`Tools.ShippingFGCircuitS3wComb`) against the source terms `ofData` reads off a child's `MachineData`, evaluated by the KERNEL (`decide +kernel`) on the two closed generated children `pilotK0` (`httpGetByte`) and `pilotK1` (`tlpCplByte`, 159 statements).  Negative controls: every S3t control for `pilotK0` still rejected; mutated `pilotK1`s, the other child's data, and the Bool-to-bit rule applied to a swapped pair rejected.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §72.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3wRun
open Tools.ShippingFGCircuitS3tComb Tools.ShippingFGCircuitS3tCombRun Tools.ShippingFGCircuitS3wComb
open Tools.ShippingFGCircuitS3rArtifact
open Sparkle.IR.AST

/-- the data's source terms checked against a module with the normalising validator -/
noncomputable def checkWithN (d : Tools.ShippingMachineAuto.MachineData) (m : Module) : Bool :=
  match ofData d with
  | some s => checkCombN s m
  | none => false

noncomputable abbrev kd0 : Tools.ShippingMachineAuto.MachineData := Sparkle.IP.Net.HTTP.httpGetByte.machineData
noncomputable abbrev kd1 : Tools.ShippingMachineAuto.MachineData := Sparkle.IP.Bus.PCIe.tlpCplByte.machineData

/-- `pilotK0` is still accepted -/
theorem k0_checkN : checkWithN kd0 pilotK0 = true := by decide +kernel
/-- **`pilotK1` (`tlpCplByte`) is accepted** -/
theorem k1_checkN : checkWithN kd1 pilotK1 = true := by decide +kernel

/-! ### the first difference (the diagnosis), as kernel facts -/

/-- `ofData` reads the data of `tlpCplByte` (no `ofData` failure) -/
theorem k1_ofData_some : (ofData kd1).isSome = true := by decide +kernel
/-- the unnormalised comparison rejects `pilotK1` -/
theorem k1_check_unnormalised : (match ofData kd1 with | some s => checkComb s pilotK1 | none => true) = false := by decide +kernel

/-! ### negative controls -/

/-- the S3t controls, for the normalising validator (all on `pilotK0`) -/
theorem neg0_drop_first : checkWithN kd0 (dropFirst pilotK0) = false := by decide +kernel
theorem neg0_drop_last : checkWithN kd0 (dropLast pilotK0) = false := by decide +kernel
theorem neg0_flip_const : checkWithN kd0 (flipConst pilotK0) = false := by decide +kernel
theorem neg0_swap_mux : checkWithN kd0 (swapMux pilotK0) = false := by decide +kernel
theorem neg0_wrong_width : checkWithN kd0 (wrongWidth pilotK0) = false := by decide +kernel
theorem neg0_wrong_out_w : checkWithN kd0 (wrongOutW pilotK0) = false := by decide +kernel
theorem neg0_wrong_out_name : checkWithN kd0 (wrongOutName pilotK0) = false := by decide +kernel
theorem neg0_other_child : checkWithN kd0 pilotK1 = false := by decide +kernel
theorem neg0_wrong_source : checkCombN ⟨[1], [CTerm.lit 8 0]⟩ pilotK0 = false := by decide +kernel

/-- `pilotK1` mutated: the first statement dropped, the last (the output) dropped, the constant 74 (`b0`) changed to 75, a slice bound moved, the two data operands of every `mux` swapped (this includes the Bool-to-bit `mux` pairs), the declared width of `_gen_b0` changed, the output port 7 bits wide, renamed -/
def flip74 (m : Module) : Module :=
  { m with body := m.body.map fun st => match st with
      | .assign l (.const 74 8) => .assign l (.const 75 8)
      | s => s }
def moveSlice (m : Module) : Module :=
  { m with body := m.body.map fun st => match st with
      | .assign "_gen_b4" (.slice e 7 0) => .assign "_gen_b4" (.slice e 6 0)
      | s => s }
/-- only the Bool-to-bit constants of the LAST condition swapped (1 and 0 exchanged in `_tmp_mux_then_55`/`_tmp_mux_else_56`): the rule must not fire on the swapped pair -/
def swapBoolPair (m : Module) : Module :=
  { m with body := m.body.map fun st => match st with
      | .assign "_tmp_mux_then_55" e => .assign "_tmp_mux_else_56" e
      | .assign "_tmp_mux_else_56" e => .assign "_tmp_mux_then_55" e
      | s => s }

theorem neg1_drop_first : checkWithN kd1 (dropFirst pilotK1) = false := by decide +kernel
theorem neg1_drop_last : checkWithN kd1 (dropLast pilotK1) = false := by decide +kernel
theorem neg1_flip_const : checkWithN kd1 (flip74 pilotK1) = false := by decide +kernel
theorem neg1_move_slice : checkWithN kd1 (moveSlice pilotK1) = false := by decide +kernel
theorem neg1_swap_mux : checkWithN kd1 (swapMux pilotK1) = false := by decide +kernel
theorem neg1_swap_bool_pair : checkWithN kd1 (swapBoolPair pilotK1) = false := by decide +kernel
theorem neg1_wrong_width : checkWithN kd1 (wrongWidth pilotK1) = false := by decide +kernel
theorem neg1_wrong_out_w : checkWithN kd1 (wrongOutW pilotK1) = false := by decide +kernel
theorem neg1_wrong_out_name : checkWithN kd1 (wrongOutName pilotK1) = false := by decide +kernel
/-- the other child's module / the other child's data -/
theorem neg1_other_child : checkWithN kd1 pilotK0 = false := by decide +kernel
/-- a wrong source term for the output -/
theorem neg1_wrong_source : checkCombN ⟨[1, 2, 3, 4, 5, 6], [CTerm.lit 8 0]⟩ pilotK1 = false := by decide +kernel
/-- the altered modules are different terms (the controls are not vacuous) -/
theorem neg1_distinct : decide ((flip74 pilotK1).body = pilotK1.body) = false ∧
    decide ((moveSlice pilotK1).body = pilotK1.body) = false ∧ decide ((swapBoolPair pilotK1).body = pilotK1.body) = false ∧
    decide ((swapMux pilotK1).body = pilotK1.body) = false ∧ decide ((dropFirst pilotK1).body = pilotK1.body) = false := by
  decide +kernel

end Tools.ShippingFGCircuitS3wRun
