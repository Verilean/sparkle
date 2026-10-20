import Sparkle.IR.RefineCheck
import Sparkle.Backend.VerilogDesign

/-! # The shipped module keeps the ports, in every branch (round par/a-2)

`checkedOptimize_ports`: `(checkedOptimize m).inputs = m.inputs` and the
same of the outputs, with NO hypothesis on `m` — the fact `#simChecked`
(and any consumer that numbers ports by position) needs of the top module.

* `optimizeModule_ports`: the optimizer never touches the port lists (a
  primitive module is returned as it is; otherwise the result is
  `eliminateZeroBits { m' with body, wires }` over
  `m' = eliminateZeroBits m`, both record updates of body and wires only).
  In particular it cannot drop an unused port.
* `deinline_ports`: `deinline m o` is `m` or `{ o with body, wires }`.
* every branch of `checkedOptimize` returns `m`, the optimizer's output, or
  `deinline m` of it — the checks' own port conjuncts are not used.
* `designArtifact_ports`: every module of a design has a module of the
  writer's artifact with its ports.

(Existing, weaker: `Tools.ShippingModuleNames.checkedOptimize_name`
(unconditional, the name), `Tools.ShippingHierShipsSV.checkedOptimize_inputs`
(under `hierBinds`), `Tools.ShippingOptSoundness.checkedOptimize_ports`
(under `simpleBody`).)

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingOptimizePorts
open Sparkle.IR.AST
open Sparkle.IR.OptCheck (checkedOptimize)

set_option maxRecDepth 4096 in
/-- The optimizer keeps the port lists. -/
theorem optimizeModule_ports (m : Sparkle.IR.AST.Module) :
    (Sparkle.IR.Optimize.optimizeModule m).inputs = m.inputs ∧
      (Sparkle.IR.Optimize.optimizeModule m).outputs = m.outputs := by
  unfold Sparkle.IR.Optimize.optimizeModule
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- The guarded candidate keeps the port lists of a candidate that has them. -/
theorem deinline_ports (m o : Sparkle.IR.AST.Module) (hi : o.inputs = m.inputs)
    (ho : o.outputs = m.outputs) :
    (Sparkle.IR.HierCheck.deinline m o).inputs = m.inputs ∧
      (Sparkle.IR.HierCheck.deinline m o).outputs = m.outputs := by
  rcases Sparkle.IR.HierCheck.deinline_cases m o with ⟨e, -, -⟩ | e
  · rw [e]
    exact ⟨hi, ho⟩
  · rw [e]
    exact ⟨rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- **The shipped module has the input module's ports**, whatever branch
the compiler took. -/
theorem checkedOptimize_ports (m : Sparkle.IR.AST.Module) :
    (checkedOptimize m).inputs = m.inputs ∧ (checkedOptimize m).outputs = m.outputs := by
  have hp := optimizeModule_ports m
  unfold checkedOptimize
  dsimp only
  repeat' split
  all_goals first
    | exact hp
    | exact ⟨rfl, rfl⟩
    | exact deinline_ports _ _ hp.1 hp.2

/-- Every module of a design has, in the writer's artifact, a module with
its ports. -/
theorem designArtifact_ports (d : Design) {m : Sparkle.IR.AST.Module} (hm : m ∈ d.modules) :
    ∃ a ∈ Sparkle.Backend.Verilog.designArtifact d,
      a.inputs = m.inputs ∧ a.outputs = m.outputs := by
  unfold Sparkle.Backend.Verilog.designArtifact
  refine ⟨if m.name == d.topModule then checkedOptimize m else m,
    List.mem_map.mpr ⟨m, hm, rfl⟩, ?_⟩
  split
  · exact checkedOptimize_ports m
  · exact ⟨rfl, rfl⟩

end Tools.ShippingOptimizePorts
