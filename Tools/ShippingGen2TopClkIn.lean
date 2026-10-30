import Tools.ShippingGen2Defs
import Tools.ShippingOutsExtractedParts
import Tools.ShippingMachineCleanup
import Tools.ShippingRegisterSoundness
set_option autoImplicit false
-- NOT BUILT (no build run yet at this commit). No `sorry`, no `axiom`, no `native_decide`.

/-! # U-TOP-CLKIN: a module with slots has `"rst"` and `"clk"` among its inputs
(scripts/gen2/TOP_CONTRACT_REVISION.md §4 rows "memory parent" / "one-output parents", rev1.1 note 2)

The producers of the R-G `TopShips` whose consumer-1 `key` still has the OLD premises (`machine_ships_hierC_run`,
FitChain:1073-1232; unchanged) wrap it with L2 (`topShipsRG_of_old`), which needs BOTH memberships in `b.inputs`.
They come from the run, not from a new premise: the trace's `MachineWired` (`MachineTraceLB`/`LBX` second-to-last
witness) has the input clause (MachineEntry:741-751)

    m.inputs = (ports.take K ++ (if slots.isEmpty then [] else [clk, rst]) ++ extra).filter (fun p => !outWs.contains p.name)

with `outWs` the calls' ports (allocated names, hence neither `clk` nor `rst`); `b.inputs = m.inputs` for the post-processed
`b` (`hpost`: zero-width cleanup, optional merge: neither changes the inputs).

* `machineWired_clk_rst_in`: `slots ≠ []` → `"clk"` and `"rst"` are inputs of `m`. Works with or without calls.
* `b_inputs_of_hpost`: `hpost` → `b.inputs = raw.inputs`.
* `clk_rst_in_b_of_wired`: the two combined. -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineEntry

/-- `hpost` keeps the inputs. -/
theorem b_inputs_of_hpost {raw b : Sparkle.IR.AST.Module}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    b.inputs = raw.inputs := by
  rcases hpost with h | h
  · rw [h]; exact Tools.ShippingOutsExtractedParts.dropZW_inputs raw
  · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1]
    exact Tools.ShippingOutsExtractedParts.dropZW_inputs raw

/-- **U-TOP-CLKIN (raw module).** A wired machine with slots has `"clk"` and `"rst"` among its inputs. -/
theorem machineWired_clk_rst_in {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Sparkle.IR.AST.Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName shape ids cache m dsn regs lets) (hsl : shape.layout.slots ≠ []) :
    "clk" ∈ m.inputs.map (·.name) ∧ "rst" ∈ m.inputs.map (·.name) := by
  obtain ⟨-, hnamesA, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinM, -⟩ := wired
  obtain ⟨outWs, extra, houtW, -, -, hMin⟩ := hinM
  have hnotin : ∀ x : String, ¬ Sparkle.IR.NameHints.Allocated x → outWs.contains x = false := by
    intro x hx
    refine Bool.eq_false_iff.mpr (fun hc => ?_)
    obtain ⟨k, -, hk⟩ := houtW x (List.contains_iff_mem.mp hc)
    exact hx (hnamesA x (List.mem_of_getElem? hk))
  have hc : (!outWs.contains "clk") = true :=
    congrArg (fun v : Bool => !v) (hnotin "clk" Tools.ShippingMachineCleanup.not_allocated_clk)
  have hr : (!outWs.contains "rst") = true :=
    congrArg (fun v : Bool => !v) (hnotin "rst" Tools.ShippingRegisterSoundness.not_allocated_rst)
  have hs' : ¬ (shape.layout.slots.isEmpty = true) := fun h => hsl (List.isEmpty_iff.mp h)
  rw [hMin, if_neg hs']
  constructor
  · refine List.mem_map.mpr ⟨({ name := "clk", ty := .bit } : Port), List.mem_filter.mpr ⟨?_, hc⟩, rfl⟩
    simp
  · refine List.mem_map.mpr ⟨({ name := "rst", ty := .bit } : Port), List.mem_filter.mpr ⟨?_, hr⟩, rfl⟩
    simp

/-- **U-TOP-CLKIN (shipped module).** The same for `b`, the post-processed module. -/
theorem clk_rst_in_b_of_wired {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {raw b : Sparkle.IR.AST.Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName shape ids cache raw dsn regs lets) (hsl : shape.layout.slots ≠ [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    "clk" ∈ b.inputs.map (·.name) ∧ "rst" ∈ b.inputs.map (·.name) := by
  rw [b_inputs_of_hpost hpost]
  exact machineWired_clk_rst_in wired hsl

end Tools.ShippingGen2
