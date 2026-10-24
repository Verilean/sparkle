import Tools.ShippingSrm28Regs
import Tools.ShippingShipsFree
set_option autoImplicit false
-- UNBUILT (unit SRM32): see REPORT-SRM32.md for the dev runs and the final-SHA rebuild (the only final evidence).
-- SCOPE (generic, no topshare instance): `MachineWired` (Tools/ShippingMachineEntry.lean) now EXPORTS, as its 20th conjunct, the slot-register WIDTH relation for its own `m`, `regs`,
-- UNCONDITIONALLY (also for shape.insts ≠ []); it is PROVED at the producer (closeMachine wires + closeInsts_some / closeInstsG_some).  Here: (1) that conjunct read off;
-- (2) the width link `f.width ≤ declWidth b r` for the shipped `b` (b = dropZeroWidthModule m via hpost, hierGate b, the cleanup conjunct of MachineWired).
-- G1, G3, K1, hsk, FitTree, hRK, hst facts, hW, hinit and every other binder are untouched.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm32
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.IR.RefineCheck (hierGate mergeChecked)
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.Machine (SlotField)
open Tools.ShippingMachineEntry
open Tools.ShippingEntrySoundness (weOf)

/-- **PROVED**: `MachineWired` exports the slot-register widths for its own `regs` (any machine, with or without calls). -/
theorem slotWidths_of_wired {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (hW : MachineWired declName shape ids cache m dsn regs lets) :
    ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
      shape.layout.slots[k]? = some f → weOf m r = f.width := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hwd⟩ := hW
  exact hwd

/-- **PROVED**: the width link for the shipped `b`: every slot's width is at most the declared width of its register. -/
theorem hWd_of_wired {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m b : Module} {dsn : Design} {regs lets : List String}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule m ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m))
    (hgate : hierGate b = true)
    (houtTy : ∀ o ∈ shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : MachineWired declName shape ids cache m dsn regs lets) :
    ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
      shape.layout.slots[k]? = some f → f.width ≤ declWidth b r := by
  have hwd := slotWidths_of_wired hW
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hclean, -⟩ := hW
  obtain ⟨-, hw, -, -⟩ := hclean houtTy
  have hI : Tools.ShippingMachineShipsHier.hasInst b :=
    Tools.ShippingGuardsSound.hasInst_of_hierGate hgate
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule m := by
    rcases hpost with h | h
    · exact h
    · exact Tools.ShippingMachineShipsHier.mergeChecked_inst h hI
  have hbW : declWidth b = weOf m := by rw [hbr]; exact hw
  intro k r f hr hf
  rw [hbW]
  exact Nat.le_of_eq (hwd k r f hr hf).symm

end Tools.ShippingSrm32

#print axioms Tools.ShippingSrm32.slotWidths_of_wired
#print axioms Tools.ShippingSrm32.hWd_of_wired
