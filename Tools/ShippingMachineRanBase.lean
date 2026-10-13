import Tools.ShippingChildRun

/-! # `MachineRan` and its producer from the all-worlds closing, in an EARLY file (round par/g-1)

WRITTEN, NOT BUILT. The two declarations below are MOVED here, name,
namespace, statement and proof unchanged, from `Tools/ShippingMachineRan.lean`
(BUILT, round par/a-43), which imports `Tools.ShippingKidsSelf`. The base
lemmas of the design-level chain (`Tools/ShippingChecksCore.lean`, …,
`Tools/ShippingKidsSelf.lean`, `Tools/ShippingMachineTraceX.lean`) are split
into a tail over `MachineRan` and a corollary from `machineRan_of_closes`;
they sit BELOW `ShippingKidsSelf` in the import order, so the definition and
its first producer must sit below them: this file imports
`Tools.ShippingChildRun` only (where `machine_run_of_core`, `MachineClosesAt`,
`InvW`, `DepthPos`, `ChildBnd` are).

`Tools/ShippingMachineRan.lean` now imports this file and keeps `Start0`,
`Start0.childBnd`, `machineRan_outermost` (which needs
`Tools.ShippingCacheCoherentOuter`), `core_kids_self_ran` and
`core_kids_self_of_closes`. Every full name is what it was. -/
namespace Tools.ShippingMachineRan
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv
open Sparkle.IR.AST (Design)

/-- **The machine synthesis a core run performs returned the run's result**,
from an invariant world of positive depth. -/
def MachineRan (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (c : Name) (shape : MachineShape) (M : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) c shape)
      mctx mref cctx cref w9 (some (M, D)) w10 ∧
    InvW mref cref w9 ∧ DepthPos mref cref w9

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`MachineRan` from the all-worlds closing** — the three lines every base
lemma of the design-level chain starts with, once. -/
theorem machineRan_of_closes {c : Name} {shape : MachineShape}
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c shape)
    (hB : ChildBnd mref cref w)
    (closes : MachineClosesAt mctx mref cctx cref c shape) :
    MachineRan mctx mref cctx cref c shape M D := by
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ := machine_run_of_core hcore entry hB
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have hres' := hres res rfl
    subst hres'
    exact ⟨bb, w9, w10, hrun9, hw9, hd9⟩

end Tools.ShippingMachineRan
