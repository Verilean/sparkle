import Tools.ShippingMachineRan

variable {tenv : Lean.Environment}

/-! # `RanAt`: the run's machine synthesis as a conjunct of the run boundary (round par/g-1)

WRITTEN, NOT BUILT. NEW file; no built file is edited by it.

The check-free head `Tools.ShippingNoPorts.machine_design_noPorts` is
parametric in the closing predicate `C` and in the run boundary `Bnd`
(`Tools.ShippingMachineShipsHier.CtxBnd`: a predicate of the run's contexts,
its start world, and the CORE run's module and design). Every hypothesis of
the head receives `Bnd mctx mref cctx cref w raw D` together with a core run
from `w` returning `(raw, D)`. So what the design-level chain takes of the
closing — `Tools.ShippingMachineRan.MachineRan … raw D`, "the machine
synthesis this core run performed returned `(raw, D)`" — can be carried by
the boundary, with `C := fun _ _ _ _ => True`:

    RanAt mctx mref cctx cref c shape w M D :=
      ∀ w1, RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 →
        MachineRan mctx mref cctx cref c shape M D

`RanAt` is stated for EVERY result `(M, D)` of a core run from `w`, so it can
be proved without knowing the witnesses the head's conclusion hides
(`∃ raw D, …`). Two producers:

* `ranAt_of_closes`: from the all-worlds `MachineClosesAt` and `ChildBnd w`
  (the premise of every built endpoint);
* `ranAt_outermost`: from a depth-0 start (`Start0 mref cref w`) and a
  closing at `Prov` worlds only — NO `MachineClosesAt`.

Nothing here is a fact about the compiler beyond
`Tools.ShippingMachineRan.machineRan_of_closes` / `machineRan_outermost`
(BUILT). -/
namespace Tools.ShippingOutermost
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv
open Tools.ShippingMachineRan
open Tools.ShippingCacheCoherentRun (Prov)

/-- **Every core run from `w` returning `(M, D)` performed a machine
synthesis that returned `(M, D)`** from an invariant world of positive
depth. -/
def RanAt (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (c : Name) (shape : MachineShape) (w : Void IO.RealWorld)
    (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  ∀ w1 : Void IO.RealWorld,
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1 →
    MachineRan mctx mref cctx cref c shape M D

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `RanAt` at a core run. -/
theorem RanAt.ran {c : Name} {shape : MachineShape} {w : Void IO.RealWorld}
    {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : RanAt mctx mref cctx cref c shape w M D) {w1 : Void IO.RealWorld}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1) :
    MachineRan mctx mref cctx cref c shape M D :=
  h w1 hcore

/-- **`RanAt` from the all-worlds closing** and the child boundary of the
start world: what the built endpoints assume gives it. -/
theorem ranAt_of_closes {c : Name} {shape : MachineShape} {w : Void IO.RealWorld}
    (entry : MachineDefines mctx mref cctx cref c shape)
    (hB : ChildBnd mref cref w)
    (closes : MachineClosesAt mctx mref cctx cref c shape)
    (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) :
    RanAt mctx mref cctx cref c shape w M D :=
  fun _ hcore => machineRan_of_closes hcore entry hB closes

/-- **`RanAt` at an OUTERMOST start**: from `Start0 mref cref w` and a
closing at `Prov` worlds only (`hclose`). No `MachineClosesAt`. -/
theorem ranAt_outermost {c : Name} {shape : MachineShape} {w : Void IO.RealWorld}
    (entry : MachineDefines mctx mref cctx cref c shape)
    (h0 : Start0 mref cref w)
    (hclose : ∀ {tenv : Lean.Environment} (L : RefLaws mref cref) (b : Bool)
      (w9 : Void IO.RealWorld) (r : Option Res)
      (w10 : Void IO.RealWorld), InvV L w9 → L.dval w9 ≠ 0 → Prov (L.val w9) →
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
        mctx mref cctx cref w9 r w10 → r ≠ none)
    (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) :
    RanAt mctx mref cctx cref c shape w M D :=
  fun _ hcore => machineRan_outermost hcore entry h0 hclose

end Tools.ShippingOutermost
