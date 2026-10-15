import Tools.ShippingMemOnly
import Tools.ShippingReaderOutsInv

/-! # Two generated premises of `#machine_no_ports_mem` discharged in general

WRITTEN, NOT BUILT (branch `par/r-1`; record `docs/parallel/R-reader-outs-inv.md`).
No `sorry`, no axiom, no `native_decide`. A leaf: nothing depends on it.

`#machine_no_ports_mem f` (`Tools/ShippingNoPortsMemCommand.lean`) decides,
per declaration, `f.noPortsMem_outTy` and `f.noPortsMem_outScalar` on the
reflected data and packs them into `MemOnlyData`; its four run theorems
(`runFacts`, `outsG0`, `kidsMemG`, `designP0`) use `MemOnlyData` together
with `hcore` and `entry`. `MemOnlyDataR` is `MemOnlyData` WITHOUT those two
fields; the four `…_of_reader` theorems below have the SAME conclusions and
the SAME run hypotheses as `memOnly_runFacts` / `memOnly_outsCheck` /
`memOnly_kidsMem` / `memOnly_designCheck`, and supply the two fields from
`Tools.ShippingReaderOutsInv.outTy_of_core` / `outScalar_of_core` — a
general theorem about every reader result, no evaluation.

The generator is NOT changed here (no existing statement changes): using
these theorems, it would stop emitting the two `decide`s. -/
namespace Tools.ShippingReaderOutsMemOnly
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingChildInv
open Tools.ShippingMemOnly Tools.ShippingMemKid
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Sparkle.Compiler.MachMemory (memModule memChild?)
open Tools.ShippingReaderOutsInv (outTy_of_core outScalar_of_core)

/-- `MemOnlyData` without `outTy` and `outScalar` (the field types are the
same text). -/
structure MemOnlyDataR (d : MachineData) (nDecl aw dw : Nat) : Prop where
  ok : d.ok = true
  body : d.shape.body = quote d.dom
    (fun j => inputExpr d.shape.binders.length (d.bpos j))
    (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  calls : d.callsOk nDecl = true
  slots : d.ss.length = d.shape.layout.slots.length
  domB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain
  ins : d.shape.insts ≠ []
  sl : d.shape.layout.slots ≠ []
  fne : d.shape.instFields ≠ []
  mem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
    ∃ cb, memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw)
  cw : Tools.ShippingCallWidths.callWidthsOk d nDecl (fun _ => memOuts dw) = true
  args : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl (fun _ => memIns aw dw) = true
  outNames : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name

/-- The full data from the reduced data and the two output facts. -/
theorem MemOnlyDataR.toData {d : MachineData} {nDecl aw dw : Nat} (h : MemOnlyDataR d nDecl aw dw)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (outScalar : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    MemOnlyData d nDecl aw dw :=
  ⟨h.ok, h.body, h.calls, h.slots, h.domB, h.ins, h.sl, h.fne, outTy, h.mem, h.cw, h.args,
    h.outNames, outScalar⟩

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `MemOnlyData` inside a run of the real entry, from `MemOnlyDataR`: the
two output facts come from the reader (`outTy_of_core`, `outScalar_of_core`). -/
theorem memOnlyData_of_reader {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyDataR d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (entry : MachineDefines mctx mref cctx cref c d.shape) :
    MemOnlyData d nDecl aw dw :=
  h.toData (outTy_of_core hcore entry) (outScalar_of_core hcore entry)

/-- `memOnly_runFacts` without `outTy` / `outScalar` premises. -/
theorem memOnly_runFacts_of_reader {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyDataR d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  memOnly_runFacts (memOnlyData_of_reader h hcore entry) hB hcore hpost entry closes

/-- `memOnly_outsCheck` without `outTy` / `outScalar` premises. -/
theorem memOnly_outsCheck_of_reader {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyDataR d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) 0 (checkedOptimize b) = true :=
  memOnly_outsCheck (memOnlyData_of_reader h hcore entry) hB hcore hpost entry closes hg

/-- `memOnly_kidsMem` without `outTy` / `outScalar` premises. -/
theorem memOnly_kidsMem_of_reader {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyDataR d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineShipsHier.kidsMem (childMap D.modules) b.body = true :=
  memOnly_kidsMem (memOnlyData_of_reader h hcore entry) hB hcore hpost entry closes

/-- `memOnly_designCheck` without `outTy` / `outScalar` premises. -/
theorem memOnly_designCheck_of_reader {c : Name} {d : MachineData} {nDecl aw dw : Nat}
    (h : MemOnlyDataR d nDecl aw dw)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) 0 (checkedOptimize b) = true :=
  memOnly_designCheck (memOnlyData_of_reader h hcore entry) hB hcore hpost entry closes

end Tools.ShippingReaderOutsMemOnly
