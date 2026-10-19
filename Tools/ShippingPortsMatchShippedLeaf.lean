import Tools.ShippingPortsMatchRawLeaf
import Tools.ShippingPortsMatchShipped
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # `portsMatchB` of the SHIPPED module, for a parent of LEAF register machines (G1, round par/a-4)

The composition of two theorems built on poc:

* `Tools.ShippingPortsMatchRawLeaf.core_portsMatch_raw_leaf` — `portsMatchB`
  of the full entry's module `b` BEFORE the optimizer, from the core run, the
  reflections, the closings and data conditions (no hypothesis about a
  module);
* `Tools.ShippingPortsMatchShipped.portsMatchB_shipped` — under the
  statement-kind gate `hierGate b`, `portsMatchB C b` gives
  `portsMatchB C (checkedOptimize b)` (through the fifth guard `connsKept`
  of `keepGuarded`: a kept candidate declares every connected wire at the
  width the input module gives it, otherwise the input module is shipped).

The gate is `Tools.ShippingChecksWidths.core_hierGate` at the same run, as in
`Tools.ShippingTextShipped.core_text_shipped`.

`core_portsMatch_shipped_leaf` has EXACTLY the hypotheses of
`core_portsMatch_raw_leaf` (statement copied; `hfne` is already one of them
and is what the gate asks besides). Its conclusion is the last compiler-check
premise of the depth endpoints of `parent` and `chained`
(`Tests/Compiler/NoKidsTest.lean`: gap `gap_portsMatchB`).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingPortsMatchShippedLeaf
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingPortsMatchRawLeaf (LeafKid)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`portsMatchB` of the SHIPPED module of a parent of leaf register
machines**: from the runs, the reflections, the closings and data conditions
only (`core_portsMatch_raw_leaf`'s hypotheses, unchanged). -/
theorem core_portsMatch_shipped_leaf {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    -- the parent has slots (its own clock and reset)
    (hsl : d.shape.layout.slots ≠ [])
    -- every call entry's callee is a leaf register machine
    (kid : Nat → MachineData)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      LeafKid mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
    -- the two width conditions on the declarations' data
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl
      (fun k => (kid k).shape.layout.outs) = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl
      (fun k => Tools.ShippingPortWidthsPure.declWidths (kid k)) = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) = true :=
  Tools.ShippingPortsMatchShipped.portsMatchB_shipped
    (Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy hnomem
      hB hcore hpost entry closes)
    (Tools.ShippingPortsMatchRawLeaf.core_portsMatch_raw_leaf d ok hbody hC hslots hdomB hins
      hfne outTy hnomem hsl kid hkid hcw hargs hB hcore hpost entry closes hon hoty)

end Tools.ShippingPortsMatchShippedLeaf
