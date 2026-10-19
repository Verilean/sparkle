import Tools.ShippingChecksCore
import Tools.ShippingChecksDepthGate
import Tools.ShippingMachineRanBase
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # `outsCheck` at the core run's design under the GATE (isolated branch `fix/opt-fallback`)

`Tools.ShippingChecksCore.core_outsCheck_all` asks `hierBinds b = true`
(given by `shipsHierCheck` in the heads that keep that antecedent). The
heads WITHOUT `shipsHierCheck` have no `hierBinds b`; they have the
statement-kind gate `hierGate b` (a field of
`Tools.ShippingGuardsSound.RunFacts`, derived from the core run by
`core_hierGate`).

* `core_outsCheck_all_gate`: `core_outsCheck_all` with `hierGate b` in place
  of `hierBinds b`. Statement and proof are the original's, COPIED, with
  `outsCheck_opt_all_gate` in place of `outsCheck_opt_all`; the original is
  not changed. If the original changes, this copy does not follow.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksCoreGate
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

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_outsCheck_all_gate` over `MachineRan`:
the proof of the built theorem, MOVED here (split in place, branch
`fix/ran-threading-split`) with the run, the reflection, the closing and the boundary
replaced by `ran` and every callee of the chain by its `_ran` form. It takes of the run only
that the machine synthesis this core run performed returned the result from an invariant
world; the theorem below, its statement unchanged, is the instance at the all-worlds closing
(`Tools.ShippingMachineRan.machineRan_of_closes`). -/
theorem core_outsCheck_all_gate_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y.2.modules, g2.name = mn)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) (n : Nat) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true := by
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
  refine Tools.ShippingChecksDepthGate.outsCheck_opt_all_gate hg ?_ ?_ ?_ n
  · intro mn iname conns hm
    rw [hbody'] at hm
    exact hresM mn iname conns hm
  · intro g hg
    obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD g hg
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidA k hk y hre).1
    · exact (hkidA k hk y hre).2 g hin
  · intro g hg mn iname conns hm
    obtain ⟨k, hk, y, hre, hor, hnm⟩ := hrealD g hg
    have hg' : g ∈ y.1 :: y.2.modules := by
      rcases hor with heq | hin
      · rw [heq]
        exact List.Mem.head _
      · exact List.Mem.tail _ hin
    obtain ⟨g2, hg2, hn2⟩ := hkidR k hk y hre g hg' mn iname conns hm
    obtain ⟨g', hg'D, hn'⟩ := hnm g2 (List.Mem.tail _ hg2)
    exact Tools.ShippingChecksDepth.resolves_by_name ⟨g', hg'D, hn'.trans hn2⟩

set_option maxHeartbeats 4000000 in
/-- **`outsCheck` of the printed module of a machine with calls, on the core
run's design, at every depth, under the statement-kind gate** (no
`hierBinds`). -/
theorem core_outsCheck_all_gate {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y.2.modules, g2.name = mn)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) (n : Nat) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true :=
  core_outsCheck_all_gate_ran d ok hbody hC hslots hdomB hins outTy hnomem hkidA hkidR hpost
    (Tools.ShippingMachineRan.machineRan_of_closes hcore entry hB closes) hg n

end Tools.ShippingChecksCoreGate
