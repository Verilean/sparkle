import Tools.ShippingSeqChildDeepKidFactsA
import Tools.ShippingParentPortsA
import Tools.ShippingKidsSelfA
import Tools.ShippingParentDesignFA
import Tools.ShippingParentTailsA
-- BUILT (unit SR3r): r4 exit 0.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit SR3r: the parent-side consumer of `KidFactsA`

The four parent obligations of the check-free depth chain (`RunFacts`, `outsCheck`, `kidsMaskedN`, `designCheck`) of a machine
with calls, over `MachineRanA O` (the run), from `KidFactsA O` of every call entry's callee (`Tools.ShippingSeqChildDeepKidFactsA`)
and the parent's data conditions.  They are the `RealChildA` / `MachineRanA` analogues of `Tools.ShippingKidFacts.kids_*_ran`
(the old theorems are unchanged; no `KidFacts`, `ChildBnd`, `StartV`, `GenKid` in the closure).

* `kidsA_runFacts`, `kidsA_outsCheck`, `kidsA_maskedN`, `kidsA_designCheck`: PROVED (relative to `ran`, `hkid`, data).
  `kidsA_designCheck` takes the children's check from `KidFactsA.check` in its `ms`-quantified form (via
  `core_kidsPass_deep_ranA`), NOT the leaf form `∀ C n` of `core_designCheck_ranFA`; this is what a callee with instances needs.
`RealChildA` is a history of past synthesis results, not freshness, not runtime fit. -/

namespace Tools.ShippingSeqParentKidFactsA
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
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingCallsChildPorts (CallsPorts argWidths)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingSeqChildDeepConsumerA Tools.ShippingSeqChildDeepFactsA
open Tools.ShippingSeqChildDeepKidFactsA (KidFactsA)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`RunFacts`** of the run's module from `KidFactsA` of every callee. -/
theorem kidsA_runFacts (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsA O (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingParentRunFactsA.core_runFacts_ranA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    (Tools.ShippingParentRunFactsA.hkidW_of_dataA O hcw (fun k hk y hy => (hkid k hk).outTys y hy))
    hpost ran

/-- **`outsCheck` at depth `n`** (under the statement-kind gate) from `KidFactsA` of every callee. -/
theorem kidsA_outsCheck (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsA O (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true :=
  Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA O d ok hbody hC hslots hdomB hins outTy hnomem
    (fun k hk y hy => (hkid k hk).kidA y hy)
    (fun k hk y hy => (hkid k hk).kidR y hy)
    hpost ran hg n

/-- **`kidsMaskedN`** of the run's design from `KidFactsA.masked` of every callee. -/
theorem kidsA_maskedN (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsA O (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidsSelfA.core_kidsMaskedN_top_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem
    (fun k hk y hy => (hkid k hk).masked y hy) hpost ran

set_option maxHeartbeats 4000000 in
/-- **`designCheck` at depth `n`** from `KidFactsA` of every callee: `portsMatchB` by `core_portsMatch_raw_ranA` +
`core_clk_ranA` through `portsMatchB_shipped`; the children's check from `KidFactsA.check` (`ms`-quantified form,
`core_kidsPass_deep_ranA`) — no check premise beyond the callees' bundles. -/
theorem kidsA_designCheck (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsA O (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  have hkidW := Tools.ShippingParentRunFactsA.hkidW_of_dataA O hcw (fun k hk y hy => (hkid k hk).outTys y hy)
  exact Tools.ShippingTextShipped.core_designCheck_rest2
    (kidsA_runFacts O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem kidOuts kidIns n hkid hcw hpost ran)
    (Tools.ShippingParentTailsA.core_closed_typedIn_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran hon hoty)
    n
    (Tools.ShippingPortsMatchShipped.portsMatchB_shipped
      (Tools.ShippingParentDesignA.core_hierGate_anyA O d ok hbody hC hslots hdomB hins outTy hnomem hpost ran)
      (Tools.ShippingParentDesignFA.core_portsMatch_raw_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidW
        (fun k hk y hy => (hkid k hk).portsIn y hy) hargs
        (fun k hk y hy j q hq => (hkid k hk).inW y hy j q hq)
        (fun k hk y hy hs => (hkid k hk).clk y hy hs)
        hpost ran hon hoty
        (Tools.ShippingParentDesignFA.core_clk_ranA O d ok hbody hC hslots hdomB hins outTy hnomem hsl hpost ran)))
    (Tools.ShippingKidsSelfA.core_kidsPass_deep_ranA O d ok hbody hC hslots hdomB hins outTy hnomem n
      (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2) hpost ran)

end Tools.ShippingSeqParentKidFactsA
