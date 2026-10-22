import Tools.ShippingSrm4Core6
import Tools.ShippingSeqParentKidFactsA
-- UNBUILT (unit SRM4): see REPORT-SRM4.md for the run names and exits.
-- SCOPE (binding, residue R5): the parent-side consumers of the callees' facts WITHOUT the `check` field: `kidsA_runFacts` / `kidsA_outsCheck` / `kidsA_maskedN` of `Tools/ShippingSeqParentKidFactsA.lean` with `KidFactsNC`
-- (`Tools/ShippingSrm4Core6.lean`: `KidFactsA` minus `check`, which is unsatisfiable for a design with a memory module, `Tools/ShippingSrm4Check.lean`) in place of `KidFactsA`, and `kidsNC_designCheck_of_kidsPass`: the parent's
-- `designCheck` with EVERYTHING derived except the children's check, which is the NAMED premise `hkids` (`kidsPass … (kidCheck … n) … = true`, the conclusion of `core_kidsPass_deep_ranA`).
-- The parent's OWN entries are ordinary calls (`hnomem` of the parent), so the `hnomem`-bearing `core_*_ranA` apply to it; only the CALLEES may have a memory child.
-- PREMISES kept (named): `ran` (`MachineRanA` of the parent), `hkid` (`KidFactsNC` of every call entry's callee), the parent's decidable data, and for `designCheck` the children's check `hkids` (OPEN for a design with a memory module: needs the
-- height-indexed check, see `Tools/ShippingSrm4Check.lean`).  `RealChildA` is a history of past synthesis results, not freshness or runtime fit.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field, no heartbeat option.

namespace Tools.ShippingSrm4Parent
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingChildInv
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingSrm4Core6

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`RunFacts`** of the run's module from `KidFactsNC` of every callee. -/
theorem kidsNC_runFacts (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsNC O (d.shape.insts[k]).1 (kidOuts k) (kidIns k))
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

/-- **`outsCheck` at depth `n`** (under the statement-kind gate) from `KidFactsNC` of every callee. -/
theorem kidsNC_outsCheck (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
      KidFactsNC O (d.shape.insts[k]).1 (kidOuts k) (kidIns k))
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

/-- **`kidsMaskedN`** of the run's design from `KidFactsNC.masked` of every callee. -/
theorem kidsNC_maskedN (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsNC O (d.shape.insts[k]).1 (kidOuts k) (kidIns k))
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidsSelfA.core_kidsMaskedN_top_ranA O d ok hbody hC hslots hdomB hins hfne outTy hnomem
    (fun k hk y hy => (hkid k hk).masked y hy) hpost ran

/-- **`designCheck` at depth `n` from `KidFactsNC` of every callee and the children's check `hkids`** (everything but the children's check DERIVED: `RunFacts`, typedness, `portsMatchB` by `core_portsMatch_raw_ranA` +
`core_clk_ranA` through `portsMatchB_shipped`).  `hkids` is the conclusion of `core_kidsPass_deep_ranA`; for a design with a memory module it cannot come from `KidFactsA.check` (`Tools.ShippingSrm4Check`) and is the
OPEN residue. -/
theorem kidsNC_designCheck_of_kidsPass (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
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
      KidFactsNC O (d.shape.insts[k]).1 (kidOuts k) (kidIns k))
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (hkids : Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n) (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  have hkidW := Tools.ShippingParentRunFactsA.hkidW_of_dataA O hcw (fun k hk y hy => (hkid k hk).outTys y hy)
  exact Tools.ShippingTextShipped.core_designCheck_rest2
    (kidsNC_runFacts O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem kidOuts kidIns hkid hcw hpost ran)
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
    hkids

end Tools.ShippingSrm4Parent

#print axioms Tools.ShippingSrm4Parent.kidsNC_runFacts
#print axioms Tools.ShippingSrm4Parent.kidsNC_outsCheck
#print axioms Tools.ShippingSrm4Parent.kidsNC_maskedN
#print axioms Tools.ShippingSrm4Parent.kidsNC_designCheck_of_kidsPass
