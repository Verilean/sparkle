import Tools.ShippingSlotlessClk
import Tools.ShippingKidFacts

/-! # The run hypotheses of the no-ports head for a parent with a register OR a sequential child (G1, unit U5a, round par/a-20)

Of the four run hypotheses of `Tools.ShippingNoPorts.machine_design_noPorts`
that `Tools/ShippingKidFacts.lean` proves from `KidFacts` of every call
entry's callee, two ask the parent's register (`hsl`):

    kids_runFacts      → core_runFacts → core_raw_facts          ("rst" an input)
    kids_designCheck   → core_clk                                 (weS b "clk" = 1 ∧ weS b "rst" = 1)
                       → core_designCheck_run → core_runFacts

`kids_outsCheck` and `kids_maskedN` have no such hypothesis. This file
states the two (and the two general theorems between) with `hsl` replaced
by

    hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d

(`Tools.ShippingSlotlessClk.SeqKid`: some call entry's real children are
sequential), from `core_raw_factsS` / `core_clkS`:

* `core_runFactsS`, `core_designCheck_runS` — `core_runFacts`,
  `core_designCheck_run`;
* `kids_runFactsS`, `kids_designCheckS` — `kids_runFacts`,
  `kids_designCheck`.

The bodies are the built theorems' bodies with the two `…S` facts in place
of `core_raw_facts` / `core_clk`; every other theorem applied is BUILT and
has no hypothesis on the slots (`core_hierGate`, `core_linkedWF`,
`core_outsExtracted`, `core_instOutWidthsOk`, `core_closed_typedIn`,
`core_portsMatch_raw`, `portsMatchB_shipped`, `core_kidsPass_deep`,
`core_designCheck_rest2`). The statements with a register are re-derived
from the new ones (`kids_runFacts_again`, `kids_designCheck_again`: the
first disjunct) — which shows the new statements are generalisations; it is
NOT an independent proof of the register case, since `core_raw_factsS` /
`core_clkS` apply the built theorems there.

NO head changes: `machine_ships_hierC` / `machine_design_noPorts` take the
run's facts as a hypothesis (`RunFacts.rst`), not the slots.

WRITTEN, NOT BUILT. -/
namespace Tools.ShippingSlotlessKidFacts
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
open Tools.ShippingSlotlessClk (SeqKid)
open Tools.ShippingKidFacts (KidFacts)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The run's facts of the full entry's module** of a machine with calls
closed by `closeInstsG`, with a register OR a sequential child
(`core_runFacts` with `core_raw_factsS`). -/
theorem core_runFactsS {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d)
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨hrst, hndB, hself⟩ :=
    Tools.ShippingSlotlessClk.core_raw_factsS d ok hbody hC hslots hdomB hins hck hfne outTy
      hnomem hB hcore hpost entry closes
  exact
    { gate := Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hB hcore hpost entry closes
      wfB := Tools.ShippingLinkedFresh.core_linkedWF d ok hbody hC hslots hdomB hins outTy hnomem
        hB hcore hpost entry closes
      ndB := hndB
      self := hself
      outs := Tools.ShippingChecksOuts.core_outsExtracted d ok hbody hC hslots hdomB hins hfne
        outTy hnomem hkidP hB hcore hpost entry closes
      rst := hrst
      wid := Tools.ShippingChecksWidths.core_instOutWidthsOk d ok hbody hC hslots hdomB hins hfne
        outTy hnomem hkidP hkidW hB hcore hpost entry closes }

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the shipped module from the core run**, with a
register OR a sequential child (`core_designCheck_run` with
`core_runFactsS`): the connection widths and the children's check are left. -/
theorem core_designCheck_runS {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d)
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (n : Nat)
    (hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) = true)
    (hkids : Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true :=
  Tools.ShippingTextShipped.core_designCheck_rest2
    (core_runFactsS d ok hbody hC hslots hdomB hins hck hfne outTy
      hnomem hkidP hkidW hB hcore hpost entry closes)
    (Tools.ShippingClosedTyped.core_closed_typedIn d ok hbody hC hslots hdomB hins outTy hnomem
      hB hcore hpost entry closes hon hoty)
    n hports hkids

/-- **The run's facts of the full entry's module**, from `KidFacts` of every
call entry's callee, for a parent with a register OR a sequential child
(`kids_runFacts` with `core_runFactsS`). -/
theorem kids_runFactsS {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d)
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  core_runFactsS d ok hbody hC hslots hdomB hins hck hfne outTy
    hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    (Tools.ShippingCallWidths.hkidW_of_data hcw (fun k hk y hy => (hkid k hk).outTys y hy))
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the shipped module at depth `n` with NO check
premise**, from `KidFacts`, for a parent with a register OR a sequential
child (`kids_designCheck` with `core_clkS` and `core_designCheck_runS`). -/
theorem kids_designCheckS {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hck : d.shape.layout.slots ≠ [] ∨ SeqKid mref cref d)
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  have hkidW := Tools.ShippingCallWidths.hkidW_of_data hcw
    (fun k hk y hy => (hkid k hk).outTys y hy)
  have hraw : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true :=
    Tools.ShippingPortsMatchRaw.core_portsMatch_raw d ok hbody hC hslots hdomB hins hfne outTy
      hnomem hkidW
      (fun k hk y hy => (hkid k hk).portsIn y hy)
      (kidIns := kidIns) hargs
      (fun k hk y hy j q hq => (hkid k hk).inW y hy j q hq)
      (fun k hk y hy hs => (hkid k hk).clk y hy hs)
      hB hcore hpost entry closes hon hoty
      (Tools.ShippingSlotlessClk.core_clkS d ok hbody hC hslots hdomB hins hfne outTy hnomem hck
        hB hcore hpost entry closes)
  have hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) =
      true :=
    Tools.ShippingPortsMatchShipped.portsMatchB_shipped
      (Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hB hcore hpost entry closes)
      hraw
  have hkids := Tools.ShippingKidsSelf.core_kidsPass_deep d ok hbody hC hslots hdomB hins hfne
    outTy hnomem n
    (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2)
    hB hcore hpost entry closes
  exact core_designCheck_runS d ok hbody hC hslots hdomB hins hck hfne
    outTy hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    hkidW hB hcore hpost entry closes hon hoty n hports hkids

/-! ## The statements with a register, re-derived (the first disjunct) -/

/-- `Tools.ShippingKidFacts.kids_runFacts`, from `kids_runFactsS`. -/
theorem kids_runFacts_again {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  kids_runFactsS d ok hbody hC hslots hdomB hins (Or.inl hsl) hfne outTy hnomem kidOuts kidIns n
    hkid hcw hB hcore hpost entry closes

/-- `Tools.ShippingKidFacts.kids_designCheck`, from `kids_designCheckS`. -/
theorem kids_designCheck_again {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true :=
  kids_designCheckS d ok hbody hC hslots hdomB hins (Or.inl hsl) hfne outTy hnomem kidOuts kidIns
    n hkid hcw hargs hB hcore hpost entry closes hon hoty

end Tools.ShippingSlotlessKidFacts
